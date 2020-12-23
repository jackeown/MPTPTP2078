%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:37 EST 2020

% Result     : CounterSatisfiable 0.13s
% Output     : Saturation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 347 expanded)
%              Number of clauses        :   61 ( 128 expanded)
%              Number of leaves         :    9 (  83 expanded)
%              Depth                    :    9
%              Number of atoms          :  273 (2839 expanded)
%              Number of equality atoms :    4 ( 172 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t62_yellow_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_yellow_0(X2,X1)
            & m1_yellow_0(X2,X1) )
         => ! [X3,X4] :
              ( m1_subset_1(X4,u1_struct_0(X1))
             => ! [X5] :
                  ( m1_subset_1(X5,u1_struct_0(X2))
                 => ( X5 = X4
                   => ( ( r1_lattice3(X1,X3,X4)
                       => r1_lattice3(X2,X3,X5) )
                      & ( r2_lattice3(X1,X3,X4)
                       => r2_lattice3(X2,X3,X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_yellow_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(d8_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r1_lattice3(X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r1_orders_2(X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(d9_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r2_lattice3(X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r1_orders_2(X1,X4,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_yellow_0(X2,X1)
              & m1_yellow_0(X2,X1) )
           => ! [X3,X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ! [X5] :
                    ( m1_subset_1(X5,u1_struct_0(X2))
                   => ( X5 = X4
                     => ( ( r1_lattice3(X1,X3,X4)
                         => r1_lattice3(X2,X3,X5) )
                        & ( r2_lattice3(X1,X3,X4)
                         => r2_lattice3(X2,X3,X5) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t62_yellow_0])).

fof(c_0_10,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X8,X9)
      | v1_xboole_0(X9)
      | r2_hidden(X8,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & l1_orders_2(esk3_0)
    & ~ v2_struct_0(esk4_0)
    & v4_yellow_0(esk4_0,esk3_0)
    & m1_yellow_0(esk4_0,esk3_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk7_0,u1_struct_0(esk4_0))
    & esk7_0 = esk6_0
    & ( r2_lattice3(esk3_0,esk5_0,esk6_0)
      | r1_lattice3(esk3_0,esk5_0,esk6_0) )
    & ( ~ r2_lattice3(esk4_0,esk5_0,esk7_0)
      | r1_lattice3(esk3_0,esk5_0,esk6_0) )
    & ( r2_lattice3(esk3_0,esk5_0,esk6_0)
      | ~ r1_lattice3(esk4_0,esk5_0,esk7_0) )
    & ( ~ r2_lattice3(esk4_0,esk5_0,esk7_0)
      | ~ r1_lattice3(esk4_0,esk5_0,esk7_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])).

fof(c_0_12,plain,(
    ! [X15] :
      ( v2_struct_0(X15)
      | ~ l1_struct_0(X15)
      | ~ v1_xboole_0(u1_struct_0(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_13,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

fof(c_0_15,plain,(
    ! [X17,X18,X19,X20] :
      ( ( ~ r1_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r2_hidden(X20,X18)
        | r1_orders_2(X17,X19,X20)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ l1_orders_2(X17) )
      & ( m1_subset_1(esk1_3(X17,X18,X19),u1_struct_0(X17))
        | r1_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ l1_orders_2(X17) )
      & ( r2_hidden(esk1_3(X17,X18,X19),X18)
        | r1_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ l1_orders_2(X17) )
      & ( ~ r1_orders_2(X17,X19,esk1_3(X17,X18,X19))
        | r1_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ l1_orders_2(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).

cnf(c_0_16,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_17,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | r2_hidden(esk6_0,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

fof(c_0_19,plain,(
    ! [X16] :
      ( ~ l1_orders_2(X16)
      | l1_struct_0(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_20,plain,(
    ! [X22,X23,X24,X25] :
      ( ( ~ r2_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ r2_hidden(X25,X23)
        | r1_orders_2(X22,X25,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ l1_orders_2(X22) )
      & ( m1_subset_1(esk2_3(X22,X23,X24),u1_struct_0(X22))
        | r2_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ l1_orders_2(X22) )
      & ( r2_hidden(esk2_3(X22,X23,X24),X23)
        | r2_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ l1_orders_2(X22) )
      & ( ~ r1_orders_2(X22,esk2_3(X22,X23,X24),X24)
        | r2_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ l1_orders_2(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

cnf(c_0_21,plain,
    ( r1_orders_2(X1,X3,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

cnf(c_0_22,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(esk3_0))
    | ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_24,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19]),
    [final]).

cnf(c_0_25,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20]),
    [final]).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_27,negated_conjecture,
    ( esk7_0 = esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_28,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk6_0)
    | ~ r1_lattice3(esk3_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(esk6_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_14]),c_0_22])]),
    [final]).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_22])]),
    [final]).

fof(c_0_30,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,X7)
      | m1_subset_1(X6,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_31,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

cnf(c_0_32,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,X1)
    | ~ r2_lattice3(esk3_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(esk6_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_14]),c_0_22])]),
    [final]).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27]),
    [final]).

cnf(c_0_34,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk6_0)
    | ~ r1_lattice3(esk3_0,u1_struct_0(esk3_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29]),
    [final]).

cnf(c_0_35,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30]),
    [final]).

cnf(c_0_36,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk6_0)
    | r2_hidden(esk1_3(esk3_0,X1,esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_14]),c_0_22])]),
    [final]).

cnf(c_0_37,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20]),
    [final]).

cnf(c_0_38,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,X1)
    | ~ r2_lattice3(esk3_0,u1_struct_0(esk3_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_29]),
    [final]).

cnf(c_0_39,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20]),
    [final]).

cnf(c_0_40,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk6_0,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_33]),
    [final]).

cnf(c_0_41,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_42,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk6_0)
    | ~ r1_lattice3(esk3_0,u1_struct_0(esk3_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_14]),
    [final]).

cnf(c_0_43,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,X1,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36]),
    [final]).

cnf(c_0_44,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | r2_hidden(esk2_3(esk3_0,X1,esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_14]),c_0_22])]),
    [final]).

cnf(c_0_45,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk6_0)
    | ~ r2_lattice3(esk3_0,u1_struct_0(esk3_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_14]),
    [final]).

cnf(c_0_46,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk2_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_14]),c_0_22])]),
    [final]).

cnf(c_0_47,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk2_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20]),
    [final]).

cnf(c_0_48,plain,
    ( r1_lattice3(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,esk1_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

cnf(c_0_49,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(esk4_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_40]),c_0_41]),
    [final]).

fof(c_0_51,plain,(
    ! [X12,X13,X14] :
      ( ~ r2_hidden(X12,X13)
      | ~ m1_subset_1(X13,k1_zfmisc_1(X14))
      | m1_subset_1(X12,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_52,plain,(
    ! [X10,X11] :
      ( ( ~ m1_subset_1(X10,k1_zfmisc_1(X11))
        | r1_tarski(X10,X11) )
      & ( ~ r1_tarski(X10,X11)
        | m1_subset_1(X10,k1_zfmisc_1(X11)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_53,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0)
    | ~ r1_lattice3(esk4_0,esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_54,negated_conjecture,
    ( r1_lattice3(esk3_0,esk5_0,esk6_0)
    | ~ r2_lattice3(esk4_0,esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_55,negated_conjecture,
    ( ~ r2_lattice3(esk4_0,esk5_0,esk7_0)
    | ~ r1_lattice3(esk4_0,esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_56,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,u1_struct_0(esk3_0),esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43]),
    [final]).

cnf(c_0_57,negated_conjecture,
    ( r1_orders_2(esk4_0,X1,esk6_0)
    | ~ r1_lattice3(esk4_0,X2,X1)
    | ~ l1_orders_2(esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(esk6_0,X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_33]),
    [final]).

cnf(c_0_58,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk2_3(esk3_0,X1,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_44]),
    [final]).

cnf(c_0_59,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk6_0)
    | m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk3_0),esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46]),
    [final]).

cnf(c_0_60,negated_conjecture,
    ( r1_orders_2(esk4_0,esk6_0,X1)
    | ~ r2_lattice3(esk4_0,X2,X1)
    | ~ l1_orders_2(esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(esk6_0,X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_33]),
    [final]).

cnf(c_0_61,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk6_0)
    | r2_hidden(esk2_3(esk4_0,X1,esk6_0),X1)
    | ~ l1_orders_2(esk4_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_33]),
    [final]).

cnf(c_0_62,negated_conjecture,
    ( r1_lattice3(esk4_0,X1,esk6_0)
    | r2_hidden(esk1_3(esk4_0,X1,esk6_0),X1)
    | ~ l1_orders_2(esk4_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_33]),
    [final]).

cnf(c_0_63,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk6_0)
    | m1_subset_1(esk2_3(esk4_0,X1,esk6_0),u1_struct_0(esk4_0))
    | ~ l1_orders_2(esk4_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_33]),
    [final]).

cnf(c_0_64,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | ~ r1_orders_2(esk3_0,esk2_3(esk3_0,X1,esk6_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_14]),c_0_22])]),
    [final]).

cnf(c_0_65,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk6_0)
    | ~ r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,X1,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_14]),c_0_22])]),
    [final]).

cnf(c_0_66,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk6_0)
    | ~ r1_orders_2(esk4_0,esk2_3(esk4_0,X1,esk6_0),esk6_0)
    | ~ l1_orders_2(esk4_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_33]),
    [final]).

cnf(c_0_67,negated_conjecture,
    ( r1_lattice3(esk4_0,X1,esk6_0)
    | ~ r1_orders_2(esk4_0,esk6_0,esk1_3(esk4_0,X1,esk6_0))
    | ~ l1_orders_2(esk4_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_33]),
    [final]).

cnf(c_0_68,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_14]),c_0_22])]),
    [final]).

cnf(c_0_69,negated_conjecture,
    ( r1_lattice3(esk4_0,X1,esk6_0)
    | m1_subset_1(esk1_3(esk4_0,X1,esk6_0),u1_struct_0(esk4_0))
    | ~ l1_orders_2(esk4_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_33]),
    [final]).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(esk4_0))
    | ~ l1_orders_2(esk4_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_24]),
    [final]).

cnf(c_0_71,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0)
    | r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_72,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_51]),
    [final]).

cnf(c_0_73,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_52]),
    [final]).

cnf(c_0_74,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52]),
    [final]).

cnf(c_0_75,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0)
    | ~ r1_lattice3(esk4_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_53,c_0_27]),
    [final]).

cnf(c_0_76,negated_conjecture,
    ( r1_lattice3(esk3_0,esk5_0,esk6_0)
    | ~ r2_lattice3(esk4_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_54,c_0_27]),
    [final]).

cnf(c_0_77,negated_conjecture,
    ( ~ r2_lattice3(esk4_0,esk5_0,esk6_0)
    | ~ r1_lattice3(esk4_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_27]),c_0_27]),
    [final]).

cnf(c_0_78,negated_conjecture,
    ( m1_yellow_0(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_79,negated_conjecture,
    ( v4_yellow_0(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:36:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.13/0.40  # and selection function SelectNewComplexAHP.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.050 s
% 0.13/0.40  # Presaturation interreduction done
% 0.13/0.40  
% 0.13/0.40  # No proof found!
% 0.13/0.40  # SZS status CounterSatisfiable
% 0.13/0.40  # SZS output start Saturation
% 0.13/0.40  fof(t62_yellow_0, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:(((~(v2_struct_0(X2))&v4_yellow_0(X2,X1))&m1_yellow_0(X2,X1))=>![X3, X4]:(m1_subset_1(X4,u1_struct_0(X1))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>(X5=X4=>((r1_lattice3(X1,X3,X4)=>r1_lattice3(X2,X3,X5))&(r2_lattice3(X1,X3,X4)=>r2_lattice3(X2,X3,X5)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_yellow_0)).
% 0.13/0.40  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.13/0.40  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.13/0.40  fof(d8_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattice3)).
% 0.13/0.40  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.13/0.40  fof(d9_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 0.13/0.40  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.13/0.40  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.13/0.40  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.40  fof(c_0_9, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:(((~(v2_struct_0(X2))&v4_yellow_0(X2,X1))&m1_yellow_0(X2,X1))=>![X3, X4]:(m1_subset_1(X4,u1_struct_0(X1))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>(X5=X4=>((r1_lattice3(X1,X3,X4)=>r1_lattice3(X2,X3,X5))&(r2_lattice3(X1,X3,X4)=>r2_lattice3(X2,X3,X5))))))))), inference(assume_negation,[status(cth)],[t62_yellow_0])).
% 0.13/0.40  fof(c_0_10, plain, ![X8, X9]:(~m1_subset_1(X8,X9)|(v1_xboole_0(X9)|r2_hidden(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.13/0.40  fof(c_0_11, negated_conjecture, ((~v2_struct_0(esk3_0)&l1_orders_2(esk3_0))&(((~v2_struct_0(esk4_0)&v4_yellow_0(esk4_0,esk3_0))&m1_yellow_0(esk4_0,esk3_0))&(m1_subset_1(esk6_0,u1_struct_0(esk3_0))&(m1_subset_1(esk7_0,u1_struct_0(esk4_0))&(esk7_0=esk6_0&(((r2_lattice3(esk3_0,esk5_0,esk6_0)|r1_lattice3(esk3_0,esk5_0,esk6_0))&(~r2_lattice3(esk4_0,esk5_0,esk7_0)|r1_lattice3(esk3_0,esk5_0,esk6_0)))&((r2_lattice3(esk3_0,esk5_0,esk6_0)|~r1_lattice3(esk4_0,esk5_0,esk7_0))&(~r2_lattice3(esk4_0,esk5_0,esk7_0)|~r1_lattice3(esk4_0,esk5_0,esk7_0))))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])).
% 0.13/0.40  fof(c_0_12, plain, ![X15]:(v2_struct_0(X15)|~l1_struct_0(X15)|~v1_xboole_0(u1_struct_0(X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.13/0.40  cnf(c_0_13, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.13/0.40  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.13/0.40  fof(c_0_15, plain, ![X17, X18, X19, X20]:((~r1_lattice3(X17,X18,X19)|(~m1_subset_1(X20,u1_struct_0(X17))|(~r2_hidden(X20,X18)|r1_orders_2(X17,X19,X20)))|~m1_subset_1(X19,u1_struct_0(X17))|~l1_orders_2(X17))&((m1_subset_1(esk1_3(X17,X18,X19),u1_struct_0(X17))|r1_lattice3(X17,X18,X19)|~m1_subset_1(X19,u1_struct_0(X17))|~l1_orders_2(X17))&((r2_hidden(esk1_3(X17,X18,X19),X18)|r1_lattice3(X17,X18,X19)|~m1_subset_1(X19,u1_struct_0(X17))|~l1_orders_2(X17))&(~r1_orders_2(X17,X19,esk1_3(X17,X18,X19))|r1_lattice3(X17,X18,X19)|~m1_subset_1(X19,u1_struct_0(X17))|~l1_orders_2(X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).
% 0.13/0.40  cnf(c_0_16, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.13/0.40  cnf(c_0_17, negated_conjecture, (v1_xboole_0(u1_struct_0(esk3_0))|r2_hidden(esk6_0,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.13/0.40  cnf(c_0_18, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.13/0.40  fof(c_0_19, plain, ![X16]:(~l1_orders_2(X16)|l1_struct_0(X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.13/0.40  fof(c_0_20, plain, ![X22, X23, X24, X25]:((~r2_lattice3(X22,X23,X24)|(~m1_subset_1(X25,u1_struct_0(X22))|(~r2_hidden(X25,X23)|r1_orders_2(X22,X25,X24)))|~m1_subset_1(X24,u1_struct_0(X22))|~l1_orders_2(X22))&((m1_subset_1(esk2_3(X22,X23,X24),u1_struct_0(X22))|r2_lattice3(X22,X23,X24)|~m1_subset_1(X24,u1_struct_0(X22))|~l1_orders_2(X22))&((r2_hidden(esk2_3(X22,X23,X24),X23)|r2_lattice3(X22,X23,X24)|~m1_subset_1(X24,u1_struct_0(X22))|~l1_orders_2(X22))&(~r1_orders_2(X22,esk2_3(X22,X23,X24),X24)|r2_lattice3(X22,X23,X24)|~m1_subset_1(X24,u1_struct_0(X22))|~l1_orders_2(X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).
% 0.13/0.40  cnf(c_0_21, plain, (r1_orders_2(X1,X3,X4)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.13/0.40  cnf(c_0_22, negated_conjecture, (l1_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.13/0.40  cnf(c_0_23, negated_conjecture, (r2_hidden(esk6_0,u1_struct_0(esk3_0))|~l1_struct_0(esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])).
% 0.13/0.40  cnf(c_0_24, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_19]), ['final']).
% 0.13/0.40  cnf(c_0_25, plain, (r1_orders_2(X1,X4,X3)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_20]), ['final']).
% 0.13/0.40  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.40  cnf(c_0_27, negated_conjecture, (esk7_0=esk6_0), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.13/0.40  cnf(c_0_28, negated_conjecture, (r1_orders_2(esk3_0,X1,esk6_0)|~r1_lattice3(esk3_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(esk6_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_14]), c_0_22])]), ['final']).
% 0.13/0.40  cnf(c_0_29, negated_conjecture, (r2_hidden(esk6_0,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_22])]), ['final']).
% 0.13/0.40  fof(c_0_30, plain, ![X6, X7]:(~r2_hidden(X6,X7)|m1_subset_1(X6,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.13/0.40  cnf(c_0_31, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.13/0.40  cnf(c_0_32, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,X1)|~r2_lattice3(esk3_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(esk6_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_14]), c_0_22])]), ['final']).
% 0.13/0.40  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk4_0))), inference(rw,[status(thm)],[c_0_26, c_0_27]), ['final']).
% 0.13/0.40  cnf(c_0_34, negated_conjecture, (r1_orders_2(esk3_0,X1,esk6_0)|~r1_lattice3(esk3_0,u1_struct_0(esk3_0),X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_28, c_0_29]), ['final']).
% 0.13/0.40  cnf(c_0_35, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30]), ['final']).
% 0.13/0.40  cnf(c_0_36, negated_conjecture, (r1_lattice3(esk3_0,X1,esk6_0)|r2_hidden(esk1_3(esk3_0,X1,esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_14]), c_0_22])]), ['final']).
% 0.13/0.40  cnf(c_0_37, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_20]), ['final']).
% 0.13/0.40  cnf(c_0_38, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,X1)|~r2_lattice3(esk3_0,u1_struct_0(esk3_0),X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_32, c_0_29]), ['final']).
% 0.13/0.40  cnf(c_0_39, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_20]), ['final']).
% 0.13/0.40  cnf(c_0_40, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|r2_hidden(esk6_0,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_13, c_0_33]), ['final']).
% 0.13/0.40  cnf(c_0_41, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.13/0.40  cnf(c_0_42, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,esk6_0)|~r1_lattice3(esk3_0,u1_struct_0(esk3_0),esk6_0)), inference(spm,[status(thm)],[c_0_34, c_0_14]), ['final']).
% 0.13/0.40  cnf(c_0_43, negated_conjecture, (r1_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk1_3(esk3_0,X1,esk6_0),X1)), inference(spm,[status(thm)],[c_0_35, c_0_36]), ['final']).
% 0.13/0.40  cnf(c_0_44, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|r2_hidden(esk2_3(esk3_0,X1,esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_14]), c_0_22])]), ['final']).
% 0.13/0.40  cnf(c_0_45, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,esk6_0)|~r2_lattice3(esk3_0,u1_struct_0(esk3_0),esk6_0)), inference(spm,[status(thm)],[c_0_38, c_0_14]), ['final']).
% 0.13/0.40  cnf(c_0_46, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk2_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_14]), c_0_22])]), ['final']).
% 0.13/0.40  cnf(c_0_47, plain, (r2_lattice3(X1,X2,X3)|~r1_orders_2(X1,esk2_3(X1,X2,X3),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_20]), ['final']).
% 0.13/0.40  cnf(c_0_48, plain, (r1_lattice3(X1,X3,X2)|~r1_orders_2(X1,X2,esk1_3(X1,X3,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.13/0.40  cnf(c_0_49, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.13/0.40  cnf(c_0_50, negated_conjecture, (r2_hidden(esk6_0,u1_struct_0(esk4_0))|~l1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_40]), c_0_41]), ['final']).
% 0.13/0.40  fof(c_0_51, plain, ![X12, X13, X14]:(~r2_hidden(X12,X13)|~m1_subset_1(X13,k1_zfmisc_1(X14))|m1_subset_1(X12,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.13/0.40  fof(c_0_52, plain, ![X10, X11]:((~m1_subset_1(X10,k1_zfmisc_1(X11))|r1_tarski(X10,X11))&(~r1_tarski(X10,X11)|m1_subset_1(X10,k1_zfmisc_1(X11)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.40  cnf(c_0_53, negated_conjecture, (r2_lattice3(esk3_0,esk5_0,esk6_0)|~r1_lattice3(esk4_0,esk5_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.40  cnf(c_0_54, negated_conjecture, (r1_lattice3(esk3_0,esk5_0,esk6_0)|~r2_lattice3(esk4_0,esk5_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.40  cnf(c_0_55, negated_conjecture, (~r2_lattice3(esk4_0,esk5_0,esk7_0)|~r1_lattice3(esk4_0,esk5_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.40  cnf(c_0_56, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,esk6_0)|m1_subset_1(esk1_3(esk3_0,u1_struct_0(esk3_0),esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_42, c_0_43]), ['final']).
% 0.13/0.40  cnf(c_0_57, negated_conjecture, (r1_orders_2(esk4_0,X1,esk6_0)|~r1_lattice3(esk4_0,X2,X1)|~l1_orders_2(esk4_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))|~r2_hidden(esk6_0,X2)), inference(spm,[status(thm)],[c_0_21, c_0_33]), ['final']).
% 0.13/0.40  cnf(c_0_58, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk2_3(esk3_0,X1,esk6_0),X1)), inference(spm,[status(thm)],[c_0_35, c_0_44]), ['final']).
% 0.13/0.40  cnf(c_0_59, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,esk6_0)|m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk3_0),esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_45, c_0_46]), ['final']).
% 0.13/0.40  cnf(c_0_60, negated_conjecture, (r1_orders_2(esk4_0,esk6_0,X1)|~r2_lattice3(esk4_0,X2,X1)|~l1_orders_2(esk4_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))|~r2_hidden(esk6_0,X2)), inference(spm,[status(thm)],[c_0_25, c_0_33]), ['final']).
% 0.13/0.40  cnf(c_0_61, negated_conjecture, (r2_lattice3(esk4_0,X1,esk6_0)|r2_hidden(esk2_3(esk4_0,X1,esk6_0),X1)|~l1_orders_2(esk4_0)), inference(spm,[status(thm)],[c_0_37, c_0_33]), ['final']).
% 0.13/0.40  cnf(c_0_62, negated_conjecture, (r1_lattice3(esk4_0,X1,esk6_0)|r2_hidden(esk1_3(esk4_0,X1,esk6_0),X1)|~l1_orders_2(esk4_0)), inference(spm,[status(thm)],[c_0_31, c_0_33]), ['final']).
% 0.13/0.40  cnf(c_0_63, negated_conjecture, (r2_lattice3(esk4_0,X1,esk6_0)|m1_subset_1(esk2_3(esk4_0,X1,esk6_0),u1_struct_0(esk4_0))|~l1_orders_2(esk4_0)), inference(spm,[status(thm)],[c_0_39, c_0_33]), ['final']).
% 0.13/0.40  cnf(c_0_64, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|~r1_orders_2(esk3_0,esk2_3(esk3_0,X1,esk6_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_14]), c_0_22])]), ['final']).
% 0.13/0.40  cnf(c_0_65, negated_conjecture, (r1_lattice3(esk3_0,X1,esk6_0)|~r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,X1,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_14]), c_0_22])]), ['final']).
% 0.13/0.40  cnf(c_0_66, negated_conjecture, (r2_lattice3(esk4_0,X1,esk6_0)|~r1_orders_2(esk4_0,esk2_3(esk4_0,X1,esk6_0),esk6_0)|~l1_orders_2(esk4_0)), inference(spm,[status(thm)],[c_0_47, c_0_33]), ['final']).
% 0.13/0.40  cnf(c_0_67, negated_conjecture, (r1_lattice3(esk4_0,X1,esk6_0)|~r1_orders_2(esk4_0,esk6_0,esk1_3(esk4_0,X1,esk6_0))|~l1_orders_2(esk4_0)), inference(spm,[status(thm)],[c_0_48, c_0_33]), ['final']).
% 0.13/0.40  cnf(c_0_68, negated_conjecture, (r1_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk1_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_14]), c_0_22])]), ['final']).
% 0.13/0.40  cnf(c_0_69, negated_conjecture, (r1_lattice3(esk4_0,X1,esk6_0)|m1_subset_1(esk1_3(esk4_0,X1,esk6_0),u1_struct_0(esk4_0))|~l1_orders_2(esk4_0)), inference(spm,[status(thm)],[c_0_49, c_0_33]), ['final']).
% 0.13/0.40  cnf(c_0_70, negated_conjecture, (r2_hidden(esk6_0,u1_struct_0(esk4_0))|~l1_orders_2(esk4_0)), inference(spm,[status(thm)],[c_0_50, c_0_24]), ['final']).
% 0.13/0.40  cnf(c_0_71, negated_conjecture, (r2_lattice3(esk3_0,esk5_0,esk6_0)|r1_lattice3(esk3_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.13/0.40  cnf(c_0_72, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_51]), ['final']).
% 0.13/0.40  cnf(c_0_73, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_52]), ['final']).
% 0.13/0.40  cnf(c_0_74, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_52]), ['final']).
% 0.13/0.40  cnf(c_0_75, negated_conjecture, (r2_lattice3(esk3_0,esk5_0,esk6_0)|~r1_lattice3(esk4_0,esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_53, c_0_27]), ['final']).
% 0.13/0.40  cnf(c_0_76, negated_conjecture, (r1_lattice3(esk3_0,esk5_0,esk6_0)|~r2_lattice3(esk4_0,esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_54, c_0_27]), ['final']).
% 0.13/0.40  cnf(c_0_77, negated_conjecture, (~r2_lattice3(esk4_0,esk5_0,esk6_0)|~r1_lattice3(esk4_0,esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_27]), c_0_27]), ['final']).
% 0.13/0.40  cnf(c_0_78, negated_conjecture, (m1_yellow_0(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.13/0.40  cnf(c_0_79, negated_conjecture, (v4_yellow_0(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.13/0.40  # SZS output end Saturation
% 0.13/0.40  # Proof object total steps             : 80
% 0.13/0.40  # Proof object clause steps            : 61
% 0.13/0.40  # Proof object formula steps           : 19
% 0.13/0.40  # Proof object conjectures             : 49
% 0.13/0.40  # Proof object clause conjectures      : 46
% 0.13/0.40  # Proof object formula conjectures     : 3
% 0.13/0.40  # Proof object initial clauses used    : 27
% 0.13/0.40  # Proof object initial formulas used   : 9
% 0.13/0.40  # Proof object generating inferences   : 30
% 0.13/0.40  # Proof object simplifying inferences  : 25
% 0.13/0.40  # Parsed axioms                        : 9
% 0.13/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.40  # Initial clauses                      : 27
% 0.13/0.40  # Removed in clause preprocessing      : 0
% 0.13/0.40  # Initial clauses in saturation        : 27
% 0.13/0.40  # Processed clauses                    : 86
% 0.13/0.40  # ...of these trivial                  : 0
% 0.13/0.40  # ...subsumed                          : 2
% 0.13/0.40  # ...remaining for further processing  : 84
% 0.13/0.40  # Other redundant clauses eliminated   : 0
% 0.13/0.40  # Clauses deleted for lack of memory   : 0
% 0.13/0.40  # Backward-subsumed                    : 0
% 0.13/0.40  # Backward-rewritten                   : 2
% 0.13/0.40  # Generated clauses                    : 33
% 0.13/0.40  # ...of the previous two non-trivial   : 32
% 0.13/0.40  # Contextual simplify-reflections      : 0
% 0.13/0.40  # Paramodulations                      : 33
% 0.13/0.40  # Factorizations                       : 0
% 0.13/0.40  # Equation resolutions                 : 0
% 0.13/0.40  # Propositional unsat checks           : 0
% 0.13/0.40  #    Propositional check models        : 0
% 0.13/0.40  #    Propositional check unsatisfiable : 0
% 0.13/0.40  #    Propositional clauses             : 0
% 0.13/0.40  #    Propositional clauses after purity: 0
% 0.13/0.40  #    Propositional unsat core size     : 0
% 0.13/0.40  #    Propositional preprocessing time  : 0.000
% 0.13/0.40  #    Propositional encoding time       : 0.000
% 0.13/0.40  #    Propositional solver time         : 0.000
% 0.13/0.40  #    Success case prop preproc time    : 0.000
% 0.13/0.40  #    Success case prop encoding time   : 0.000
% 0.13/0.40  #    Success case prop solver time     : 0.000
% 0.13/0.40  # Current number of processed clauses  : 55
% 0.13/0.40  #    Positive orientable unit clauses  : 7
% 0.13/0.40  #    Positive unorientable unit clauses: 0
% 0.13/0.40  #    Negative unit clauses             : 2
% 0.13/0.40  #    Non-unit-clauses                  : 46
% 0.13/0.40  # Current number of unprocessed clauses: 0
% 0.13/0.40  # ...number of literals in the above   : 0
% 0.13/0.40  # Current number of archived formulas  : 0
% 0.13/0.40  # Current number of archived clauses   : 29
% 0.13/0.40  # Clause-clause subsumption calls (NU) : 282
% 0.13/0.40  # Rec. Clause-clause subsumption calls : 120
% 0.13/0.40  # Non-unit clause-clause subsumptions  : 2
% 0.13/0.40  # Unit Clause-clause subsumption calls : 0
% 0.13/0.40  # Rewrite failures with RHS unbound    : 0
% 0.13/0.40  # BW rewrite match attempts            : 1
% 0.13/0.40  # BW rewrite match successes           : 1
% 0.13/0.40  # Condensation attempts                : 0
% 0.13/0.40  # Condensation successes               : 0
% 0.13/0.40  # Termbank termtop insertions          : 2807
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.052 s
% 0.13/0.40  # System time              : 0.008 s
% 0.13/0.40  # Total time               : 0.060 s
% 0.13/0.40  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
