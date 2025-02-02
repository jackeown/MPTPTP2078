%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:21 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  140 (7936 expanded)
%              Number of clauses        :  127 (3147 expanded)
%              Number of leaves         :    6 (1866 expanded)
%              Depth                    :   17
%              Number of atoms          :  907 (54119 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   8 average)
%              Maximal clause size      :   18 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t36_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_lattice3(X1,X2,X3)
              <=> r1_lattice3(X1,k4_waybel_0(X1,X2),X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_waybel_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(t26_orders_2,axiom,(
    ! [X1] :
      ( ( v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( ( r1_orders_2(X1,X2,X3)
                      & r1_orders_2(X1,X3,X4) )
                   => r1_orders_2(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_orders_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r1_lattice3(X1,X2,X3)
                <=> r1_lattice3(X1,k4_waybel_0(X1,X2),X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t36_waybel_0])).

fof(c_0_7,plain,(
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

fof(c_0_8,plain,(
    ! [X5,X6,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(X5))
      | ~ r2_hidden(X7,X6)
      | r2_hidden(X7,X5) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_9,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v3_orders_2(esk2_0)
    & v4_orders_2(esk2_0)
    & l1_orders_2(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & m1_subset_1(esk4_0,u1_struct_0(esk2_0))
    & ( ~ r1_lattice3(esk2_0,esk3_0,esk4_0)
      | ~ r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0) )
    & ( r1_lattice3(esk2_0,esk3_0,esk4_0)
      | r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).

cnf(c_0_10,plain,
    ( r1_lattice3(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,esk1_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_11,plain,
    ( r1_orders_2(X1,X3,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_12,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_13,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_15,plain,
    ( r1_lattice3(X1,X2,X3)
    | ~ r1_lattice3(X1,X4,X3)
    | ~ l1_orders_2(X1)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X4)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),
    [final]).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14]),
    [final]).

fof(c_0_17,plain,(
    ! [X13,X14,X15,X16] :
      ( ~ v4_orders_2(X13)
      | ~ l1_orders_2(X13)
      | ~ m1_subset_1(X14,u1_struct_0(X13))
      | ~ m1_subset_1(X15,u1_struct_0(X13))
      | ~ m1_subset_1(X16,u1_struct_0(X13))
      | ~ r1_orders_2(X13,X14,X15)
      | ~ r1_orders_2(X13,X15,X16)
      | r1_orders_2(X13,X14,X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_orders_2])])])).

cnf(c_0_18,negated_conjecture,
    ( r1_lattice3(X1,X2,X3)
    | ~ r1_lattice3(X1,u1_struct_0(esk2_0),X3)
    | ~ l1_orders_2(X1)
    | ~ r2_hidden(esk1_3(X1,X2,X3),esk3_0)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16]),
    [final]).

cnf(c_0_19,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_20,plain,
    ( r1_orders_2(X1,X2,X4)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_21,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_22,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_23,negated_conjecture,
    ( r1_lattice3(X1,esk3_0,X2)
    | ~ r1_lattice3(X1,u1_struct_0(esk2_0),X2)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19]),
    [final]).

fof(c_0_24,plain,(
    ! [X10,X11,X12] :
      ( ~ r2_hidden(X10,X11)
      | ~ m1_subset_1(X11,k1_zfmisc_1(X12))
      | m1_subset_1(X10,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_25,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,X2)
    | ~ r1_orders_2(esk2_0,X3,X2)
    | ~ r1_orders_2(esk2_0,X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])]),
    [final]).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_27,negated_conjecture,
    ( ~ r1_lattice3(esk2_0,esk3_0,esk4_0)
    | ~ r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_28,negated_conjecture,
    ( r1_lattice3(esk2_0,X1,X2)
    | m1_subset_1(esk1_3(esk2_0,X1,X2),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_22]),
    [final]).

cnf(c_0_29,negated_conjecture,
    ( r1_lattice3(esk2_0,esk3_0,X1)
    | ~ r1_lattice3(esk2_0,u1_struct_0(esk2_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_22]),
    [final]).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_24]),
    [final]).

cnf(c_0_31,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | ~ r1_orders_2(esk2_0,X2,esk4_0)
    | ~ r1_orders_2(esk2_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26]),
    [final]).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_26])]),
    [final]).

cnf(c_0_33,negated_conjecture,
    ( r1_lattice3(esk2_0,esk3_0,X1)
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),X1),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_28]),
    [final]).

cnf(c_0_34,plain,
    ( r1_lattice3(X1,X2,X3)
    | m1_subset_1(esk1_3(X1,X2,X3),X4)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_19]),
    [final]).

cnf(c_0_35,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | ~ r1_lattice3(esk2_0,X2,X3)
    | ~ r1_orders_2(esk2_0,X1,X3)
    | ~ r2_hidden(esk4_0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_11]),c_0_22]),c_0_26])]),
    [final]).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),u1_struct_0(esk2_0))
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_26])]),
    [final]).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),u1_struct_0(esk2_0))
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_28]),c_0_26])]),
    [final]).

cnf(c_0_38,negated_conjecture,
    ( r1_lattice3(esk2_0,X1,X2)
    | m1_subset_1(esk1_3(esk2_0,X1,X2),X3)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_22]),
    [final]).

cnf(c_0_39,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | ~ r1_orders_2(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | ~ r2_hidden(esk4_0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36]),
    [final]).

cnf(c_0_40,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | ~ r1_orders_2(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | ~ r2_hidden(esk4_0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_37]),
    [final]).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X1)
    | ~ r1_lattice3(esk2_0,esk3_0,esk4_0)
    | ~ m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_38]),c_0_26])]),
    [final]).

cnf(c_0_42,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | ~ r1_lattice3(esk2_0,X3,X1)
    | ~ r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X3)
    | ~ r2_hidden(esk4_0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_11]),c_0_22])]),c_0_36]),
    [final]).

cnf(c_0_43,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | ~ r1_lattice3(esk2_0,X3,X1)
    | ~ r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X3)
    | ~ r2_hidden(esk4_0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_11]),c_0_22])]),c_0_37]),
    [final]).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))
    | m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X1)
    | ~ m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_33]),c_0_26])]),
    [final]).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X1)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_28]),c_0_26])]),
    [final]).

cnf(c_0_46,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | ~ r1_lattice3(esk2_0,X3,X4)
    | ~ r1_orders_2(esk2_0,X1,X4)
    | ~ r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X3)
    | ~ r2_hidden(esk4_0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_42]),
    [final]).

cnf(c_0_47,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | ~ r1_lattice3(esk2_0,X3,X4)
    | ~ r1_orders_2(esk2_0,X1,X4)
    | ~ r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X3)
    | ~ r2_hidden(esk4_0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_43]),
    [final]).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(X1,X2)
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | ~ m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(spm,[status(thm)],[c_0_13,c_0_44]),
    [final]).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(X1,X2)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | ~ m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(spm,[status(thm)],[c_0_13,c_0_45]),
    [final]).

cnf(c_0_50,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X3)
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,X4,X5)
    | ~ r1_orders_2(esk2_0,X1,X5)
    | ~ r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X4)
    | ~ r2_hidden(esk4_0,X2)
    | ~ m1_subset_1(X5,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_38]),c_0_36]),
    [final]).

cnf(c_0_51,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X3)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,X4,X5)
    | ~ r1_orders_2(esk2_0,X1,X5)
    | ~ r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X4)
    | ~ r2_hidden(esk4_0,X2)
    | ~ m1_subset_1(X5,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_38]),c_0_37]),
    [final]).

cnf(c_0_52,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,X3,X4)
    | ~ r1_orders_2(esk2_0,X1,X4)
    | ~ r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X3)
    | ~ r2_hidden(esk4_0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_28]),c_0_36]),
    [final]).

cnf(c_0_53,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,X3,X4)
    | ~ r1_orders_2(esk2_0,X1,X4)
    | ~ r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X3)
    | ~ r2_hidden(esk4_0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_28]),c_0_37]),
    [final]).

cnf(c_0_54,negated_conjecture,
    ( r1_lattice3(X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2)
    | r2_hidden(esk1_3(X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2),X3)
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(X3)))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_19]),
    [final]).

cnf(c_0_55,negated_conjecture,
    ( r1_lattice3(X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2)
    | r2_hidden(esk1_3(X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2),X3)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(X3)))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_19]),
    [final]).

cnf(c_0_56,negated_conjecture,
    ( r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)
    | r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X3)
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X4)
    | ~ r1_orders_2(esk2_0,X1,X4)
    | ~ r2_hidden(esk4_0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_19]),c_0_22]),c_0_26])]),
    [final]).

cnf(c_0_57,negated_conjecture,
    ( r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)
    | r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X3)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X4)
    | ~ r1_orders_2(esk2_0,X1,X4)
    | ~ r2_hidden(esk4_0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_19]),c_0_22]),c_0_26])]),
    [final]).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,esk3_0)
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_16]),
    [final]).

cnf(c_0_59,negated_conjecture,
    ( r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)
    | r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X3)
    | ~ r1_orders_2(esk2_0,X1,X3)
    | ~ r2_hidden(esk4_0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_19]),c_0_22]),c_0_26])]),
    [final]).

cnf(c_0_60,negated_conjecture,
    ( r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)
    | r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X3)
    | ~ r1_orders_2(esk2_0,X1,X3)
    | ~ r2_hidden(esk4_0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_19]),c_0_22]),c_0_26])]),
    [final]).

cnf(c_0_61,negated_conjecture,
    ( r1_lattice3(X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2)
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(X1,u1_struct_0(esk2_0),X2)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk3_0)))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_54]),
    [final]).

cnf(c_0_62,negated_conjecture,
    ( r1_lattice3(X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(X1,u1_struct_0(esk2_0),X2)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk3_0)))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_55]),
    [final]).

cnf(c_0_63,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))
    | ~ r1_orders_2(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | ~ r1_orders_2(esk2_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_36]),
    [final]).

cnf(c_0_64,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ r1_orders_2(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | ~ r1_orders_2(esk2_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_37]),
    [final]).

cnf(c_0_65,negated_conjecture,
    ( r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)
    | r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X3)
    | m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X4),u1_struct_0(esk2_0))
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))
    | ~ r1_orders_2(esk2_0,X1,X4)
    | ~ r2_hidden(esk4_0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_28]),
    [final]).

cnf(c_0_66,negated_conjecture,
    ( r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)
    | r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X3)
    | m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X4),u1_struct_0(esk2_0))
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ r1_orders_2(esk2_0,X1,X4)
    | ~ r2_hidden(esk4_0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_28]),
    [final]).

cnf(c_0_67,negated_conjecture,
    ( r1_lattice3(X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2)
    | m1_subset_1(esk1_3(X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2),X3)
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk3_0)))
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_54]),
    [final]).

cnf(c_0_68,negated_conjecture,
    ( r1_lattice3(X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2)
    | m1_subset_1(esk1_3(X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2),X3)
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(X4)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_54]),
    [final]).

cnf(c_0_69,negated_conjecture,
    ( r1_lattice3(X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2)
    | m1_subset_1(esk1_3(X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2),X3)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(X4)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_55]),
    [final]).

cnf(c_0_70,negated_conjecture,
    ( r1_lattice3(X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2)
    | m1_subset_1(esk1_3(X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2),X3)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk3_0)))
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_55]),
    [final]).

cnf(c_0_71,negated_conjecture,
    ( r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)
    | r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))
    | m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X3),u1_struct_0(esk2_0))
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))
    | ~ r1_orders_2(esk2_0,X1,X3)
    | ~ r2_hidden(esk4_0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_28]),
    [final]).

cnf(c_0_72,negated_conjecture,
    ( r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)
    | r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))
    | m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X3),u1_struct_0(esk2_0))
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ r1_orders_2(esk2_0,X1,X3)
    | ~ r2_hidden(esk4_0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_28]),
    [final]).

cnf(c_0_73,negated_conjecture,
    ( r1_lattice3(esk2_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X1)
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,u1_struct_0(esk2_0),X1)
    | ~ m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_22]),
    [final]).

cnf(c_0_74,negated_conjecture,
    ( r1_lattice3(esk2_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X1)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,u1_struct_0(esk2_0),X1)
    | ~ m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_22]),
    [final]).

cnf(c_0_75,negated_conjecture,
    ( r1_lattice3(X1,esk3_0,X2)
    | m1_subset_1(esk1_3(X1,esk3_0,X2),X3)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_19]),
    [final]).

cnf(c_0_76,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,X2,X3)
    | ~ r1_orders_2(esk2_0,X1,X3)
    | ~ r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2)
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_11]),c_0_22])]),c_0_36]),
    [final]).

cnf(c_0_77,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,X2,X3)
    | ~ r1_orders_2(esk2_0,X1,X3)
    | ~ r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2)
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_11]),c_0_22])]),c_0_37]),
    [final]).

cnf(c_0_78,negated_conjecture,
    ( r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)
    | r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))
    | m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X3)
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))
    | ~ r1_orders_2(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | ~ r2_hidden(esk4_0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_36]),
    [final]).

cnf(c_0_79,negated_conjecture,
    ( r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)
    | r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))
    | m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X3)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ r1_orders_2(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | ~ r2_hidden(esk4_0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_37]),
    [final]).

cnf(c_0_80,negated_conjecture,
    ( r1_lattice3(esk2_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X1)
    | m1_subset_1(esk1_3(esk2_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X1),X2)
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk3_0)))
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_22]),
    [final]).

cnf(c_0_81,negated_conjecture,
    ( r1_lattice3(esk2_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X1)
    | m1_subset_1(esk1_3(esk2_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X1),X2)
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_22]),
    [final]).

cnf(c_0_82,negated_conjecture,
    ( r1_lattice3(esk2_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X1)
    | m1_subset_1(esk1_3(esk2_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X1),X2)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_22]),
    [final]).

cnf(c_0_83,negated_conjecture,
    ( r1_lattice3(esk2_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X1)
    | m1_subset_1(esk1_3(esk2_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X1),X2)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk3_0)))
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_22]),
    [final]).

cnf(c_0_84,negated_conjecture,
    ( r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)
    | r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))
    | m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))
    | ~ r1_orders_2(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | ~ r2_hidden(esk4_0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_36]),
    [final]).

cnf(c_0_85,negated_conjecture,
    ( r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)
    | r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))
    | m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ r1_orders_2(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | ~ r2_hidden(esk4_0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_37]),
    [final]).

cnf(c_0_86,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,u1_struct_0(esk2_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | ~ r1_lattice3(esk2_0,X2,X3)
    | ~ r1_orders_2(esk2_0,X1,X3)
    | ~ r2_hidden(esk4_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | ~ r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2)
    | ~ m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk3_0)))
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_73]),c_0_36]),
    [final]).

cnf(c_0_87,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,u1_struct_0(esk2_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | ~ r1_lattice3(esk2_0,X2,X3)
    | ~ r1_orders_2(esk2_0,X1,X3)
    | ~ r2_hidden(esk4_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | ~ r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2)
    | ~ m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk3_0)))
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_74]),c_0_37]),
    [final]).

cnf(c_0_88,negated_conjecture,
    ( r1_lattice3(esk2_0,esk3_0,X1)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,X1),X2)
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_22]),
    [final]).

cnf(c_0_89,negated_conjecture,
    ( r1_lattice3(esk2_0,esk3_0,X1)
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),X1),X2)
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_38]),
    [final]).

cnf(c_0_90,negated_conjecture,
    ( r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)
    | r1_orders_2(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X2)
    | ~ r1_orders_2(esk2_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_19]),c_0_22]),c_0_26])]),
    [final]).

cnf(c_0_91,negated_conjecture,
    ( r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)
    | r1_orders_2(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X2)
    | ~ r1_orders_2(esk2_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_19]),c_0_22]),c_0_26])]),
    [final]).

cnf(c_0_92,negated_conjecture,
    ( r1_lattice3(X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2)
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(X1,X3,X2)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(X3)))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_54]),
    [final]).

cnf(c_0_93,negated_conjecture,
    ( r1_lattice3(X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(X1,X3,X2)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(X3)))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_55]),
    [final]).

fof(c_0_94,plain,(
    ! [X8,X9] :
      ( ( ~ m1_subset_1(X8,k1_zfmisc_1(X9))
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | m1_subset_1(X8,k1_zfmisc_1(X9)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_95,negated_conjecture,
    ( r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)
    | r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))
    | m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X3)
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,X4,X1)
    | ~ r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X4)
    | ~ r2_hidden(esk4_0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_11]),c_0_22])]),c_0_36]),
    [final]).

cnf(c_0_96,negated_conjecture,
    ( r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)
    | r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))
    | m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X3)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,X4,X1)
    | ~ r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X4)
    | ~ r2_hidden(esk4_0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_11]),c_0_22])]),c_0_37]),
    [final]).

cnf(c_0_97,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X2)
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,X3,X4)
    | ~ r1_orders_2(esk2_0,X1,X4)
    | ~ r2_hidden(esk4_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | ~ r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X3)
    | ~ m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk3_0)))
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X4,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_80]),c_0_36]),
    [final]).

cnf(c_0_98,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X2)
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,X3,X4)
    | ~ r1_orders_2(esk2_0,X1,X4)
    | ~ r2_hidden(esk4_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | ~ r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X3)
    | ~ m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(X5)))
    | ~ m1_subset_1(X4,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_81]),c_0_36]),
    [final]).

cnf(c_0_99,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X2)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,X3,X4)
    | ~ r1_orders_2(esk2_0,X1,X4)
    | ~ r2_hidden(esk4_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | ~ r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X3)
    | ~ m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(X5)))
    | ~ m1_subset_1(X4,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_82]),c_0_37]),
    [final]).

cnf(c_0_100,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X2)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,X3,X4)
    | ~ r1_orders_2(esk2_0,X1,X4)
    | ~ r2_hidden(esk4_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | ~ r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X3)
    | ~ m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk3_0)))
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X4,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_83]),c_0_37]),
    [final]).

cnf(c_0_101,negated_conjecture,
    ( r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)
    | r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))
    | m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,X3,X1)
    | ~ r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X3)
    | ~ r2_hidden(esk4_0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_11]),c_0_22])]),c_0_36]),
    [final]).

cnf(c_0_102,negated_conjecture,
    ( r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)
    | r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))
    | m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,X3,X1)
    | ~ r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X3)
    | ~ r2_hidden(esk4_0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_11]),c_0_22])]),c_0_37]),
    [final]).

cnf(c_0_103,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X2)
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,X3,X4)
    | ~ r1_orders_2(esk2_0,X1,X4)
    | ~ r2_hidden(esk4_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | ~ r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X3)
    | ~ m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk3_0)))
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X4,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_38]),c_0_36]),
    [final]).

cnf(c_0_104,negated_conjecture,
    ( r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)
    | r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X3)
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))
    | m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X4),X5)
    | ~ r1_orders_2(esk2_0,X1,X4)
    | ~ r2_hidden(esk4_0,X2)
    | ~ m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(X5))
    | ~ m1_subset_1(X4,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_38]),
    [final]).

cnf(c_0_105,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X2)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,X3,X4)
    | ~ r1_orders_2(esk2_0,X1,X4)
    | ~ r2_hidden(esk4_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | ~ r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X3)
    | ~ m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk3_0)))
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X4,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_38]),c_0_37]),
    [final]).

cnf(c_0_106,negated_conjecture,
    ( r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)
    | r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X3)
    | m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X4),X5)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ r1_orders_2(esk2_0,X1,X4)
    | ~ r2_hidden(esk4_0,X2)
    | ~ m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(X5))
    | ~ m1_subset_1(X4,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_38]),
    [final]).

cnf(c_0_107,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,X2,X3)
    | ~ r1_orders_2(esk2_0,X1,X3)
    | ~ r2_hidden(esk4_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | ~ r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2)
    | ~ m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk3_0)))
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_28]),c_0_36]),
    [final]).

cnf(c_0_108,negated_conjecture,
    ( r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)
    | r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))
    | m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X3),X4)
    | ~ r1_orders_2(esk2_0,X1,X3)
    | ~ r2_hidden(esk4_0,X2)
    | ~ m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_38]),
    [final]).

cnf(c_0_109,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,X2,X3)
    | ~ r1_orders_2(esk2_0,X1,X3)
    | ~ r2_hidden(esk4_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | ~ r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2)
    | ~ m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk3_0)))
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_28]),c_0_37]),
    [final]).

cnf(c_0_110,negated_conjecture,
    ( r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)
    | r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))
    | m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X3),X4)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ r1_orders_2(esk2_0,X1,X3)
    | ~ r2_hidden(esk4_0,X2)
    | ~ m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_38]),
    [final]).

cnf(c_0_111,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X2)
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,X3,X4)
    | ~ r1_orders_2(esk2_0,X1,X4)
    | ~ r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X3)
    | ~ r2_hidden(esk4_0,esk3_0)
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X4,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_88]),c_0_36]),
    [final]).

cnf(c_0_112,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X3)
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,u1_struct_0(esk2_0),X4)
    | ~ r1_orders_2(esk2_0,X1,X4)
    | ~ r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),esk3_0)
    | ~ r2_hidden(esk4_0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_16]),
    [final]).

cnf(c_0_113,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X2)
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,X3,X4)
    | ~ r1_orders_2(esk2_0,X1,X4)
    | ~ r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X3)
    | ~ r2_hidden(esk4_0,esk3_0)
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X4,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_89]),c_0_36]),
    [final]).

cnf(c_0_114,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,u1_struct_0(esk2_0),X3)
    | ~ r1_orders_2(esk2_0,X1,X3)
    | ~ r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),esk3_0)
    | ~ r2_hidden(esk4_0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_16]),
    [final]).

cnf(c_0_115,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X2)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,X3,X4)
    | ~ r1_orders_2(esk2_0,X1,X4)
    | ~ r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X3)
    | ~ r2_hidden(esk4_0,esk3_0)
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X4,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_88]),c_0_37]),
    [final]).

cnf(c_0_116,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,X2,X3)
    | ~ r1_orders_2(esk2_0,X1,X3)
    | ~ r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2)
    | ~ r2_hidden(esk4_0,esk3_0)
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_33]),c_0_36]),
    [final]).

cnf(c_0_117,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X3)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,u1_struct_0(esk2_0),X4)
    | ~ r1_orders_2(esk2_0,X1,X4)
    | ~ r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),esk3_0)
    | ~ r2_hidden(esk4_0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_16]),
    [final]).

cnf(c_0_118,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X2)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,X3,X4)
    | ~ r1_orders_2(esk2_0,X1,X4)
    | ~ r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X3)
    | ~ r2_hidden(esk4_0,esk3_0)
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X4,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_89]),c_0_37]),
    [final]).

cnf(c_0_119,negated_conjecture,
    ( r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)
    | r1_orders_2(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))
    | m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X2),X3)
    | ~ r1_orders_2(esk2_0,X1,X2)
    | ~ m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_38]),
    [final]).

cnf(c_0_120,negated_conjecture,
    ( r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)
    | r1_orders_2(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X2),X3)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ r1_orders_2(esk2_0,X1,X2)
    | ~ m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_91,c_0_38]),
    [final]).

cnf(c_0_121,negated_conjecture,
    ( r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)
    | r1_orders_2(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X2),u1_struct_0(esk2_0))
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))
    | ~ r1_orders_2(esk2_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_28]),
    [final]).

cnf(c_0_122,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,u1_struct_0(esk2_0),X3)
    | ~ r1_orders_2(esk2_0,X1,X3)
    | ~ r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),esk3_0)
    | ~ r2_hidden(esk4_0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_16]),
    [final]).

cnf(c_0_123,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,X2,X3)
    | ~ r1_orders_2(esk2_0,X1,X3)
    | ~ r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2)
    | ~ r2_hidden(esk4_0,esk3_0)
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_33]),c_0_37]),
    [final]).

cnf(c_0_124,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,u1_struct_0(esk2_0),X2)
    | ~ r1_orders_2(esk2_0,X1,X2)
    | ~ r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),esk3_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_16]),
    [final]).

cnf(c_0_125,negated_conjecture,
    ( r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)
    | r1_orders_2(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X2),u1_struct_0(esk2_0))
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ r1_orders_2(esk2_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_91,c_0_28]),
    [final]).

cnf(c_0_126,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,u1_struct_0(esk2_0),X2)
    | ~ r1_orders_2(esk2_0,X1,X2)
    | ~ r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),esk3_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_16]),
    [final]).

cnf(c_0_127,negated_conjecture,
    ( r1_lattice3(esk2_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X1)
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,X2,X1)
    | ~ m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_22]),
    [final]).

cnf(c_0_128,negated_conjecture,
    ( r1_lattice3(esk2_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X1)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,X2,X1)
    | ~ m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_22]),
    [final]).

cnf(c_0_129,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X1)
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),X2)
    | ~ m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_89]),c_0_26])]),
    [final]).

cnf(c_0_130,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X1)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),X2)
    | ~ m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_88]),c_0_26])]),
    [final]).

cnf(c_0_131,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),u1_struct_0(esk2_0))
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),X1)
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_88]),c_0_26])]),
    [final]).

cnf(c_0_132,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X1)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),X2)
    | ~ m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_38]),c_0_26])]),
    [final]).

cnf(c_0_133,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),u1_struct_0(esk2_0))
    | m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),X1)
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_89]),c_0_26])]),
    [final]).

cnf(c_0_134,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),u1_struct_0(esk2_0))
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),X1)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_38]),c_0_26])]),
    [final]).

cnf(c_0_135,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_94]),
    [final]).

cnf(c_0_136,negated_conjecture,
    ( r1_lattice3(esk2_0,esk3_0,esk4_0)
    | r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_137,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_94]),
    [final]).

cnf(c_0_138,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_139,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:10:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S033I
% 0.20/0.41  # and selection function PSelectUnlessUniqMax.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.027 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # No proof found!
% 0.20/0.41  # SZS status CounterSatisfiable
% 0.20/0.41  # SZS output start Saturation
% 0.20/0.41  fof(t36_waybel_0, conjecture, ![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X3)<=>r1_lattice3(X1,k4_waybel_0(X1,X2),X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_waybel_0)).
% 0.20/0.41  fof(d8_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_lattice3)).
% 0.20/0.41  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.20/0.41  fof(t26_orders_2, axiom, ![X1]:((v4_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X3,X4))=>r1_orders_2(X1,X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_orders_2)).
% 0.20/0.41  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.20/0.41  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.41  fof(c_0_6, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X3)<=>r1_lattice3(X1,k4_waybel_0(X1,X2),X3)))))), inference(assume_negation,[status(cth)],[t36_waybel_0])).
% 0.20/0.41  fof(c_0_7, plain, ![X17, X18, X19, X20]:((~r1_lattice3(X17,X18,X19)|(~m1_subset_1(X20,u1_struct_0(X17))|(~r2_hidden(X20,X18)|r1_orders_2(X17,X19,X20)))|~m1_subset_1(X19,u1_struct_0(X17))|~l1_orders_2(X17))&((m1_subset_1(esk1_3(X17,X18,X19),u1_struct_0(X17))|r1_lattice3(X17,X18,X19)|~m1_subset_1(X19,u1_struct_0(X17))|~l1_orders_2(X17))&((r2_hidden(esk1_3(X17,X18,X19),X18)|r1_lattice3(X17,X18,X19)|~m1_subset_1(X19,u1_struct_0(X17))|~l1_orders_2(X17))&(~r1_orders_2(X17,X19,esk1_3(X17,X18,X19))|r1_lattice3(X17,X18,X19)|~m1_subset_1(X19,u1_struct_0(X17))|~l1_orders_2(X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).
% 0.20/0.41  fof(c_0_8, plain, ![X5, X6, X7]:(~m1_subset_1(X6,k1_zfmisc_1(X5))|(~r2_hidden(X7,X6)|r2_hidden(X7,X5))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.20/0.41  fof(c_0_9, negated_conjecture, ((((~v2_struct_0(esk2_0)&v3_orders_2(esk2_0))&v4_orders_2(esk2_0))&l1_orders_2(esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(m1_subset_1(esk4_0,u1_struct_0(esk2_0))&((~r1_lattice3(esk2_0,esk3_0,esk4_0)|~r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))&(r1_lattice3(esk2_0,esk3_0,esk4_0)|r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).
% 0.20/0.41  cnf(c_0_10, plain, (r1_lattice3(X1,X3,X2)|~r1_orders_2(X1,X2,esk1_3(X1,X3,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.20/0.41  cnf(c_0_11, plain, (r1_orders_2(X1,X3,X4)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.20/0.41  cnf(c_0_12, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.20/0.41  cnf(c_0_13, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.20/0.41  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.20/0.41  cnf(c_0_15, plain, (r1_lattice3(X1,X2,X3)|~r1_lattice3(X1,X4,X3)|~l1_orders_2(X1)|~r2_hidden(esk1_3(X1,X2,X3),X4)|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12]), ['final']).
% 0.20/0.41  cnf(c_0_16, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_13, c_0_14]), ['final']).
% 0.20/0.41  fof(c_0_17, plain, ![X13, X14, X15, X16]:(~v4_orders_2(X13)|~l1_orders_2(X13)|(~m1_subset_1(X14,u1_struct_0(X13))|(~m1_subset_1(X15,u1_struct_0(X13))|(~m1_subset_1(X16,u1_struct_0(X13))|(~r1_orders_2(X13,X14,X15)|~r1_orders_2(X13,X15,X16)|r1_orders_2(X13,X14,X16)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_orders_2])])])).
% 0.20/0.41  cnf(c_0_18, negated_conjecture, (r1_lattice3(X1,X2,X3)|~r1_lattice3(X1,u1_struct_0(esk2_0),X3)|~l1_orders_2(X1)|~r2_hidden(esk1_3(X1,X2,X3),esk3_0)|~m1_subset_1(X3,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_15, c_0_16]), ['final']).
% 0.20/0.41  cnf(c_0_19, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.20/0.41  cnf(c_0_20, plain, (r1_orders_2(X1,X2,X4)|~v4_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~r1_orders_2(X1,X2,X3)|~r1_orders_2(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.20/0.41  cnf(c_0_21, negated_conjecture, (v4_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.20/0.41  cnf(c_0_22, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.20/0.41  cnf(c_0_23, negated_conjecture, (r1_lattice3(X1,esk3_0,X2)|~r1_lattice3(X1,u1_struct_0(esk2_0),X2)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_18, c_0_19]), ['final']).
% 0.20/0.41  fof(c_0_24, plain, ![X10, X11, X12]:(~r2_hidden(X10,X11)|~m1_subset_1(X11,k1_zfmisc_1(X12))|m1_subset_1(X10,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.20/0.41  cnf(c_0_25, negated_conjecture, (r1_orders_2(esk2_0,X1,X2)|~r1_orders_2(esk2_0,X3,X2)|~r1_orders_2(esk2_0,X1,X3)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X3,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])]), ['final']).
% 0.20/0.41  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.20/0.41  cnf(c_0_27, negated_conjecture, (~r1_lattice3(esk2_0,esk3_0,esk4_0)|~r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.20/0.41  cnf(c_0_28, negated_conjecture, (r1_lattice3(esk2_0,X1,X2)|m1_subset_1(esk1_3(esk2_0,X1,X2),u1_struct_0(esk2_0))|~m1_subset_1(X2,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_12, c_0_22]), ['final']).
% 0.20/0.41  cnf(c_0_29, negated_conjecture, (r1_lattice3(esk2_0,esk3_0,X1)|~r1_lattice3(esk2_0,u1_struct_0(esk2_0),X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_23, c_0_22]), ['final']).
% 0.20/0.41  cnf(c_0_30, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_24]), ['final']).
% 0.20/0.41  cnf(c_0_31, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|~r1_orders_2(esk2_0,X2,esk4_0)|~r1_orders_2(esk2_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_25, c_0_26]), ['final']).
% 0.20/0.41  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_26])]), ['final']).
% 0.20/0.41  cnf(c_0_33, negated_conjecture, (r1_lattice3(esk2_0,esk3_0,X1)|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),X1),u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_29, c_0_28]), ['final']).
% 0.20/0.41  cnf(c_0_34, plain, (r1_lattice3(X1,X2,X3)|m1_subset_1(esk1_3(X1,X2,X3),X4)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(X4))|~m1_subset_1(X3,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_30, c_0_19]), ['final']).
% 0.20/0.41  cnf(c_0_35, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|~r1_lattice3(esk2_0,X2,X3)|~r1_orders_2(esk2_0,X1,X3)|~r2_hidden(esk4_0,X2)|~m1_subset_1(X3,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_11]), c_0_22]), c_0_26])]), ['final']).
% 0.20/0.41  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),u1_struct_0(esk2_0))|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_26])]), ['final']).
% 0.20/0.41  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),u1_struct_0(esk2_0))|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_28]), c_0_26])]), ['final']).
% 0.20/0.41  cnf(c_0_38, negated_conjecture, (r1_lattice3(esk2_0,X1,X2)|m1_subset_1(esk1_3(esk2_0,X1,X2),X3)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_34, c_0_22]), ['final']).
% 0.20/0.41  cnf(c_0_39, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|~r1_orders_2(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|~r2_hidden(esk4_0,X2)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_35, c_0_36]), ['final']).
% 0.20/0.41  cnf(c_0_40, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|~r1_orders_2(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|~r2_hidden(esk4_0,X2)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_35, c_0_37]), ['final']).
% 0.20/0.41  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X1)|~r1_lattice3(esk2_0,esk3_0,esk4_0)|~m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_38]), c_0_26])]), ['final']).
% 0.20/0.41  cnf(c_0_42, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|~r1_lattice3(esk2_0,X3,X1)|~r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X3)|~r2_hidden(esk4_0,X2)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_11]), c_0_22])]), c_0_36]), ['final']).
% 0.20/0.41  cnf(c_0_43, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|~r1_lattice3(esk2_0,X3,X1)|~r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X3)|~r2_hidden(esk4_0,X2)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_11]), c_0_22])]), c_0_37]), ['final']).
% 0.20/0.41  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))|m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X1)|~m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_33]), c_0_26])]), ['final']).
% 0.20/0.41  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X1)|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_28]), c_0_26])]), ['final']).
% 0.20/0.41  cnf(c_0_46, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|~r1_lattice3(esk2_0,X3,X4)|~r1_orders_2(esk2_0,X1,X4)|~r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X3)|~r2_hidden(esk4_0,X2)|~m1_subset_1(X4,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_31, c_0_42]), ['final']).
% 0.20/0.41  cnf(c_0_47, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|~r1_lattice3(esk2_0,X3,X4)|~r1_orders_2(esk2_0,X1,X4)|~r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X3)|~r2_hidden(esk4_0,X2)|~m1_subset_1(X4,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_31, c_0_43]), ['final']).
% 0.20/0.41  cnf(c_0_48, negated_conjecture, (r2_hidden(X1,X2)|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))|~r2_hidden(X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|~m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(spm,[status(thm)],[c_0_13, c_0_44]), ['final']).
% 0.20/0.41  cnf(c_0_49, negated_conjecture, (r2_hidden(X1,X2)|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~r2_hidden(X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|~m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(spm,[status(thm)],[c_0_13, c_0_45]), ['final']).
% 0.20/0.41  cnf(c_0_50, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X3)|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,X4,X5)|~r1_orders_2(esk2_0,X1,X5)|~r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X4)|~r2_hidden(esk4_0,X2)|~m1_subset_1(X5,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_38]), c_0_36]), ['final']).
% 0.20/0.41  cnf(c_0_51, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X3)|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,X4,X5)|~r1_orders_2(esk2_0,X1,X5)|~r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X4)|~r2_hidden(esk4_0,X2)|~m1_subset_1(X5,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_38]), c_0_37]), ['final']).
% 0.20/0.41  cnf(c_0_52, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,X3,X4)|~r1_orders_2(esk2_0,X1,X4)|~r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X3)|~r2_hidden(esk4_0,X2)|~m1_subset_1(X4,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_28]), c_0_36]), ['final']).
% 0.20/0.41  cnf(c_0_53, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,X3,X4)|~r1_orders_2(esk2_0,X1,X4)|~r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X3)|~r2_hidden(esk4_0,X2)|~m1_subset_1(X4,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_28]), c_0_37]), ['final']).
% 0.20/0.41  cnf(c_0_54, negated_conjecture, (r1_lattice3(X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2)|r2_hidden(esk1_3(X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2),X3)|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))|~l1_orders_2(X1)|~m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(X3)))|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_48, c_0_19]), ['final']).
% 0.20/0.41  cnf(c_0_55, negated_conjecture, (r1_lattice3(X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2)|r2_hidden(esk1_3(X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2),X3)|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~l1_orders_2(X1)|~m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(X3)))|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_49, c_0_19]), ['final']).
% 0.20/0.41  cnf(c_0_56, negated_conjecture, (r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)|r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X3)|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X4)|~r1_orders_2(esk2_0,X1,X4)|~r2_hidden(esk4_0,X2)|~m1_subset_1(X4,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_19]), c_0_22]), c_0_26])]), ['final']).
% 0.20/0.41  cnf(c_0_57, negated_conjecture, (r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)|r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X3)|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X4)|~r1_orders_2(esk2_0,X1,X4)|~r2_hidden(esk4_0,X2)|~m1_subset_1(X4,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_19]), c_0_22]), c_0_26])]), ['final']).
% 0.20/0.41  cnf(c_0_58, negated_conjecture, (m1_subset_1(X1,X2)|~r2_hidden(X1,esk3_0)|~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_30, c_0_16]), ['final']).
% 0.20/0.41  cnf(c_0_59, negated_conjecture, (r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)|r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X3)|~r1_orders_2(esk2_0,X1,X3)|~r2_hidden(esk4_0,X2)|~m1_subset_1(X3,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_19]), c_0_22]), c_0_26])]), ['final']).
% 0.20/0.41  cnf(c_0_60, negated_conjecture, (r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)|r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X3)|~r1_orders_2(esk2_0,X1,X3)|~r2_hidden(esk4_0,X2)|~m1_subset_1(X3,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_19]), c_0_22]), c_0_26])]), ['final']).
% 0.20/0.41  cnf(c_0_61, negated_conjecture, (r1_lattice3(X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2)|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(X1,u1_struct_0(esk2_0),X2)|~l1_orders_2(X1)|~m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk3_0)))|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_18, c_0_54]), ['final']).
% 0.20/0.41  cnf(c_0_62, negated_conjecture, (r1_lattice3(X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2)|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(X1,u1_struct_0(esk2_0),X2)|~l1_orders_2(X1)|~m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk3_0)))|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_18, c_0_55]), ['final']).
% 0.20/0.41  cnf(c_0_63, negated_conjecture, (r1_orders_2(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))|~r1_orders_2(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|~r1_orders_2(esk2_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_25, c_0_36]), ['final']).
% 0.20/0.41  cnf(c_0_64, negated_conjecture, (r1_orders_2(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~r1_orders_2(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|~r1_orders_2(esk2_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_25, c_0_37]), ['final']).
% 0.20/0.41  cnf(c_0_65, negated_conjecture, (r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)|r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X3)|m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X4),u1_struct_0(esk2_0))|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))|~r1_orders_2(esk2_0,X1,X4)|~r2_hidden(esk4_0,X2)|~m1_subset_1(X4,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_56, c_0_28]), ['final']).
% 0.20/0.41  cnf(c_0_66, negated_conjecture, (r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)|r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X3)|m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X4),u1_struct_0(esk2_0))|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~r1_orders_2(esk2_0,X1,X4)|~r2_hidden(esk4_0,X2)|~m1_subset_1(X4,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_57, c_0_28]), ['final']).
% 0.20/0.41  cnf(c_0_67, negated_conjecture, (r1_lattice3(X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2)|m1_subset_1(esk1_3(X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2),X3)|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))|~l1_orders_2(X1)|~m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk3_0)))|~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X3))|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_58, c_0_54]), ['final']).
% 0.20/0.41  cnf(c_0_68, negated_conjecture, (r1_lattice3(X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2)|m1_subset_1(esk1_3(X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2),X3)|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))|~l1_orders_2(X1)|~m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(X4)))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_30, c_0_54]), ['final']).
% 0.20/0.41  cnf(c_0_69, negated_conjecture, (r1_lattice3(X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2)|m1_subset_1(esk1_3(X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2),X3)|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~l1_orders_2(X1)|~m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(X4)))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_30, c_0_55]), ['final']).
% 0.20/0.41  cnf(c_0_70, negated_conjecture, (r1_lattice3(X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2)|m1_subset_1(esk1_3(X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2),X3)|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~l1_orders_2(X1)|~m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk3_0)))|~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X3))|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_58, c_0_55]), ['final']).
% 0.20/0.41  cnf(c_0_71, negated_conjecture, (r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)|r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))|m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X3),u1_struct_0(esk2_0))|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))|~r1_orders_2(esk2_0,X1,X3)|~r2_hidden(esk4_0,X2)|~m1_subset_1(X3,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_59, c_0_28]), ['final']).
% 0.20/0.41  cnf(c_0_72, negated_conjecture, (r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)|r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))|m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X3),u1_struct_0(esk2_0))|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~r1_orders_2(esk2_0,X1,X3)|~r2_hidden(esk4_0,X2)|~m1_subset_1(X3,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_60, c_0_28]), ['final']).
% 0.20/0.41  cnf(c_0_73, negated_conjecture, (r1_lattice3(esk2_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X1)|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,u1_struct_0(esk2_0),X1)|~m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk3_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_61, c_0_22]), ['final']).
% 0.20/0.41  cnf(c_0_74, negated_conjecture, (r1_lattice3(esk2_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X1)|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,u1_struct_0(esk2_0),X1)|~m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk3_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_62, c_0_22]), ['final']).
% 0.20/0.41  cnf(c_0_75, negated_conjecture, (r1_lattice3(X1,esk3_0,X2)|m1_subset_1(esk1_3(X1,esk3_0,X2),X3)|~l1_orders_2(X1)|~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X3))|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_58, c_0_19]), ['final']).
% 0.20/0.41  cnf(c_0_76, negated_conjecture, (r1_orders_2(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,X2,X3)|~r1_orders_2(esk2_0,X1,X3)|~r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2)|~m1_subset_1(X3,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_11]), c_0_22])]), c_0_36]), ['final']).
% 0.20/0.41  cnf(c_0_77, negated_conjecture, (r1_orders_2(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,X2,X3)|~r1_orders_2(esk2_0,X1,X3)|~r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2)|~m1_subset_1(X3,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_11]), c_0_22])]), c_0_37]), ['final']).
% 0.20/0.41  cnf(c_0_78, negated_conjecture, (r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)|r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))|m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X3)|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))|~r1_orders_2(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|~r2_hidden(esk4_0,X2)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_65, c_0_36]), ['final']).
% 0.20/0.41  cnf(c_0_79, negated_conjecture, (r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)|r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))|m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X3)|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~r1_orders_2(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|~r2_hidden(esk4_0,X2)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_66, c_0_37]), ['final']).
% 0.20/0.41  cnf(c_0_80, negated_conjecture, (r1_lattice3(esk2_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X1)|m1_subset_1(esk1_3(esk2_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X1),X2)|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))|~m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk3_0)))|~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X2))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_67, c_0_22]), ['final']).
% 0.20/0.41  cnf(c_0_81, negated_conjecture, (r1_lattice3(esk2_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X1)|m1_subset_1(esk1_3(esk2_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X1),X2)|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))|~m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(X3)))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_68, c_0_22]), ['final']).
% 0.20/0.41  cnf(c_0_82, negated_conjecture, (r1_lattice3(esk2_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X1)|m1_subset_1(esk1_3(esk2_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X1),X2)|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(X3)))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_69, c_0_22]), ['final']).
% 0.20/0.41  cnf(c_0_83, negated_conjecture, (r1_lattice3(esk2_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X1)|m1_subset_1(esk1_3(esk2_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X1),X2)|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk3_0)))|~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X2))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_70, c_0_22]), ['final']).
% 0.20/0.41  cnf(c_0_84, negated_conjecture, (r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)|r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))|m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))|~r1_orders_2(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|~r2_hidden(esk4_0,X2)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_71, c_0_36]), ['final']).
% 0.20/0.41  cnf(c_0_85, negated_conjecture, (r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)|r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))|m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~r1_orders_2(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|~r2_hidden(esk4_0,X2)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_72, c_0_37]), ['final']).
% 0.20/0.41  cnf(c_0_86, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,u1_struct_0(esk2_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|~r1_lattice3(esk2_0,X2,X3)|~r1_orders_2(esk2_0,X1,X3)|~r2_hidden(esk4_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|~r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2)|~m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk3_0)))|~m1_subset_1(X3,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_73]), c_0_36]), ['final']).
% 0.20/0.41  cnf(c_0_87, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,u1_struct_0(esk2_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|~r1_lattice3(esk2_0,X2,X3)|~r1_orders_2(esk2_0,X1,X3)|~r2_hidden(esk4_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|~r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2)|~m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk3_0)))|~m1_subset_1(X3,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_74]), c_0_37]), ['final']).
% 0.20/0.41  cnf(c_0_88, negated_conjecture, (r1_lattice3(esk2_0,esk3_0,X1)|m1_subset_1(esk1_3(esk2_0,esk3_0,X1),X2)|~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X2))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_75, c_0_22]), ['final']).
% 0.20/0.41  cnf(c_0_89, negated_conjecture, (r1_lattice3(esk2_0,esk3_0,X1)|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),X1),X2)|~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X2))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_29, c_0_38]), ['final']).
% 0.20/0.41  cnf(c_0_90, negated_conjecture, (r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)|r1_orders_2(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X2)|~r1_orders_2(esk2_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_19]), c_0_22]), c_0_26])]), ['final']).
% 0.20/0.41  cnf(c_0_91, negated_conjecture, (r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)|r1_orders_2(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X2)|~r1_orders_2(esk2_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_19]), c_0_22]), c_0_26])]), ['final']).
% 0.20/0.41  cnf(c_0_92, negated_conjecture, (r1_lattice3(X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2)|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(X1,X3,X2)|~l1_orders_2(X1)|~m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(X3)))|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_15, c_0_54]), ['final']).
% 0.20/0.41  cnf(c_0_93, negated_conjecture, (r1_lattice3(X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2)|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(X1,X3,X2)|~l1_orders_2(X1)|~m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(X3)))|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_15, c_0_55]), ['final']).
% 0.20/0.41  fof(c_0_94, plain, ![X8, X9]:((~m1_subset_1(X8,k1_zfmisc_1(X9))|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|m1_subset_1(X8,k1_zfmisc_1(X9)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.41  cnf(c_0_95, negated_conjecture, (r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)|r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))|m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X3)|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,X4,X1)|~r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X4)|~r2_hidden(esk4_0,X2)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_11]), c_0_22])]), c_0_36]), ['final']).
% 0.20/0.41  cnf(c_0_96, negated_conjecture, (r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)|r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))|m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X3)|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,X4,X1)|~r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X4)|~r2_hidden(esk4_0,X2)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_11]), c_0_22])]), c_0_37]), ['final']).
% 0.20/0.41  cnf(c_0_97, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X2)|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,X3,X4)|~r1_orders_2(esk2_0,X1,X4)|~r2_hidden(esk4_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|~r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X3)|~m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk3_0)))|~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X2))|~m1_subset_1(X4,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_80]), c_0_36]), ['final']).
% 0.20/0.41  cnf(c_0_98, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X2)|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,X3,X4)|~r1_orders_2(esk2_0,X1,X4)|~r2_hidden(esk4_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|~r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X3)|~m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(X5)))|~m1_subset_1(X4,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_subset_1(X5,k1_zfmisc_1(X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_81]), c_0_36]), ['final']).
% 0.20/0.41  cnf(c_0_99, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X2)|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,X3,X4)|~r1_orders_2(esk2_0,X1,X4)|~r2_hidden(esk4_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|~r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X3)|~m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(X5)))|~m1_subset_1(X4,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_subset_1(X5,k1_zfmisc_1(X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_82]), c_0_37]), ['final']).
% 0.20/0.41  cnf(c_0_100, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X2)|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,X3,X4)|~r1_orders_2(esk2_0,X1,X4)|~r2_hidden(esk4_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|~r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X3)|~m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk3_0)))|~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X2))|~m1_subset_1(X4,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_83]), c_0_37]), ['final']).
% 0.20/0.41  cnf(c_0_101, negated_conjecture, (r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)|r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))|m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,X3,X1)|~r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X3)|~r2_hidden(esk4_0,X2)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_11]), c_0_22])]), c_0_36]), ['final']).
% 0.20/0.41  cnf(c_0_102, negated_conjecture, (r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)|r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))|m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,X3,X1)|~r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X3)|~r2_hidden(esk4_0,X2)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_11]), c_0_22])]), c_0_37]), ['final']).
% 0.20/0.41  cnf(c_0_103, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X2)|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,X3,X4)|~r1_orders_2(esk2_0,X1,X4)|~r2_hidden(esk4_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|~r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X3)|~m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk3_0)))|~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X2))|~m1_subset_1(X4,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_38]), c_0_36]), ['final']).
% 0.20/0.41  cnf(c_0_104, negated_conjecture, (r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)|r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X3)|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))|m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X4),X5)|~r1_orders_2(esk2_0,X1,X4)|~r2_hidden(esk4_0,X2)|~m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(X5))|~m1_subset_1(X4,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_56, c_0_38]), ['final']).
% 0.20/0.41  cnf(c_0_105, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X2)|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,X3,X4)|~r1_orders_2(esk2_0,X1,X4)|~r2_hidden(esk4_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|~r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X3)|~m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk3_0)))|~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X2))|~m1_subset_1(X4,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_38]), c_0_37]), ['final']).
% 0.20/0.41  cnf(c_0_106, negated_conjecture, (r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)|r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X3)|m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X4),X5)|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~r1_orders_2(esk2_0,X1,X4)|~r2_hidden(esk4_0,X2)|~m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(X5))|~m1_subset_1(X4,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_57, c_0_38]), ['final']).
% 0.20/0.41  cnf(c_0_107, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,X2,X3)|~r1_orders_2(esk2_0,X1,X3)|~r2_hidden(esk4_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|~r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2)|~m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk3_0)))|~m1_subset_1(X3,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_28]), c_0_36]), ['final']).
% 0.20/0.41  cnf(c_0_108, negated_conjecture, (r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)|r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))|m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X3),X4)|~r1_orders_2(esk2_0,X1,X3)|~r2_hidden(esk4_0,X2)|~m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(X4))|~m1_subset_1(X3,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_59, c_0_38]), ['final']).
% 0.20/0.41  cnf(c_0_109, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,X2,X3)|~r1_orders_2(esk2_0,X1,X3)|~r2_hidden(esk4_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|~r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2)|~m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk3_0)))|~m1_subset_1(X3,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_28]), c_0_37]), ['final']).
% 0.20/0.41  cnf(c_0_110, negated_conjecture, (r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)|r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))|m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X3),X4)|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~r1_orders_2(esk2_0,X1,X3)|~r2_hidden(esk4_0,X2)|~m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(X4))|~m1_subset_1(X3,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_60, c_0_38]), ['final']).
% 0.20/0.41  cnf(c_0_111, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,esk3_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X2)|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,X3,X4)|~r1_orders_2(esk2_0,X1,X4)|~r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X3)|~r2_hidden(esk4_0,esk3_0)|~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X2))|~m1_subset_1(X4,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_88]), c_0_36]), ['final']).
% 0.20/0.41  cnf(c_0_112, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X3)|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,u1_struct_0(esk2_0),X4)|~r1_orders_2(esk2_0,X1,X4)|~r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),esk3_0)|~r2_hidden(esk4_0,X2)|~m1_subset_1(X4,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_50, c_0_16]), ['final']).
% 0.20/0.41  cnf(c_0_113, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X2)|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,X3,X4)|~r1_orders_2(esk2_0,X1,X4)|~r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X3)|~r2_hidden(esk4_0,esk3_0)|~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X2))|~m1_subset_1(X4,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_89]), c_0_36]), ['final']).
% 0.20/0.41  cnf(c_0_114, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,u1_struct_0(esk2_0),X3)|~r1_orders_2(esk2_0,X1,X3)|~r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),esk3_0)|~r2_hidden(esk4_0,X2)|~m1_subset_1(X3,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_52, c_0_16]), ['final']).
% 0.20/0.41  cnf(c_0_115, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,esk3_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X2)|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,X3,X4)|~r1_orders_2(esk2_0,X1,X4)|~r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X3)|~r2_hidden(esk4_0,esk3_0)|~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X2))|~m1_subset_1(X4,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_88]), c_0_37]), ['final']).
% 0.20/0.41  cnf(c_0_116, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,X2,X3)|~r1_orders_2(esk2_0,X1,X3)|~r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2)|~r2_hidden(esk4_0,esk3_0)|~m1_subset_1(X3,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_33]), c_0_36]), ['final']).
% 0.20/0.41  cnf(c_0_117, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X3)|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,u1_struct_0(esk2_0),X4)|~r1_orders_2(esk2_0,X1,X4)|~r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),esk3_0)|~r2_hidden(esk4_0,X2)|~m1_subset_1(X4,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_51, c_0_16]), ['final']).
% 0.20/0.41  cnf(c_0_118, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),X2)|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,X3,X4)|~r1_orders_2(esk2_0,X1,X4)|~r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X3)|~r2_hidden(esk4_0,esk3_0)|~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X2))|~m1_subset_1(X4,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_89]), c_0_37]), ['final']).
% 0.20/0.41  cnf(c_0_119, negated_conjecture, (r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)|r1_orders_2(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))|m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X2),X3)|~r1_orders_2(esk2_0,X1,X2)|~m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(X3))|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_90, c_0_38]), ['final']).
% 0.20/0.41  cnf(c_0_120, negated_conjecture, (r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)|r1_orders_2(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X2),X3)|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~r1_orders_2(esk2_0,X1,X2)|~m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(X3))|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_91, c_0_38]), ['final']).
% 0.20/0.41  cnf(c_0_121, negated_conjecture, (r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)|r1_orders_2(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X2),u1_struct_0(esk2_0))|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))|~r1_orders_2(esk2_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_90, c_0_28]), ['final']).
% 0.20/0.41  cnf(c_0_122, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,u1_struct_0(esk2_0),X3)|~r1_orders_2(esk2_0,X1,X3)|~r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),esk3_0)|~r2_hidden(esk4_0,X2)|~m1_subset_1(X3,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_53, c_0_16]), ['final']).
% 0.20/0.41  cnf(c_0_123, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)),u1_struct_0(esk2_0))|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,X2,X3)|~r1_orders_2(esk2_0,X1,X3)|~r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X2)|~r2_hidden(esk4_0,esk3_0)|~m1_subset_1(X3,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_33]), c_0_37]), ['final']).
% 0.20/0.41  cnf(c_0_124, negated_conjecture, (r1_orders_2(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,u1_struct_0(esk2_0),X2)|~r1_orders_2(esk2_0,X1,X2)|~r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),esk3_0)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_76, c_0_16]), ['final']).
% 0.20/0.41  cnf(c_0_125, negated_conjecture, (r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)|r1_orders_2(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X2),u1_struct_0(esk2_0))|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~r1_orders_2(esk2_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_91, c_0_28]), ['final']).
% 0.20/0.41  cnf(c_0_126, negated_conjecture, (r1_orders_2(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,u1_struct_0(esk2_0),X2)|~r1_orders_2(esk2_0,X1,X2)|~r2_hidden(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),esk3_0)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_77, c_0_16]), ['final']).
% 0.20/0.41  cnf(c_0_127, negated_conjecture, (r1_lattice3(esk2_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X1)|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,X2,X1)|~m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_92, c_0_22]), ['final']).
% 0.20/0.41  cnf(c_0_128, negated_conjecture, (r1_lattice3(esk2_0,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X1)|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,X2,X1)|~m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_93, c_0_22]), ['final']).
% 0.20/0.41  cnf(c_0_129, negated_conjecture, (m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X1)|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),X2)|~m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(X1))|~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_89]), c_0_26])]), ['final']).
% 0.20/0.41  cnf(c_0_130, negated_conjecture, (m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X1)|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),X2)|~m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(X1))|~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_88]), c_0_26])]), ['final']).
% 0.20/0.41  cnf(c_0_131, negated_conjecture, (m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),u1_struct_0(esk2_0))|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),X1)|~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_88]), c_0_26])]), ['final']).
% 0.20/0.41  cnf(c_0_132, negated_conjecture, (m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),X1)|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),X2)|~m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(X1))|~m1_subset_1(esk3_0,k1_zfmisc_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_38]), c_0_26])]), ['final']).
% 0.20/0.41  cnf(c_0_133, negated_conjecture, (m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),u1_struct_0(esk2_0))|m1_subset_1(esk1_3(esk2_0,u1_struct_0(esk2_0),esk4_0),X1)|~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_89]), c_0_26])]), ['final']).
% 0.20/0.41  cnf(c_0_134, negated_conjecture, (m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),u1_struct_0(esk2_0))|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),X1)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_38]), c_0_26])]), ['final']).
% 0.20/0.41  cnf(c_0_135, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_94]), ['final']).
% 0.20/0.41  cnf(c_0_136, negated_conjecture, (r1_lattice3(esk2_0,esk3_0,esk4_0)|r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.20/0.41  cnf(c_0_137, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_94]), ['final']).
% 0.20/0.41  cnf(c_0_138, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.20/0.41  cnf(c_0_139, negated_conjecture, (v3_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.20/0.41  # SZS output end Saturation
% 0.20/0.41  # Proof object total steps             : 140
% 0.20/0.41  # Proof object clause steps            : 127
% 0.20/0.41  # Proof object formula steps           : 13
% 0.20/0.41  # Proof object conjectures             : 119
% 0.20/0.41  # Proof object clause conjectures      : 116
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 17
% 0.20/0.41  # Proof object initial formulas used   : 6
% 0.20/0.41  # Proof object generating inferences   : 110
% 0.20/0.41  # Proof object simplifying inferences  : 92
% 0.20/0.41  # Parsed axioms                        : 6
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 17
% 0.20/0.41  # Removed in clause preprocessing      : 0
% 0.20/0.41  # Initial clauses in saturation        : 17
% 0.20/0.41  # Processed clauses                    : 179
% 0.20/0.41  # ...of these trivial                  : 0
% 0.20/0.41  # ...subsumed                          : 33
% 0.20/0.41  # ...remaining for further processing  : 146
% 0.20/0.41  # Other redundant clauses eliminated   : 0
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 2
% 0.20/0.41  # Backward-rewritten                   : 0
% 0.20/0.41  # Generated clauses                    : 165
% 0.20/0.41  # ...of the previous two non-trivial   : 145
% 0.20/0.41  # Contextual simplify-reflections      : 29
% 0.20/0.41  # Paramodulations                      : 165
% 0.20/0.41  # Factorizations                       : 0
% 0.20/0.41  # Equation resolutions                 : 0
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 127
% 0.20/0.41  #    Positive orientable unit clauses  : 5
% 0.20/0.41  #    Positive unorientable unit clauses: 0
% 0.20/0.41  #    Negative unit clauses             : 1
% 0.20/0.41  #    Non-unit-clauses                  : 121
% 0.20/0.41  # Current number of unprocessed clauses: 0
% 0.20/0.41  # ...number of literals in the above   : 0
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 19
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 10328
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 1603
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 64
% 0.20/0.41  # Unit Clause-clause subsumption calls : 0
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 0
% 0.20/0.41  # BW rewrite match successes           : 0
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 13456
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.060 s
% 0.20/0.41  # System time              : 0.003 s
% 0.20/0.41  # Total time               : 0.063 s
% 0.20/0.41  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
