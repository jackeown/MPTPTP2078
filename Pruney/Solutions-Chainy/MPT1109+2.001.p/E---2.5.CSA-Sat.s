%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:05 EST 2020

% Result     : CounterSatisfiable 0.06s
% Output     : Saturation 0.06s
% Verified   : 
% Statistics : Number of formulae       :   64 (1099 expanded)
%              Number of clauses        :   53 ( 455 expanded)
%              Number of leaves         :    5 ( 258 expanded)
%              Depth                    :    9
%              Number of atoms          :  286 (5841 expanded)
%              Number of equality atoms :   58 (1698 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   61 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(free_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3,X4] :
          ( g1_pre_topc(X1,X2) = g1_pre_topc(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(t31_pre_topc,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( l1_pre_topc(X3)
             => ! [X4] :
                  ( l1_pre_topc(X4)
                 => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                      & g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) = g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))
                      & m1_pre_topc(X3,X1) )
                   => m1_pre_topc(X4,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_pre_topc)).

fof(d9_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( m1_pre_topc(X2,X1)
          <=> ( r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
              & ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( r2_hidden(X3,u1_pre_topc(X2))
                  <=> ? [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                        & r2_hidden(X4,u1_pre_topc(X1))
                        & X3 = k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_5,plain,(
    ! [X15,X16,X17,X18] :
      ( ( X15 = X17
        | g1_pre_topc(X15,X16) != g1_pre_topc(X17,X18)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(X15))) )
      & ( X16 = X18
        | g1_pre_topc(X15,X16) != g1_pre_topc(X17,X18)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(X15))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).

fof(c_0_6,plain,(
    ! [X14] :
      ( ~ l1_pre_topc(X14)
      | m1_subset_1(u1_pre_topc(X14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( l1_pre_topc(X2)
           => ! [X3] :
                ( l1_pre_topc(X3)
               => ! [X4] :
                    ( l1_pre_topc(X4)
                   => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                        & g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) = g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))
                        & m1_pre_topc(X3,X1) )
                     => m1_pre_topc(X4,X2) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_pre_topc])).

cnf(c_0_8,plain,
    ( X1 = X2
    | g1_pre_topc(X3,X1) != g1_pre_topc(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_9,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

fof(c_0_10,negated_conjecture,
    ( l1_pre_topc(esk4_0)
    & l1_pre_topc(esk5_0)
    & l1_pre_topc(esk6_0)
    & l1_pre_topc(esk7_0)
    & g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) = g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))
    & g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)) = g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))
    & m1_pre_topc(esk6_0,esk4_0)
    & ~ m1_pre_topc(esk7_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_11,plain,
    ( u1_pre_topc(X1) = X2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9]),
    [final]).

cnf(c_0_12,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) = g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_14,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)) = g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_16,negated_conjecture,
    ( u1_pre_topc(esk4_0) = X1
    | g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) != g1_pre_topc(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])])).

cnf(c_0_17,negated_conjecture,
    ( u1_pre_topc(esk7_0) = X1
    | g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)) != g1_pre_topc(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_14]),c_0_15])])).

cnf(c_0_18,plain,
    ( X1 = X2
    | g1_pre_topc(X1,X3) != g1_pre_topc(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_19,negated_conjecture,
    ( u1_pre_topc(esk4_0) = u1_pre_topc(esk5_0) ),
    inference(er,[status(thm)],[c_0_16]),
    [final]).

cnf(c_0_20,negated_conjecture,
    ( u1_pre_topc(esk7_0) = u1_pre_topc(esk6_0) ),
    inference(er,[status(thm)],[c_0_17]),
    [final]).

fof(c_0_21,plain,(
    ! [X5,X6,X7,X9,X11] :
      ( ( r1_tarski(k2_struct_0(X6),k2_struct_0(X5))
        | ~ m1_pre_topc(X6,X5)
        | ~ l1_pre_topc(X6)
        | ~ l1_pre_topc(X5) )
      & ( m1_subset_1(esk1_3(X5,X6,X7),k1_zfmisc_1(u1_struct_0(X5)))
        | ~ r2_hidden(X7,u1_pre_topc(X6))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_pre_topc(X6,X5)
        | ~ l1_pre_topc(X6)
        | ~ l1_pre_topc(X5) )
      & ( r2_hidden(esk1_3(X5,X6,X7),u1_pre_topc(X5))
        | ~ r2_hidden(X7,u1_pre_topc(X6))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_pre_topc(X6,X5)
        | ~ l1_pre_topc(X6)
        | ~ l1_pre_topc(X5) )
      & ( X7 = k9_subset_1(u1_struct_0(X6),esk1_3(X5,X6,X7),k2_struct_0(X6))
        | ~ r2_hidden(X7,u1_pre_topc(X6))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_pre_topc(X6,X5)
        | ~ l1_pre_topc(X6)
        | ~ l1_pre_topc(X5) )
      & ( ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ r2_hidden(X9,u1_pre_topc(X5))
        | X7 != k9_subset_1(u1_struct_0(X6),X9,k2_struct_0(X6))
        | r2_hidden(X7,u1_pre_topc(X6))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_pre_topc(X6,X5)
        | ~ l1_pre_topc(X6)
        | ~ l1_pre_topc(X5) )
      & ( m1_subset_1(esk2_2(X5,X6),k1_zfmisc_1(u1_struct_0(X6)))
        | ~ r1_tarski(k2_struct_0(X6),k2_struct_0(X5))
        | m1_pre_topc(X6,X5)
        | ~ l1_pre_topc(X6)
        | ~ l1_pre_topc(X5) )
      & ( ~ r2_hidden(esk2_2(X5,X6),u1_pre_topc(X6))
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ r2_hidden(X11,u1_pre_topc(X5))
        | esk2_2(X5,X6) != k9_subset_1(u1_struct_0(X6),X11,k2_struct_0(X6))
        | ~ r1_tarski(k2_struct_0(X6),k2_struct_0(X5))
        | m1_pre_topc(X6,X5)
        | ~ l1_pre_topc(X6)
        | ~ l1_pre_topc(X5) )
      & ( m1_subset_1(esk3_2(X5,X6),k1_zfmisc_1(u1_struct_0(X5)))
        | r2_hidden(esk2_2(X5,X6),u1_pre_topc(X6))
        | ~ r1_tarski(k2_struct_0(X6),k2_struct_0(X5))
        | m1_pre_topc(X6,X5)
        | ~ l1_pre_topc(X6)
        | ~ l1_pre_topc(X5) )
      & ( r2_hidden(esk3_2(X5,X6),u1_pre_topc(X5))
        | r2_hidden(esk2_2(X5,X6),u1_pre_topc(X6))
        | ~ r1_tarski(k2_struct_0(X6),k2_struct_0(X5))
        | m1_pre_topc(X6,X5)
        | ~ l1_pre_topc(X6)
        | ~ l1_pre_topc(X5) )
      & ( esk2_2(X5,X6) = k9_subset_1(u1_struct_0(X6),esk3_2(X5,X6),k2_struct_0(X6))
        | r2_hidden(esk2_2(X5,X6),u1_pre_topc(X6))
        | ~ r1_tarski(k2_struct_0(X6),k2_struct_0(X5))
        | m1_pre_topc(X6,X5)
        | ~ l1_pre_topc(X6)
        | ~ l1_pre_topc(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).

cnf(c_0_22,plain,
    ( u1_struct_0(X1) = X2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_9]),
    [final]).

cnf(c_0_23,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk5_0)) = g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_12,c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(esk6_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_20]),c_0_15])])).

cnf(c_0_25,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk6_0)) = g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)) ),
    inference(rw,[status(thm)],[c_0_14,c_0_20])).

cnf(c_0_26,plain,
    ( r2_hidden(X3,u1_pre_topc(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | X3 != k9_subset_1(u1_struct_0(X4),X1,k2_struct_0(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_pre_topc(X4,X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( u1_struct_0(esk4_0) = X1
    | g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) != g1_pre_topc(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_19]),c_0_23]),c_0_13])])).

cnf(c_0_28,negated_conjecture,
    ( u1_struct_0(esk7_0) = X1
    | g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)) != g1_pre_topc(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_24]),c_0_25])).

cnf(c_0_29,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(X2,u1_pre_topc(X3))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3) ),
    inference(er,[status(thm)],[c_0_26]),
    [final]).

cnf(c_0_30,negated_conjecture,
    ( u1_struct_0(esk4_0) = u1_struct_0(esk5_0) ),
    inference(er,[status(thm)],[c_0_27]),
    [final]).

cnf(c_0_31,negated_conjecture,
    ( u1_struct_0(esk7_0) = u1_struct_0(esk6_0) ),
    inference(er,[status(thm)],[c_0_28]),
    [final]).

cnf(c_0_32,plain,
    ( X1 = k9_subset_1(u1_struct_0(X2),esk1_3(X3,X2,X1),k2_struct_0(X2))
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21]),
    [final]).

cnf(c_0_33,plain,
    ( m1_pre_topc(X2,X1)
    | ~ r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,u1_pre_topc(X1))
    | esk2_2(X1,X2) != k9_subset_1(u1_struct_0(X2),X3,k2_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21]),
    [final]).

cnf(c_0_34,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,u1_pre_topc(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21]),
    [final]).

cnf(c_0_35,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),u1_pre_topc(X1))
    | ~ r2_hidden(X3,u1_pre_topc(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21]),
    [final]).

fof(c_0_36,plain,(
    ! [X13] :
      ( ~ l1_pre_topc(X13)
      | l1_struct_0(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_19]),c_0_13])])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k9_subset_1(u1_struct_0(esk5_0),X1,k2_struct_0(esk4_0)),u1_pre_topc(esk5_0))
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(esk5_0),X1,k2_struct_0(esk4_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(esk4_0,X2)
    | ~ l1_pre_topc(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_19]),c_0_13])]),
    [final]).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(k9_subset_1(u1_struct_0(esk6_0),X1,k2_struct_0(esk7_0)),u1_pre_topc(esk6_0))
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(esk6_0),X1,k2_struct_0(esk7_0)),k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(esk7_0,X2)
    | ~ l1_pre_topc(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_31]),c_0_20]),c_0_15])]),
    [final]).

cnf(c_0_40,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk5_0),esk1_3(X1,esk4_0,X2),k2_struct_0(esk4_0)) = X2
    | ~ r2_hidden(X2,u1_pre_topc(esk5_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_30]),c_0_19]),c_0_13])]),
    [final]).

cnf(c_0_41,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk6_0),esk1_3(X1,esk7_0,X2),k2_struct_0(esk7_0)) = X2
    | ~ r2_hidden(X2,u1_pre_topc(esk6_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ m1_pre_topc(esk7_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_31]),c_0_20]),c_0_15])]),
    [final]).

cnf(c_0_42,negated_conjecture,
    ( m1_pre_topc(esk4_0,X1)
    | esk2_2(X1,esk4_0) != k9_subset_1(u1_struct_0(esk5_0),X2,k2_struct_0(esk4_0))
    | ~ r2_hidden(esk2_2(X1,esk4_0),u1_pre_topc(esk5_0))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(esk4_0),k2_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_19]),c_0_13])]),c_0_30]),
    [final]).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk1_3(esk4_0,X1,X2),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_30]),c_0_13])]),
    [final]).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk1_3(esk7_0,X1,X2),k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,esk7_0)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_31]),c_0_15])]),
    [final]).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk1_3(esk4_0,X1,X2),u1_pre_topc(esk5_0))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_19]),c_0_13])]),
    [final]).

cnf(c_0_46,negated_conjecture,
    ( m1_pre_topc(esk7_0,X1)
    | esk2_2(X1,esk7_0) != k9_subset_1(u1_struct_0(esk6_0),X2,k2_struct_0(esk7_0))
    | ~ r2_hidden(esk2_2(X1,esk7_0),u1_pre_topc(esk6_0))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(esk7_0),k2_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_20]),c_0_15])]),c_0_31]),
    [final]).

cnf(c_0_47,negated_conjecture,
    ( u1_struct_0(esk5_0) = X1
    | g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) != g1_pre_topc(X1,X2) ),
    inference(rw,[status(thm)],[c_0_27,c_0_30]),
    [final]).

cnf(c_0_48,negated_conjecture,
    ( u1_struct_0(esk6_0) = X1
    | g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)) != g1_pre_topc(X1,X2) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_20]),c_0_25]),c_0_15])]),c_0_31]),
    [final]).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk1_3(esk7_0,X1,X2),u1_pre_topc(esk6_0))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,esk7_0)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_20]),c_0_15])]),
    [final]).

cnf(c_0_50,negated_conjecture,
    ( u1_pre_topc(esk5_0) = X1
    | g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) != g1_pre_topc(X2,X1) ),
    inference(rw,[status(thm)],[c_0_16,c_0_19]),
    [final]).

cnf(c_0_51,negated_conjecture,
    ( u1_pre_topc(esk6_0) = X1
    | g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)) != g1_pre_topc(X2,X1) ),
    inference(rw,[status(thm)],[c_0_17,c_0_20]),
    [final]).

cnf(c_0_52,plain,
    ( esk2_2(X1,X2) = k9_subset_1(u1_struct_0(X2),esk3_2(X1,X2),k2_struct_0(X2))
    | r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))
    | m1_pre_topc(X2,X1)
    | ~ r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21]),
    [final]).

cnf(c_0_53,plain,
    ( m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))
    | m1_pre_topc(X2,X1)
    | ~ r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21]),
    [final]).

cnf(c_0_54,plain,
    ( r2_hidden(esk3_2(X1,X2),u1_pre_topc(X1))
    | r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))
    | m1_pre_topc(X2,X1)
    | ~ r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21]),
    [final]).

cnf(c_0_55,plain,
    ( m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
    | m1_pre_topc(X2,X1)
    | ~ r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21]),
    [final]).

cnf(c_0_56,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21]),
    [final]).

cnf(c_0_57,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36]),
    [final]).

cnf(c_0_58,negated_conjecture,
    ( ~ m1_pre_topc(esk7_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(rw,[status(thm)],[c_0_37,c_0_30]),
    [final]).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(esk6_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0)))) ),
    inference(rw,[status(thm)],[c_0_24,c_0_31]),
    [final]).

cnf(c_0_61,negated_conjecture,
    ( m1_pre_topc(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_62,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_63,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.06/0.26  % Computer   : n020.cluster.edu
% 0.06/0.26  % Model      : x86_64 x86_64
% 0.06/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.26  % Memory     : 8042.1875MB
% 0.06/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.26  % CPULimit   : 60
% 0.06/0.26  % WCLimit    : 600
% 0.06/0.26  % DateTime   : Tue Dec  1 18:06:52 EST 2020
% 0.06/0.26  % CPUTime    : 
% 0.06/0.26  # Version: 2.5pre002
% 0.06/0.27  # No SInE strategy applied
% 0.06/0.27  # Trying AutoSched0 for 299 seconds
% 0.06/0.28  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.06/0.28  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.06/0.28  #
% 0.06/0.28  # Preprocessing time       : 0.016 s
% 0.06/0.28  # Presaturation interreduction done
% 0.06/0.28  
% 0.06/0.28  # No proof found!
% 0.06/0.28  # SZS status CounterSatisfiable
% 0.06/0.28  # SZS output start Saturation
% 0.06/0.28  fof(free_g1_pre_topc, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3, X4]:(g1_pre_topc(X1,X2)=g1_pre_topc(X3,X4)=>(X1=X3&X2=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 0.06/0.28  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.06/0.28  fof(t31_pre_topc, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>![X3]:(l1_pre_topc(X3)=>![X4]:(l1_pre_topc(X4)=>(((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))&g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))=g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)))&m1_pre_topc(X3,X1))=>m1_pre_topc(X4,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_pre_topc)).
% 0.06/0.28  fof(d9_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X2,X1)<=>(r1_tarski(k2_struct_0(X2),k2_struct_0(X1))&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>(r2_hidden(X3,u1_pre_topc(X2))<=>?[X4]:((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&r2_hidden(X4,u1_pre_topc(X1)))&X3=k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_pre_topc)).
% 0.06/0.28  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.06/0.28  fof(c_0_5, plain, ![X15, X16, X17, X18]:((X15=X17|g1_pre_topc(X15,X16)!=g1_pre_topc(X17,X18)|~m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(X15))))&(X16=X18|g1_pre_topc(X15,X16)!=g1_pre_topc(X17,X18)|~m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).
% 0.06/0.28  fof(c_0_6, plain, ![X14]:(~l1_pre_topc(X14)|m1_subset_1(u1_pre_topc(X14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.06/0.28  fof(c_0_7, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>![X3]:(l1_pre_topc(X3)=>![X4]:(l1_pre_topc(X4)=>(((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))&g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))=g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)))&m1_pre_topc(X3,X1))=>m1_pre_topc(X4,X2))))))), inference(assume_negation,[status(cth)],[t31_pre_topc])).
% 0.06/0.28  cnf(c_0_8, plain, (X1=X2|g1_pre_topc(X3,X1)!=g1_pre_topc(X4,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.06/0.28  cnf(c_0_9, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.06/0.28  fof(c_0_10, negated_conjecture, (l1_pre_topc(esk4_0)&(l1_pre_topc(esk5_0)&(l1_pre_topc(esk6_0)&(l1_pre_topc(esk7_0)&(((g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))=g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))&g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))=g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)))&m1_pre_topc(esk6_0,esk4_0))&~m1_pre_topc(esk7_0,esk5_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.06/0.28  cnf(c_0_11, plain, (u1_pre_topc(X1)=X2|g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))!=g1_pre_topc(X3,X2)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_8, c_0_9]), ['final']).
% 0.06/0.28  cnf(c_0_12, negated_conjecture, (g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))=g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.06/0.28  cnf(c_0_13, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.06/0.28  cnf(c_0_14, negated_conjecture, (g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))=g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.06/0.28  cnf(c_0_15, negated_conjecture, (l1_pre_topc(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.06/0.28  cnf(c_0_16, negated_conjecture, (u1_pre_topc(esk4_0)=X1|g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))!=g1_pre_topc(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13])])).
% 0.06/0.28  cnf(c_0_17, negated_conjecture, (u1_pre_topc(esk7_0)=X1|g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))!=g1_pre_topc(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_14]), c_0_15])])).
% 0.06/0.28  cnf(c_0_18, plain, (X1=X2|g1_pre_topc(X1,X3)!=g1_pre_topc(X2,X4)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.06/0.28  cnf(c_0_19, negated_conjecture, (u1_pre_topc(esk4_0)=u1_pre_topc(esk5_0)), inference(er,[status(thm)],[c_0_16]), ['final']).
% 0.06/0.28  cnf(c_0_20, negated_conjecture, (u1_pre_topc(esk7_0)=u1_pre_topc(esk6_0)), inference(er,[status(thm)],[c_0_17]), ['final']).
% 0.06/0.28  fof(c_0_21, plain, ![X5, X6, X7, X9, X11]:(((r1_tarski(k2_struct_0(X6),k2_struct_0(X5))|~m1_pre_topc(X6,X5)|~l1_pre_topc(X6)|~l1_pre_topc(X5))&((((m1_subset_1(esk1_3(X5,X6,X7),k1_zfmisc_1(u1_struct_0(X5)))|~r2_hidden(X7,u1_pre_topc(X6))|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))|~m1_pre_topc(X6,X5)|~l1_pre_topc(X6)|~l1_pre_topc(X5))&(r2_hidden(esk1_3(X5,X6,X7),u1_pre_topc(X5))|~r2_hidden(X7,u1_pre_topc(X6))|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))|~m1_pre_topc(X6,X5)|~l1_pre_topc(X6)|~l1_pre_topc(X5)))&(X7=k9_subset_1(u1_struct_0(X6),esk1_3(X5,X6,X7),k2_struct_0(X6))|~r2_hidden(X7,u1_pre_topc(X6))|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))|~m1_pre_topc(X6,X5)|~l1_pre_topc(X6)|~l1_pre_topc(X5)))&(~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X5)))|~r2_hidden(X9,u1_pre_topc(X5))|X7!=k9_subset_1(u1_struct_0(X6),X9,k2_struct_0(X6))|r2_hidden(X7,u1_pre_topc(X6))|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))|~m1_pre_topc(X6,X5)|~l1_pre_topc(X6)|~l1_pre_topc(X5))))&((m1_subset_1(esk2_2(X5,X6),k1_zfmisc_1(u1_struct_0(X6)))|~r1_tarski(k2_struct_0(X6),k2_struct_0(X5))|m1_pre_topc(X6,X5)|~l1_pre_topc(X6)|~l1_pre_topc(X5))&((~r2_hidden(esk2_2(X5,X6),u1_pre_topc(X6))|(~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X5)))|~r2_hidden(X11,u1_pre_topc(X5))|esk2_2(X5,X6)!=k9_subset_1(u1_struct_0(X6),X11,k2_struct_0(X6)))|~r1_tarski(k2_struct_0(X6),k2_struct_0(X5))|m1_pre_topc(X6,X5)|~l1_pre_topc(X6)|~l1_pre_topc(X5))&(((m1_subset_1(esk3_2(X5,X6),k1_zfmisc_1(u1_struct_0(X5)))|r2_hidden(esk2_2(X5,X6),u1_pre_topc(X6))|~r1_tarski(k2_struct_0(X6),k2_struct_0(X5))|m1_pre_topc(X6,X5)|~l1_pre_topc(X6)|~l1_pre_topc(X5))&(r2_hidden(esk3_2(X5,X6),u1_pre_topc(X5))|r2_hidden(esk2_2(X5,X6),u1_pre_topc(X6))|~r1_tarski(k2_struct_0(X6),k2_struct_0(X5))|m1_pre_topc(X6,X5)|~l1_pre_topc(X6)|~l1_pre_topc(X5)))&(esk2_2(X5,X6)=k9_subset_1(u1_struct_0(X6),esk3_2(X5,X6),k2_struct_0(X6))|r2_hidden(esk2_2(X5,X6),u1_pre_topc(X6))|~r1_tarski(k2_struct_0(X6),k2_struct_0(X5))|m1_pre_topc(X6,X5)|~l1_pre_topc(X6)|~l1_pre_topc(X5)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).
% 0.06/0.28  cnf(c_0_22, plain, (u1_struct_0(X1)=X2|g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))!=g1_pre_topc(X2,X3)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_18, c_0_9]), ['final']).
% 0.06/0.28  cnf(c_0_23, negated_conjecture, (g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk5_0))=g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))), inference(rw,[status(thm)],[c_0_12, c_0_19])).
% 0.06/0.28  cnf(c_0_24, negated_conjecture, (m1_subset_1(u1_pre_topc(esk6_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_20]), c_0_15])])).
% 0.06/0.28  cnf(c_0_25, negated_conjecture, (g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk6_0))=g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))), inference(rw,[status(thm)],[c_0_14, c_0_20])).
% 0.06/0.28  cnf(c_0_26, plain, (r2_hidden(X3,u1_pre_topc(X4))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X1,u1_pre_topc(X2))|X3!=k9_subset_1(u1_struct_0(X4),X1,k2_struct_0(X4))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|~m1_pre_topc(X4,X2)|~l1_pre_topc(X4)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.06/0.28  cnf(c_0_27, negated_conjecture, (u1_struct_0(esk4_0)=X1|g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))!=g1_pre_topc(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_19]), c_0_23]), c_0_13])])).
% 0.06/0.28  cnf(c_0_28, negated_conjecture, (u1_struct_0(esk7_0)=X1|g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))!=g1_pre_topc(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_24]), c_0_25])).
% 0.06/0.28  cnf(c_0_29, plain, (r2_hidden(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),u1_pre_topc(X1))|~r2_hidden(X2,u1_pre_topc(X3))|~m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_pre_topc(X1,X3)|~l1_pre_topc(X1)|~l1_pre_topc(X3)), inference(er,[status(thm)],[c_0_26]), ['final']).
% 0.06/0.28  cnf(c_0_30, negated_conjecture, (u1_struct_0(esk4_0)=u1_struct_0(esk5_0)), inference(er,[status(thm)],[c_0_27]), ['final']).
% 0.06/0.28  cnf(c_0_31, negated_conjecture, (u1_struct_0(esk7_0)=u1_struct_0(esk6_0)), inference(er,[status(thm)],[c_0_28]), ['final']).
% 0.06/0.28  cnf(c_0_32, plain, (X1=k9_subset_1(u1_struct_0(X2),esk1_3(X3,X2,X1),k2_struct_0(X2))|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X2,X3)|~l1_pre_topc(X2)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_21]), ['final']).
% 0.06/0.28  cnf(c_0_33, plain, (m1_pre_topc(X2,X1)|~r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X3,u1_pre_topc(X1))|esk2_2(X1,X2)!=k9_subset_1(u1_struct_0(X2),X3,k2_struct_0(X2))|~r1_tarski(k2_struct_0(X2),k2_struct_0(X1))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_21]), ['final']).
% 0.06/0.28  cnf(c_0_34, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X3,u1_pre_topc(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_21]), ['final']).
% 0.06/0.28  cnf(c_0_35, plain, (r2_hidden(esk1_3(X1,X2,X3),u1_pre_topc(X1))|~r2_hidden(X3,u1_pre_topc(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_21]), ['final']).
% 0.06/0.28  fof(c_0_36, plain, ![X13]:(~l1_pre_topc(X13)|l1_struct_0(X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.06/0.28  cnf(c_0_37, negated_conjecture, (m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_19]), c_0_13])])).
% 0.06/0.28  cnf(c_0_38, negated_conjecture, (r2_hidden(k9_subset_1(u1_struct_0(esk5_0),X1,k2_struct_0(esk4_0)),u1_pre_topc(esk5_0))|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(k9_subset_1(u1_struct_0(esk5_0),X1,k2_struct_0(esk4_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(esk4_0,X2)|~l1_pre_topc(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_19]), c_0_13])]), ['final']).
% 0.06/0.28  cnf(c_0_39, negated_conjecture, (r2_hidden(k9_subset_1(u1_struct_0(esk6_0),X1,k2_struct_0(esk7_0)),u1_pre_topc(esk6_0))|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(k9_subset_1(u1_struct_0(esk6_0),X1,k2_struct_0(esk7_0)),k1_zfmisc_1(u1_struct_0(esk6_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(esk7_0,X2)|~l1_pre_topc(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_31]), c_0_20]), c_0_15])]), ['final']).
% 0.06/0.28  cnf(c_0_40, negated_conjecture, (k9_subset_1(u1_struct_0(esk5_0),esk1_3(X1,esk4_0,X2),k2_struct_0(esk4_0))=X2|~r2_hidden(X2,u1_pre_topc(esk5_0))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_30]), c_0_19]), c_0_13])]), ['final']).
% 0.06/0.28  cnf(c_0_41, negated_conjecture, (k9_subset_1(u1_struct_0(esk6_0),esk1_3(X1,esk7_0,X2),k2_struct_0(esk7_0))=X2|~r2_hidden(X2,u1_pre_topc(esk6_0))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk6_0)))|~m1_pre_topc(esk7_0,X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_31]), c_0_20]), c_0_15])]), ['final']).
% 0.06/0.28  cnf(c_0_42, negated_conjecture, (m1_pre_topc(esk4_0,X1)|esk2_2(X1,esk4_0)!=k9_subset_1(u1_struct_0(esk5_0),X2,k2_struct_0(esk4_0))|~r2_hidden(esk2_2(X1,esk4_0),u1_pre_topc(esk5_0))|~r2_hidden(X2,u1_pre_topc(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(esk4_0),k2_struct_0(X1))|~l1_pre_topc(X1)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_19]), c_0_13])]), c_0_30]), ['final']).
% 0.06/0.28  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk1_3(esk4_0,X1,X2),k1_zfmisc_1(u1_struct_0(esk5_0)))|~r2_hidden(X2,u1_pre_topc(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X1,esk4_0)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_30]), c_0_13])]), ['final']).
% 0.06/0.28  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk1_3(esk7_0,X1,X2),k1_zfmisc_1(u1_struct_0(esk6_0)))|~r2_hidden(X2,u1_pre_topc(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X1,esk7_0)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_31]), c_0_15])]), ['final']).
% 0.06/0.28  cnf(c_0_45, negated_conjecture, (r2_hidden(esk1_3(esk4_0,X1,X2),u1_pre_topc(esk5_0))|~r2_hidden(X2,u1_pre_topc(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X1,esk4_0)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_19]), c_0_13])]), ['final']).
% 0.06/0.28  cnf(c_0_46, negated_conjecture, (m1_pre_topc(esk7_0,X1)|esk2_2(X1,esk7_0)!=k9_subset_1(u1_struct_0(esk6_0),X2,k2_struct_0(esk7_0))|~r2_hidden(esk2_2(X1,esk7_0),u1_pre_topc(esk6_0))|~r2_hidden(X2,u1_pre_topc(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(esk7_0),k2_struct_0(X1))|~l1_pre_topc(X1)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_20]), c_0_15])]), c_0_31]), ['final']).
% 0.06/0.28  cnf(c_0_47, negated_conjecture, (u1_struct_0(esk5_0)=X1|g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))!=g1_pre_topc(X1,X2)), inference(rw,[status(thm)],[c_0_27, c_0_30]), ['final']).
% 0.06/0.28  cnf(c_0_48, negated_conjecture, (u1_struct_0(esk6_0)=X1|g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))!=g1_pre_topc(X1,X2)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_20]), c_0_25]), c_0_15])]), c_0_31]), ['final']).
% 0.06/0.28  cnf(c_0_49, negated_conjecture, (r2_hidden(esk1_3(esk7_0,X1,X2),u1_pre_topc(esk6_0))|~r2_hidden(X2,u1_pre_topc(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X1,esk7_0)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_20]), c_0_15])]), ['final']).
% 0.06/0.28  cnf(c_0_50, negated_conjecture, (u1_pre_topc(esk5_0)=X1|g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))!=g1_pre_topc(X2,X1)), inference(rw,[status(thm)],[c_0_16, c_0_19]), ['final']).
% 0.06/0.28  cnf(c_0_51, negated_conjecture, (u1_pre_topc(esk6_0)=X1|g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))!=g1_pre_topc(X2,X1)), inference(rw,[status(thm)],[c_0_17, c_0_20]), ['final']).
% 0.06/0.28  cnf(c_0_52, plain, (esk2_2(X1,X2)=k9_subset_1(u1_struct_0(X2),esk3_2(X1,X2),k2_struct_0(X2))|r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))|m1_pre_topc(X2,X1)|~r1_tarski(k2_struct_0(X2),k2_struct_0(X1))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_21]), ['final']).
% 0.06/0.28  cnf(c_0_53, plain, (m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))|m1_pre_topc(X2,X1)|~r1_tarski(k2_struct_0(X2),k2_struct_0(X1))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_21]), ['final']).
% 0.06/0.28  cnf(c_0_54, plain, (r2_hidden(esk3_2(X1,X2),u1_pre_topc(X1))|r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))|m1_pre_topc(X2,X1)|~r1_tarski(k2_struct_0(X2),k2_struct_0(X1))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_21]), ['final']).
% 0.06/0.28  cnf(c_0_55, plain, (m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X2)))|m1_pre_topc(X2,X1)|~r1_tarski(k2_struct_0(X2),k2_struct_0(X1))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_21]), ['final']).
% 0.06/0.28  cnf(c_0_56, plain, (r1_tarski(k2_struct_0(X1),k2_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_21]), ['final']).
% 0.06/0.28  cnf(c_0_57, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_36]), ['final']).
% 0.06/0.28  cnf(c_0_58, negated_conjecture, (~m1_pre_topc(esk7_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.06/0.28  cnf(c_0_59, negated_conjecture, (m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))), inference(rw,[status(thm)],[c_0_37, c_0_30]), ['final']).
% 0.06/0.28  cnf(c_0_60, negated_conjecture, (m1_subset_1(u1_pre_topc(esk6_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0))))), inference(rw,[status(thm)],[c_0_24, c_0_31]), ['final']).
% 0.06/0.28  cnf(c_0_61, negated_conjecture, (m1_pre_topc(esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.06/0.28  cnf(c_0_62, negated_conjecture, (l1_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.06/0.28  cnf(c_0_63, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.06/0.28  # SZS output end Saturation
% 0.06/0.28  # Proof object total steps             : 64
% 0.06/0.28  # Proof object clause steps            : 53
% 0.06/0.28  # Proof object formula steps           : 11
% 0.06/0.28  # Proof object conjectures             : 39
% 0.06/0.28  # Proof object clause conjectures      : 36
% 0.06/0.28  # Proof object formula conjectures     : 3
% 0.06/0.28  # Proof object initial clauses used    : 22
% 0.06/0.28  # Proof object initial formulas used   : 5
% 0.06/0.28  # Proof object generating inferences   : 23
% 0.06/0.28  # Proof object simplifying inferences  : 50
% 0.06/0.28  # Parsed axioms                        : 5
% 0.06/0.28  # Removed by relevancy pruning/SinE    : 0
% 0.06/0.28  # Initial clauses                      : 22
% 0.06/0.28  # Removed in clause preprocessing      : 0
% 0.06/0.28  # Initial clauses in saturation        : 22
% 0.06/0.28  # Processed clauses                    : 92
% 0.06/0.28  # ...of these trivial                  : 2
% 0.06/0.28  # ...subsumed                          : 14
% 0.06/0.28  # ...remaining for further processing  : 76
% 0.06/0.28  # Other redundant clauses eliminated   : 1
% 0.06/0.28  # Clauses deleted for lack of memory   : 0
% 0.06/0.28  # Backward-subsumed                    : 1
% 0.06/0.28  # Backward-rewritten                   : 10
% 0.06/0.28  # Generated clauses                    : 64
% 0.06/0.28  # ...of the previous two non-trivial   : 59
% 0.06/0.28  # Contextual simplify-reflections      : 0
% 0.06/0.28  # Paramodulations                      : 53
% 0.06/0.28  # Factorizations                       : 0
% 0.06/0.28  # Equation resolutions                 : 11
% 0.06/0.28  # Propositional unsat checks           : 0
% 0.06/0.28  #    Propositional check models        : 0
% 0.06/0.28  #    Propositional check unsatisfiable : 0
% 0.06/0.28  #    Propositional clauses             : 0
% 0.06/0.28  #    Propositional clauses after purity: 0
% 0.06/0.28  #    Propositional unsat core size     : 0
% 0.06/0.28  #    Propositional preprocessing time  : 0.000
% 0.06/0.28  #    Propositional encoding time       : 0.000
% 0.06/0.28  #    Propositional solver time         : 0.000
% 0.06/0.28  #    Success case prop preproc time    : 0.000
% 0.06/0.28  #    Success case prop encoding time   : 0.000
% 0.06/0.28  #    Success case prop solver time     : 0.000
% 0.06/0.28  # Current number of processed clauses  : 42
% 0.06/0.28  #    Positive orientable unit clauses  : 11
% 0.06/0.28  #    Positive unorientable unit clauses: 0
% 0.06/0.28  #    Negative unit clauses             : 1
% 0.06/0.28  #    Non-unit-clauses                  : 30
% 0.06/0.28  # Current number of unprocessed clauses: 0
% 0.06/0.28  # ...number of literals in the above   : 0
% 0.06/0.28  # Current number of archived formulas  : 0
% 0.06/0.28  # Current number of archived clauses   : 33
% 0.06/0.28  # Clause-clause subsumption calls (NU) : 553
% 0.06/0.28  # Rec. Clause-clause subsumption calls : 39
% 0.06/0.28  # Non-unit clause-clause subsumptions  : 15
% 0.06/0.28  # Unit Clause-clause subsumption calls : 3
% 0.06/0.28  # Rewrite failures with RHS unbound    : 0
% 0.06/0.28  # BW rewrite match attempts            : 4
% 0.06/0.28  # BW rewrite match successes           : 4
% 0.06/0.28  # Condensation attempts                : 0
% 0.06/0.28  # Condensation successes               : 0
% 0.06/0.28  # Termbank termtop insertions          : 3823
% 0.06/0.28  
% 0.06/0.28  # -------------------------------------------------
% 0.06/0.28  # User time                : 0.020 s
% 0.06/0.28  # System time              : 0.001 s
% 0.06/0.28  # Total time               : 0.021 s
% 0.06/0.28  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
