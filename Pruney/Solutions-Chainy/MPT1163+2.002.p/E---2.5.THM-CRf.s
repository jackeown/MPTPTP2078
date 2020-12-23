%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:58 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   64 (1012 expanded)
%              Number of clauses        :   53 ( 324 expanded)
%              Number of leaves         :    5 ( 243 expanded)
%              Depth                    :   16
%              Number of atoms          :  283 (7592 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   31 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t65_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r1_tarski(X3,X4)
                   => r1_tarski(k3_orders_2(X1,X3,X2),k3_orders_2(X1,X4,X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_orders_2)).

fof(t7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => ( r2_hidden(X4,X2)
                 => r2_hidden(X4,X3) ) )
           => r1_tarski(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

fof(dt_k3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_orders_2)).

fof(t57_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,k3_orders_2(X1,X4,X3))
                  <=> ( r2_orders_2(X1,X2,X3)
                      & r2_hidden(X2,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( r1_tarski(X3,X4)
                     => r1_tarski(k3_orders_2(X1,X3,X2),k3_orders_2(X1,X4,X2)) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t65_orders_2])).

fof(c_0_6,plain,(
    ! [X11,X12,X13] :
      ( ( m1_subset_1(esk2_3(X11,X12,X13),X11)
        | r1_tarski(X12,X13)
        | ~ m1_subset_1(X13,k1_zfmisc_1(X11))
        | ~ m1_subset_1(X12,k1_zfmisc_1(X11)) )
      & ( r2_hidden(esk2_3(X11,X12,X13),X12)
        | r1_tarski(X12,X13)
        | ~ m1_subset_1(X13,k1_zfmisc_1(X11))
        | ~ m1_subset_1(X12,k1_zfmisc_1(X11)) )
      & ( ~ r2_hidden(esk2_3(X11,X12,X13),X13)
        | r1_tarski(X12,X13)
        | ~ m1_subset_1(X13,k1_zfmisc_1(X11))
        | ~ m1_subset_1(X12,k1_zfmisc_1(X11)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).

fof(c_0_7,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v3_orders_2(esk3_0)
    & v4_orders_2(esk3_0)
    & v5_orders_2(esk3_0)
    & l1_orders_2(esk3_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & r1_tarski(esk5_0,esk6_0)
    & ~ r1_tarski(k3_orders_2(esk3_0,esk5_0,esk4_0),k3_orders_2(esk3_0,esk6_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

fof(c_0_8,plain,(
    ! [X15,X16,X17] :
      ( v2_struct_0(X15)
      | ~ v3_orders_2(X15)
      | ~ v4_orders_2(X15)
      | ~ v5_orders_2(X15)
      | ~ l1_orders_2(X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
      | ~ m1_subset_1(X17,u1_struct_0(X15))
      | m1_subset_1(k3_orders_2(X15,X16,X17),k1_zfmisc_1(u1_struct_0(X15))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_orders_2])])])).

cnf(c_0_9,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( v5_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( v4_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,negated_conjecture,
    ( v3_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),X1)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_19,plain,(
    ! [X18,X19,X20,X21] :
      ( ( r2_orders_2(X18,X19,X20)
        | ~ r2_hidden(X19,k3_orders_2(X18,X21,X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | v2_struct_0(X18)
        | ~ v3_orders_2(X18)
        | ~ v4_orders_2(X18)
        | ~ v5_orders_2(X18)
        | ~ l1_orders_2(X18) )
      & ( r2_hidden(X19,X21)
        | ~ r2_hidden(X19,k3_orders_2(X18,X21,X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | v2_struct_0(X18)
        | ~ v3_orders_2(X18)
        | ~ v4_orders_2(X18)
        | ~ v5_orders_2(X18)
        | ~ l1_orders_2(X18) )
      & ( ~ r2_orders_2(X18,X19,X20)
        | ~ r2_hidden(X19,X21)
        | r2_hidden(X19,k3_orders_2(X18,X21,X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | v2_struct_0(X18)
        | ~ v3_orders_2(X18)
        | ~ v4_orders_2(X18)
        | ~ v5_orders_2(X18)
        | ~ l1_orders_2(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_orders_2])])])])])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk2_3(u1_struct_0(esk3_0),X1,esk6_0),X1)
    | r1_tarski(X1,esk6_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(k3_orders_2(esk3_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_14]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk2_3(u1_struct_0(esk3_0),X1,esk6_0),u1_struct_0(esk3_0))
    | r1_tarski(X1,esk6_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_10])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,k3_orders_2(X3,X2,X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ v3_orders_2(X3)
    | ~ v4_orders_2(X3)
    | ~ v5_orders_2(X3)
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk5_0,X1),esk6_0),k3_orders_2(esk3_0,esk5_0,X1))
    | r1_tarski(k3_orders_2(esk3_0,esk5_0,X1),esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk5_0,X1),esk6_0),u1_struct_0(esk3_0))
    | r1_tarski(k3_orders_2(esk3_0,esk5_0,X1),esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_21])).

fof(c_0_27,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,k3_orders_2(esk3_0,esk5_0,X2)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_12]),c_0_13]),c_0_14]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk5_0,esk4_0),esk6_0),k3_orders_2(esk3_0,esk5_0,esk4_0))
    | r1_tarski(k3_orders_2(esk3_0,esk5_0,esk4_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk5_0,esk4_0),esk6_0),u1_struct_0(esk3_0))
    | r1_tarski(k3_orders_2(esk3_0,esk5_0,esk4_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(k3_orders_2(esk3_0,esk6_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_10]),c_0_13]),c_0_14]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_32,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk5_0,esk4_0),esk6_0),esk5_0)
    | r1_tarski(k3_orders_2(esk3_0,esk5_0,esk4_0),esk6_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_25])]),c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk2_3(u1_struct_0(esk3_0),X1,k3_orders_2(esk3_0,esk6_0,X2)),X1)
    | r1_tarski(X1,k3_orders_2(esk3_0,esk6_0,X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk2_3(u1_struct_0(esk3_0),X1,k3_orders_2(esk3_0,esk6_0,X2)),u1_struct_0(esk3_0))
    | r1_tarski(X1,k3_orders_2(esk3_0,esk6_0,X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_31])).

cnf(c_0_36,plain,
    ( r2_hidden(X2,k3_orders_2(X1,X4,X3))
    | v2_struct_0(X1)
    | ~ r2_orders_2(X1,X2,X3)
    | ~ r2_hidden(X2,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk5_0,esk4_0),esk6_0),X1)
    | r1_tarski(k3_orders_2(esk3_0,esk5_0,esk4_0),esk6_0)
    | ~ r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk5_0,X1),k3_orders_2(esk3_0,esk6_0,X2)),k3_orders_2(esk3_0,esk5_0,X1))
    | r1_tarski(k3_orders_2(esk3_0,esk5_0,X1),k3_orders_2(esk3_0,esk6_0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_21])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk5_0,X1),k3_orders_2(esk3_0,esk6_0,X2)),u1_struct_0(esk3_0))
    | r1_tarski(k3_orders_2(esk3_0,esk5_0,X1),k3_orders_2(esk3_0,esk6_0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_21])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(X1,k3_orders_2(esk3_0,esk5_0,X2))
    | ~ r2_orders_2(esk3_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_12]),c_0_13]),c_0_14]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_42,plain,
    ( r1_tarski(X2,X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk5_0,esk4_0),esk6_0),esk6_0)
    | r1_tarski(k3_orders_2(esk3_0,esk5_0,esk4_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,plain,
    ( r2_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,k3_orders_2(X1,X4,X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk5_0,X1),k3_orders_2(esk3_0,esk6_0,esk4_0)),k3_orders_2(esk3_0,esk5_0,X1))
    | r1_tarski(k3_orders_2(esk3_0,esk5_0,X1),k3_orders_2(esk3_0,esk6_0,esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_25])).

cnf(c_0_46,negated_conjecture,
    ( ~ r1_tarski(k3_orders_2(esk3_0,esk5_0,esk4_0),k3_orders_2(esk3_0,esk6_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk5_0,X1),k3_orders_2(esk3_0,esk6_0,esk4_0)),u1_struct_0(esk3_0))
    | r1_tarski(k3_orders_2(esk3_0,esk5_0,X1),k3_orders_2(esk3_0,esk6_0,esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_25])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_orders_2(esk3_0,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk5_0)
    | ~ r1_tarski(k3_orders_2(esk3_0,esk5_0,X3),X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(k3_orders_2(esk3_0,esk5_0,esk4_0),esk6_0)
    | ~ m1_subset_1(k3_orders_2(esk3_0,esk5_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_10])])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(X1,k3_orders_2(esk3_0,esk6_0,X2))
    | ~ r2_orders_2(esk3_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_10]),c_0_13]),c_0_14]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_51,negated_conjecture,
    ( r2_orders_2(esk3_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,k3_orders_2(esk3_0,esk5_0,X2)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_12]),c_0_13]),c_0_14]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk5_0,esk4_0),k3_orders_2(esk3_0,esk6_0,esk4_0)),k3_orders_2(esk3_0,esk5_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_25]),c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk5_0,esk4_0),k3_orders_2(esk3_0,esk6_0,esk4_0)),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_25]),c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_orders_2(esk3_0,X1,esk4_0)
    | ~ m1_subset_1(k3_orders_2(esk3_0,esk5_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_25])])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(X1,k3_orders_2(esk3_0,esk6_0,X2))
    | ~ r2_orders_2(esk3_0,esk2_3(X3,X1,k3_orders_2(esk3_0,esk6_0,X2)),X2)
    | ~ m1_subset_1(esk2_3(X3,X1,k3_orders_2(esk3_0,esk6_0,X2)),u1_struct_0(esk3_0))
    | ~ m1_subset_1(k3_orders_2(esk3_0,esk6_0,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ r2_hidden(esk2_3(X3,X1,k3_orders_2(esk3_0,esk6_0,X2)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( r2_orders_2(esk3_0,esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk5_0,esk4_0),k3_orders_2(esk3_0,esk6_0,esk4_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_25]),c_0_53])])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_orders_2(esk3_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_21]),c_0_25])])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk5_0,esk4_0),k3_orders_2(esk3_0,esk6_0,esk4_0)),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_52]),c_0_25]),c_0_53])])).

cnf(c_0_59,negated_conjecture,
    ( ~ m1_subset_1(k3_orders_2(esk3_0,esk6_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(k3_orders_2(esk3_0,esk5_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk5_0,esk4_0),k3_orders_2(esk3_0,esk6_0,esk4_0)),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_53]),c_0_25])]),c_0_46])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk5_0,esk4_0),k3_orders_2(esk3_0,esk6_0,esk4_0)),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_56]),c_0_53]),c_0_58])])).

cnf(c_0_61,negated_conjecture,
    ( ~ m1_subset_1(k3_orders_2(esk3_0,esk6_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(k3_orders_2(esk3_0,esk5_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_60])])).

cnf(c_0_62,negated_conjecture,
    ( ~ m1_subset_1(k3_orders_2(esk3_0,esk5_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_31]),c_0_25])])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_21]),c_0_25])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:14:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.45  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.45  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.45  #
% 0.20/0.45  # Preprocessing time       : 0.029 s
% 0.20/0.45  # Presaturation interreduction done
% 0.20/0.45  
% 0.20/0.45  # Proof found!
% 0.20/0.45  # SZS status Theorem
% 0.20/0.45  # SZS output start CNFRefutation
% 0.20/0.45  fof(t65_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X3,X4)=>r1_tarski(k3_orders_2(X1,X3,X2),k3_orders_2(X1,X4,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_orders_2)).
% 0.20/0.45  fof(t7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,X2)=>r2_hidden(X4,X3)))=>r1_tarski(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_subset_1)).
% 0.20/0.45  fof(dt_k3_orders_2, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 0.20/0.45  fof(t57_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,k3_orders_2(X1,X4,X3))<=>(r2_orders_2(X1,X2,X3)&r2_hidden(X2,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 0.20/0.45  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.45  fof(c_0_5, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X3,X4)=>r1_tarski(k3_orders_2(X1,X3,X2),k3_orders_2(X1,X4,X2)))))))), inference(assume_negation,[status(cth)],[t65_orders_2])).
% 0.20/0.45  fof(c_0_6, plain, ![X11, X12, X13]:((m1_subset_1(esk2_3(X11,X12,X13),X11)|r1_tarski(X12,X13)|~m1_subset_1(X13,k1_zfmisc_1(X11))|~m1_subset_1(X12,k1_zfmisc_1(X11)))&((r2_hidden(esk2_3(X11,X12,X13),X12)|r1_tarski(X12,X13)|~m1_subset_1(X13,k1_zfmisc_1(X11))|~m1_subset_1(X12,k1_zfmisc_1(X11)))&(~r2_hidden(esk2_3(X11,X12,X13),X13)|r1_tarski(X12,X13)|~m1_subset_1(X13,k1_zfmisc_1(X11))|~m1_subset_1(X12,k1_zfmisc_1(X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).
% 0.20/0.45  fof(c_0_7, negated_conjecture, (((((~v2_struct_0(esk3_0)&v3_orders_2(esk3_0))&v4_orders_2(esk3_0))&v5_orders_2(esk3_0))&l1_orders_2(esk3_0))&(m1_subset_1(esk4_0,u1_struct_0(esk3_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(r1_tarski(esk5_0,esk6_0)&~r1_tarski(k3_orders_2(esk3_0,esk5_0,esk4_0),k3_orders_2(esk3_0,esk6_0,esk4_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).
% 0.20/0.45  fof(c_0_8, plain, ![X15, X16, X17]:(v2_struct_0(X15)|~v3_orders_2(X15)|~v4_orders_2(X15)|~v5_orders_2(X15)|~l1_orders_2(X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|~m1_subset_1(X17,u1_struct_0(X15))|m1_subset_1(k3_orders_2(X15,X16,X17),k1_zfmisc_1(u1_struct_0(X15)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_orders_2])])])).
% 0.20/0.45  cnf(c_0_9, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r1_tarski(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.45  cnf(c_0_10, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.45  cnf(c_0_11, plain, (v2_struct_0(X1)|m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.45  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.45  cnf(c_0_13, negated_conjecture, (l1_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.45  cnf(c_0_14, negated_conjecture, (v5_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.45  cnf(c_0_15, negated_conjecture, (v4_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.45  cnf(c_0_16, negated_conjecture, (v3_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.45  cnf(c_0_17, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.45  cnf(c_0_18, plain, (m1_subset_1(esk2_3(X1,X2,X3),X1)|r1_tarski(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.45  fof(c_0_19, plain, ![X18, X19, X20, X21]:(((r2_orders_2(X18,X19,X20)|~r2_hidden(X19,k3_orders_2(X18,X21,X20))|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X18)))|~m1_subset_1(X20,u1_struct_0(X18))|~m1_subset_1(X19,u1_struct_0(X18))|(v2_struct_0(X18)|~v3_orders_2(X18)|~v4_orders_2(X18)|~v5_orders_2(X18)|~l1_orders_2(X18)))&(r2_hidden(X19,X21)|~r2_hidden(X19,k3_orders_2(X18,X21,X20))|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X18)))|~m1_subset_1(X20,u1_struct_0(X18))|~m1_subset_1(X19,u1_struct_0(X18))|(v2_struct_0(X18)|~v3_orders_2(X18)|~v4_orders_2(X18)|~v5_orders_2(X18)|~l1_orders_2(X18))))&(~r2_orders_2(X18,X19,X20)|~r2_hidden(X19,X21)|r2_hidden(X19,k3_orders_2(X18,X21,X20))|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X18)))|~m1_subset_1(X20,u1_struct_0(X18))|~m1_subset_1(X19,u1_struct_0(X18))|(v2_struct_0(X18)|~v3_orders_2(X18)|~v4_orders_2(X18)|~v5_orders_2(X18)|~l1_orders_2(X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_orders_2])])])])])).
% 0.20/0.45  cnf(c_0_20, negated_conjecture, (r2_hidden(esk2_3(u1_struct_0(esk3_0),X1,esk6_0),X1)|r1_tarski(X1,esk6_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.20/0.45  cnf(c_0_21, negated_conjecture, (m1_subset_1(k3_orders_2(esk3_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13]), c_0_14]), c_0_15]), c_0_16])]), c_0_17])).
% 0.20/0.45  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk2_3(u1_struct_0(esk3_0),X1,esk6_0),u1_struct_0(esk3_0))|r1_tarski(X1,esk6_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_18, c_0_10])).
% 0.20/0.45  cnf(c_0_23, plain, (r2_hidden(X1,X2)|v2_struct_0(X3)|~r2_hidden(X1,k3_orders_2(X3,X2,X4))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X4,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~v3_orders_2(X3)|~v4_orders_2(X3)|~v5_orders_2(X3)|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.45  cnf(c_0_24, negated_conjecture, (r2_hidden(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk5_0,X1),esk6_0),k3_orders_2(esk3_0,esk5_0,X1))|r1_tarski(k3_orders_2(esk3_0,esk5_0,X1),esk6_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.45  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.45  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk5_0,X1),esk6_0),u1_struct_0(esk3_0))|r1_tarski(k3_orders_2(esk3_0,esk5_0,X1),esk6_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_22, c_0_21])).
% 0.20/0.45  fof(c_0_27, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.45  cnf(c_0_28, negated_conjecture, (r2_hidden(X1,esk5_0)|~m1_subset_1(X2,u1_struct_0(esk3_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,k3_orders_2(esk3_0,esk5_0,X2))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_12]), c_0_13]), c_0_14]), c_0_15]), c_0_16])]), c_0_17])).
% 0.20/0.45  cnf(c_0_29, negated_conjecture, (r2_hidden(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk5_0,esk4_0),esk6_0),k3_orders_2(esk3_0,esk5_0,esk4_0))|r1_tarski(k3_orders_2(esk3_0,esk5_0,esk4_0),esk6_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.45  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk5_0,esk4_0),esk6_0),u1_struct_0(esk3_0))|r1_tarski(k3_orders_2(esk3_0,esk5_0,esk4_0),esk6_0)), inference(spm,[status(thm)],[c_0_26, c_0_25])).
% 0.20/0.45  cnf(c_0_31, negated_conjecture, (m1_subset_1(k3_orders_2(esk3_0,esk6_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_10]), c_0_13]), c_0_14]), c_0_15]), c_0_16])]), c_0_17])).
% 0.20/0.45  cnf(c_0_32, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.45  cnf(c_0_33, negated_conjecture, (r2_hidden(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk5_0,esk4_0),esk6_0),esk5_0)|r1_tarski(k3_orders_2(esk3_0,esk5_0,esk4_0),esk6_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_25])]), c_0_30])).
% 0.20/0.45  cnf(c_0_34, negated_conjecture, (r2_hidden(esk2_3(u1_struct_0(esk3_0),X1,k3_orders_2(esk3_0,esk6_0,X2)),X1)|r1_tarski(X1,k3_orders_2(esk3_0,esk6_0,X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_9, c_0_31])).
% 0.20/0.45  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk2_3(u1_struct_0(esk3_0),X1,k3_orders_2(esk3_0,esk6_0,X2)),u1_struct_0(esk3_0))|r1_tarski(X1,k3_orders_2(esk3_0,esk6_0,X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_18, c_0_31])).
% 0.20/0.45  cnf(c_0_36, plain, (r2_hidden(X2,k3_orders_2(X1,X4,X3))|v2_struct_0(X1)|~r2_orders_2(X1,X2,X3)|~r2_hidden(X2,X4)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.45  cnf(c_0_37, negated_conjecture, (r2_hidden(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk5_0,esk4_0),esk6_0),X1)|r1_tarski(k3_orders_2(esk3_0,esk5_0,esk4_0),esk6_0)|~r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.45  cnf(c_0_38, negated_conjecture, (r1_tarski(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.45  cnf(c_0_39, negated_conjecture, (r2_hidden(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk5_0,X1),k3_orders_2(esk3_0,esk6_0,X2)),k3_orders_2(esk3_0,esk5_0,X1))|r1_tarski(k3_orders_2(esk3_0,esk5_0,X1),k3_orders_2(esk3_0,esk6_0,X2))|~m1_subset_1(X2,u1_struct_0(esk3_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_34, c_0_21])).
% 0.20/0.45  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk5_0,X1),k3_orders_2(esk3_0,esk6_0,X2)),u1_struct_0(esk3_0))|r1_tarski(k3_orders_2(esk3_0,esk5_0,X1),k3_orders_2(esk3_0,esk6_0,X2))|~m1_subset_1(X2,u1_struct_0(esk3_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_35, c_0_21])).
% 0.20/0.45  cnf(c_0_41, negated_conjecture, (r2_hidden(X1,k3_orders_2(esk3_0,esk5_0,X2))|~r2_orders_2(esk3_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk3_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_12]), c_0_13]), c_0_14]), c_0_15]), c_0_16])]), c_0_17])).
% 0.20/0.45  cnf(c_0_42, plain, (r1_tarski(X2,X3)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.45  cnf(c_0_43, negated_conjecture, (r2_hidden(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk5_0,esk4_0),esk6_0),esk6_0)|r1_tarski(k3_orders_2(esk3_0,esk5_0,esk4_0),esk6_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.45  cnf(c_0_44, plain, (r2_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r2_hidden(X2,k3_orders_2(X1,X4,X3))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.45  cnf(c_0_45, negated_conjecture, (r2_hidden(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk5_0,X1),k3_orders_2(esk3_0,esk6_0,esk4_0)),k3_orders_2(esk3_0,esk5_0,X1))|r1_tarski(k3_orders_2(esk3_0,esk5_0,X1),k3_orders_2(esk3_0,esk6_0,esk4_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_39, c_0_25])).
% 0.20/0.45  cnf(c_0_46, negated_conjecture, (~r1_tarski(k3_orders_2(esk3_0,esk5_0,esk4_0),k3_orders_2(esk3_0,esk6_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.45  cnf(c_0_47, negated_conjecture, (m1_subset_1(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk5_0,X1),k3_orders_2(esk3_0,esk6_0,esk4_0)),u1_struct_0(esk3_0))|r1_tarski(k3_orders_2(esk3_0,esk5_0,X1),k3_orders_2(esk3_0,esk6_0,esk4_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_40, c_0_25])).
% 0.20/0.45  cnf(c_0_48, negated_conjecture, (r2_hidden(X1,X2)|~r2_orders_2(esk3_0,X1,X3)|~m1_subset_1(X3,u1_struct_0(esk3_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,esk5_0)|~r1_tarski(k3_orders_2(esk3_0,esk5_0,X3),X2)), inference(spm,[status(thm)],[c_0_32, c_0_41])).
% 0.20/0.45  cnf(c_0_49, negated_conjecture, (r1_tarski(k3_orders_2(esk3_0,esk5_0,esk4_0),esk6_0)|~m1_subset_1(k3_orders_2(esk3_0,esk5_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_10])])).
% 0.20/0.45  cnf(c_0_50, negated_conjecture, (r2_hidden(X1,k3_orders_2(esk3_0,esk6_0,X2))|~r2_orders_2(esk3_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk3_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_10]), c_0_13]), c_0_14]), c_0_15]), c_0_16])]), c_0_17])).
% 0.20/0.45  cnf(c_0_51, negated_conjecture, (r2_orders_2(esk3_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk3_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,k3_orders_2(esk3_0,esk5_0,X2))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_12]), c_0_13]), c_0_14]), c_0_15]), c_0_16])]), c_0_17])).
% 0.20/0.45  cnf(c_0_52, negated_conjecture, (r2_hidden(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk5_0,esk4_0),k3_orders_2(esk3_0,esk6_0,esk4_0)),k3_orders_2(esk3_0,esk5_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_25]), c_0_46])).
% 0.20/0.45  cnf(c_0_53, negated_conjecture, (m1_subset_1(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk5_0,esk4_0),k3_orders_2(esk3_0,esk6_0,esk4_0)),u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_25]), c_0_46])).
% 0.20/0.45  cnf(c_0_54, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_orders_2(esk3_0,X1,esk4_0)|~m1_subset_1(k3_orders_2(esk3_0,esk5_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_25])])).
% 0.20/0.45  cnf(c_0_55, negated_conjecture, (r1_tarski(X1,k3_orders_2(esk3_0,esk6_0,X2))|~r2_orders_2(esk3_0,esk2_3(X3,X1,k3_orders_2(esk3_0,esk6_0,X2)),X2)|~m1_subset_1(esk2_3(X3,X1,k3_orders_2(esk3_0,esk6_0,X2)),u1_struct_0(esk3_0))|~m1_subset_1(k3_orders_2(esk3_0,esk6_0,X2),k1_zfmisc_1(X3))|~m1_subset_1(X2,u1_struct_0(esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(X3))|~r2_hidden(esk2_3(X3,X1,k3_orders_2(esk3_0,esk6_0,X2)),esk6_0)), inference(spm,[status(thm)],[c_0_42, c_0_50])).
% 0.20/0.45  cnf(c_0_56, negated_conjecture, (r2_orders_2(esk3_0,esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk5_0,esk4_0),k3_orders_2(esk3_0,esk6_0,esk4_0)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_25]), c_0_53])])).
% 0.20/0.45  cnf(c_0_57, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_orders_2(esk3_0,X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_21]), c_0_25])])).
% 0.20/0.45  cnf(c_0_58, negated_conjecture, (r2_hidden(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk5_0,esk4_0),k3_orders_2(esk3_0,esk6_0,esk4_0)),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_52]), c_0_25]), c_0_53])])).
% 0.20/0.45  cnf(c_0_59, negated_conjecture, (~m1_subset_1(k3_orders_2(esk3_0,esk6_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(k3_orders_2(esk3_0,esk5_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk5_0,esk4_0),k3_orders_2(esk3_0,esk6_0,esk4_0)),esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_53]), c_0_25])]), c_0_46])).
% 0.20/0.45  cnf(c_0_60, negated_conjecture, (r2_hidden(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk5_0,esk4_0),k3_orders_2(esk3_0,esk6_0,esk4_0)),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_56]), c_0_53]), c_0_58])])).
% 0.20/0.45  cnf(c_0_61, negated_conjecture, (~m1_subset_1(k3_orders_2(esk3_0,esk6_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(k3_orders_2(esk3_0,esk5_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_60])])).
% 0.20/0.45  cnf(c_0_62, negated_conjecture, (~m1_subset_1(k3_orders_2(esk3_0,esk5_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_31]), c_0_25])])).
% 0.20/0.45  cnf(c_0_63, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_21]), c_0_25])]), ['proof']).
% 0.20/0.45  # SZS output end CNFRefutation
% 0.20/0.45  # Proof object total steps             : 64
% 0.20/0.45  # Proof object clause steps            : 53
% 0.20/0.45  # Proof object formula steps           : 11
% 0.20/0.45  # Proof object conjectures             : 48
% 0.20/0.45  # Proof object clause conjectures      : 45
% 0.20/0.45  # Proof object formula conjectures     : 3
% 0.20/0.45  # Proof object initial clauses used    : 18
% 0.20/0.45  # Proof object initial formulas used   : 5
% 0.20/0.45  # Proof object generating inferences   : 34
% 0.20/0.45  # Proof object simplifying inferences  : 66
% 0.20/0.45  # Training examples: 0 positive, 0 negative
% 0.20/0.45  # Parsed axioms                        : 5
% 0.20/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.45  # Initial clauses                      : 20
% 0.20/0.45  # Removed in clause preprocessing      : 0
% 0.20/0.45  # Initial clauses in saturation        : 20
% 0.20/0.45  # Processed clauses                    : 317
% 0.20/0.45  # ...of these trivial                  : 0
% 0.20/0.45  # ...subsumed                          : 40
% 0.20/0.45  # ...remaining for further processing  : 277
% 0.20/0.45  # Other redundant clauses eliminated   : 0
% 0.20/0.45  # Clauses deleted for lack of memory   : 0
% 0.20/0.45  # Backward-subsumed                    : 6
% 0.20/0.45  # Backward-rewritten                   : 18
% 0.20/0.45  # Generated clauses                    : 2871
% 0.20/0.45  # ...of the previous two non-trivial   : 2845
% 0.20/0.45  # Contextual simplify-reflections      : 5
% 0.20/0.45  # Paramodulations                      : 2871
% 0.20/0.45  # Factorizations                       : 0
% 0.20/0.45  # Equation resolutions                 : 0
% 0.20/0.45  # Propositional unsat checks           : 0
% 0.20/0.45  #    Propositional check models        : 0
% 0.20/0.45  #    Propositional check unsatisfiable : 0
% 0.20/0.45  #    Propositional clauses             : 0
% 0.20/0.45  #    Propositional clauses after purity: 0
% 0.20/0.45  #    Propositional unsat core size     : 0
% 0.20/0.45  #    Propositional preprocessing time  : 0.000
% 0.20/0.45  #    Propositional encoding time       : 0.000
% 0.20/0.45  #    Propositional solver time         : 0.000
% 0.20/0.45  #    Success case prop preproc time    : 0.000
% 0.20/0.45  #    Success case prop encoding time   : 0.000
% 0.20/0.45  #    Success case prop solver time     : 0.000
% 0.20/0.45  # Current number of processed clauses  : 233
% 0.20/0.45  #    Positive orientable unit clauses  : 17
% 0.20/0.45  #    Positive unorientable unit clauses: 0
% 0.20/0.45  #    Negative unit clauses             : 3
% 0.20/0.45  #    Non-unit-clauses                  : 213
% 0.20/0.45  # Current number of unprocessed clauses: 2546
% 0.20/0.45  # ...number of literals in the above   : 10347
% 0.20/0.45  # Current number of archived formulas  : 0
% 0.20/0.45  # Current number of archived clauses   : 44
% 0.20/0.45  # Clause-clause subsumption calls (NU) : 9827
% 0.20/0.45  # Rec. Clause-clause subsumption calls : 3610
% 0.20/0.45  # Non-unit clause-clause subsumptions  : 48
% 0.20/0.45  # Unit Clause-clause subsumption calls : 689
% 0.20/0.45  # Rewrite failures with RHS unbound    : 0
% 0.20/0.45  # BW rewrite match attempts            : 52
% 0.20/0.45  # BW rewrite match successes           : 4
% 0.20/0.45  # Condensation attempts                : 0
% 0.20/0.45  # Condensation successes               : 0
% 0.20/0.45  # Termbank termtop insertions          : 144994
% 0.20/0.45  
% 0.20/0.45  # -------------------------------------------------
% 0.20/0.45  # User time                : 0.102 s
% 0.20/0.45  # System time              : 0.004 s
% 0.20/0.45  # Total time               : 0.106 s
% 0.20/0.45  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
