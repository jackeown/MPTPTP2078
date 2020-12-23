%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:02 EST 2020

% Result     : Theorem 1.16s
% Output     : CNFRefutation 1.16s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 779 expanded)
%              Number of clauses        :   51 ( 258 expanded)
%              Number of leaves         :    9 ( 187 expanded)
%              Depth                    :   12
%              Number of atoms          :  358 (6009 expanded)
%              Number of equality atoms :   12 ( 492 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal clause size      :   31 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t71_orders_2,conjecture,(
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
                 => ( ( r2_hidden(X2,X3)
                      & m1_orders_2(X3,X1,X4) )
                   => k3_orders_2(X1,X3,X2) = k3_orders_2(X1,X4,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_orders_2)).

fof(t67_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_orders_2(X3,X1,X2)
             => r1_tarski(X3,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_orders_2)).

fof(t65_orders_2,axiom,(
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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

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

fof(t70_orders_2,axiom,(
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
                 => ! [X5] :
                      ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( ( r2_orders_2(X1,X2,X3)
                          & r2_hidden(X2,X4)
                          & r2_hidden(X3,X5)
                          & m1_orders_2(X5,X1,X4) )
                       => r2_hidden(X2,X5) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_orders_2)).

fof(c_0_9,negated_conjecture,(
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
                   => ( ( r2_hidden(X2,X3)
                        & m1_orders_2(X3,X1,X4) )
                     => k3_orders_2(X1,X3,X2) = k3_orders_2(X1,X4,X2) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t71_orders_2])).

fof(c_0_10,plain,(
    ! [X29,X30,X31] :
      ( v2_struct_0(X29)
      | ~ v3_orders_2(X29)
      | ~ v4_orders_2(X29)
      | ~ v5_orders_2(X29)
      | ~ l1_orders_2(X29)
      | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
      | ~ m1_orders_2(X31,X29,X30)
      | r1_tarski(X31,X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t67_orders_2])])])])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v3_orders_2(esk3_0)
    & v4_orders_2(esk3_0)
    & v5_orders_2(esk3_0)
    & l1_orders_2(esk3_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & r2_hidden(esk4_0,esk5_0)
    & m1_orders_2(esk5_0,esk3_0,esk6_0)
    & k3_orders_2(esk3_0,esk5_0,esk4_0) != k3_orders_2(esk3_0,esk6_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

fof(c_0_12,plain,(
    ! [X25,X26,X27,X28] :
      ( v2_struct_0(X25)
      | ~ v3_orders_2(X25)
      | ~ v4_orders_2(X25)
      | ~ v5_orders_2(X25)
      | ~ l1_orders_2(X25)
      | ~ m1_subset_1(X26,u1_struct_0(X25))
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
      | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X25)))
      | ~ r1_tarski(X27,X28)
      | r1_tarski(k3_orders_2(X25,X27,X26),k3_orders_2(X25,X28,X26)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_orders_2])])])])).

cnf(c_0_13,plain,
    ( v2_struct_0(X1)
    | r1_tarski(X3,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_orders_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( v5_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( v4_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( v3_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_20,plain,(
    ! [X18,X19,X20] :
      ( v2_struct_0(X18)
      | ~ v3_orders_2(X18)
      | ~ v4_orders_2(X18)
      | ~ v5_orders_2(X18)
      | ~ l1_orders_2(X18)
      | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
      | ~ m1_subset_1(X20,u1_struct_0(X18))
      | m1_subset_1(k3_orders_2(X18,X19,X20),k1_zfmisc_1(u1_struct_0(X18))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_orders_2])])])).

cnf(c_0_21,plain,
    ( v2_struct_0(X1)
    | r1_tarski(k3_orders_2(X1,X3,X2),k3_orders_2(X1,X4,X2))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(X1,esk6_0)
    | ~ m1_orders_2(X1,esk3_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( m1_orders_2(esk5_0,esk3_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_25,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_26,plain,(
    ! [X12,X13] :
      ( ( ~ r2_hidden(esk2_2(X12,X13),X12)
        | ~ r2_hidden(esk2_2(X12,X13),X13)
        | X12 = X13 )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r2_hidden(esk2_2(X12,X13),X13)
        | X12 = X13 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(k3_orders_2(esk3_0,X1,X2),k3_orders_2(esk3_0,esk6_0,X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ r1_tarski(X1,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_30,plain,(
    ! [X15,X16,X17] :
      ( ~ r2_hidden(X15,X16)
      | ~ m1_subset_1(X16,k1_zfmisc_1(X17))
      | m1_subset_1(X15,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(k3_orders_2(esk3_0,esk6_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_33,plain,(
    ! [X21,X22,X23,X24] :
      ( ( r2_orders_2(X21,X22,X23)
        | ~ r2_hidden(X22,k3_orders_2(X21,X24,X23))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ v3_orders_2(X21)
        | ~ v4_orders_2(X21)
        | ~ v5_orders_2(X21)
        | ~ l1_orders_2(X21) )
      & ( r2_hidden(X22,X24)
        | ~ r2_hidden(X22,k3_orders_2(X21,X24,X23))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ v3_orders_2(X21)
        | ~ v4_orders_2(X21)
        | ~ v5_orders_2(X21)
        | ~ l1_orders_2(X21) )
      & ( ~ r2_orders_2(X21,X22,X23)
        | ~ r2_hidden(X22,X24)
        | r2_hidden(X22,k3_orders_2(X21,X24,X23))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ v3_orders_2(X21)
        | ~ v4_orders_2(X21)
        | ~ v5_orders_2(X21)
        | ~ l1_orders_2(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_orders_2])])])])])).

cnf(c_0_34,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r2_hidden(esk2_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k3_orders_2(esk3_0,esk5_0,X1),k3_orders_2(esk3_0,esk6_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(k3_orders_2(esk3_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_28]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(k3_orders_2(esk3_0,esk6_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_40,plain,(
    ! [X32,X33,X34,X35,X36] :
      ( v2_struct_0(X32)
      | ~ v3_orders_2(X32)
      | ~ v4_orders_2(X32)
      | ~ v5_orders_2(X32)
      | ~ l1_orders_2(X32)
      | ~ m1_subset_1(X33,u1_struct_0(X32))
      | ~ m1_subset_1(X34,u1_struct_0(X32))
      | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X32)))
      | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X32)))
      | ~ r2_orders_2(X32,X33,X34)
      | ~ r2_hidden(X33,X35)
      | ~ r2_hidden(X34,X36)
      | ~ m1_orders_2(X36,X32,X35)
      | r2_hidden(X33,X36) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_orders_2])])])])).

cnf(c_0_41,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( X1 = X2
    | r2_hidden(esk2_2(X1,X2),X2)
    | r2_hidden(esk2_2(X1,X2),X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k3_orders_2(esk3_0,esk5_0,esk4_0),k3_orders_2(esk3_0,esk6_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_32])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(k3_orders_2(esk3_0,esk5_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_32])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,k3_orders_2(esk3_0,esk6_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,X5)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_orders_2(X1,X2,X3)
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X3,X5)
    | ~ m1_orders_2(X5,X1,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k3_orders_2(X1,X3,X4))
    | ~ r2_orders_2(X1,X2,X4)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X2,X3) ),
    inference(csr,[status(thm)],[c_0_41,c_0_38])).

cnf(c_0_48,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_49,negated_conjecture,
    ( k3_orders_2(esk3_0,esk5_0,esk4_0) = X1
    | r2_hidden(esk2_2(k3_orders_2(esk3_0,esk5_0,esk4_0),X1),k3_orders_2(esk3_0,esk6_0,esk4_0))
    | r2_hidden(esk2_2(k3_orders_2(esk3_0,esk5_0,esk4_0),X1),X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( k3_orders_2(esk3_0,esk5_0,esk4_0) != k3_orders_2(esk3_0,esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,k3_orders_2(esk3_0,esk5_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( X1 = k3_orders_2(esk3_0,esk6_0,esk4_0)
    | m1_subset_1(esk2_2(X1,k3_orders_2(esk3_0,esk6_0,esk4_0)),u1_struct_0(esk3_0))
    | r2_hidden(esk2_2(X1,k3_orders_2(esk3_0,esk6_0,esk4_0)),X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_35])).

cnf(c_0_53,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,X3)
    | ~ m1_orders_2(X3,X1,X4)
    | ~ r2_orders_2(X1,X2,X5)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X5,X3)
    | ~ r2_hidden(X2,X4) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_46,c_0_38]),c_0_38])).

cnf(c_0_54,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(X1,k3_orders_2(esk3_0,esk5_0,X2))
    | ~ r2_orders_2(esk3_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_28]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_56,negated_conjecture,
    ( r2_orders_2(esk3_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,k3_orders_2(esk3_0,esk6_0,X2)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk2_2(k3_orders_2(esk3_0,esk5_0,esk4_0),k3_orders_2(esk3_0,esk6_0,esk4_0)),k3_orders_2(esk3_0,esk6_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_49]),c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk2_2(k3_orders_2(esk3_0,esk5_0,esk4_0),k3_orders_2(esk3_0,esk6_0,esk4_0)),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_50])).

cnf(c_0_59,plain,
    ( X1 = X2
    | ~ r2_hidden(esk2_2(X1,X2),X1)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ m1_orders_2(esk5_0,esk3_0,X2)
    | ~ r2_orders_2(esk3_0,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(X3,esk5_0)
    | ~ r2_hidden(X1,X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_28]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,k3_orders_2(esk3_0,esk6_0,X2)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(X1,k3_orders_2(esk3_0,esk5_0,esk4_0))
    | ~ r2_orders_2(esk3_0,X1,esk4_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_32])).

cnf(c_0_63,negated_conjecture,
    ( r2_orders_2(esk3_0,esk2_2(k3_orders_2(esk3_0,esk5_0,esk4_0),k3_orders_2(esk3_0,esk6_0,esk4_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_32]),c_0_58])])).

cnf(c_0_64,negated_conjecture,
    ( ~ r2_hidden(esk2_2(k3_orders_2(esk3_0,esk5_0,esk4_0),k3_orders_2(esk3_0,esk6_0,esk4_0)),k3_orders_2(esk3_0,esk5_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_57]),c_0_50])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_orders_2(esk3_0,X1,X2)
    | ~ r2_hidden(X2,esk5_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_14]),c_0_23])])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk2_2(k3_orders_2(esk3_0,esk5_0,esk4_0),k3_orders_2(esk3_0,esk6_0,esk4_0)),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_57]),c_0_32]),c_0_58])])).

cnf(c_0_68,negated_conjecture,
    ( ~ r2_hidden(esk2_2(k3_orders_2(esk3_0,esk5_0,esk4_0),k3_orders_2(esk3_0,esk6_0,esk4_0)),esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_63]),c_0_66]),c_0_67])]),c_0_68]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:50:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 1.16/1.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S064I
% 1.16/1.37  # and selection function SelectComplexG.
% 1.16/1.37  #
% 1.16/1.37  # Preprocessing time       : 0.029 s
% 1.16/1.37  # Presaturation interreduction done
% 1.16/1.37  
% 1.16/1.37  # Proof found!
% 1.16/1.37  # SZS status Theorem
% 1.16/1.37  # SZS output start CNFRefutation
% 1.16/1.37  fof(t71_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,X3)&m1_orders_2(X3,X1,X4))=>k3_orders_2(X1,X3,X2)=k3_orders_2(X1,X4,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_orders_2)).
% 1.16/1.37  fof(t67_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_orders_2(X3,X1,X2)=>r1_tarski(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_orders_2)).
% 1.16/1.37  fof(t65_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X3,X4)=>r1_tarski(k3_orders_2(X1,X3,X2),k3_orders_2(X1,X4,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_orders_2)).
% 1.16/1.37  fof(dt_k3_orders_2, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 1.16/1.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.16/1.37  fof(t2_tarski, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)<=>r2_hidden(X3,X2))=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 1.16/1.37  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 1.16/1.37  fof(t57_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,k3_orders_2(X1,X4,X3))<=>(r2_orders_2(X1,X2,X3)&r2_hidden(X2,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 1.16/1.37  fof(t70_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))=>((((r2_orders_2(X1,X2,X3)&r2_hidden(X2,X4))&r2_hidden(X3,X5))&m1_orders_2(X5,X1,X4))=>r2_hidden(X2,X5))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_orders_2)).
% 1.16/1.37  fof(c_0_9, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,X3)&m1_orders_2(X3,X1,X4))=>k3_orders_2(X1,X3,X2)=k3_orders_2(X1,X4,X2))))))), inference(assume_negation,[status(cth)],[t71_orders_2])).
% 1.16/1.37  fof(c_0_10, plain, ![X29, X30, X31]:(v2_struct_0(X29)|~v3_orders_2(X29)|~v4_orders_2(X29)|~v5_orders_2(X29)|~l1_orders_2(X29)|(~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(~m1_orders_2(X31,X29,X30)|r1_tarski(X31,X30)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t67_orders_2])])])])).
% 1.16/1.37  fof(c_0_11, negated_conjecture, (((((~v2_struct_0(esk3_0)&v3_orders_2(esk3_0))&v4_orders_2(esk3_0))&v5_orders_2(esk3_0))&l1_orders_2(esk3_0))&(m1_subset_1(esk4_0,u1_struct_0(esk3_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&((r2_hidden(esk4_0,esk5_0)&m1_orders_2(esk5_0,esk3_0,esk6_0))&k3_orders_2(esk3_0,esk5_0,esk4_0)!=k3_orders_2(esk3_0,esk6_0,esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).
% 1.16/1.37  fof(c_0_12, plain, ![X25, X26, X27, X28]:(v2_struct_0(X25)|~v3_orders_2(X25)|~v4_orders_2(X25)|~v5_orders_2(X25)|~l1_orders_2(X25)|(~m1_subset_1(X26,u1_struct_0(X25))|(~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))|(~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X25)))|(~r1_tarski(X27,X28)|r1_tarski(k3_orders_2(X25,X27,X26),k3_orders_2(X25,X28,X26))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_orders_2])])])])).
% 1.16/1.37  cnf(c_0_13, plain, (v2_struct_0(X1)|r1_tarski(X3,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_orders_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.16/1.37  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.16/1.37  cnf(c_0_15, negated_conjecture, (l1_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.16/1.37  cnf(c_0_16, negated_conjecture, (v5_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.16/1.37  cnf(c_0_17, negated_conjecture, (v4_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.16/1.37  cnf(c_0_18, negated_conjecture, (v3_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.16/1.37  cnf(c_0_19, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.16/1.37  fof(c_0_20, plain, ![X18, X19, X20]:(v2_struct_0(X18)|~v3_orders_2(X18)|~v4_orders_2(X18)|~v5_orders_2(X18)|~l1_orders_2(X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|~m1_subset_1(X20,u1_struct_0(X18))|m1_subset_1(k3_orders_2(X18,X19,X20),k1_zfmisc_1(u1_struct_0(X18)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_orders_2])])])).
% 1.16/1.37  cnf(c_0_21, plain, (v2_struct_0(X1)|r1_tarski(k3_orders_2(X1,X3,X2),k3_orders_2(X1,X4,X2))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.16/1.37  cnf(c_0_22, negated_conjecture, (r1_tarski(X1,esk6_0)|~m1_orders_2(X1,esk3_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15]), c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 1.16/1.37  cnf(c_0_23, negated_conjecture, (m1_orders_2(esk5_0,esk3_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.16/1.37  cnf(c_0_24, plain, (v2_struct_0(X1)|m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.16/1.37  fof(c_0_25, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 1.16/1.37  fof(c_0_26, plain, ![X12, X13]:((~r2_hidden(esk2_2(X12,X13),X12)|~r2_hidden(esk2_2(X12,X13),X13)|X12=X13)&(r2_hidden(esk2_2(X12,X13),X12)|r2_hidden(esk2_2(X12,X13),X13)|X12=X13)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).
% 1.16/1.37  cnf(c_0_27, negated_conjecture, (r1_tarski(k3_orders_2(esk3_0,X1,X2),k3_orders_2(esk3_0,esk6_0,X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X2,u1_struct_0(esk3_0))|~r1_tarski(X1,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_14]), c_0_15]), c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 1.16/1.37  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.16/1.37  cnf(c_0_29, negated_conjecture, (r1_tarski(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 1.16/1.37  fof(c_0_30, plain, ![X15, X16, X17]:(~r2_hidden(X15,X16)|~m1_subset_1(X16,k1_zfmisc_1(X17))|m1_subset_1(X15,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 1.16/1.37  cnf(c_0_31, negated_conjecture, (m1_subset_1(k3_orders_2(esk3_0,esk6_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_14]), c_0_15]), c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 1.16/1.37  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.16/1.37  fof(c_0_33, plain, ![X21, X22, X23, X24]:(((r2_orders_2(X21,X22,X23)|~r2_hidden(X22,k3_orders_2(X21,X24,X23))|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X21)))|~m1_subset_1(X23,u1_struct_0(X21))|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~v3_orders_2(X21)|~v4_orders_2(X21)|~v5_orders_2(X21)|~l1_orders_2(X21)))&(r2_hidden(X22,X24)|~r2_hidden(X22,k3_orders_2(X21,X24,X23))|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X21)))|~m1_subset_1(X23,u1_struct_0(X21))|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~v3_orders_2(X21)|~v4_orders_2(X21)|~v5_orders_2(X21)|~l1_orders_2(X21))))&(~r2_orders_2(X21,X22,X23)|~r2_hidden(X22,X24)|r2_hidden(X22,k3_orders_2(X21,X24,X23))|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X21)))|~m1_subset_1(X23,u1_struct_0(X21))|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~v3_orders_2(X21)|~v4_orders_2(X21)|~v5_orders_2(X21)|~l1_orders_2(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_orders_2])])])])])).
% 1.16/1.37  cnf(c_0_34, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.16/1.37  cnf(c_0_35, plain, (r2_hidden(esk2_2(X1,X2),X1)|r2_hidden(esk2_2(X1,X2),X2)|X1=X2), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.16/1.37  cnf(c_0_36, negated_conjecture, (r1_tarski(k3_orders_2(esk3_0,esk5_0,X1),k3_orders_2(esk3_0,esk6_0,X1))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])])).
% 1.16/1.37  cnf(c_0_37, negated_conjecture, (m1_subset_1(k3_orders_2(esk3_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_28]), c_0_15]), c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 1.16/1.37  cnf(c_0_38, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.16/1.37  cnf(c_0_39, negated_conjecture, (m1_subset_1(k3_orders_2(esk3_0,esk6_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 1.16/1.37  fof(c_0_40, plain, ![X32, X33, X34, X35, X36]:(v2_struct_0(X32)|~v3_orders_2(X32)|~v4_orders_2(X32)|~v5_orders_2(X32)|~l1_orders_2(X32)|(~m1_subset_1(X33,u1_struct_0(X32))|(~m1_subset_1(X34,u1_struct_0(X32))|(~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X32)))|(~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X32)))|(~r2_orders_2(X32,X33,X34)|~r2_hidden(X33,X35)|~r2_hidden(X34,X36)|~m1_orders_2(X36,X32,X35)|r2_hidden(X33,X36))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_orders_2])])])])).
% 1.16/1.37  cnf(c_0_41, plain, (r2_hidden(X2,k3_orders_2(X1,X4,X3))|v2_struct_0(X1)|~r2_orders_2(X1,X2,X3)|~r2_hidden(X2,X4)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.16/1.37  cnf(c_0_42, plain, (X1=X2|r2_hidden(esk2_2(X1,X2),X2)|r2_hidden(esk2_2(X1,X2),X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 1.16/1.37  cnf(c_0_43, negated_conjecture, (r1_tarski(k3_orders_2(esk3_0,esk5_0,esk4_0),k3_orders_2(esk3_0,esk6_0,esk4_0))), inference(spm,[status(thm)],[c_0_36, c_0_32])).
% 1.16/1.37  cnf(c_0_44, negated_conjecture, (m1_subset_1(k3_orders_2(esk3_0,esk5_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_37, c_0_32])).
% 1.16/1.37  cnf(c_0_45, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,k3_orders_2(esk3_0,esk6_0,esk4_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 1.16/1.37  cnf(c_0_46, plain, (v2_struct_0(X1)|r2_hidden(X2,X5)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))|~r2_orders_2(X1,X2,X3)|~r2_hidden(X2,X4)|~r2_hidden(X3,X5)|~m1_orders_2(X5,X1,X4)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 1.16/1.37  cnf(c_0_47, plain, (v2_struct_0(X1)|r2_hidden(X2,k3_orders_2(X1,X3,X4))|~r2_orders_2(X1,X2,X4)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X2,X3)), inference(csr,[status(thm)],[c_0_41, c_0_38])).
% 1.16/1.37  cnf(c_0_48, plain, (r2_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r2_hidden(X2,k3_orders_2(X1,X4,X3))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.16/1.37  cnf(c_0_49, negated_conjecture, (k3_orders_2(esk3_0,esk5_0,esk4_0)=X1|r2_hidden(esk2_2(k3_orders_2(esk3_0,esk5_0,esk4_0),X1),k3_orders_2(esk3_0,esk6_0,esk4_0))|r2_hidden(esk2_2(k3_orders_2(esk3_0,esk5_0,esk4_0),X1),X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 1.16/1.37  cnf(c_0_50, negated_conjecture, (k3_orders_2(esk3_0,esk5_0,esk4_0)!=k3_orders_2(esk3_0,esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.16/1.37  cnf(c_0_51, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,k3_orders_2(esk3_0,esk5_0,esk4_0))), inference(spm,[status(thm)],[c_0_38, c_0_44])).
% 1.16/1.37  cnf(c_0_52, negated_conjecture, (X1=k3_orders_2(esk3_0,esk6_0,esk4_0)|m1_subset_1(esk2_2(X1,k3_orders_2(esk3_0,esk6_0,esk4_0)),u1_struct_0(esk3_0))|r2_hidden(esk2_2(X1,k3_orders_2(esk3_0,esk6_0,esk4_0)),X1)), inference(spm,[status(thm)],[c_0_45, c_0_35])).
% 1.16/1.37  cnf(c_0_53, plain, (v2_struct_0(X1)|r2_hidden(X2,X3)|~m1_orders_2(X3,X1,X4)|~r2_orders_2(X1,X2,X5)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X5,X3)|~r2_hidden(X2,X4)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_46, c_0_38]), c_0_38])).
% 1.16/1.37  cnf(c_0_54, plain, (r2_hidden(X1,X2)|v2_struct_0(X3)|~r2_hidden(X1,k3_orders_2(X3,X2,X4))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X4,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~v3_orders_2(X3)|~v4_orders_2(X3)|~v5_orders_2(X3)|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.16/1.37  cnf(c_0_55, negated_conjecture, (r2_hidden(X1,k3_orders_2(esk3_0,esk5_0,X2))|~r2_orders_2(esk3_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk3_0))|~r2_hidden(X1,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_28]), c_0_15]), c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 1.16/1.37  cnf(c_0_56, negated_conjecture, (r2_orders_2(esk3_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk3_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,k3_orders_2(esk3_0,esk6_0,X2))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_14]), c_0_15]), c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 1.16/1.37  cnf(c_0_57, negated_conjecture, (r2_hidden(esk2_2(k3_orders_2(esk3_0,esk5_0,esk4_0),k3_orders_2(esk3_0,esk6_0,esk4_0)),k3_orders_2(esk3_0,esk6_0,esk4_0))), inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_49]), c_0_50])).
% 1.16/1.37  cnf(c_0_58, negated_conjecture, (m1_subset_1(esk2_2(k3_orders_2(esk3_0,esk5_0,esk4_0),k3_orders_2(esk3_0,esk6_0,esk4_0)),u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_50])).
% 1.16/1.37  cnf(c_0_59, plain, (X1=X2|~r2_hidden(esk2_2(X1,X2),X1)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.16/1.37  cnf(c_0_60, negated_conjecture, (r2_hidden(X1,esk5_0)|~m1_orders_2(esk5_0,esk3_0,X2)|~r2_orders_2(esk3_0,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(X3,esk5_0)|~r2_hidden(X1,X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_28]), c_0_15]), c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 1.16/1.37  cnf(c_0_61, negated_conjecture, (r2_hidden(X1,esk6_0)|~m1_subset_1(X2,u1_struct_0(esk3_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,k3_orders_2(esk3_0,esk6_0,X2))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_14]), c_0_15]), c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 1.16/1.37  cnf(c_0_62, negated_conjecture, (r2_hidden(X1,k3_orders_2(esk3_0,esk5_0,esk4_0))|~r2_orders_2(esk3_0,X1,esk4_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_55, c_0_32])).
% 1.16/1.37  cnf(c_0_63, negated_conjecture, (r2_orders_2(esk3_0,esk2_2(k3_orders_2(esk3_0,esk5_0,esk4_0),k3_orders_2(esk3_0,esk6_0,esk4_0)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_32]), c_0_58])])).
% 1.16/1.37  cnf(c_0_64, negated_conjecture, (~r2_hidden(esk2_2(k3_orders_2(esk3_0,esk5_0,esk4_0),k3_orders_2(esk3_0,esk6_0,esk4_0)),k3_orders_2(esk3_0,esk5_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_57]), c_0_50])).
% 1.16/1.37  cnf(c_0_65, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_orders_2(esk3_0,X1,X2)|~r2_hidden(X2,esk5_0)|~r2_hidden(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_14]), c_0_23])])).
% 1.16/1.37  cnf(c_0_66, negated_conjecture, (r2_hidden(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.16/1.37  cnf(c_0_67, negated_conjecture, (r2_hidden(esk2_2(k3_orders_2(esk3_0,esk5_0,esk4_0),k3_orders_2(esk3_0,esk6_0,esk4_0)),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_57]), c_0_32]), c_0_58])])).
% 1.16/1.37  cnf(c_0_68, negated_conjecture, (~r2_hidden(esk2_2(k3_orders_2(esk3_0,esk5_0,esk4_0),k3_orders_2(esk3_0,esk6_0,esk4_0)),esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])).
% 1.16/1.37  cnf(c_0_69, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_63]), c_0_66]), c_0_67])]), c_0_68]), ['proof']).
% 1.16/1.37  # SZS output end CNFRefutation
% 1.16/1.37  # Proof object total steps             : 70
% 1.16/1.37  # Proof object clause steps            : 51
% 1.16/1.37  # Proof object formula steps           : 19
% 1.16/1.37  # Proof object conjectures             : 40
% 1.16/1.37  # Proof object clause conjectures      : 37
% 1.16/1.37  # Proof object formula conjectures     : 3
% 1.16/1.37  # Proof object initial clauses used    : 22
% 1.16/1.37  # Proof object initial formulas used   : 9
% 1.16/1.37  # Proof object generating inferences   : 27
% 1.16/1.37  # Proof object simplifying inferences  : 69
% 1.16/1.37  # Training examples: 0 positive, 0 negative
% 1.16/1.37  # Parsed axioms                        : 9
% 1.16/1.37  # Removed by relevancy pruning/SinE    : 0
% 1.16/1.37  # Initial clauses                      : 24
% 1.16/1.37  # Removed in clause preprocessing      : 0
% 1.16/1.37  # Initial clauses in saturation        : 24
% 1.16/1.37  # Processed clauses                    : 3050
% 1.16/1.37  # ...of these trivial                  : 0
% 1.16/1.37  # ...subsumed                          : 956
% 1.16/1.37  # ...remaining for further processing  : 2093
% 1.16/1.37  # Other redundant clauses eliminated   : 0
% 1.16/1.37  # Clauses deleted for lack of memory   : 0
% 1.16/1.37  # Backward-subsumed                    : 44
% 1.16/1.37  # Backward-rewritten                   : 11
% 1.16/1.37  # Generated clauses                    : 96429
% 1.16/1.37  # ...of the previous two non-trivial   : 85368
% 1.16/1.37  # Contextual simplify-reflections      : 42
% 1.16/1.37  # Paramodulations                      : 96355
% 1.16/1.37  # Factorizations                       : 74
% 1.16/1.37  # Equation resolutions                 : 0
% 1.16/1.37  # Propositional unsat checks           : 0
% 1.16/1.37  #    Propositional check models        : 0
% 1.16/1.37  #    Propositional check unsatisfiable : 0
% 1.16/1.37  #    Propositional clauses             : 0
% 1.16/1.37  #    Propositional clauses after purity: 0
% 1.16/1.37  #    Propositional unsat core size     : 0
% 1.16/1.37  #    Propositional preprocessing time  : 0.000
% 1.16/1.37  #    Propositional encoding time       : 0.000
% 1.16/1.37  #    Propositional solver time         : 0.000
% 1.16/1.37  #    Success case prop preproc time    : 0.000
% 1.16/1.37  #    Success case prop encoding time   : 0.000
% 1.16/1.37  #    Success case prop solver time     : 0.000
% 1.16/1.37  # Current number of processed clauses  : 2014
% 1.16/1.37  #    Positive orientable unit clauses  : 69
% 1.16/1.37  #    Positive unorientable unit clauses: 0
% 1.16/1.37  #    Negative unit clauses             : 4
% 1.16/1.37  #    Non-unit-clauses                  : 1941
% 1.16/1.37  # Current number of unprocessed clauses: 82363
% 1.16/1.37  # ...number of literals in the above   : 361850
% 1.16/1.37  # Current number of archived formulas  : 0
% 1.16/1.37  # Current number of archived clauses   : 79
% 1.16/1.37  # Clause-clause subsumption calls (NU) : 452207
% 1.16/1.37  # Rec. Clause-clause subsumption calls : 125526
% 1.16/1.37  # Non-unit clause-clause subsumptions  : 1038
% 1.16/1.37  # Unit Clause-clause subsumption calls : 8494
% 1.16/1.37  # Rewrite failures with RHS unbound    : 0
% 1.16/1.37  # BW rewrite match attempts            : 6501
% 1.16/1.37  # BW rewrite match successes           : 5
% 1.16/1.37  # Condensation attempts                : 0
% 1.16/1.37  # Condensation successes               : 0
% 1.16/1.37  # Termbank termtop insertions          : 2979158
% 1.16/1.38  
% 1.16/1.38  # -------------------------------------------------
% 1.16/1.38  # User time                : 0.994 s
% 1.16/1.38  # System time              : 0.040 s
% 1.16/1.38  # Total time               : 1.034 s
% 1.16/1.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
