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
% DateTime   : Thu Dec  3 11:09:58 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 226 expanded)
%              Number of clauses        :   35 (  74 expanded)
%              Number of leaves         :    6 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :  241 (1665 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   31 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t64_orders_2,conjecture,(
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
                 => ( r2_orders_2(X1,X2,X3)
                   => r1_tarski(k3_orders_2(X1,X4,X2),k3_orders_2(X1,X4,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_orders_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_orders_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t29_orders_2,axiom,(
    ! [X1] :
      ( ( v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( ( r2_orders_2(X1,X2,X3)
                      & r2_orders_2(X1,X3,X4) )
                   => r2_orders_2(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_orders_2)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
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
                   => ( r2_orders_2(X1,X2,X3)
                     => r1_tarski(k3_orders_2(X1,X4,X2),k3_orders_2(X1,X4,X3)) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t64_orders_2])).

fof(c_0_7,plain,(
    ! [X14,X15,X16] :
      ( v2_struct_0(X14)
      | ~ v3_orders_2(X14)
      | ~ v4_orders_2(X14)
      | ~ v5_orders_2(X14)
      | ~ l1_orders_2(X14)
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
      | ~ m1_subset_1(X16,u1_struct_0(X14))
      | m1_subset_1(k3_orders_2(X14,X15,X16),k1_zfmisc_1(u1_struct_0(X14))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_orders_2])])])).

fof(c_0_8,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v3_orders_2(esk2_0)
    & v4_orders_2(esk2_0)
    & v5_orders_2(esk2_0)
    & l1_orders_2(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk4_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & r2_orders_2(esk2_0,esk3_0,esk4_0)
    & ~ r1_tarski(k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).

fof(c_0_9,plain,(
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

fof(c_0_10,plain,(
    ! [X11,X12,X13] :
      ( ~ r2_hidden(X11,X12)
      | ~ m1_subset_1(X12,k1_zfmisc_1(X13))
      | m1_subset_1(X11,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_11,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_20,plain,(
    ! [X17,X18,X19,X20] :
      ( ~ v4_orders_2(X17)
      | ~ v5_orders_2(X17)
      | ~ l1_orders_2(X17)
      | ~ m1_subset_1(X18,u1_struct_0(X17))
      | ~ m1_subset_1(X19,u1_struct_0(X17))
      | ~ m1_subset_1(X20,u1_struct_0(X17))
      | ~ r2_orders_2(X17,X18,X19)
      | ~ r2_orders_2(X17,X19,X20)
      | r2_orders_2(X17,X18,X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_orders_2])])])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(k3_orders_2(esk2_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_14]),c_0_15]),c_0_16])]),c_0_17])).

fof(c_0_22,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_23,plain,
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
    inference(csr,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,plain,
    ( r2_orders_2(X1,X2,X4)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_orders_2(X1,X2,X3)
    | ~ r2_orders_2(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_26,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,k3_orders_2(esk2_0,esk5_0,X2)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_21])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(X1,k3_orders_2(esk2_0,esk5_0,X2))
    | ~ r2_orders_2(esk2_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_12]),c_0_13]),c_0_14]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_30,negated_conjecture,
    ( r2_orders_2(esk2_0,X1,esk4_0)
    | ~ r2_orders_2(esk2_0,X2,esk4_0)
    | ~ r2_orders_2(esk2_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_13]),c_0_14]),c_0_15])])).

cnf(c_0_31,negated_conjecture,
    ( r2_orders_2(esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_33,negated_conjecture,
    ( r2_orders_2(esk2_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,k3_orders_2(esk2_0,esk5_0,X2)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_12]),c_0_13]),c_0_14]),c_0_15]),c_0_16])]),c_0_17]),c_0_27])).

cnf(c_0_34,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(X1,k3_orders_2(esk2_0,esk5_0,X2))
    | ~ r2_orders_2(esk2_0,esk1_2(X1,k3_orders_2(esk2_0,esk5_0,X2)),X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ r2_hidden(esk1_2(X1,k3_orders_2(esk2_0,esk5_0,X2)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( r2_orders_2(esk2_0,X1,esk4_0)
    | ~ r2_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_12])).

cnf(c_0_39,negated_conjecture,
    ( r2_orders_2(esk2_0,esk1_2(k3_orders_2(esk2_0,esk5_0,X1),X2),X1)
    | r1_tarski(k3_orders_2(esk2_0,esk5_0,X1),X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,k3_orders_2(esk2_0,esk5_0,X2)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_12]),c_0_13]),c_0_14]),c_0_15]),c_0_16])]),c_0_17]),c_0_27])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(X1,k3_orders_2(esk2_0,esk5_0,esk4_0))
    | ~ r2_orders_2(esk2_0,esk1_2(X1,k3_orders_2(esk2_0,esk5_0,esk4_0)),esk3_0)
    | ~ r2_hidden(esk1_2(X1,k3_orders_2(esk2_0,esk5_0,esk4_0)),esk5_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_25])]),c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( r2_orders_2(esk2_0,esk1_2(k3_orders_2(esk2_0,esk5_0,esk3_0),X1),esk3_0)
    | r1_tarski(k3_orders_2(esk2_0,esk5_0,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( ~ r1_tarski(k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk1_2(k3_orders_2(esk2_0,esk5_0,X1),X2),esk5_0)
    | r1_tarski(k3_orders_2(esk2_0,esk5_0,X1),X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_34])).

cnf(c_0_45,negated_conjecture,
    ( ~ r2_hidden(esk1_2(k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0)),esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk1_2(k3_orders_2(esk2_0,esk5_0,esk3_0),X1),esk5_0)
    | r1_tarski(k3_orders_2(esk2_0,esk5_0,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_32])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_43]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:40:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.028 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t64_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_orders_2(X1,X2,X3)=>r1_tarski(k3_orders_2(X1,X4,X2),k3_orders_2(X1,X4,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_orders_2)).
% 0.14/0.38  fof(dt_k3_orders_2, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 0.14/0.38  fof(t57_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,k3_orders_2(X1,X4,X3))<=>(r2_orders_2(X1,X2,X3)&r2_hidden(X2,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_orders_2)).
% 0.14/0.38  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.14/0.38  fof(t29_orders_2, axiom, ![X1]:(((v4_orders_2(X1)&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r2_orders_2(X1,X2,X3)&r2_orders_2(X1,X3,X4))=>r2_orders_2(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_orders_2)).
% 0.14/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.14/0.38  fof(c_0_6, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_orders_2(X1,X2,X3)=>r1_tarski(k3_orders_2(X1,X4,X2),k3_orders_2(X1,X4,X3)))))))), inference(assume_negation,[status(cth)],[t64_orders_2])).
% 0.14/0.38  fof(c_0_7, plain, ![X14, X15, X16]:(v2_struct_0(X14)|~v3_orders_2(X14)|~v4_orders_2(X14)|~v5_orders_2(X14)|~l1_orders_2(X14)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|~m1_subset_1(X16,u1_struct_0(X14))|m1_subset_1(k3_orders_2(X14,X15,X16),k1_zfmisc_1(u1_struct_0(X14)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_orders_2])])])).
% 0.14/0.38  fof(c_0_8, negated_conjecture, (((((~v2_struct_0(esk2_0)&v3_orders_2(esk2_0))&v4_orders_2(esk2_0))&v5_orders_2(esk2_0))&l1_orders_2(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&(m1_subset_1(esk4_0,u1_struct_0(esk2_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(r2_orders_2(esk2_0,esk3_0,esk4_0)&~r1_tarski(k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).
% 0.14/0.38  fof(c_0_9, plain, ![X21, X22, X23, X24]:(((r2_orders_2(X21,X22,X23)|~r2_hidden(X22,k3_orders_2(X21,X24,X23))|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X21)))|~m1_subset_1(X23,u1_struct_0(X21))|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~v3_orders_2(X21)|~v4_orders_2(X21)|~v5_orders_2(X21)|~l1_orders_2(X21)))&(r2_hidden(X22,X24)|~r2_hidden(X22,k3_orders_2(X21,X24,X23))|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X21)))|~m1_subset_1(X23,u1_struct_0(X21))|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~v3_orders_2(X21)|~v4_orders_2(X21)|~v5_orders_2(X21)|~l1_orders_2(X21))))&(~r2_orders_2(X21,X22,X23)|~r2_hidden(X22,X24)|r2_hidden(X22,k3_orders_2(X21,X24,X23))|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X21)))|~m1_subset_1(X23,u1_struct_0(X21))|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~v3_orders_2(X21)|~v4_orders_2(X21)|~v5_orders_2(X21)|~l1_orders_2(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_orders_2])])])])])).
% 0.14/0.38  fof(c_0_10, plain, ![X11, X12, X13]:(~r2_hidden(X11,X12)|~m1_subset_1(X12,k1_zfmisc_1(X13))|m1_subset_1(X11,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.14/0.38  cnf(c_0_11, plain, (v2_struct_0(X1)|m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_13, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_14, negated_conjecture, (v5_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_15, negated_conjecture, (v4_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_16, negated_conjecture, (v3_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_17, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_18, plain, (r2_hidden(X2,k3_orders_2(X1,X4,X3))|v2_struct_0(X1)|~r2_orders_2(X1,X2,X3)|~r2_hidden(X2,X4)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_19, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  fof(c_0_20, plain, ![X17, X18, X19, X20]:(~v4_orders_2(X17)|~v5_orders_2(X17)|~l1_orders_2(X17)|(~m1_subset_1(X18,u1_struct_0(X17))|(~m1_subset_1(X19,u1_struct_0(X17))|(~m1_subset_1(X20,u1_struct_0(X17))|(~r2_orders_2(X17,X18,X19)|~r2_orders_2(X17,X19,X20)|r2_orders_2(X17,X18,X20)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_orders_2])])])).
% 0.14/0.38  cnf(c_0_21, negated_conjecture, (m1_subset_1(k3_orders_2(esk2_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13]), c_0_14]), c_0_15]), c_0_16])]), c_0_17])).
% 0.14/0.38  fof(c_0_22, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.14/0.38  cnf(c_0_23, plain, (v2_struct_0(X1)|r2_hidden(X2,k3_orders_2(X1,X3,X4))|~r2_orders_2(X1,X2,X4)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X2,X3)), inference(csr,[status(thm)],[c_0_18, c_0_19])).
% 0.14/0.38  cnf(c_0_24, plain, (r2_orders_2(X1,X2,X4)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~r2_orders_2(X1,X2,X3)|~r2_orders_2(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.38  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_26, plain, (r2_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r2_hidden(X2,k3_orders_2(X1,X4,X3))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_27, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_subset_1(X2,u1_struct_0(esk2_0))|~r2_hidden(X1,k3_orders_2(esk2_0,esk5_0,X2))), inference(spm,[status(thm)],[c_0_19, c_0_21])).
% 0.14/0.38  cnf(c_0_28, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.38  cnf(c_0_29, negated_conjecture, (r2_hidden(X1,k3_orders_2(esk2_0,esk5_0,X2))|~r2_orders_2(esk2_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~r2_hidden(X1,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_12]), c_0_13]), c_0_14]), c_0_15]), c_0_16])]), c_0_17])).
% 0.14/0.38  cnf(c_0_30, negated_conjecture, (r2_orders_2(esk2_0,X1,esk4_0)|~r2_orders_2(esk2_0,X2,esk4_0)|~r2_orders_2(esk2_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_13]), c_0_14]), c_0_15])])).
% 0.14/0.38  cnf(c_0_31, negated_conjecture, (r2_orders_2(esk2_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_33, negated_conjecture, (r2_orders_2(esk2_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~r2_hidden(X1,k3_orders_2(esk2_0,esk5_0,X2))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_12]), c_0_13]), c_0_14]), c_0_15]), c_0_16])]), c_0_17]), c_0_27])).
% 0.14/0.38  cnf(c_0_34, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.38  cnf(c_0_35, plain, (r2_hidden(X1,X2)|v2_struct_0(X3)|~r2_hidden(X1,k3_orders_2(X3,X2,X4))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X4,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~v3_orders_2(X3)|~v4_orders_2(X3)|~v5_orders_2(X3)|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_36, negated_conjecture, (r1_tarski(X1,k3_orders_2(esk2_0,esk5_0,X2))|~r2_orders_2(esk2_0,esk1_2(X1,k3_orders_2(esk2_0,esk5_0,X2)),X2)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~r2_hidden(esk1_2(X1,k3_orders_2(esk2_0,esk5_0,X2)),esk5_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.14/0.38  cnf(c_0_37, negated_conjecture, (r2_orders_2(esk2_0,X1,esk4_0)|~r2_orders_2(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])])).
% 0.14/0.38  cnf(c_0_38, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_19, c_0_12])).
% 0.14/0.38  cnf(c_0_39, negated_conjecture, (r2_orders_2(esk2_0,esk1_2(k3_orders_2(esk2_0,esk5_0,X1),X2),X1)|r1_tarski(k3_orders_2(esk2_0,esk5_0,X1),X2)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.14/0.38  cnf(c_0_40, negated_conjecture, (r2_hidden(X1,esk5_0)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~r2_hidden(X1,k3_orders_2(esk2_0,esk5_0,X2))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_12]), c_0_13]), c_0_14]), c_0_15]), c_0_16])]), c_0_17]), c_0_27])).
% 0.14/0.38  cnf(c_0_41, negated_conjecture, (r1_tarski(X1,k3_orders_2(esk2_0,esk5_0,esk4_0))|~r2_orders_2(esk2_0,esk1_2(X1,k3_orders_2(esk2_0,esk5_0,esk4_0)),esk3_0)|~r2_hidden(esk1_2(X1,k3_orders_2(esk2_0,esk5_0,esk4_0)),esk5_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_25])]), c_0_38])).
% 0.14/0.38  cnf(c_0_42, negated_conjecture, (r2_orders_2(esk2_0,esk1_2(k3_orders_2(esk2_0,esk5_0,esk3_0),X1),esk3_0)|r1_tarski(k3_orders_2(esk2_0,esk5_0,esk3_0),X1)), inference(spm,[status(thm)],[c_0_39, c_0_32])).
% 0.14/0.38  cnf(c_0_43, negated_conjecture, (~r1_tarski(k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_44, negated_conjecture, (r2_hidden(esk1_2(k3_orders_2(esk2_0,esk5_0,X1),X2),esk5_0)|r1_tarski(k3_orders_2(esk2_0,esk5_0,X1),X2)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_40, c_0_34])).
% 0.14/0.38  cnf(c_0_45, negated_conjecture, (~r2_hidden(esk1_2(k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0)),esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])).
% 0.14/0.38  cnf(c_0_46, negated_conjecture, (r2_hidden(esk1_2(k3_orders_2(esk2_0,esk5_0,esk3_0),X1),esk5_0)|r1_tarski(k3_orders_2(esk2_0,esk5_0,esk3_0),X1)), inference(spm,[status(thm)],[c_0_44, c_0_32])).
% 0.14/0.38  cnf(c_0_47, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_43]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 48
% 0.14/0.38  # Proof object clause steps            : 35
% 0.14/0.38  # Proof object formula steps           : 13
% 0.14/0.38  # Proof object conjectures             : 29
% 0.14/0.38  # Proof object clause conjectures      : 26
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 18
% 0.14/0.38  # Proof object initial formulas used   : 6
% 0.14/0.38  # Proof object generating inferences   : 16
% 0.14/0.38  # Proof object simplifying inferences  : 38
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 6
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 19
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 19
% 0.14/0.38  # Processed clauses                    : 91
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 11
% 0.14/0.38  # ...remaining for further processing  : 80
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 0
% 0.14/0.38  # Generated clauses                    : 94
% 0.14/0.38  # ...of the previous two non-trivial   : 84
% 0.14/0.38  # Contextual simplify-reflections      : 7
% 0.14/0.38  # Paramodulations                      : 94
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 0
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 61
% 0.14/0.38  #    Positive orientable unit clauses  : 11
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 3
% 0.14/0.38  #    Non-unit-clauses                  : 47
% 0.14/0.38  # Current number of unprocessed clauses: 31
% 0.14/0.38  # ...number of literals in the above   : 147
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 19
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 1112
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 336
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 18
% 0.14/0.38  # Unit Clause-clause subsumption calls : 27
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 4
% 0.14/0.38  # BW rewrite match successes           : 0
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 5140
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.033 s
% 0.14/0.38  # System time              : 0.006 s
% 0.14/0.38  # Total time               : 0.039 s
% 0.14/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
