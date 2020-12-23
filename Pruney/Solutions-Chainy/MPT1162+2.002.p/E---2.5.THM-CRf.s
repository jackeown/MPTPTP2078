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
% DateTime   : Thu Dec  3 11:09:57 EST 2020

% Result     : Theorem 1.08s
% Output     : CNFRefutation 1.08s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 675 expanded)
%              Number of clauses        :   44 ( 218 expanded)
%              Number of leaves         :    6 ( 161 expanded)
%              Depth                    :   12
%              Number of atoms          :  290 (5007 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   18 (   5 average)
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

fof(d10_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_orders_2(X1,X2,X3)
              <=> ( r1_orders_2(X1,X2,X3)
                  & X2 != X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

fof(t32_orders_2,axiom,(
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
                 => ( ( ( r2_orders_2(X1,X2,X3)
                        & r1_orders_2(X1,X3,X4) )
                      | ( r1_orders_2(X1,X2,X3)
                        & r2_orders_2(X1,X3,X4) ) )
                   => r2_orders_2(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_orders_2)).

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
    ! [X12,X13,X14] :
      ( v2_struct_0(X12)
      | ~ v3_orders_2(X12)
      | ~ v4_orders_2(X12)
      | ~ v5_orders_2(X12)
      | ~ l1_orders_2(X12)
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
      | ~ m1_subset_1(X14,u1_struct_0(X12))
      | m1_subset_1(k3_orders_2(X12,X13,X14),k1_zfmisc_1(u1_struct_0(X12))) ) ),
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

cnf(c_0_9,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_16,plain,(
    ! [X9,X10,X11] :
      ( ( r1_orders_2(X9,X10,X11)
        | ~ r2_orders_2(X9,X10,X11)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | ~ l1_orders_2(X9) )
      & ( X10 != X11
        | ~ r2_orders_2(X9,X10,X11)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | ~ l1_orders_2(X9) )
      & ( ~ r1_orders_2(X9,X10,X11)
        | X10 = X11
        | r2_orders_2(X9,X10,X11)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | ~ l1_orders_2(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_orders_2])])])])).

fof(c_0_17,plain,(
    ! [X5,X6,X7] :
      ( ( m1_subset_1(esk1_3(X5,X6,X7),X5)
        | r1_tarski(X6,X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(X5)) )
      & ( r2_hidden(esk1_3(X5,X6,X7),X6)
        | r1_tarski(X6,X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(X5)) )
      & ( ~ r2_hidden(esk1_3(X5,X6,X7),X7)
        | r1_tarski(X6,X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(X5)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(k3_orders_2(esk2_0,X1,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_21,plain,(
    ! [X15,X16,X17,X18] :
      ( ( ~ r2_orders_2(X15,X16,X17)
        | ~ r1_orders_2(X15,X17,X18)
        | r2_orders_2(X15,X16,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X15))
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v4_orders_2(X15)
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) )
      & ( ~ r1_orders_2(X15,X16,X17)
        | ~ r2_orders_2(X15,X17,X18)
        | r2_orders_2(X15,X16,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X15))
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v4_orders_2(X15)
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_orders_2])])])])).

cnf(c_0_22,plain,
    ( r1_orders_2(X1,X2,X3)
    | ~ r2_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,plain,(
    ! [X19,X20,X21,X22] :
      ( ( r2_orders_2(X19,X20,X21)
        | ~ r2_hidden(X20,k3_orders_2(X19,X22,X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ v3_orders_2(X19)
        | ~ v4_orders_2(X19)
        | ~ v5_orders_2(X19)
        | ~ l1_orders_2(X19) )
      & ( r2_hidden(X20,X22)
        | ~ r2_hidden(X20,k3_orders_2(X19,X22,X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ v3_orders_2(X19)
        | ~ v4_orders_2(X19)
        | ~ v5_orders_2(X19)
        | ~ l1_orders_2(X19) )
      & ( ~ r2_orders_2(X19,X20,X21)
        | ~ r2_hidden(X20,X22)
        | r2_hidden(X20,k3_orders_2(X19,X22,X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ v3_orders_2(X19)
        | ~ v4_orders_2(X19)
        | ~ v5_orders_2(X19)
        | ~ l1_orders_2(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_orders_2])])])])])).

cnf(c_0_24,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),X1)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(k3_orders_2(esk2_0,esk5_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(k3_orders_2(esk2_0,X1,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_20]),c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_27,plain,
    ( r2_orders_2(X1,X2,X4)
    | ~ r2_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | ~ r2_orders_2(esk2_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_10]),c_0_14])])).

cnf(c_0_29,negated_conjecture,
    ( r2_orders_2(esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_30,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(X1,k3_orders_2(esk2_0,esk5_0,esk4_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk2_0),X1,k3_orders_2(esk2_0,esk5_0,esk4_0)),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(k3_orders_2(esk2_0,esk5_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_19])).

cnf(c_0_33,negated_conjecture,
    ( ~ r1_tarski(k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_34,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_35,negated_conjecture,
    ( r2_orders_2(esk2_0,X1,esk4_0)
    | ~ r1_orders_2(esk2_0,X2,esk4_0)
    | ~ r2_orders_2(esk2_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_10]),c_0_11]),c_0_12]),c_0_14])])).

cnf(c_0_36,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_20])])).

cnf(c_0_37,negated_conjecture,
    ( r2_orders_2(esk2_0,X1,esk3_0)
    | ~ r2_hidden(X1,k3_orders_2(esk2_0,X2,esk3_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_20]),c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0)),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(X1,k3_orders_2(esk2_0,esk5_0,esk4_0))
    | r2_hidden(esk1_3(u1_struct_0(esk2_0),X1,k3_orders_2(esk2_0,esk5_0,esk4_0)),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_25])).

cnf(c_0_40,negated_conjecture,
    ( r2_orders_2(esk2_0,X1,esk4_0)
    | ~ r2_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_20])])).

cnf(c_0_41,negated_conjecture,
    ( r2_orders_2(esk2_0,esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0)),esk3_0)
    | ~ r2_hidden(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0)),k3_orders_2(esk2_0,X1,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0)),k3_orders_2(esk2_0,esk5_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_32]),c_0_33])).

cnf(c_0_43,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_44,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_45,negated_conjecture,
    ( r2_orders_2(esk2_0,esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0)),esk4_0)
    | ~ r2_orders_2(esk2_0,esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( r2_orders_2(esk2_0,esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_19]),c_0_42])])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_orders_2(esk2_0,X2,esk3_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_20]),c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_48,plain,
    ( r1_tarski(X2,X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(X1,k3_orders_2(esk2_0,X2,esk4_0))
    | ~ r2_orders_2(esk2_0,X1,esk4_0)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_50,negated_conjecture,
    ( r2_orders_2(esk2_0,esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46])])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0)),X1)
    | ~ r2_hidden(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0)),k3_orders_2(esk2_0,X1,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_38])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(X1,k3_orders_2(esk2_0,esk5_0,esk4_0))
    | ~ r2_hidden(esk1_3(u1_struct_0(esk2_0),X1,k3_orders_2(esk2_0,esk5_0,esk4_0)),k3_orders_2(esk2_0,esk5_0,esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_25])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0)),k3_orders_2(esk2_0,X1,esk4_0))
    | ~ r2_hidden(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0)),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_38])])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0)),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_19]),c_0_42])])).

cnf(c_0_55,negated_conjecture,
    ( ~ r2_hidden(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0)),k3_orders_2(esk2_0,esk5_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_32]),c_0_33])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_19]),c_0_54])]),c_0_55]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:22:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 1.08/1.25  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 1.08/1.25  # and selection function SelectNewComplexAHP.
% 1.08/1.25  #
% 1.08/1.25  # Preprocessing time       : 0.028 s
% 1.08/1.25  # Presaturation interreduction done
% 1.08/1.25  
% 1.08/1.25  # Proof found!
% 1.08/1.25  # SZS status Theorem
% 1.08/1.25  # SZS output start CNFRefutation
% 1.08/1.25  fof(t64_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_orders_2(X1,X2,X3)=>r1_tarski(k3_orders_2(X1,X4,X2),k3_orders_2(X1,X4,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_orders_2)).
% 1.08/1.25  fof(dt_k3_orders_2, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 1.08/1.25  fof(d10_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_orders_2(X1,X2,X3)<=>(r1_orders_2(X1,X2,X3)&X2!=X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_orders_2)).
% 1.08/1.25  fof(t7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,X2)=>r2_hidden(X4,X3)))=>r1_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_subset_1)).
% 1.08/1.25  fof(t32_orders_2, axiom, ![X1]:(((v4_orders_2(X1)&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(((r2_orders_2(X1,X2,X3)&r1_orders_2(X1,X3,X4))|(r1_orders_2(X1,X2,X3)&r2_orders_2(X1,X3,X4)))=>r2_orders_2(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_orders_2)).
% 1.08/1.25  fof(t57_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,k3_orders_2(X1,X4,X3))<=>(r2_orders_2(X1,X2,X3)&r2_hidden(X2,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_orders_2)).
% 1.08/1.25  fof(c_0_6, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_orders_2(X1,X2,X3)=>r1_tarski(k3_orders_2(X1,X4,X2),k3_orders_2(X1,X4,X3)))))))), inference(assume_negation,[status(cth)],[t64_orders_2])).
% 1.08/1.25  fof(c_0_7, plain, ![X12, X13, X14]:(v2_struct_0(X12)|~v3_orders_2(X12)|~v4_orders_2(X12)|~v5_orders_2(X12)|~l1_orders_2(X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|~m1_subset_1(X14,u1_struct_0(X12))|m1_subset_1(k3_orders_2(X12,X13,X14),k1_zfmisc_1(u1_struct_0(X12)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_orders_2])])])).
% 1.08/1.25  fof(c_0_8, negated_conjecture, (((((~v2_struct_0(esk2_0)&v3_orders_2(esk2_0))&v4_orders_2(esk2_0))&v5_orders_2(esk2_0))&l1_orders_2(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&(m1_subset_1(esk4_0,u1_struct_0(esk2_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(r2_orders_2(esk2_0,esk3_0,esk4_0)&~r1_tarski(k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).
% 1.08/1.25  cnf(c_0_9, plain, (v2_struct_0(X1)|m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 1.08/1.25  cnf(c_0_10, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.08/1.25  cnf(c_0_11, negated_conjecture, (v5_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.08/1.25  cnf(c_0_12, negated_conjecture, (v4_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.08/1.25  cnf(c_0_13, negated_conjecture, (v3_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.08/1.25  cnf(c_0_14, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.08/1.25  cnf(c_0_15, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.08/1.25  fof(c_0_16, plain, ![X9, X10, X11]:(((r1_orders_2(X9,X10,X11)|~r2_orders_2(X9,X10,X11)|~m1_subset_1(X11,u1_struct_0(X9))|~m1_subset_1(X10,u1_struct_0(X9))|~l1_orders_2(X9))&(X10!=X11|~r2_orders_2(X9,X10,X11)|~m1_subset_1(X11,u1_struct_0(X9))|~m1_subset_1(X10,u1_struct_0(X9))|~l1_orders_2(X9)))&(~r1_orders_2(X9,X10,X11)|X10=X11|r2_orders_2(X9,X10,X11)|~m1_subset_1(X11,u1_struct_0(X9))|~m1_subset_1(X10,u1_struct_0(X9))|~l1_orders_2(X9))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_orders_2])])])])).
% 1.08/1.25  fof(c_0_17, plain, ![X5, X6, X7]:((m1_subset_1(esk1_3(X5,X6,X7),X5)|r1_tarski(X6,X7)|~m1_subset_1(X7,k1_zfmisc_1(X5))|~m1_subset_1(X6,k1_zfmisc_1(X5)))&((r2_hidden(esk1_3(X5,X6,X7),X6)|r1_tarski(X6,X7)|~m1_subset_1(X7,k1_zfmisc_1(X5))|~m1_subset_1(X6,k1_zfmisc_1(X5)))&(~r2_hidden(esk1_3(X5,X6,X7),X7)|r1_tarski(X6,X7)|~m1_subset_1(X7,k1_zfmisc_1(X5))|~m1_subset_1(X6,k1_zfmisc_1(X5))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).
% 1.08/1.25  cnf(c_0_18, negated_conjecture, (m1_subset_1(k3_orders_2(esk2_0,X1,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11]), c_0_12]), c_0_13]), c_0_14])]), c_0_15])).
% 1.08/1.25  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.08/1.25  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.08/1.25  fof(c_0_21, plain, ![X15, X16, X17, X18]:((~r2_orders_2(X15,X16,X17)|~r1_orders_2(X15,X17,X18)|r2_orders_2(X15,X16,X18)|~m1_subset_1(X18,u1_struct_0(X15))|~m1_subset_1(X17,u1_struct_0(X15))|~m1_subset_1(X16,u1_struct_0(X15))|(~v4_orders_2(X15)|~v5_orders_2(X15)|~l1_orders_2(X15)))&(~r1_orders_2(X15,X16,X17)|~r2_orders_2(X15,X17,X18)|r2_orders_2(X15,X16,X18)|~m1_subset_1(X18,u1_struct_0(X15))|~m1_subset_1(X17,u1_struct_0(X15))|~m1_subset_1(X16,u1_struct_0(X15))|(~v4_orders_2(X15)|~v5_orders_2(X15)|~l1_orders_2(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_orders_2])])])])).
% 1.08/1.25  cnf(c_0_22, plain, (r1_orders_2(X1,X2,X3)|~r2_orders_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.08/1.25  fof(c_0_23, plain, ![X19, X20, X21, X22]:(((r2_orders_2(X19,X20,X21)|~r2_hidden(X20,k3_orders_2(X19,X22,X21))|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X19)))|~m1_subset_1(X21,u1_struct_0(X19))|~m1_subset_1(X20,u1_struct_0(X19))|(v2_struct_0(X19)|~v3_orders_2(X19)|~v4_orders_2(X19)|~v5_orders_2(X19)|~l1_orders_2(X19)))&(r2_hidden(X20,X22)|~r2_hidden(X20,k3_orders_2(X19,X22,X21))|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X19)))|~m1_subset_1(X21,u1_struct_0(X19))|~m1_subset_1(X20,u1_struct_0(X19))|(v2_struct_0(X19)|~v3_orders_2(X19)|~v4_orders_2(X19)|~v5_orders_2(X19)|~l1_orders_2(X19))))&(~r2_orders_2(X19,X20,X21)|~r2_hidden(X20,X22)|r2_hidden(X20,k3_orders_2(X19,X22,X21))|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X19)))|~m1_subset_1(X21,u1_struct_0(X19))|~m1_subset_1(X20,u1_struct_0(X19))|(v2_struct_0(X19)|~v3_orders_2(X19)|~v4_orders_2(X19)|~v5_orders_2(X19)|~l1_orders_2(X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_orders_2])])])])])).
% 1.08/1.25  cnf(c_0_24, plain, (m1_subset_1(esk1_3(X1,X2,X3),X1)|r1_tarski(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.08/1.25  cnf(c_0_25, negated_conjecture, (m1_subset_1(k3_orders_2(esk2_0,esk5_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 1.08/1.25  cnf(c_0_26, negated_conjecture, (m1_subset_1(k3_orders_2(esk2_0,X1,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_20]), c_0_11]), c_0_12]), c_0_13]), c_0_14])]), c_0_15])).
% 1.08/1.25  cnf(c_0_27, plain, (r2_orders_2(X1,X2,X4)|~r2_orders_2(X1,X2,X3)|~r1_orders_2(X1,X3,X4)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.08/1.25  cnf(c_0_28, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|~r2_orders_2(esk2_0,X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_10]), c_0_14])])).
% 1.08/1.25  cnf(c_0_29, negated_conjecture, (r2_orders_2(esk2_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.08/1.25  cnf(c_0_30, plain, (r2_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r2_hidden(X2,k3_orders_2(X1,X4,X3))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.08/1.25  cnf(c_0_31, negated_conjecture, (r1_tarski(X1,k3_orders_2(esk2_0,esk5_0,esk4_0))|m1_subset_1(esk1_3(u1_struct_0(esk2_0),X1,k3_orders_2(esk2_0,esk5_0,esk4_0)),u1_struct_0(esk2_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 1.08/1.25  cnf(c_0_32, negated_conjecture, (m1_subset_1(k3_orders_2(esk2_0,esk5_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_26, c_0_19])).
% 1.08/1.25  cnf(c_0_33, negated_conjecture, (~r1_tarski(k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.08/1.25  cnf(c_0_34, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r1_tarski(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.08/1.25  cnf(c_0_35, negated_conjecture, (r2_orders_2(esk2_0,X1,esk4_0)|~r1_orders_2(esk2_0,X2,esk4_0)|~r2_orders_2(esk2_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_10]), c_0_11]), c_0_12]), c_0_14])])).
% 1.08/1.25  cnf(c_0_36, negated_conjecture, (r1_orders_2(esk2_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_20])])).
% 1.08/1.25  cnf(c_0_37, negated_conjecture, (r2_orders_2(esk2_0,X1,esk3_0)|~r2_hidden(X1,k3_orders_2(esk2_0,X2,esk3_0))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_20]), c_0_11]), c_0_12]), c_0_13]), c_0_14])]), c_0_15])).
% 1.08/1.25  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0)),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])).
% 1.08/1.25  cnf(c_0_39, negated_conjecture, (r1_tarski(X1,k3_orders_2(esk2_0,esk5_0,esk4_0))|r2_hidden(esk1_3(u1_struct_0(esk2_0),X1,k3_orders_2(esk2_0,esk5_0,esk4_0)),X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_34, c_0_25])).
% 1.08/1.25  cnf(c_0_40, negated_conjecture, (r2_orders_2(esk2_0,X1,esk4_0)|~r2_orders_2(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_20])])).
% 1.08/1.25  cnf(c_0_41, negated_conjecture, (r2_orders_2(esk2_0,esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0)),esk3_0)|~r2_hidden(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0)),k3_orders_2(esk2_0,X1,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 1.08/1.25  cnf(c_0_42, negated_conjecture, (r2_hidden(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0)),k3_orders_2(esk2_0,esk5_0,esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_32]), c_0_33])).
% 1.08/1.25  cnf(c_0_43, plain, (r2_hidden(X1,X2)|v2_struct_0(X3)|~r2_hidden(X1,k3_orders_2(X3,X2,X4))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X4,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~v3_orders_2(X3)|~v4_orders_2(X3)|~v5_orders_2(X3)|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.08/1.25  cnf(c_0_44, plain, (r2_hidden(X2,k3_orders_2(X1,X4,X3))|v2_struct_0(X1)|~r2_orders_2(X1,X2,X3)|~r2_hidden(X2,X4)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.08/1.25  cnf(c_0_45, negated_conjecture, (r2_orders_2(esk2_0,esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0)),esk4_0)|~r2_orders_2(esk2_0,esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0)),esk3_0)), inference(spm,[status(thm)],[c_0_40, c_0_38])).
% 1.08/1.25  cnf(c_0_46, negated_conjecture, (r2_orders_2(esk2_0,esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_19]), c_0_42])])).
% 1.08/1.25  cnf(c_0_47, negated_conjecture, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_orders_2(esk2_0,X2,esk3_0))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_20]), c_0_11]), c_0_12]), c_0_13]), c_0_14])]), c_0_15])).
% 1.08/1.25  cnf(c_0_48, plain, (r1_tarski(X2,X3)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.08/1.25  cnf(c_0_49, negated_conjecture, (r2_hidden(X1,k3_orders_2(esk2_0,X2,esk4_0))|~r2_orders_2(esk2_0,X1,esk4_0)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_10]), c_0_11]), c_0_12]), c_0_13]), c_0_14])]), c_0_15])).
% 1.08/1.25  cnf(c_0_50, negated_conjecture, (r2_orders_2(esk2_0,esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46])])).
% 1.08/1.25  cnf(c_0_51, negated_conjecture, (r2_hidden(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0)),X1)|~r2_hidden(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0)),k3_orders_2(esk2_0,X1,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_47, c_0_38])).
% 1.08/1.25  cnf(c_0_52, negated_conjecture, (r1_tarski(X1,k3_orders_2(esk2_0,esk5_0,esk4_0))|~r2_hidden(esk1_3(u1_struct_0(esk2_0),X1,k3_orders_2(esk2_0,esk5_0,esk4_0)),k3_orders_2(esk2_0,esk5_0,esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_48, c_0_25])).
% 1.08/1.25  cnf(c_0_53, negated_conjecture, (r2_hidden(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0)),k3_orders_2(esk2_0,X1,esk4_0))|~r2_hidden(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0)),X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_38])])).
% 1.08/1.25  cnf(c_0_54, negated_conjecture, (r2_hidden(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0)),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_19]), c_0_42])])).
% 1.08/1.25  cnf(c_0_55, negated_conjecture, (~r2_hidden(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0)),k3_orders_2(esk2_0,esk5_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_32]), c_0_33])).
% 1.08/1.25  cnf(c_0_56, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_19]), c_0_54])]), c_0_55]), ['proof']).
% 1.08/1.25  # SZS output end CNFRefutation
% 1.08/1.25  # Proof object total steps             : 57
% 1.08/1.25  # Proof object clause steps            : 44
% 1.08/1.25  # Proof object formula steps           : 13
% 1.08/1.25  # Proof object conjectures             : 38
% 1.08/1.25  # Proof object clause conjectures      : 35
% 1.08/1.25  # Proof object formula conjectures     : 3
% 1.08/1.25  # Proof object initial clauses used    : 19
% 1.08/1.25  # Proof object initial formulas used   : 6
% 1.08/1.25  # Proof object generating inferences   : 24
% 1.08/1.25  # Proof object simplifying inferences  : 54
% 1.08/1.25  # Training examples: 0 positive, 0 negative
% 1.08/1.25  # Parsed axioms                        : 6
% 1.08/1.25  # Removed by relevancy pruning/SinE    : 0
% 1.08/1.25  # Initial clauses                      : 22
% 1.08/1.25  # Removed in clause preprocessing      : 0
% 1.08/1.25  # Initial clauses in saturation        : 22
% 1.08/1.25  # Processed clauses                    : 3956
% 1.08/1.25  # ...of these trivial                  : 0
% 1.08/1.25  # ...subsumed                          : 557
% 1.08/1.25  # ...remaining for further processing  : 3399
% 1.08/1.25  # Other redundant clauses eliminated   : 1
% 1.08/1.25  # Clauses deleted for lack of memory   : 0
% 1.08/1.25  # Backward-subsumed                    : 11
% 1.08/1.25  # Backward-rewritten                   : 4
% 1.08/1.25  # Generated clauses                    : 65984
% 1.08/1.25  # ...of the previous two non-trivial   : 65408
% 1.08/1.25  # Contextual simplify-reflections      : 4
% 1.08/1.25  # Paramodulations                      : 65983
% 1.08/1.25  # Factorizations                       : 0
% 1.08/1.25  # Equation resolutions                 : 1
% 1.08/1.25  # Propositional unsat checks           : 0
% 1.08/1.25  #    Propositional check models        : 0
% 1.08/1.25  #    Propositional check unsatisfiable : 0
% 1.08/1.25  #    Propositional clauses             : 0
% 1.08/1.25  #    Propositional clauses after purity: 0
% 1.08/1.25  #    Propositional unsat core size     : 0
% 1.08/1.25  #    Propositional preprocessing time  : 0.000
% 1.08/1.25  #    Propositional encoding time       : 0.000
% 1.08/1.25  #    Propositional solver time         : 0.000
% 1.08/1.25  #    Success case prop preproc time    : 0.000
% 1.08/1.25  #    Success case prop encoding time   : 0.000
% 1.08/1.25  #    Success case prop solver time     : 0.000
% 1.08/1.25  # Current number of processed clauses  : 3361
% 1.08/1.25  #    Positive orientable unit clauses  : 580
% 1.08/1.25  #    Positive unorientable unit clauses: 0
% 1.08/1.25  #    Negative unit clauses             : 2232
% 1.08/1.25  #    Non-unit-clauses                  : 549
% 1.08/1.25  # Current number of unprocessed clauses: 61473
% 1.08/1.25  # ...number of literals in the above   : 120717
% 1.08/1.25  # Current number of archived formulas  : 0
% 1.08/1.25  # Current number of archived clauses   : 37
% 1.08/1.25  # Clause-clause subsumption calls (NU) : 53107
% 1.08/1.25  # Rec. Clause-clause subsumption calls : 51996
% 1.08/1.25  # Non-unit clause-clause subsumptions  : 8
% 1.08/1.25  # Unit Clause-clause subsumption calls : 740498
% 1.08/1.25  # Rewrite failures with RHS unbound    : 0
% 1.08/1.25  # BW rewrite match attempts            : 154491
% 1.08/1.25  # BW rewrite match successes           : 6
% 1.08/1.25  # Condensation attempts                : 0
% 1.08/1.25  # Condensation successes               : 0
% 1.08/1.25  # Termbank termtop insertions          : 5277635
% 1.08/1.26  
% 1.08/1.26  # -------------------------------------------------
% 1.08/1.26  # User time                : 0.886 s
% 1.08/1.26  # System time              : 0.037 s
% 1.08/1.26  # Total time               : 0.922 s
% 1.08/1.26  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
