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
% DateTime   : Thu Dec  3 11:10:01 EST 2020

% Result     : Theorem 1.43s
% Output     : CNFRefutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :  107 (1211 expanded)
%              Number of clauses        :   86 ( 414 expanded)
%              Number of leaves         :   10 ( 304 expanded)
%              Depth                    :   28
%              Number of atoms          :  639 (10118 expanded)
%              Number of equality atoms :   12 ( 581 expanded)
%              Maximal formula depth    :   23 (   7 average)
%              Maximal clause size      :   31 (   5 average)
%              Maximal term depth       :    4 (   2 average)

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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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

fof(dt_m1_orders_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ! [X3] :
          ( m1_orders_2(X3,X1,X2)
         => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_orders_2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(c_0_10,negated_conjecture,(
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

fof(c_0_11,plain,(
    ! [X30,X31,X32] :
      ( v2_struct_0(X30)
      | ~ v3_orders_2(X30)
      | ~ v4_orders_2(X30)
      | ~ v5_orders_2(X30)
      | ~ l1_orders_2(X30)
      | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
      | ~ m1_orders_2(X32,X30,X31)
      | r1_tarski(X32,X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t67_orders_2])])])])).

fof(c_0_12,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_13,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_14,plain,
    ( v2_struct_0(X1)
    | r1_tarski(X3,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_orders_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( m1_orders_2(esk5_0,esk3_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( v5_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( v4_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( v3_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_22,plain,(
    ! [X14,X15,X16] :
      ( ( m1_subset_1(esk2_3(X14,X15,X16),X14)
        | r1_tarski(X15,X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(X14)) )
      & ( r2_hidden(esk2_3(X14,X15,X16),X15)
        | r1_tarski(X15,X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(X14)) )
      & ( ~ r2_hidden(esk2_3(X14,X15,X16),X16)
        | r1_tarski(X15,X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(X14)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).

cnf(c_0_23,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21])).

fof(c_0_25,plain,(
    ! [X26,X27,X28,X29] :
      ( ( r2_orders_2(X26,X27,X28)
        | ~ r2_hidden(X27,k3_orders_2(X26,X29,X28))
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | v2_struct_0(X26)
        | ~ v3_orders_2(X26)
        | ~ v4_orders_2(X26)
        | ~ v5_orders_2(X26)
        | ~ l1_orders_2(X26) )
      & ( r2_hidden(X27,X29)
        | ~ r2_hidden(X27,k3_orders_2(X26,X29,X28))
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | v2_struct_0(X26)
        | ~ v3_orders_2(X26)
        | ~ v4_orders_2(X26)
        | ~ v5_orders_2(X26)
        | ~ l1_orders_2(X26) )
      & ( ~ r2_orders_2(X26,X27,X28)
        | ~ r2_hidden(X27,X29)
        | r2_hidden(X27,k3_orders_2(X26,X29,X28))
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | v2_struct_0(X26)
        | ~ v3_orders_2(X26)
        | ~ v4_orders_2(X26)
        | ~ v5_orders_2(X26)
        | ~ l1_orders_2(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_orders_2])])])])])).

cnf(c_0_26,plain,
    ( r1_tarski(X2,X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(X1,esk6_0)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(esk2_3(X2,X1,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,plain,
    ( v2_struct_0(X1)
    | r2_hidden(esk2_3(X2,k3_orders_2(X1,X3,X4),X5),X3)
    | r1_tarski(k3_orders_2(X1,X3,X4),X5)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(esk2_3(X2,k3_orders_2(X1,X3,X4),X5),u1_struct_0(X1))
    | ~ m1_subset_1(k3_orders_2(X1,X3,X4),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_32,plain,(
    ! [X20,X21,X22] :
      ( v2_struct_0(X20)
      | ~ v3_orders_2(X20)
      | ~ v4_orders_2(X20)
      | ~ v5_orders_2(X20)
      | ~ l1_orders_2(X20)
      | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
      | ~ m1_subset_1(X22,u1_struct_0(X20))
      | m1_subset_1(k3_orders_2(X20,X21,X22),k1_zfmisc_1(u1_struct_0(X20))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_orders_2])])])).

cnf(c_0_33,negated_conjecture,
    ( v2_struct_0(X1)
    | r1_tarski(k3_orders_2(X1,esk5_0,X2),esk6_0)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(esk2_3(X3,k3_orders_2(X1,esk5_0,X2),esk6_0),u1_struct_0(X1))
    | ~ m1_subset_1(k3_orders_2(X1,esk5_0,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_34,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),X1)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( v2_struct_0(X1)
    | r1_tarski(k3_orders_2(X1,esk5_0,X2),esk6_0)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(k3_orders_2(esk3_0,esk5_0,X1),esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_20]),c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_37])]),c_0_21])).

cnf(c_0_39,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,k3_orders_2(esk3_0,esk5_0,X2)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_38])).

fof(c_0_41,plain,(
    ! [X33,X34,X35,X36,X37] :
      ( v2_struct_0(X33)
      | ~ v3_orders_2(X33)
      | ~ v4_orders_2(X33)
      | ~ v5_orders_2(X33)
      | ~ l1_orders_2(X33)
      | ~ m1_subset_1(X34,u1_struct_0(X33))
      | ~ m1_subset_1(X35,u1_struct_0(X33))
      | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X33)))
      | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X33)))
      | ~ r2_orders_2(X33,X34,X35)
      | ~ r2_hidden(X34,X36)
      | ~ r2_hidden(X35,X37)
      | ~ m1_orders_2(X37,X33,X36)
      | r2_hidden(X34,X37) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_orders_2])])])])).

fof(c_0_42,plain,(
    ! [X23,X24,X25] :
      ( v2_struct_0(X23)
      | ~ v3_orders_2(X23)
      | ~ v4_orders_2(X23)
      | ~ v5_orders_2(X23)
      | ~ l1_orders_2(X23)
      | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
      | ~ m1_orders_2(X25,X23,X24)
      | m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_orders_2])])])])).

cnf(c_0_43,plain,
    ( v2_struct_0(X1)
    | r1_tarski(X2,k3_orders_2(X1,X3,X4))
    | ~ r2_orders_2(X1,esk2_3(X5,X2,k3_orders_2(X1,X3,X4)),X4)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(esk2_3(X5,X2,k3_orders_2(X1,X3,X4)),u1_struct_0(X1))
    | ~ m1_subset_1(k3_orders_2(X1,X3,X4),k1_zfmisc_1(X5))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(esk2_3(X5,X2,k3_orders_2(X1,X3,X4)),X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk2_3(X1,k3_orders_2(esk3_0,esk5_0,X2),X3),esk6_0)
    | r1_tarski(k3_orders_2(esk3_0,esk5_0,X2),X3)
    | ~ m1_subset_1(k3_orders_2(esk3_0,esk5_0,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_29])).

cnf(c_0_45,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_25])).

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
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_orders_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( v2_struct_0(X1)
    | r1_tarski(k3_orders_2(esk3_0,esk5_0,X2),k3_orders_2(X1,esk6_0,X3))
    | ~ r2_orders_2(X1,esk2_3(X4,k3_orders_2(esk3_0,esk5_0,X2),k3_orders_2(X1,esk6_0,X3)),X3)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(esk2_3(X4,k3_orders_2(esk3_0,esk5_0,X2),k3_orders_2(X1,esk6_0,X3)),u1_struct_0(X1))
    | ~ m1_subset_1(k3_orders_2(esk3_0,esk5_0,X2),k1_zfmisc_1(X4))
    | ~ m1_subset_1(k3_orders_2(X1,esk6_0,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,plain,
    ( r2_orders_2(X1,esk2_3(X2,k3_orders_2(X1,X3,X4),X5),X4)
    | v2_struct_0(X1)
    | r1_tarski(k3_orders_2(X1,X3,X4),X5)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(esk2_3(X2,k3_orders_2(X1,X3,X4),X5),u1_struct_0(X1))
    | ~ m1_subset_1(k3_orders_2(X1,X3,X4),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_29])).

cnf(c_0_50,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,X3)
    | ~ r2_orders_2(X1,X2,X4)
    | ~ m1_orders_2(X3,X1,X5)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X4,X3)
    | ~ r2_hidden(X2,X5) ),
    inference(csr,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_52,negated_conjecture,
    ( v2_struct_0(X1)
    | r1_tarski(k3_orders_2(esk3_0,esk5_0,X2),k3_orders_2(X1,esk6_0,X3))
    | ~ r2_orders_2(X1,esk2_3(u1_struct_0(X1),k3_orders_2(esk3_0,esk5_0,X2),k3_orders_2(X1,esk6_0,X3)),X3)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(k3_orders_2(esk3_0,esk5_0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_34]),c_0_35])).

cnf(c_0_53,plain,
    ( r2_orders_2(X1,esk2_3(u1_struct_0(X1),k3_orders_2(X1,X2,X3),X4),X3)
    | v2_struct_0(X1)
    | r1_tarski(k3_orders_2(X1,X2,X3),X4)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_34]),c_0_35])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_orders_2(esk3_0,X1,esk4_0)
    | ~ m1_orders_2(X2,esk3_0,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(esk4_0,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_16]),c_0_17]),c_0_18]),c_0_19])]),c_0_21])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k3_orders_2(esk3_0,esk5_0,X1),k3_orders_2(esk3_0,esk6_0,X1))
    | ~ m1_subset_1(k3_orders_2(esk3_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(k3_orders_2(esk3_0,esk6_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_37])]),c_0_21])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,X1,esk4_0),X2),X3)
    | r1_tarski(k3_orders_2(esk3_0,X1,esk4_0),X2)
    | ~ m1_orders_2(X3,esk3_0,X4)
    | ~ m1_subset_1(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,X1,esk4_0),X2),u1_struct_0(esk3_0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,X1,esk4_0),X2),X4)
    | ~ r2_hidden(esk4_0,X3) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_53]),c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_51])]),c_0_21])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k3_orders_2(esk3_0,esk5_0,X1),k3_orders_2(esk3_0,esk6_0,X1))
    | ~ m1_subset_1(k3_orders_2(esk3_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_35]),c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,X1,esk4_0),X2),X3)
    | r1_tarski(k3_orders_2(esk3_0,X1,esk4_0),X2)
    | ~ m1_orders_2(X3,esk3_0,X1)
    | ~ m1_subset_1(k3_orders_2(esk3_0,X1,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(esk4_0,X3) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_31]),c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_51])]),c_0_21]),c_0_34])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(X1,k3_orders_2(esk3_0,esk6_0,X2))
    | ~ m1_subset_1(k3_orders_2(esk3_0,esk5_0,X2),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,k3_orders_2(esk3_0,esk5_0,X2)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk6_0,esk4_0),X1),esk5_0)
    | r1_tarski(k3_orders_2(esk3_0,esk6_0,esk4_0),X1)
    | ~ m1_subset_1(k3_orders_2(esk3_0,esk6_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_15]),c_0_20]),c_0_59])])).

cnf(c_0_62,negated_conjecture,
    ( r2_orders_2(esk3_0,X1,X2)
    | ~ m1_subset_1(k3_orders_2(esk3_0,esk5_0,X2),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,k3_orders_2(esk3_0,esk5_0,X2)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_60]),c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(k3_orders_2(esk3_0,esk6_0,esk4_0),esk5_0)
    | ~ m1_subset_1(k3_orders_2(esk3_0,esk6_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_61]),c_0_37])])).

cnf(c_0_64,plain,
    ( v2_struct_0(X1)
    | r1_tarski(X2,k3_orders_2(X1,X2,X3))
    | ~ r2_orders_2(X1,esk2_3(X4,X2,k3_orders_2(X1,X2,X3)),X3)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(esk2_3(X4,X2,k3_orders_2(X1,X2,X3)),u1_struct_0(X1))
    | ~ m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_29])).

cnf(c_0_65,negated_conjecture,
    ( r2_orders_2(esk3_0,esk2_3(X1,k3_orders_2(esk3_0,esk5_0,X2),X3),X2)
    | r1_tarski(k3_orders_2(esk3_0,esk5_0,X2),X3)
    | ~ m1_subset_1(esk2_3(X1,k3_orders_2(esk3_0,esk5_0,X2),X3),u1_struct_0(esk3_0))
    | ~ m1_subset_1(k3_orders_2(esk3_0,esk5_0,X2),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(k3_orders_2(esk3_0,esk5_0,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_29])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(k3_orders_2(esk3_0,esk6_0,esk4_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_35]),c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_51])]),c_0_21])).

fof(c_0_67,plain,(
    ! [X12,X13] :
      ( ( r1_tarski(X12,X13)
        | X12 != X13 )
      & ( r1_tarski(X13,X12)
        | X12 != X13 )
      & ( ~ r1_tarski(X12,X13)
        | ~ r1_tarski(X13,X12)
        | X12 = X13 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_68,plain,
    ( v2_struct_0(X1)
    | r1_tarski(k3_orders_2(X1,X2,X3),X2)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(esk2_3(X4,k3_orders_2(X1,X2,X3),X2),u1_struct_0(X1))
    | ~ m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_31])).

cnf(c_0_69,plain,
    ( v2_struct_0(X1)
    | r1_tarski(X2,k3_orders_2(X1,X2,X3))
    | ~ r2_orders_2(X1,esk2_3(u1_struct_0(X1),X2,k3_orders_2(X1,X2,X3)),X3)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_34]),c_0_35])).

cnf(c_0_70,negated_conjecture,
    ( r2_orders_2(esk3_0,esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk5_0,X1),X2),X1)
    | r1_tarski(k3_orders_2(esk3_0,esk5_0,X1),X2)
    | ~ m1_subset_1(k3_orders_2(esk3_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_34])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,k3_orders_2(esk3_0,esk6_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_66])).

cnf(c_0_72,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_73,plain,
    ( v2_struct_0(X1)
    | r1_tarski(k3_orders_2(X1,X2,X3),X2)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_34]),c_0_35])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(k3_orders_2(esk3_0,esk5_0,X1),k3_orders_2(esk3_0,k3_orders_2(esk3_0,esk5_0,X1),X1))
    | ~ m1_subset_1(k3_orders_2(esk3_0,k3_orders_2(esk3_0,esk5_0,X1),X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(k3_orders_2(esk3_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_16]),c_0_17]),c_0_18]),c_0_19])]),c_0_21])).

fof(c_0_75,plain,(
    ! [X18,X19] :
      ( ( ~ m1_subset_1(X18,k1_zfmisc_1(X19))
        | r1_tarski(X18,X19) )
      & ( ~ r1_tarski(X18,X19)
        | m1_subset_1(X18,k1_zfmisc_1(X19)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk5_0,esk4_0),X1),X2)
    | r1_tarski(k3_orders_2(esk3_0,esk5_0,esk4_0),X1)
    | ~ m1_orders_2(X2,esk3_0,esk6_0)
    | ~ m1_subset_1(k3_orders_2(esk3_0,esk5_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(esk4_0,X2) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_44]),c_0_20]),c_0_37]),c_0_51])]),c_0_34])).

cnf(c_0_77,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r1_tarski(X3,k3_orders_2(X2,k3_orders_2(X1,X4,X5),X6))
    | ~ r2_orders_2(X2,esk2_3(X7,X3,k3_orders_2(X2,k3_orders_2(X1,X4,X5),X6)),X6)
    | ~ r2_orders_2(X1,esk2_3(X7,X3,k3_orders_2(X2,k3_orders_2(X1,X4,X5),X6)),X5)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X2)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X2)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X2)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(esk2_3(X7,X3,k3_orders_2(X2,k3_orders_2(X1,X4,X5),X6)),u1_struct_0(X2))
    | ~ m1_subset_1(esk2_3(X7,X3,k3_orders_2(X2,k3_orders_2(X1,X4,X5),X6)),u1_struct_0(X1))
    | ~ m1_subset_1(k3_orders_2(X2,k3_orders_2(X1,X4,X5),X6),k1_zfmisc_1(X7))
    | ~ m1_subset_1(k3_orders_2(X1,X4,X5),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X7))
    | ~ m1_subset_1(X6,u1_struct_0(X2))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ r2_hidden(esk2_3(X7,X3,k3_orders_2(X2,k3_orders_2(X1,X4,X5),X6)),X4) ),
    inference(spm,[status(thm)],[c_0_43,c_0_39])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk2_3(X1,k3_orders_2(esk3_0,esk6_0,esk4_0),X2),esk5_0)
    | r1_tarski(k3_orders_2(esk3_0,esk6_0,esk4_0),X2)
    | ~ m1_subset_1(k3_orders_2(esk3_0,esk6_0,esk4_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_29])).

cnf(c_0_79,plain,
    ( k3_orders_2(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_tarski(X2,k3_orders_2(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(k3_orders_2(esk3_0,esk5_0,X1),k3_orders_2(esk3_0,k3_orders_2(esk3_0,esk5_0,X1),X1))
    | ~ m1_subset_1(k3_orders_2(esk3_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_35]),c_0_16]),c_0_17]),c_0_18]),c_0_19])]),c_0_21])).

cnf(c_0_81,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk5_0,esk4_0),X1),esk5_0)
    | r1_tarski(k3_orders_2(esk3_0,esk5_0,esk4_0),X1)
    | ~ m1_subset_1(k3_orders_2(esk3_0,esk5_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_15]),c_0_59])])).

cnf(c_0_83,negated_conjecture,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r1_tarski(k3_orders_2(esk3_0,esk6_0,esk4_0),k3_orders_2(X1,k3_orders_2(X2,esk5_0,X3),X4))
    | ~ r2_orders_2(X1,esk2_3(X5,k3_orders_2(esk3_0,esk6_0,esk4_0),k3_orders_2(X1,k3_orders_2(X2,esk5_0,X3),X4)),X4)
    | ~ r2_orders_2(X2,esk2_3(X5,k3_orders_2(esk3_0,esk6_0,esk4_0),k3_orders_2(X1,k3_orders_2(X2,esk5_0,X3),X4)),X3)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(X1)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X1)
    | ~ v3_orders_2(X2)
    | ~ m1_subset_1(esk2_3(X5,k3_orders_2(esk3_0,esk6_0,esk4_0),k3_orders_2(X1,k3_orders_2(X2,esk5_0,X3),X4)),u1_struct_0(X1))
    | ~ m1_subset_1(esk2_3(X5,k3_orders_2(esk3_0,esk6_0,esk4_0),k3_orders_2(X1,k3_orders_2(X2,esk5_0,X3),X4)),u1_struct_0(X2))
    | ~ m1_subset_1(k3_orders_2(X1,k3_orders_2(X2,esk5_0,X3),X4),k1_zfmisc_1(X5))
    | ~ m1_subset_1(k3_orders_2(X2,esk5_0,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k3_orders_2(esk3_0,esk6_0,esk4_0),k1_zfmisc_1(X5))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_84,negated_conjecture,
    ( k3_orders_2(esk3_0,k3_orders_2(esk3_0,esk5_0,X1),X1) = k3_orders_2(esk3_0,esk5_0,X1)
    | ~ m1_subset_1(k3_orders_2(esk3_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_16]),c_0_17]),c_0_18]),c_0_19])]),c_0_21])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(esk5_0,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_37])).

cnf(c_0_86,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(k3_orders_2(esk3_0,esk5_0,esk4_0),esk5_0)
    | ~ m1_subset_1(k3_orders_2(esk3_0,esk5_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_82]),c_0_37])])).

cnf(c_0_88,negated_conjecture,
    ( r1_tarski(k3_orders_2(esk3_0,esk6_0,esk4_0),k3_orders_2(esk3_0,esk5_0,X1))
    | ~ r2_orders_2(esk3_0,esk2_3(X2,k3_orders_2(esk3_0,esk6_0,esk4_0),k3_orders_2(esk3_0,esk5_0,X1)),X1)
    | ~ m1_subset_1(esk2_3(X2,k3_orders_2(esk3_0,esk6_0,esk4_0),k3_orders_2(esk3_0,esk5_0,X1)),u1_struct_0(esk3_0))
    | ~ m1_subset_1(k3_orders_2(esk3_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(k3_orders_2(esk3_0,esk6_0,esk4_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(k3_orders_2(esk3_0,esk5_0,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_37])]),c_0_21])).

cnf(c_0_89,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_85])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(esk1_2(k3_orders_2(esk3_0,esk6_0,esk4_0),X1),esk5_0)
    | r1_tarski(k3_orders_2(esk3_0,esk6_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_86])).

cnf(c_0_91,negated_conjecture,
    ( r1_tarski(k3_orders_2(esk3_0,esk5_0,esk4_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_35]),c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_37]),c_0_51])]),c_0_21])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(k3_orders_2(esk3_0,esk6_0,esk4_0),k3_orders_2(esk3_0,esk5_0,X1))
    | ~ r2_orders_2(esk3_0,esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk6_0,esk4_0),k3_orders_2(esk3_0,esk5_0,X1)),X1)
    | ~ m1_subset_1(k3_orders_2(esk3_0,esk6_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(k3_orders_2(esk3_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_34])).

cnf(c_0_93,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_94,negated_conjecture,
    ( r2_hidden(esk1_2(k3_orders_2(esk3_0,esk6_0,esk4_0),X1),u1_struct_0(esk3_0))
    | r1_tarski(k3_orders_2(esk3_0,esk6_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,k3_orders_2(esk3_0,esk5_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_91])).

cnf(c_0_96,negated_conjecture,
    ( r1_tarski(k3_orders_2(esk3_0,esk6_0,esk4_0),k3_orders_2(esk3_0,esk5_0,esk4_0))
    | ~ m1_subset_1(k3_orders_2(esk3_0,esk6_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(k3_orders_2(esk3_0,esk5_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_53]),c_0_51]),c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_97,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_98,negated_conjecture,
    ( r1_tarski(k3_orders_2(esk3_0,esk6_0,esk4_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_99,negated_conjecture,
    ( r2_hidden(esk1_2(k3_orders_2(esk3_0,esk5_0,esk4_0),X1),esk5_0)
    | r1_tarski(k3_orders_2(esk3_0,esk5_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_95,c_0_86])).

cnf(c_0_100,negated_conjecture,
    ( k3_orders_2(esk3_0,esk6_0,X1) = k3_orders_2(esk3_0,esk5_0,X1)
    | ~ m1_subset_1(k3_orders_2(esk3_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r1_tarski(k3_orders_2(esk3_0,esk6_0,X1),k3_orders_2(esk3_0,esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_57])).

cnf(c_0_101,negated_conjecture,
    ( r1_tarski(k3_orders_2(esk3_0,esk6_0,esk4_0),k3_orders_2(esk3_0,esk5_0,esk4_0))
    | ~ m1_subset_1(k3_orders_2(esk3_0,esk5_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_98])])).

cnf(c_0_102,negated_conjecture,
    ( k3_orders_2(esk3_0,esk5_0,esk4_0) != k3_orders_2(esk3_0,esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_103,negated_conjecture,
    ( r2_hidden(esk1_2(k3_orders_2(esk3_0,esk5_0,esk4_0),X1),u1_struct_0(esk3_0))
    | r1_tarski(k3_orders_2(esk3_0,esk5_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_89,c_0_99])).

cnf(c_0_104,negated_conjecture,
    ( ~ m1_subset_1(k3_orders_2(esk3_0,esk5_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_51])]),c_0_102])).

cnf(c_0_105,negated_conjecture,
    ( r1_tarski(k3_orders_2(esk3_0,esk5_0,esk4_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_103])).

cnf(c_0_106,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_97]),c_0_105])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:08:29 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 1.43/1.65  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 1.43/1.65  # and selection function SelectMaxLComplexAvoidPosPred.
% 1.43/1.65  #
% 1.43/1.65  # Preprocessing time       : 0.029 s
% 1.43/1.65  # Presaturation interreduction done
% 1.43/1.65  
% 1.43/1.65  # Proof found!
% 1.43/1.65  # SZS status Theorem
% 1.43/1.65  # SZS output start CNFRefutation
% 1.43/1.65  fof(t71_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,X3)&m1_orders_2(X3,X1,X4))=>k3_orders_2(X1,X3,X2)=k3_orders_2(X1,X4,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_orders_2)).
% 1.43/1.65  fof(t67_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_orders_2(X3,X1,X2)=>r1_tarski(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_orders_2)).
% 1.43/1.65  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.43/1.65  fof(t7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,X2)=>r2_hidden(X4,X3)))=>r1_tarski(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_subset_1)).
% 1.43/1.65  fof(t57_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,k3_orders_2(X1,X4,X3))<=>(r2_orders_2(X1,X2,X3)&r2_hidden(X2,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 1.43/1.65  fof(dt_k3_orders_2, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 1.43/1.65  fof(t70_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))=>((((r2_orders_2(X1,X2,X3)&r2_hidden(X2,X4))&r2_hidden(X3,X5))&m1_orders_2(X5,X1,X4))=>r2_hidden(X2,X5))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_orders_2)).
% 1.43/1.65  fof(dt_m1_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_orders_2(X3,X1,X2)=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_orders_2)).
% 1.43/1.65  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.43/1.65  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.43/1.65  fof(c_0_10, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,X3)&m1_orders_2(X3,X1,X4))=>k3_orders_2(X1,X3,X2)=k3_orders_2(X1,X4,X2))))))), inference(assume_negation,[status(cth)],[t71_orders_2])).
% 1.43/1.65  fof(c_0_11, plain, ![X30, X31, X32]:(v2_struct_0(X30)|~v3_orders_2(X30)|~v4_orders_2(X30)|~v5_orders_2(X30)|~l1_orders_2(X30)|(~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|(~m1_orders_2(X32,X30,X31)|r1_tarski(X32,X31)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t67_orders_2])])])])).
% 1.43/1.65  fof(c_0_12, negated_conjecture, (((((~v2_struct_0(esk3_0)&v3_orders_2(esk3_0))&v4_orders_2(esk3_0))&v5_orders_2(esk3_0))&l1_orders_2(esk3_0))&(m1_subset_1(esk4_0,u1_struct_0(esk3_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&((r2_hidden(esk4_0,esk5_0)&m1_orders_2(esk5_0,esk3_0,esk6_0))&k3_orders_2(esk3_0,esk5_0,esk4_0)!=k3_orders_2(esk3_0,esk6_0,esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 1.43/1.65  fof(c_0_13, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 1.43/1.65  cnf(c_0_14, plain, (v2_struct_0(X1)|r1_tarski(X3,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_orders_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.43/1.65  cnf(c_0_15, negated_conjecture, (m1_orders_2(esk5_0,esk3_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.43/1.65  cnf(c_0_16, negated_conjecture, (l1_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.43/1.65  cnf(c_0_17, negated_conjecture, (v5_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.43/1.65  cnf(c_0_18, negated_conjecture, (v4_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.43/1.65  cnf(c_0_19, negated_conjecture, (v3_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.43/1.65  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.43/1.65  cnf(c_0_21, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.43/1.65  fof(c_0_22, plain, ![X14, X15, X16]:((m1_subset_1(esk2_3(X14,X15,X16),X14)|r1_tarski(X15,X16)|~m1_subset_1(X16,k1_zfmisc_1(X14))|~m1_subset_1(X15,k1_zfmisc_1(X14)))&((r2_hidden(esk2_3(X14,X15,X16),X15)|r1_tarski(X15,X16)|~m1_subset_1(X16,k1_zfmisc_1(X14))|~m1_subset_1(X15,k1_zfmisc_1(X14)))&(~r2_hidden(esk2_3(X14,X15,X16),X16)|r1_tarski(X15,X16)|~m1_subset_1(X16,k1_zfmisc_1(X14))|~m1_subset_1(X15,k1_zfmisc_1(X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).
% 1.43/1.65  cnf(c_0_23, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.43/1.65  cnf(c_0_24, negated_conjecture, (r1_tarski(esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21])).
% 1.43/1.65  fof(c_0_25, plain, ![X26, X27, X28, X29]:(((r2_orders_2(X26,X27,X28)|~r2_hidden(X27,k3_orders_2(X26,X29,X28))|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X26)))|~m1_subset_1(X28,u1_struct_0(X26))|~m1_subset_1(X27,u1_struct_0(X26))|(v2_struct_0(X26)|~v3_orders_2(X26)|~v4_orders_2(X26)|~v5_orders_2(X26)|~l1_orders_2(X26)))&(r2_hidden(X27,X29)|~r2_hidden(X27,k3_orders_2(X26,X29,X28))|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X26)))|~m1_subset_1(X28,u1_struct_0(X26))|~m1_subset_1(X27,u1_struct_0(X26))|(v2_struct_0(X26)|~v3_orders_2(X26)|~v4_orders_2(X26)|~v5_orders_2(X26)|~l1_orders_2(X26))))&(~r2_orders_2(X26,X27,X28)|~r2_hidden(X27,X29)|r2_hidden(X27,k3_orders_2(X26,X29,X28))|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X26)))|~m1_subset_1(X28,u1_struct_0(X26))|~m1_subset_1(X27,u1_struct_0(X26))|(v2_struct_0(X26)|~v3_orders_2(X26)|~v4_orders_2(X26)|~v5_orders_2(X26)|~l1_orders_2(X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_orders_2])])])])])).
% 1.43/1.65  cnf(c_0_26, plain, (r1_tarski(X2,X3)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.43/1.65  cnf(c_0_27, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 1.43/1.65  cnf(c_0_28, plain, (r2_hidden(X1,X2)|v2_struct_0(X3)|~r2_hidden(X1,k3_orders_2(X3,X2,X4))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X4,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~v3_orders_2(X3)|~v4_orders_2(X3)|~v5_orders_2(X3)|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.43/1.65  cnf(c_0_29, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r1_tarski(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.43/1.65  cnf(c_0_30, negated_conjecture, (r1_tarski(X1,esk6_0)|~m1_subset_1(esk6_0,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(esk2_3(X2,X1,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 1.43/1.65  cnf(c_0_31, plain, (v2_struct_0(X1)|r2_hidden(esk2_3(X2,k3_orders_2(X1,X3,X4),X5),X3)|r1_tarski(k3_orders_2(X1,X3,X4),X5)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(esk2_3(X2,k3_orders_2(X1,X3,X4),X5),u1_struct_0(X1))|~m1_subset_1(k3_orders_2(X1,X3,X4),k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X5,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 1.43/1.65  fof(c_0_32, plain, ![X20, X21, X22]:(v2_struct_0(X20)|~v3_orders_2(X20)|~v4_orders_2(X20)|~v5_orders_2(X20)|~l1_orders_2(X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|~m1_subset_1(X22,u1_struct_0(X20))|m1_subset_1(k3_orders_2(X20,X21,X22),k1_zfmisc_1(u1_struct_0(X20)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_orders_2])])])).
% 1.43/1.65  cnf(c_0_33, negated_conjecture, (v2_struct_0(X1)|r1_tarski(k3_orders_2(X1,esk5_0,X2),esk6_0)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(esk2_3(X3,k3_orders_2(X1,esk5_0,X2),esk6_0),u1_struct_0(X1))|~m1_subset_1(k3_orders_2(X1,esk5_0,X2),k1_zfmisc_1(X3))|~m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(esk6_0,k1_zfmisc_1(X3))|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 1.43/1.65  cnf(c_0_34, plain, (m1_subset_1(esk2_3(X1,X2,X3),X1)|r1_tarski(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.43/1.65  cnf(c_0_35, plain, (v2_struct_0(X1)|m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.43/1.65  cnf(c_0_36, negated_conjecture, (v2_struct_0(X1)|r1_tarski(k3_orders_2(X1,esk5_0,X2),esk6_0)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 1.43/1.65  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.43/1.65  cnf(c_0_38, negated_conjecture, (r1_tarski(k3_orders_2(esk3_0,esk5_0,X1),esk6_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_20]), c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_37])]), c_0_21])).
% 1.43/1.65  cnf(c_0_39, plain, (r2_hidden(X2,k3_orders_2(X1,X4,X3))|v2_struct_0(X1)|~r2_orders_2(X1,X2,X3)|~r2_hidden(X2,X4)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.43/1.65  cnf(c_0_40, negated_conjecture, (r2_hidden(X1,esk6_0)|~m1_subset_1(X2,u1_struct_0(esk3_0))|~r2_hidden(X1,k3_orders_2(esk3_0,esk5_0,X2))), inference(spm,[status(thm)],[c_0_23, c_0_38])).
% 1.43/1.65  fof(c_0_41, plain, ![X33, X34, X35, X36, X37]:(v2_struct_0(X33)|~v3_orders_2(X33)|~v4_orders_2(X33)|~v5_orders_2(X33)|~l1_orders_2(X33)|(~m1_subset_1(X34,u1_struct_0(X33))|(~m1_subset_1(X35,u1_struct_0(X33))|(~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X33)))|(~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X33)))|(~r2_orders_2(X33,X34,X35)|~r2_hidden(X34,X36)|~r2_hidden(X35,X37)|~m1_orders_2(X37,X33,X36)|r2_hidden(X34,X37))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_orders_2])])])])).
% 1.43/1.65  fof(c_0_42, plain, ![X23, X24, X25]:(v2_struct_0(X23)|~v3_orders_2(X23)|~v4_orders_2(X23)|~v5_orders_2(X23)|~l1_orders_2(X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|(~m1_orders_2(X25,X23,X24)|m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_orders_2])])])])).
% 1.43/1.65  cnf(c_0_43, plain, (v2_struct_0(X1)|r1_tarski(X2,k3_orders_2(X1,X3,X4))|~r2_orders_2(X1,esk2_3(X5,X2,k3_orders_2(X1,X3,X4)),X4)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(esk2_3(X5,X2,k3_orders_2(X1,X3,X4)),u1_struct_0(X1))|~m1_subset_1(k3_orders_2(X1,X3,X4),k1_zfmisc_1(X5))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(X5))|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(esk2_3(X5,X2,k3_orders_2(X1,X3,X4)),X3)), inference(spm,[status(thm)],[c_0_26, c_0_39])).
% 1.43/1.65  cnf(c_0_44, negated_conjecture, (r2_hidden(esk2_3(X1,k3_orders_2(esk3_0,esk5_0,X2),X3),esk6_0)|r1_tarski(k3_orders_2(esk3_0,esk5_0,X2),X3)|~m1_subset_1(k3_orders_2(esk3_0,esk5_0,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,u1_struct_0(esk3_0))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_40, c_0_29])).
% 1.43/1.65  cnf(c_0_45, plain, (r2_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r2_hidden(X2,k3_orders_2(X1,X4,X3))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.43/1.65  cnf(c_0_46, plain, (v2_struct_0(X1)|r2_hidden(X2,X5)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))|~r2_orders_2(X1,X2,X3)|~r2_hidden(X2,X4)|~r2_hidden(X3,X5)|~m1_orders_2(X5,X1,X4)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.43/1.65  cnf(c_0_47, plain, (v2_struct_0(X1)|m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_orders_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 1.43/1.65  cnf(c_0_48, negated_conjecture, (v2_struct_0(X1)|r1_tarski(k3_orders_2(esk3_0,esk5_0,X2),k3_orders_2(X1,esk6_0,X3))|~r2_orders_2(X1,esk2_3(X4,k3_orders_2(esk3_0,esk5_0,X2),k3_orders_2(X1,esk6_0,X3)),X3)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(esk2_3(X4,k3_orders_2(esk3_0,esk5_0,X2),k3_orders_2(X1,esk6_0,X3)),u1_struct_0(X1))|~m1_subset_1(k3_orders_2(esk3_0,esk5_0,X2),k1_zfmisc_1(X4))|~m1_subset_1(k3_orders_2(X1,esk6_0,X3),k1_zfmisc_1(X4))|~m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(esk3_0))|~m1_subset_1(X3,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 1.43/1.65  cnf(c_0_49, plain, (r2_orders_2(X1,esk2_3(X2,k3_orders_2(X1,X3,X4),X5),X4)|v2_struct_0(X1)|r1_tarski(k3_orders_2(X1,X3,X4),X5)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(esk2_3(X2,k3_orders_2(X1,X3,X4),X5),u1_struct_0(X1))|~m1_subset_1(k3_orders_2(X1,X3,X4),k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X5,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_45, c_0_29])).
% 1.43/1.65  cnf(c_0_50, plain, (v2_struct_0(X1)|r2_hidden(X2,X3)|~r2_orders_2(X1,X2,X4)|~m1_orders_2(X3,X1,X5)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~r2_hidden(X4,X3)|~r2_hidden(X2,X5)), inference(csr,[status(thm)],[c_0_46, c_0_47])).
% 1.43/1.65  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.43/1.65  cnf(c_0_52, negated_conjecture, (v2_struct_0(X1)|r1_tarski(k3_orders_2(esk3_0,esk5_0,X2),k3_orders_2(X1,esk6_0,X3))|~r2_orders_2(X1,esk2_3(u1_struct_0(X1),k3_orders_2(esk3_0,esk5_0,X2),k3_orders_2(X1,esk6_0,X3)),X3)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(k3_orders_2(esk3_0,esk5_0,X2),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(esk3_0))|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_34]), c_0_35])).
% 1.43/1.65  cnf(c_0_53, plain, (r2_orders_2(X1,esk2_3(u1_struct_0(X1),k3_orders_2(X1,X2,X3),X4),X3)|v2_struct_0(X1)|r1_tarski(k3_orders_2(X1,X2,X3),X4)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_34]), c_0_35])).
% 1.43/1.65  cnf(c_0_54, negated_conjecture, (r2_hidden(X1,X2)|~r2_orders_2(esk3_0,X1,esk4_0)|~m1_orders_2(X2,esk3_0,X3)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(esk4_0,X2)|~r2_hidden(X1,X3)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_16]), c_0_17]), c_0_18]), c_0_19])]), c_0_21])).
% 1.43/1.65  cnf(c_0_55, negated_conjecture, (r1_tarski(k3_orders_2(esk3_0,esk5_0,X1),k3_orders_2(esk3_0,esk6_0,X1))|~m1_subset_1(k3_orders_2(esk3_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(k3_orders_2(esk3_0,esk6_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_37])]), c_0_21])).
% 1.43/1.65  cnf(c_0_56, negated_conjecture, (r2_hidden(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,X1,esk4_0),X2),X3)|r1_tarski(k3_orders_2(esk3_0,X1,esk4_0),X2)|~m1_orders_2(X3,esk3_0,X4)|~m1_subset_1(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,X1,esk4_0),X2),u1_struct_0(esk3_0))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,X1,esk4_0),X2),X4)|~r2_hidden(esk4_0,X3)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_53]), c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_51])]), c_0_21])).
% 1.43/1.65  cnf(c_0_57, negated_conjecture, (r1_tarski(k3_orders_2(esk3_0,esk5_0,X1),k3_orders_2(esk3_0,esk6_0,X1))|~m1_subset_1(k3_orders_2(esk3_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_35]), c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21])).
% 1.43/1.65  cnf(c_0_58, negated_conjecture, (r2_hidden(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,X1,esk4_0),X2),X3)|r1_tarski(k3_orders_2(esk3_0,X1,esk4_0),X2)|~m1_orders_2(X3,esk3_0,X1)|~m1_subset_1(k3_orders_2(esk3_0,X1,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(esk4_0,X3)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_31]), c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_51])]), c_0_21]), c_0_34])).
% 1.43/1.65  cnf(c_0_59, negated_conjecture, (r2_hidden(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.43/1.65  cnf(c_0_60, negated_conjecture, (r2_hidden(X1,k3_orders_2(esk3_0,esk6_0,X2))|~m1_subset_1(k3_orders_2(esk3_0,esk5_0,X2),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X2,u1_struct_0(esk3_0))|~r2_hidden(X1,k3_orders_2(esk3_0,esk5_0,X2))), inference(spm,[status(thm)],[c_0_23, c_0_57])).
% 1.43/1.65  cnf(c_0_61, negated_conjecture, (r2_hidden(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk6_0,esk4_0),X1),esk5_0)|r1_tarski(k3_orders_2(esk3_0,esk6_0,esk4_0),X1)|~m1_subset_1(k3_orders_2(esk3_0,esk6_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_15]), c_0_20]), c_0_59])])).
% 1.43/1.65  cnf(c_0_62, negated_conjecture, (r2_orders_2(esk3_0,X1,X2)|~m1_subset_1(k3_orders_2(esk3_0,esk5_0,X2),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X2,u1_struct_0(esk3_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,k3_orders_2(esk3_0,esk5_0,X2))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_60]), c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21])).
% 1.43/1.65  cnf(c_0_63, negated_conjecture, (r1_tarski(k3_orders_2(esk3_0,esk6_0,esk4_0),esk5_0)|~m1_subset_1(k3_orders_2(esk3_0,esk6_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_61]), c_0_37])])).
% 1.43/1.65  cnf(c_0_64, plain, (v2_struct_0(X1)|r1_tarski(X2,k3_orders_2(X1,X2,X3))|~r2_orders_2(X1,esk2_3(X4,X2,k3_orders_2(X1,X2,X3)),X3)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(esk2_3(X4,X2,k3_orders_2(X1,X2,X3)),u1_struct_0(X1))|~m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(X4))|~m1_subset_1(X3,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_43, c_0_29])).
% 1.43/1.65  cnf(c_0_65, negated_conjecture, (r2_orders_2(esk3_0,esk2_3(X1,k3_orders_2(esk3_0,esk5_0,X2),X3),X2)|r1_tarski(k3_orders_2(esk3_0,esk5_0,X2),X3)|~m1_subset_1(esk2_3(X1,k3_orders_2(esk3_0,esk5_0,X2),X3),u1_struct_0(esk3_0))|~m1_subset_1(k3_orders_2(esk3_0,esk5_0,X2),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(k3_orders_2(esk3_0,esk5_0,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,u1_struct_0(esk3_0))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_62, c_0_29])).
% 1.43/1.65  cnf(c_0_66, negated_conjecture, (r1_tarski(k3_orders_2(esk3_0,esk6_0,esk4_0),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_35]), c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_51])]), c_0_21])).
% 1.43/1.65  fof(c_0_67, plain, ![X12, X13]:(((r1_tarski(X12,X13)|X12!=X13)&(r1_tarski(X13,X12)|X12!=X13))&(~r1_tarski(X12,X13)|~r1_tarski(X13,X12)|X12=X13)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.43/1.65  cnf(c_0_68, plain, (v2_struct_0(X1)|r1_tarski(k3_orders_2(X1,X2,X3),X2)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(esk2_3(X4,k3_orders_2(X1,X2,X3),X2),u1_struct_0(X1))|~m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(X4))|~m1_subset_1(X3,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_26, c_0_31])).
% 1.43/1.65  cnf(c_0_69, plain, (v2_struct_0(X1)|r1_tarski(X2,k3_orders_2(X1,X2,X3))|~r2_orders_2(X1,esk2_3(u1_struct_0(X1),X2,k3_orders_2(X1,X2,X3)),X3)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_34]), c_0_35])).
% 1.43/1.65  cnf(c_0_70, negated_conjecture, (r2_orders_2(esk3_0,esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk5_0,X1),X2),X1)|r1_tarski(k3_orders_2(esk3_0,esk5_0,X1),X2)|~m1_subset_1(k3_orders_2(esk3_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_65, c_0_34])).
% 1.43/1.65  cnf(c_0_71, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,k3_orders_2(esk3_0,esk6_0,esk4_0))), inference(spm,[status(thm)],[c_0_23, c_0_66])).
% 1.43/1.65  cnf(c_0_72, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 1.43/1.65  cnf(c_0_73, plain, (v2_struct_0(X1)|r1_tarski(k3_orders_2(X1,X2,X3),X2)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_34]), c_0_35])).
% 1.43/1.65  cnf(c_0_74, negated_conjecture, (r1_tarski(k3_orders_2(esk3_0,esk5_0,X1),k3_orders_2(esk3_0,k3_orders_2(esk3_0,esk5_0,X1),X1))|~m1_subset_1(k3_orders_2(esk3_0,k3_orders_2(esk3_0,esk5_0,X1),X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(k3_orders_2(esk3_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_16]), c_0_17]), c_0_18]), c_0_19])]), c_0_21])).
% 1.43/1.65  fof(c_0_75, plain, ![X18, X19]:((~m1_subset_1(X18,k1_zfmisc_1(X19))|r1_tarski(X18,X19))&(~r1_tarski(X18,X19)|m1_subset_1(X18,k1_zfmisc_1(X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 1.43/1.65  cnf(c_0_76, negated_conjecture, (r2_hidden(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk5_0,esk4_0),X1),X2)|r1_tarski(k3_orders_2(esk3_0,esk5_0,esk4_0),X1)|~m1_orders_2(X2,esk3_0,esk6_0)|~m1_subset_1(k3_orders_2(esk3_0,esk5_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(esk4_0,X2)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_44]), c_0_20]), c_0_37]), c_0_51])]), c_0_34])).
% 1.43/1.65  cnf(c_0_77, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r1_tarski(X3,k3_orders_2(X2,k3_orders_2(X1,X4,X5),X6))|~r2_orders_2(X2,esk2_3(X7,X3,k3_orders_2(X2,k3_orders_2(X1,X4,X5),X6)),X6)|~r2_orders_2(X1,esk2_3(X7,X3,k3_orders_2(X2,k3_orders_2(X1,X4,X5),X6)),X5)|~l1_orders_2(X2)|~l1_orders_2(X1)|~v5_orders_2(X2)|~v5_orders_2(X1)|~v4_orders_2(X2)|~v4_orders_2(X1)|~v3_orders_2(X2)|~v3_orders_2(X1)|~m1_subset_1(esk2_3(X7,X3,k3_orders_2(X2,k3_orders_2(X1,X4,X5),X6)),u1_struct_0(X2))|~m1_subset_1(esk2_3(X7,X3,k3_orders_2(X2,k3_orders_2(X1,X4,X5),X6)),u1_struct_0(X1))|~m1_subset_1(k3_orders_2(X2,k3_orders_2(X1,X4,X5),X6),k1_zfmisc_1(X7))|~m1_subset_1(k3_orders_2(X1,X4,X5),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(X7))|~m1_subset_1(X6,u1_struct_0(X2))|~m1_subset_1(X5,u1_struct_0(X1))|~r2_hidden(esk2_3(X7,X3,k3_orders_2(X2,k3_orders_2(X1,X4,X5),X6)),X4)), inference(spm,[status(thm)],[c_0_43, c_0_39])).
% 1.43/1.65  cnf(c_0_78, negated_conjecture, (r2_hidden(esk2_3(X1,k3_orders_2(esk3_0,esk6_0,esk4_0),X2),esk5_0)|r1_tarski(k3_orders_2(esk3_0,esk6_0,esk4_0),X2)|~m1_subset_1(k3_orders_2(esk3_0,esk6_0,esk4_0),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_71, c_0_29])).
% 1.43/1.65  cnf(c_0_79, plain, (k3_orders_2(X1,X2,X3)=X2|v2_struct_0(X1)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~r1_tarski(X2,k3_orders_2(X1,X2,X3))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 1.43/1.65  cnf(c_0_80, negated_conjecture, (r1_tarski(k3_orders_2(esk3_0,esk5_0,X1),k3_orders_2(esk3_0,k3_orders_2(esk3_0,esk5_0,X1),X1))|~m1_subset_1(k3_orders_2(esk3_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_35]), c_0_16]), c_0_17]), c_0_18]), c_0_19])]), c_0_21])).
% 1.43/1.65  cnf(c_0_81, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 1.43/1.65  cnf(c_0_82, negated_conjecture, (r2_hidden(esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk5_0,esk4_0),X1),esk5_0)|r1_tarski(k3_orders_2(esk3_0,esk5_0,esk4_0),X1)|~m1_subset_1(k3_orders_2(esk3_0,esk5_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_15]), c_0_59])])).
% 1.43/1.65  cnf(c_0_83, negated_conjecture, (v2_struct_0(X1)|v2_struct_0(X2)|r1_tarski(k3_orders_2(esk3_0,esk6_0,esk4_0),k3_orders_2(X1,k3_orders_2(X2,esk5_0,X3),X4))|~r2_orders_2(X1,esk2_3(X5,k3_orders_2(esk3_0,esk6_0,esk4_0),k3_orders_2(X1,k3_orders_2(X2,esk5_0,X3),X4)),X4)|~r2_orders_2(X2,esk2_3(X5,k3_orders_2(esk3_0,esk6_0,esk4_0),k3_orders_2(X1,k3_orders_2(X2,esk5_0,X3),X4)),X3)|~l1_orders_2(X1)|~l1_orders_2(X2)|~v5_orders_2(X1)|~v5_orders_2(X2)|~v4_orders_2(X1)|~v4_orders_2(X2)|~v3_orders_2(X1)|~v3_orders_2(X2)|~m1_subset_1(esk2_3(X5,k3_orders_2(esk3_0,esk6_0,esk4_0),k3_orders_2(X1,k3_orders_2(X2,esk5_0,X3),X4)),u1_struct_0(X1))|~m1_subset_1(esk2_3(X5,k3_orders_2(esk3_0,esk6_0,esk4_0),k3_orders_2(X1,k3_orders_2(X2,esk5_0,X3),X4)),u1_struct_0(X2))|~m1_subset_1(k3_orders_2(X1,k3_orders_2(X2,esk5_0,X3),X4),k1_zfmisc_1(X5))|~m1_subset_1(k3_orders_2(X2,esk5_0,X3),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k3_orders_2(esk3_0,esk6_0,esk4_0),k1_zfmisc_1(X5))|~m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 1.43/1.65  cnf(c_0_84, negated_conjecture, (k3_orders_2(esk3_0,k3_orders_2(esk3_0,esk5_0,X1),X1)=k3_orders_2(esk3_0,esk5_0,X1)|~m1_subset_1(k3_orders_2(esk3_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_16]), c_0_17]), c_0_18]), c_0_19])]), c_0_21])).
% 1.43/1.65  cnf(c_0_85, negated_conjecture, (r1_tarski(esk5_0,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_81, c_0_37])).
% 1.43/1.65  cnf(c_0_86, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.43/1.65  cnf(c_0_87, negated_conjecture, (r1_tarski(k3_orders_2(esk3_0,esk5_0,esk4_0),esk5_0)|~m1_subset_1(k3_orders_2(esk3_0,esk5_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_82]), c_0_37])])).
% 1.43/1.65  cnf(c_0_88, negated_conjecture, (r1_tarski(k3_orders_2(esk3_0,esk6_0,esk4_0),k3_orders_2(esk3_0,esk5_0,X1))|~r2_orders_2(esk3_0,esk2_3(X2,k3_orders_2(esk3_0,esk6_0,esk4_0),k3_orders_2(esk3_0,esk5_0,X1)),X1)|~m1_subset_1(esk2_3(X2,k3_orders_2(esk3_0,esk6_0,esk4_0),k3_orders_2(esk3_0,esk5_0,X1)),u1_struct_0(esk3_0))|~m1_subset_1(k3_orders_2(esk3_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(k3_orders_2(esk3_0,esk6_0,esk4_0),k1_zfmisc_1(X2))|~m1_subset_1(k3_orders_2(esk3_0,esk5_0,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_37])]), c_0_21])).
% 1.43/1.65  cnf(c_0_89, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_23, c_0_85])).
% 1.43/1.65  cnf(c_0_90, negated_conjecture, (r2_hidden(esk1_2(k3_orders_2(esk3_0,esk6_0,esk4_0),X1),esk5_0)|r1_tarski(k3_orders_2(esk3_0,esk6_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_71, c_0_86])).
% 1.43/1.65  cnf(c_0_91, negated_conjecture, (r1_tarski(k3_orders_2(esk3_0,esk5_0,esk4_0),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_35]), c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_37]), c_0_51])]), c_0_21])).
% 1.43/1.65  cnf(c_0_92, negated_conjecture, (r1_tarski(k3_orders_2(esk3_0,esk6_0,esk4_0),k3_orders_2(esk3_0,esk5_0,X1))|~r2_orders_2(esk3_0,esk2_3(u1_struct_0(esk3_0),k3_orders_2(esk3_0,esk6_0,esk4_0),k3_orders_2(esk3_0,esk5_0,X1)),X1)|~m1_subset_1(k3_orders_2(esk3_0,esk6_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(k3_orders_2(esk3_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_88, c_0_34])).
% 1.43/1.65  cnf(c_0_93, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.43/1.65  cnf(c_0_94, negated_conjecture, (r2_hidden(esk1_2(k3_orders_2(esk3_0,esk6_0,esk4_0),X1),u1_struct_0(esk3_0))|r1_tarski(k3_orders_2(esk3_0,esk6_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 1.43/1.65  cnf(c_0_95, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,k3_orders_2(esk3_0,esk5_0,esk4_0))), inference(spm,[status(thm)],[c_0_23, c_0_91])).
% 1.43/1.65  cnf(c_0_96, negated_conjecture, (r1_tarski(k3_orders_2(esk3_0,esk6_0,esk4_0),k3_orders_2(esk3_0,esk5_0,esk4_0))|~m1_subset_1(k3_orders_2(esk3_0,esk6_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(k3_orders_2(esk3_0,esk5_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_53]), c_0_51]), c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21])).
% 1.43/1.65  cnf(c_0_97, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 1.43/1.65  cnf(c_0_98, negated_conjecture, (r1_tarski(k3_orders_2(esk3_0,esk6_0,esk4_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_93, c_0_94])).
% 1.43/1.65  cnf(c_0_99, negated_conjecture, (r2_hidden(esk1_2(k3_orders_2(esk3_0,esk5_0,esk4_0),X1),esk5_0)|r1_tarski(k3_orders_2(esk3_0,esk5_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_95, c_0_86])).
% 1.43/1.65  cnf(c_0_100, negated_conjecture, (k3_orders_2(esk3_0,esk6_0,X1)=k3_orders_2(esk3_0,esk5_0,X1)|~m1_subset_1(k3_orders_2(esk3_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r1_tarski(k3_orders_2(esk3_0,esk6_0,X1),k3_orders_2(esk3_0,esk5_0,X1))), inference(spm,[status(thm)],[c_0_72, c_0_57])).
% 1.43/1.65  cnf(c_0_101, negated_conjecture, (r1_tarski(k3_orders_2(esk3_0,esk6_0,esk4_0),k3_orders_2(esk3_0,esk5_0,esk4_0))|~m1_subset_1(k3_orders_2(esk3_0,esk5_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_98])])).
% 1.43/1.65  cnf(c_0_102, negated_conjecture, (k3_orders_2(esk3_0,esk5_0,esk4_0)!=k3_orders_2(esk3_0,esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.43/1.65  cnf(c_0_103, negated_conjecture, (r2_hidden(esk1_2(k3_orders_2(esk3_0,esk5_0,esk4_0),X1),u1_struct_0(esk3_0))|r1_tarski(k3_orders_2(esk3_0,esk5_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_89, c_0_99])).
% 1.43/1.65  cnf(c_0_104, negated_conjecture, (~m1_subset_1(k3_orders_2(esk3_0,esk5_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_51])]), c_0_102])).
% 1.43/1.65  cnf(c_0_105, negated_conjecture, (r1_tarski(k3_orders_2(esk3_0,esk5_0,esk4_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_93, c_0_103])).
% 1.43/1.65  cnf(c_0_106, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_97]), c_0_105])]), ['proof']).
% 1.43/1.65  # SZS output end CNFRefutation
% 1.43/1.65  # Proof object total steps             : 107
% 1.43/1.65  # Proof object clause steps            : 86
% 1.43/1.65  # Proof object formula steps           : 21
% 1.43/1.65  # Proof object conjectures             : 62
% 1.43/1.65  # Proof object clause conjectures      : 59
% 1.43/1.65  # Proof object formula conjectures     : 3
% 1.43/1.65  # Proof object initial clauses used    : 27
% 1.43/1.65  # Proof object initial formulas used   : 10
% 1.43/1.65  # Proof object generating inferences   : 58
% 1.43/1.65  # Proof object simplifying inferences  : 133
% 1.43/1.65  # Training examples: 0 positive, 0 negative
% 1.43/1.65  # Parsed axioms                        : 10
% 1.43/1.65  # Removed by relevancy pruning/SinE    : 0
% 1.43/1.65  # Initial clauses                      : 29
% 1.43/1.65  # Removed in clause preprocessing      : 0
% 1.43/1.65  # Initial clauses in saturation        : 29
% 1.43/1.65  # Processed clauses                    : 5129
% 1.43/1.65  # ...of these trivial                  : 1
% 1.43/1.65  # ...subsumed                          : 3731
% 1.43/1.65  # ...remaining for further processing  : 1397
% 1.43/1.65  # Other redundant clauses eliminated   : 2
% 1.43/1.65  # Clauses deleted for lack of memory   : 0
% 1.43/1.65  # Backward-subsumed                    : 118
% 1.43/1.65  # Backward-rewritten                   : 3
% 1.43/1.65  # Generated clauses                    : 14999
% 1.43/1.65  # ...of the previous two non-trivial   : 14689
% 1.43/1.65  # Contextual simplify-reflections      : 47
% 1.43/1.65  # Paramodulations                      : 14997
% 1.43/1.65  # Factorizations                       : 0
% 1.43/1.65  # Equation resolutions                 : 2
% 1.43/1.65  # Propositional unsat checks           : 0
% 1.43/1.65  #    Propositional check models        : 0
% 1.43/1.65  #    Propositional check unsatisfiable : 0
% 1.43/1.65  #    Propositional clauses             : 0
% 1.43/1.65  #    Propositional clauses after purity: 0
% 1.43/1.65  #    Propositional unsat core size     : 0
% 1.43/1.65  #    Propositional preprocessing time  : 0.000
% 1.43/1.65  #    Propositional encoding time       : 0.000
% 1.43/1.65  #    Propositional solver time         : 0.000
% 1.43/1.65  #    Success case prop preproc time    : 0.000
% 1.43/1.65  #    Success case prop encoding time   : 0.000
% 1.43/1.65  #    Success case prop solver time     : 0.000
% 1.43/1.65  # Current number of processed clauses  : 1246
% 1.43/1.65  #    Positive orientable unit clauses  : 20
% 1.43/1.65  #    Positive unorientable unit clauses: 0
% 1.43/1.65  #    Negative unit clauses             : 3
% 1.43/1.65  #    Non-unit-clauses                  : 1223
% 1.43/1.65  # Current number of unprocessed clauses: 9390
% 1.43/1.65  # ...number of literals in the above   : 180737
% 1.43/1.65  # Current number of archived formulas  : 0
% 1.43/1.65  # Current number of archived clauses   : 149
% 1.43/1.65  # Clause-clause subsumption calls (NU) : 1201655
% 1.43/1.65  # Rec. Clause-clause subsumption calls : 37131
% 1.43/1.65  # Non-unit clause-clause subsumptions  : 3895
% 1.43/1.65  # Unit Clause-clause subsumption calls : 489
% 1.43/1.65  # Rewrite failures with RHS unbound    : 0
% 1.43/1.65  # BW rewrite match attempts            : 10
% 1.43/1.65  # BW rewrite match successes           : 4
% 1.43/1.65  # Condensation attempts                : 0
% 1.43/1.65  # Condensation successes               : 0
% 1.43/1.65  # Termbank termtop insertions          : 1286456
% 1.43/1.65  
% 1.43/1.65  # -------------------------------------------------
% 1.43/1.65  # User time                : 1.301 s
% 1.43/1.65  # System time              : 0.019 s
% 1.43/1.65  # Total time               : 1.320 s
% 1.43/1.65  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
