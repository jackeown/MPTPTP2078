%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:01 EST 2020

% Result     : Theorem 0.48s
% Output     : CNFRefutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 966 expanded)
%              Number of clauses        :   50 ( 314 expanded)
%              Number of leaves         :    9 ( 239 expanded)
%              Depth                    :   15
%              Number of atoms          :  453 (10600 expanded)
%              Number of equality atoms :   36 ( 354 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal clause size      :   62 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t70_orders_2,conjecture,(
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

fof(d15_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( X2 != k1_xboole_0
                 => ( m1_orders_2(X3,X1,X2)
                  <=> ? [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                        & r2_hidden(X4,X2)
                        & X3 = k3_orders_2(X1,X2,X4) ) ) )
                & ( X2 = k1_xboole_0
                 => ( m1_orders_2(X3,X1,X2)
                  <=> X3 = k1_xboole_0 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_orders_2)).

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

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(t64_orders_2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_orders_2)).

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

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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
    inference(assume_negation,[status(cth)],[t70_orders_2])).

fof(c_0_10,plain,(
    ! [X19,X20,X21] :
      ( v2_struct_0(X19)
      | ~ v3_orders_2(X19)
      | ~ v4_orders_2(X19)
      | ~ v5_orders_2(X19)
      | ~ l1_orders_2(X19)
      | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
      | ~ m1_subset_1(X21,u1_struct_0(X19))
      | m1_subset_1(k3_orders_2(X19,X20,X21),k1_zfmisc_1(u1_struct_0(X19))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_orders_2])])])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v3_orders_2(esk2_0)
    & v4_orders_2(esk2_0)
    & v5_orders_2(esk2_0)
    & l1_orders_2(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk4_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & r2_orders_2(esk2_0,esk3_0,esk4_0)
    & r2_hidden(esk3_0,esk5_0)
    & r2_hidden(esk4_0,esk6_0)
    & m1_orders_2(esk6_0,esk2_0,esk5_0)
    & ~ r2_hidden(esk3_0,esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

fof(c_0_12,plain,(
    ! [X14,X15,X16,X18] :
      ( ( m1_subset_1(esk1_3(X14,X15,X16),u1_struct_0(X14))
        | ~ m1_orders_2(X16,X14,X15)
        | X15 = k1_xboole_0
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | v2_struct_0(X14)
        | ~ v3_orders_2(X14)
        | ~ v4_orders_2(X14)
        | ~ v5_orders_2(X14)
        | ~ l1_orders_2(X14) )
      & ( r2_hidden(esk1_3(X14,X15,X16),X15)
        | ~ m1_orders_2(X16,X14,X15)
        | X15 = k1_xboole_0
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | v2_struct_0(X14)
        | ~ v3_orders_2(X14)
        | ~ v4_orders_2(X14)
        | ~ v5_orders_2(X14)
        | ~ l1_orders_2(X14) )
      & ( X16 = k3_orders_2(X14,X15,esk1_3(X14,X15,X16))
        | ~ m1_orders_2(X16,X14,X15)
        | X15 = k1_xboole_0
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | v2_struct_0(X14)
        | ~ v3_orders_2(X14)
        | ~ v4_orders_2(X14)
        | ~ v5_orders_2(X14)
        | ~ l1_orders_2(X14) )
      & ( ~ m1_subset_1(X18,u1_struct_0(X14))
        | ~ r2_hidden(X18,X15)
        | X16 != k3_orders_2(X14,X15,X18)
        | m1_orders_2(X16,X14,X15)
        | X15 = k1_xboole_0
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | v2_struct_0(X14)
        | ~ v3_orders_2(X14)
        | ~ v4_orders_2(X14)
        | ~ v5_orders_2(X14)
        | ~ l1_orders_2(X14) )
      & ( ~ m1_orders_2(X16,X14,X15)
        | X16 = k1_xboole_0
        | X15 != k1_xboole_0
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | v2_struct_0(X14)
        | ~ v3_orders_2(X14)
        | ~ v4_orders_2(X14)
        | ~ v5_orders_2(X14)
        | ~ l1_orders_2(X14) )
      & ( X16 != k1_xboole_0
        | m1_orders_2(X16,X14,X15)
        | X15 != k1_xboole_0
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | v2_struct_0(X14)
        | ~ v3_orders_2(X14)
        | ~ v4_orders_2(X14)
        | ~ v5_orders_2(X14)
        | ~ l1_orders_2(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d15_orders_2])])])])])])).

fof(c_0_13,plain,(
    ! [X22,X23,X24] :
      ( v2_struct_0(X22)
      | ~ v3_orders_2(X22)
      | ~ v4_orders_2(X22)
      | ~ v5_orders_2(X22)
      | ~ l1_orders_2(X22)
      | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
      | ~ m1_orders_2(X24,X22,X23)
      | m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_orders_2])])])])).

fof(c_0_14,plain,(
    ! [X11,X12,X13] :
      ( ~ r2_hidden(X11,X12)
      | ~ m1_subset_1(X12,k1_zfmisc_1(X13))
      | m1_subset_1(X11,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_15,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_22,plain,(
    ! [X29,X30,X31,X32] :
      ( v2_struct_0(X29)
      | ~ v3_orders_2(X29)
      | ~ v4_orders_2(X29)
      | ~ v5_orders_2(X29)
      | ~ l1_orders_2(X29)
      | ~ m1_subset_1(X30,u1_struct_0(X29))
      | ~ m1_subset_1(X31,u1_struct_0(X29))
      | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X29)))
      | ~ r2_orders_2(X29,X30,X31)
      | r1_tarski(k3_orders_2(X29,X32,X30),k3_orders_2(X29,X32,X31)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t64_orders_2])])])])).

fof(c_0_23,plain,(
    ! [X25,X26,X27,X28] :
      ( ( r2_orders_2(X25,X26,X27)
        | ~ r2_hidden(X26,k3_orders_2(X25,X28,X27))
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | ~ m1_subset_1(X26,u1_struct_0(X25))
        | v2_struct_0(X25)
        | ~ v3_orders_2(X25)
        | ~ v4_orders_2(X25)
        | ~ v5_orders_2(X25)
        | ~ l1_orders_2(X25) )
      & ( r2_hidden(X26,X28)
        | ~ r2_hidden(X26,k3_orders_2(X25,X28,X27))
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | ~ m1_subset_1(X26,u1_struct_0(X25))
        | v2_struct_0(X25)
        | ~ v3_orders_2(X25)
        | ~ v4_orders_2(X25)
        | ~ v5_orders_2(X25)
        | ~ l1_orders_2(X25) )
      & ( ~ r2_orders_2(X25,X26,X27)
        | ~ r2_hidden(X26,X28)
        | r2_hidden(X26,k3_orders_2(X25,X28,X27))
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | ~ m1_subset_1(X26,u1_struct_0(X25))
        | v2_struct_0(X25)
        | ~ v3_orders_2(X25)
        | ~ v4_orders_2(X25)
        | ~ v5_orders_2(X25)
        | ~ l1_orders_2(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_orders_2])])])])])).

cnf(c_0_24,plain,
    ( X1 = k3_orders_2(X2,X3,esk1_3(X2,X3,X1))
    | X3 = k1_xboole_0
    | v2_struct_0(X2)
    | ~ m1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_orders_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | X2 = k1_xboole_0
    | v2_struct_0(X1)
    | ~ m1_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(k3_orders_2(esk2_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_29,plain,
    ( v2_struct_0(X1)
    | r1_tarski(k3_orders_2(X1,X4,X2),k3_orders_2(X1,X4,X3))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_orders_2(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

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

cnf(c_0_31,plain,
    ( k3_orders_2(X1,X2,esk1_3(X1,X2,X3)) = X3
    | X2 = k1_xboole_0
    | v2_struct_0(X1)
    | ~ m1_orders_2(X3,X1,X2)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,plain,
    ( X1 = k1_xboole_0
    | v2_struct_0(X2)
    | m1_subset_1(esk1_3(X2,X1,X3),u1_struct_0(X2))
    | ~ m1_orders_2(X3,X2,X1)
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[c_0_26,c_0_25])).

cnf(c_0_33,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | X2 = k1_xboole_0
    | v2_struct_0(X1)
    | ~ m1_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,k3_orders_2(esk2_0,esk5_0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(k3_orders_2(esk2_0,esk5_0,X1),k3_orders_2(esk2_0,esk5_0,X2))
    | ~ r2_orders_2(esk2_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_36,plain,
    ( X1 = k1_xboole_0
    | r2_orders_2(X2,X3,esk1_3(X2,X1,X4))
    | v2_struct_0(X2)
    | ~ m1_orders_2(X4,X2,X1)
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2)
    | ~ r2_hidden(X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_16])).

cnf(c_0_38,plain,
    ( X1 = k1_xboole_0
    | v2_struct_0(X2)
    | r2_hidden(esk1_3(X2,X1,X3),X1)
    | ~ m1_orders_2(X3,X2,X1)
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[c_0_33,c_0_25])).

cnf(c_0_39,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_orders_2(X2,esk2_0,esk5_0)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(esk1_3(esk2_0,esk5_0,X2),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_31]),c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_16])]),c_0_21])).

cnf(c_0_40,negated_conjecture,
    ( X1 = k1_xboole_0
    | r1_tarski(k3_orders_2(esk2_0,esk5_0,X2),k3_orders_2(esk2_0,esk5_0,esk1_3(esk2_0,X1,X3)))
    | ~ m1_orders_2(X3,esk2_0,X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(esk1_3(esk2_0,X1,X3),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_41,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | v2_struct_0(X1)
    | m1_subset_1(esk1_3(X1,esk5_0,X2),u1_struct_0(esk2_0))
    | ~ m1_orders_2(X2,X1,esk5_0)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_orders_2(X2,esk2_0,esk5_0)
    | ~ r2_hidden(X1,X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_32]),c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_16])]),c_0_21])).

fof(c_0_43,plain,(
    ! [X6,X7,X8] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | ~ r2_hidden(X8,X7)
      | r2_hidden(X8,X6) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_44,plain,(
    ! [X9,X10] :
      ( ( ~ m1_subset_1(X9,k1_zfmisc_1(X10))
        | r1_tarski(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | m1_subset_1(X9,k1_zfmisc_1(X10)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_45,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r1_tarski(k3_orders_2(esk2_0,esk5_0,X1),k3_orders_2(esk2_0,esk5_0,esk1_3(esk2_0,esk5_0,X2)))
    | ~ m1_orders_2(X2,esk2_0,esk5_0)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_47,negated_conjecture,
    ( m1_orders_2(esk6_0,esk2_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_48,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r1_tarski(k3_orders_2(esk2_0,esk5_0,esk4_0),k3_orders_2(esk2_0,esk5_0,esk1_3(esk2_0,esk5_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])])).

cnf(c_0_51,plain,
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

cnf(c_0_52,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r1_tarski(k3_orders_2(esk2_0,esk5_0,esk4_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_31]),c_0_47]),c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_16])]),c_0_21])).

cnf(c_0_54,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k3_orders_2(X1,X3,X4))
    | ~ r2_orders_2(X1,X2,X4)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[c_0_51,c_0_27])).

cnf(c_0_55,negated_conjecture,
    ( r2_orders_2(esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_57,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,k3_orders_2(esk2_0,esk5_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk3_0,k3_orders_2(esk2_0,X1,esk4_0))
    | ~ r2_hidden(esk3_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_56])]),c_0_21])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_60,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_61,plain,
    ( X1 = k1_xboole_0
    | v2_struct_0(X2)
    | ~ m1_orders_2(X1,X2,X3)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_62,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59]),c_0_16])]),c_0_60])).

cnf(c_0_63,plain,
    ( X1 = k1_xboole_0
    | v2_struct_0(X2)
    | ~ m1_orders_2(X1,X2,k1_xboole_0)
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_61,c_0_25])])).

cnf(c_0_64,negated_conjecture,
    ( m1_orders_2(esk6_0,esk2_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_47,c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(rw,[status(thm)],[c_0_16,c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_65])])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk3_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_59,c_0_62])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_66]),c_0_67])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:26:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.48/0.67  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 0.48/0.67  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.48/0.67  #
% 0.48/0.67  # Preprocessing time       : 0.029 s
% 0.48/0.67  # Presaturation interreduction done
% 0.48/0.67  
% 0.48/0.67  # Proof found!
% 0.48/0.67  # SZS status Theorem
% 0.48/0.67  # SZS output start CNFRefutation
% 0.48/0.67  fof(t70_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))=>((((r2_orders_2(X1,X2,X3)&r2_hidden(X2,X4))&r2_hidden(X3,X5))&m1_orders_2(X5,X1,X4))=>r2_hidden(X2,X5))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_orders_2)).
% 0.48/0.67  fof(dt_k3_orders_2, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 0.48/0.67  fof(d15_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((X2!=k1_xboole_0=>(m1_orders_2(X3,X1,X2)<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X1))&r2_hidden(X4,X2))&X3=k3_orders_2(X1,X2,X4))))&(X2=k1_xboole_0=>(m1_orders_2(X3,X1,X2)<=>X3=k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d15_orders_2)).
% 0.48/0.67  fof(dt_m1_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_orders_2(X3,X1,X2)=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_orders_2)).
% 0.48/0.67  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.48/0.67  fof(t64_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_orders_2(X1,X2,X3)=>r1_tarski(k3_orders_2(X1,X4,X2),k3_orders_2(X1,X4,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_orders_2)).
% 0.48/0.67  fof(t57_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,k3_orders_2(X1,X4,X3))<=>(r2_orders_2(X1,X2,X3)&r2_hidden(X2,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 0.48/0.67  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.48/0.67  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.48/0.67  fof(c_0_9, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))=>((((r2_orders_2(X1,X2,X3)&r2_hidden(X2,X4))&r2_hidden(X3,X5))&m1_orders_2(X5,X1,X4))=>r2_hidden(X2,X5)))))))), inference(assume_negation,[status(cth)],[t70_orders_2])).
% 0.48/0.67  fof(c_0_10, plain, ![X19, X20, X21]:(v2_struct_0(X19)|~v3_orders_2(X19)|~v4_orders_2(X19)|~v5_orders_2(X19)|~l1_orders_2(X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~m1_subset_1(X21,u1_struct_0(X19))|m1_subset_1(k3_orders_2(X19,X20,X21),k1_zfmisc_1(u1_struct_0(X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_orders_2])])])).
% 0.48/0.67  fof(c_0_11, negated_conjecture, (((((~v2_struct_0(esk2_0)&v3_orders_2(esk2_0))&v4_orders_2(esk2_0))&v5_orders_2(esk2_0))&l1_orders_2(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&(m1_subset_1(esk4_0,u1_struct_0(esk2_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&((((r2_orders_2(esk2_0,esk3_0,esk4_0)&r2_hidden(esk3_0,esk5_0))&r2_hidden(esk4_0,esk6_0))&m1_orders_2(esk6_0,esk2_0,esk5_0))&~r2_hidden(esk3_0,esk6_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).
% 0.48/0.67  fof(c_0_12, plain, ![X14, X15, X16, X18]:(((((m1_subset_1(esk1_3(X14,X15,X16),u1_struct_0(X14))|~m1_orders_2(X16,X14,X15)|X15=k1_xboole_0|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|(v2_struct_0(X14)|~v3_orders_2(X14)|~v4_orders_2(X14)|~v5_orders_2(X14)|~l1_orders_2(X14)))&(r2_hidden(esk1_3(X14,X15,X16),X15)|~m1_orders_2(X16,X14,X15)|X15=k1_xboole_0|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|(v2_struct_0(X14)|~v3_orders_2(X14)|~v4_orders_2(X14)|~v5_orders_2(X14)|~l1_orders_2(X14))))&(X16=k3_orders_2(X14,X15,esk1_3(X14,X15,X16))|~m1_orders_2(X16,X14,X15)|X15=k1_xboole_0|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|(v2_struct_0(X14)|~v3_orders_2(X14)|~v4_orders_2(X14)|~v5_orders_2(X14)|~l1_orders_2(X14))))&(~m1_subset_1(X18,u1_struct_0(X14))|~r2_hidden(X18,X15)|X16!=k3_orders_2(X14,X15,X18)|m1_orders_2(X16,X14,X15)|X15=k1_xboole_0|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|(v2_struct_0(X14)|~v3_orders_2(X14)|~v4_orders_2(X14)|~v5_orders_2(X14)|~l1_orders_2(X14))))&((~m1_orders_2(X16,X14,X15)|X16=k1_xboole_0|X15!=k1_xboole_0|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|(v2_struct_0(X14)|~v3_orders_2(X14)|~v4_orders_2(X14)|~v5_orders_2(X14)|~l1_orders_2(X14)))&(X16!=k1_xboole_0|m1_orders_2(X16,X14,X15)|X15!=k1_xboole_0|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|(v2_struct_0(X14)|~v3_orders_2(X14)|~v4_orders_2(X14)|~v5_orders_2(X14)|~l1_orders_2(X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d15_orders_2])])])])])])).
% 0.48/0.67  fof(c_0_13, plain, ![X22, X23, X24]:(v2_struct_0(X22)|~v3_orders_2(X22)|~v4_orders_2(X22)|~v5_orders_2(X22)|~l1_orders_2(X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|(~m1_orders_2(X24,X22,X23)|m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_orders_2])])])])).
% 0.48/0.67  fof(c_0_14, plain, ![X11, X12, X13]:(~r2_hidden(X11,X12)|~m1_subset_1(X12,k1_zfmisc_1(X13))|m1_subset_1(X11,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.48/0.67  cnf(c_0_15, plain, (v2_struct_0(X1)|m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.48/0.67  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.48/0.67  cnf(c_0_17, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.48/0.67  cnf(c_0_18, negated_conjecture, (v5_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.48/0.67  cnf(c_0_19, negated_conjecture, (v4_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.48/0.67  cnf(c_0_20, negated_conjecture, (v3_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.48/0.67  cnf(c_0_21, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.48/0.67  fof(c_0_22, plain, ![X29, X30, X31, X32]:(v2_struct_0(X29)|~v3_orders_2(X29)|~v4_orders_2(X29)|~v5_orders_2(X29)|~l1_orders_2(X29)|(~m1_subset_1(X30,u1_struct_0(X29))|(~m1_subset_1(X31,u1_struct_0(X29))|(~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X29)))|(~r2_orders_2(X29,X30,X31)|r1_tarski(k3_orders_2(X29,X32,X30),k3_orders_2(X29,X32,X31))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t64_orders_2])])])])).
% 0.48/0.67  fof(c_0_23, plain, ![X25, X26, X27, X28]:(((r2_orders_2(X25,X26,X27)|~r2_hidden(X26,k3_orders_2(X25,X28,X27))|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X25)))|~m1_subset_1(X27,u1_struct_0(X25))|~m1_subset_1(X26,u1_struct_0(X25))|(v2_struct_0(X25)|~v3_orders_2(X25)|~v4_orders_2(X25)|~v5_orders_2(X25)|~l1_orders_2(X25)))&(r2_hidden(X26,X28)|~r2_hidden(X26,k3_orders_2(X25,X28,X27))|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X25)))|~m1_subset_1(X27,u1_struct_0(X25))|~m1_subset_1(X26,u1_struct_0(X25))|(v2_struct_0(X25)|~v3_orders_2(X25)|~v4_orders_2(X25)|~v5_orders_2(X25)|~l1_orders_2(X25))))&(~r2_orders_2(X25,X26,X27)|~r2_hidden(X26,X28)|r2_hidden(X26,k3_orders_2(X25,X28,X27))|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X25)))|~m1_subset_1(X27,u1_struct_0(X25))|~m1_subset_1(X26,u1_struct_0(X25))|(v2_struct_0(X25)|~v3_orders_2(X25)|~v4_orders_2(X25)|~v5_orders_2(X25)|~l1_orders_2(X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_orders_2])])])])])).
% 0.48/0.67  cnf(c_0_24, plain, (X1=k3_orders_2(X2,X3,esk1_3(X2,X3,X1))|X3=k1_xboole_0|v2_struct_0(X2)|~m1_orders_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.48/0.67  cnf(c_0_25, plain, (v2_struct_0(X1)|m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_orders_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.48/0.67  cnf(c_0_26, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|X2=k1_xboole_0|v2_struct_0(X1)|~m1_orders_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.48/0.67  cnf(c_0_27, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.48/0.67  cnf(c_0_28, negated_conjecture, (m1_subset_1(k3_orders_2(esk2_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21])).
% 0.48/0.67  cnf(c_0_29, plain, (v2_struct_0(X1)|r1_tarski(k3_orders_2(X1,X4,X2),k3_orders_2(X1,X4,X3))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~r2_orders_2(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.48/0.67  cnf(c_0_30, plain, (r2_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r2_hidden(X2,k3_orders_2(X1,X4,X3))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.48/0.67  cnf(c_0_31, plain, (k3_orders_2(X1,X2,esk1_3(X1,X2,X3))=X3|X2=k1_xboole_0|v2_struct_0(X1)|~m1_orders_2(X3,X1,X2)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[c_0_24, c_0_25])).
% 0.48/0.67  cnf(c_0_32, plain, (X1=k1_xboole_0|v2_struct_0(X2)|m1_subset_1(esk1_3(X2,X1,X3),u1_struct_0(X2))|~m1_orders_2(X3,X2,X1)|~l1_orders_2(X2)|~v5_orders_2(X2)|~v4_orders_2(X2)|~v3_orders_2(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[c_0_26, c_0_25])).
% 0.48/0.67  cnf(c_0_33, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|X2=k1_xboole_0|v2_struct_0(X1)|~m1_orders_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.48/0.67  cnf(c_0_34, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,k3_orders_2(esk2_0,esk5_0,X2))|~m1_subset_1(X2,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.48/0.67  cnf(c_0_35, negated_conjecture, (r1_tarski(k3_orders_2(esk2_0,esk5_0,X1),k3_orders_2(esk2_0,esk5_0,X2))|~r2_orders_2(esk2_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21])).
% 0.48/0.67  cnf(c_0_36, plain, (X1=k1_xboole_0|r2_orders_2(X2,X3,esk1_3(X2,X1,X4))|v2_struct_0(X2)|~m1_orders_2(X4,X2,X1)|~l1_orders_2(X2)|~v5_orders_2(X2)|~v4_orders_2(X2)|~v3_orders_2(X2)|~r2_hidden(X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,u1_struct_0(X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 0.48/0.67  cnf(c_0_37, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_27, c_0_16])).
% 0.48/0.67  cnf(c_0_38, plain, (X1=k1_xboole_0|v2_struct_0(X2)|r2_hidden(esk1_3(X2,X1,X3),X1)|~m1_orders_2(X3,X2,X1)|~l1_orders_2(X2)|~v5_orders_2(X2)|~v4_orders_2(X2)|~v3_orders_2(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[c_0_33, c_0_25])).
% 0.48/0.67  cnf(c_0_39, negated_conjecture, (esk5_0=k1_xboole_0|m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_orders_2(X2,esk2_0,esk5_0)|~r2_hidden(X1,X2)|~m1_subset_1(esk1_3(esk2_0,esk5_0,X2),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_31]), c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_16])]), c_0_21])).
% 0.48/0.67  cnf(c_0_40, negated_conjecture, (X1=k1_xboole_0|r1_tarski(k3_orders_2(esk2_0,esk5_0,X2),k3_orders_2(esk2_0,esk5_0,esk1_3(esk2_0,X1,X3)))|~m1_orders_2(X3,esk2_0,X1)|~r2_hidden(X2,X3)|~m1_subset_1(esk1_3(esk2_0,X1,X3),u1_struct_0(esk2_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X2,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21])).
% 0.48/0.67  cnf(c_0_41, negated_conjecture, (esk5_0=k1_xboole_0|v2_struct_0(X1)|m1_subset_1(esk1_3(X1,esk5_0,X2),u1_struct_0(esk2_0))|~m1_orders_2(X2,X1,esk5_0)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.48/0.67  cnf(c_0_42, negated_conjecture, (esk5_0=k1_xboole_0|m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_orders_2(X2,esk2_0,esk5_0)|~r2_hidden(X1,X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_32]), c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_16])]), c_0_21])).
% 0.48/0.67  fof(c_0_43, plain, ![X6, X7, X8]:(~m1_subset_1(X7,k1_zfmisc_1(X6))|(~r2_hidden(X8,X7)|r2_hidden(X8,X6))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.48/0.67  fof(c_0_44, plain, ![X9, X10]:((~m1_subset_1(X9,k1_zfmisc_1(X10))|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|m1_subset_1(X9,k1_zfmisc_1(X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.48/0.67  cnf(c_0_45, negated_conjecture, (esk5_0=k1_xboole_0|r1_tarski(k3_orders_2(esk2_0,esk5_0,X1),k3_orders_2(esk2_0,esk5_0,esk1_3(esk2_0,esk5_0,X2)))|~m1_orders_2(X2,esk2_0,esk5_0)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21]), c_0_42])).
% 0.48/0.67  cnf(c_0_46, negated_conjecture, (r2_hidden(esk4_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.48/0.67  cnf(c_0_47, negated_conjecture, (m1_orders_2(esk6_0,esk2_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.48/0.67  cnf(c_0_48, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.48/0.67  cnf(c_0_49, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.48/0.67  cnf(c_0_50, negated_conjecture, (esk5_0=k1_xboole_0|r1_tarski(k3_orders_2(esk2_0,esk5_0,esk4_0),k3_orders_2(esk2_0,esk5_0,esk1_3(esk2_0,esk5_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])])).
% 0.48/0.67  cnf(c_0_51, plain, (r2_hidden(X2,k3_orders_2(X1,X4,X3))|v2_struct_0(X1)|~r2_orders_2(X1,X2,X3)|~r2_hidden(X2,X4)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.48/0.67  cnf(c_0_52, plain, (r2_hidden(X1,X2)|~r1_tarski(X3,X2)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.48/0.67  cnf(c_0_53, negated_conjecture, (esk5_0=k1_xboole_0|r1_tarski(k3_orders_2(esk2_0,esk5_0,esk4_0),esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_31]), c_0_47]), c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_16])]), c_0_21])).
% 0.48/0.67  cnf(c_0_54, plain, (v2_struct_0(X1)|r2_hidden(X2,k3_orders_2(X1,X3,X4))|~r2_orders_2(X1,X2,X4)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~r2_hidden(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X4,u1_struct_0(X1))), inference(csr,[status(thm)],[c_0_51, c_0_27])).
% 0.48/0.67  cnf(c_0_55, negated_conjecture, (r2_orders_2(esk2_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.48/0.67  cnf(c_0_56, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.48/0.67  cnf(c_0_57, negated_conjecture, (esk5_0=k1_xboole_0|r2_hidden(X1,esk6_0)|~r2_hidden(X1,k3_orders_2(esk2_0,esk5_0,esk4_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.48/0.67  cnf(c_0_58, negated_conjecture, (r2_hidden(esk3_0,k3_orders_2(esk2_0,X1,esk4_0))|~r2_hidden(esk3_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_56])]), c_0_21])).
% 0.48/0.67  cnf(c_0_59, negated_conjecture, (r2_hidden(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.48/0.67  cnf(c_0_60, negated_conjecture, (~r2_hidden(esk3_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.48/0.67  cnf(c_0_61, plain, (X1=k1_xboole_0|v2_struct_0(X2)|~m1_orders_2(X1,X2,X3)|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.48/0.67  cnf(c_0_62, negated_conjecture, (esk5_0=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59]), c_0_16])]), c_0_60])).
% 0.48/0.67  cnf(c_0_63, plain, (X1=k1_xboole_0|v2_struct_0(X2)|~m1_orders_2(X1,X2,k1_xboole_0)|~l1_orders_2(X2)|~v5_orders_2(X2)|~v4_orders_2(X2)|~v3_orders_2(X2)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X2)))), inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_61, c_0_25])])).
% 0.48/0.67  cnf(c_0_64, negated_conjecture, (m1_orders_2(esk6_0,esk2_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_47, c_0_62])).
% 0.48/0.67  cnf(c_0_65, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(rw,[status(thm)],[c_0_16, c_0_62])).
% 0.48/0.67  cnf(c_0_66, negated_conjecture, (esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21]), c_0_65])])).
% 0.48/0.67  cnf(c_0_67, negated_conjecture, (r2_hidden(esk3_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_59, c_0_62])).
% 0.48/0.67  cnf(c_0_68, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_66]), c_0_67])]), ['proof']).
% 0.48/0.67  # SZS output end CNFRefutation
% 0.48/0.67  # Proof object total steps             : 69
% 0.48/0.67  # Proof object clause steps            : 50
% 0.48/0.67  # Proof object formula steps           : 19
% 0.48/0.67  # Proof object conjectures             : 34
% 0.48/0.67  # Proof object clause conjectures      : 31
% 0.48/0.67  # Proof object formula conjectures     : 3
% 0.48/0.67  # Proof object initial clauses used    : 24
% 0.48/0.67  # Proof object initial formulas used   : 9
% 0.48/0.67  # Proof object generating inferences   : 17
% 0.48/0.67  # Proof object simplifying inferences  : 82
% 0.48/0.67  # Training examples: 0 positive, 0 negative
% 0.48/0.67  # Parsed axioms                        : 9
% 0.48/0.67  # Removed by relevancy pruning/SinE    : 0
% 0.48/0.67  # Initial clauses                      : 30
% 0.48/0.67  # Removed in clause preprocessing      : 0
% 0.48/0.67  # Initial clauses in saturation        : 30
% 0.48/0.67  # Processed clauses                    : 1191
% 0.48/0.67  # ...of these trivial                  : 0
% 0.48/0.67  # ...subsumed                          : 372
% 0.48/0.67  # ...remaining for further processing  : 819
% 0.48/0.67  # Other redundant clauses eliminated   : 4
% 0.48/0.67  # Clauses deleted for lack of memory   : 0
% 0.48/0.67  # Backward-subsumed                    : 25
% 0.48/0.67  # Backward-rewritten                   : 711
% 0.48/0.67  # Generated clauses                    : 5878
% 0.48/0.67  # ...of the previous two non-trivial   : 6188
% 0.48/0.67  # Contextual simplify-reflections      : 56
% 0.48/0.67  # Paramodulations                      : 5875
% 0.48/0.67  # Factorizations                       : 0
% 0.48/0.67  # Equation resolutions                 : 4
% 0.48/0.67  # Propositional unsat checks           : 0
% 0.48/0.67  #    Propositional check models        : 0
% 0.48/0.67  #    Propositional check unsatisfiable : 0
% 0.48/0.67  #    Propositional clauses             : 0
% 0.48/0.67  #    Propositional clauses after purity: 0
% 0.48/0.67  #    Propositional unsat core size     : 0
% 0.48/0.67  #    Propositional preprocessing time  : 0.000
% 0.48/0.67  #    Propositional encoding time       : 0.000
% 0.48/0.67  #    Propositional solver time         : 0.000
% 0.48/0.67  #    Success case prop preproc time    : 0.000
% 0.48/0.67  #    Success case prop encoding time   : 0.000
% 0.48/0.67  #    Success case prop solver time     : 0.000
% 0.48/0.67  # Current number of processed clauses  : 50
% 0.48/0.67  #    Positive orientable unit clauses  : 13
% 0.48/0.67  #    Positive unorientable unit clauses: 0
% 0.48/0.67  #    Negative unit clauses             : 1
% 0.48/0.67  #    Non-unit-clauses                  : 36
% 0.48/0.67  # Current number of unprocessed clauses: 4732
% 0.48/0.67  # ...number of literals in the above   : 46063
% 0.48/0.67  # Current number of archived formulas  : 0
% 0.48/0.67  # Current number of archived clauses   : 766
% 0.48/0.67  # Clause-clause subsumption calls (NU) : 185714
% 0.48/0.67  # Rec. Clause-clause subsumption calls : 22821
% 0.48/0.67  # Non-unit clause-clause subsumptions  : 437
% 0.48/0.67  # Unit Clause-clause subsumption calls : 1398
% 0.48/0.67  # Rewrite failures with RHS unbound    : 0
% 0.48/0.67  # BW rewrite match attempts            : 4276
% 0.48/0.67  # BW rewrite match successes           : 5
% 0.48/0.67  # Condensation attempts                : 0
% 0.48/0.67  # Condensation successes               : 0
% 0.48/0.67  # Termbank termtop insertions          : 224951
% 0.48/0.67  
% 0.48/0.67  # -------------------------------------------------
% 0.48/0.67  # User time                : 0.319 s
% 0.48/0.67  # System time              : 0.012 s
% 0.48/0.67  # Total time               : 0.331 s
% 0.48/0.67  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
