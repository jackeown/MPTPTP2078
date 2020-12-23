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
% DateTime   : Thu Dec  3 11:10:01 EST 2020

% Result     : Theorem 5.64s
% Output     : CNFRefutation 5.64s
% Verified   : 
% Statistics : Number of formulae       :   87 (1974 expanded)
%              Number of clauses        :   70 ( 653 expanded)
%              Number of leaves         :    8 ( 469 expanded)
%              Depth                    :   21
%              Number of atoms          :  399 (20445 expanded)
%              Number of equality atoms :   34 ( 516 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   62 (   3 average)
%              Maximal term depth       :    7 (   1 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_orders_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_orders_2)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_orders_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_8,negated_conjecture,(
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

fof(c_0_9,plain,(
    ! [X27,X28,X29,X30] :
      ( v2_struct_0(X27)
      | ~ v3_orders_2(X27)
      | ~ v4_orders_2(X27)
      | ~ v5_orders_2(X27)
      | ~ l1_orders_2(X27)
      | ~ m1_subset_1(X28,u1_struct_0(X27))
      | ~ m1_subset_1(X29,u1_struct_0(X27))
      | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X27)))
      | ~ r2_orders_2(X27,X28,X29)
      | r1_tarski(k3_orders_2(X27,X30,X28),k3_orders_2(X27,X30,X29)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t64_orders_2])])])])).

fof(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v3_orders_2(esk3_0)
    & v4_orders_2(esk3_0)
    & v5_orders_2(esk3_0)
    & l1_orders_2(esk3_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk5_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & r2_orders_2(esk3_0,esk4_0,esk5_0)
    & r2_hidden(esk4_0,esk6_0)
    & r2_hidden(esk5_0,esk7_0)
    & m1_orders_2(esk7_0,esk3_0,esk6_0)
    & ~ r2_hidden(esk4_0,esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

cnf(c_0_11,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( v5_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( v4_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( v3_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_18,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(k3_orders_2(esk3_0,X1,X2),k3_orders_2(esk3_0,X1,esk5_0))
    | ~ r2_orders_2(esk3_0,X2,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_14]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( r2_orders_2(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X23,X24,X25,X26] :
      ( ( r2_orders_2(X23,X24,X25)
        | ~ r2_hidden(X24,k3_orders_2(X23,X26,X25))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ v3_orders_2(X23)
        | ~ v4_orders_2(X23)
        | ~ v5_orders_2(X23)
        | ~ l1_orders_2(X23) )
      & ( r2_hidden(X24,X26)
        | ~ r2_hidden(X24,k3_orders_2(X23,X26,X25))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ v3_orders_2(X23)
        | ~ v4_orders_2(X23)
        | ~ v5_orders_2(X23)
        | ~ l1_orders_2(X23) )
      & ( ~ r2_orders_2(X23,X24,X25)
        | ~ r2_hidden(X24,X26)
        | r2_hidden(X24,k3_orders_2(X23,X26,X25))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ v3_orders_2(X23)
        | ~ v4_orders_2(X23)
        | ~ v5_orders_2(X23)
        | ~ l1_orders_2(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_orders_2])])])])])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(k3_orders_2(esk3_0,X1,esk4_0),k3_orders_2(esk3_0,X1,esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_27,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_29,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(k3_orders_2(esk3_0,esk7_0,esk4_0),k3_orders_2(esk3_0,esk7_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,X1),esk6_0)
    | r2_hidden(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,k3_orders_2(esk3_0,X2,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_12]),c_0_13]),c_0_14]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(X1,k3_orders_2(esk3_0,esk7_0,esk5_0))
    | ~ r2_hidden(X1,k3_orders_2(esk3_0,esk7_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,X1),esk6_0)
    | r2_hidden(esk1_2(esk6_0,X2),X1)
    | r2_hidden(esk4_0,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk4_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(esk4_0,k3_orders_2(esk3_0,X1,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_21])).

cnf(c_0_36,negated_conjecture,
    ( ~ r2_hidden(esk4_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_37,plain,(
    ! [X18,X19,X20,X22] :
      ( ( m1_subset_1(esk2_3(X18,X19,X20),u1_struct_0(X18))
        | ~ m1_orders_2(X20,X18,X19)
        | X19 = k1_xboole_0
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | v2_struct_0(X18)
        | ~ v3_orders_2(X18)
        | ~ v4_orders_2(X18)
        | ~ v5_orders_2(X18)
        | ~ l1_orders_2(X18) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X19)
        | ~ m1_orders_2(X20,X18,X19)
        | X19 = k1_xboole_0
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | v2_struct_0(X18)
        | ~ v3_orders_2(X18)
        | ~ v4_orders_2(X18)
        | ~ v5_orders_2(X18)
        | ~ l1_orders_2(X18) )
      & ( X20 = k3_orders_2(X18,X19,esk2_3(X18,X19,X20))
        | ~ m1_orders_2(X20,X18,X19)
        | X19 = k1_xboole_0
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | v2_struct_0(X18)
        | ~ v3_orders_2(X18)
        | ~ v4_orders_2(X18)
        | ~ v5_orders_2(X18)
        | ~ l1_orders_2(X18) )
      & ( ~ m1_subset_1(X22,u1_struct_0(X18))
        | ~ r2_hidden(X22,X19)
        | X20 != k3_orders_2(X18,X19,X22)
        | m1_orders_2(X20,X18,X19)
        | X19 = k1_xboole_0
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | v2_struct_0(X18)
        | ~ v3_orders_2(X18)
        | ~ v4_orders_2(X18)
        | ~ v5_orders_2(X18)
        | ~ l1_orders_2(X18) )
      & ( ~ m1_orders_2(X20,X18,X19)
        | X20 = k1_xboole_0
        | X19 != k1_xboole_0
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | v2_struct_0(X18)
        | ~ v3_orders_2(X18)
        | ~ v4_orders_2(X18)
        | ~ v5_orders_2(X18)
        | ~ l1_orders_2(X18) )
      & ( X20 != k1_xboole_0
        | m1_orders_2(X20,X18,X19)
        | X19 != k1_xboole_0
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | v2_struct_0(X18)
        | ~ v3_orders_2(X18)
        | ~ v4_orders_2(X18)
        | ~ v5_orders_2(X18)
        | ~ l1_orders_2(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d15_orders_2])])])])])])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,k3_orders_2(esk3_0,esk7_0,esk4_0)),esk6_0)
    | r2_hidden(esk1_2(esk6_0,X1),k3_orders_2(esk3_0,esk7_0,esk5_0))
    | r2_hidden(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k3_orders_2(esk3_0,esk7_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_26]),c_0_36])).

fof(c_0_41,plain,(
    ! [X13,X14,X15] :
      ( ~ r2_hidden(X13,X14)
      | ~ m1_subset_1(X14,k1_zfmisc_1(X15))
      | m1_subset_1(X13,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_42,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | X2 = k1_xboole_0
    | v2_struct_0(X1)
    | ~ m1_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,k3_orders_2(esk3_0,esk7_0,esk4_0)),esk6_0)
    | r1_tarski(esk6_0,k3_orders_2(esk3_0,esk7_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_44,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_46,negated_conjecture,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_3(esk3_0,X1,esk7_0),X1)
    | ~ m1_orders_2(esk7_0,esk3_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_26]),c_0_13]),c_0_14]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_47,negated_conjecture,
    ( m1_orders_2(esk7_0,esk3_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_48,plain,(
    ! [X16,X17] :
      ( ~ r2_hidden(X16,X17)
      | ~ r1_tarski(X17,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,k3_orders_2(esk3_0,esk7_0,esk4_0)),esk6_0)
    | r2_hidden(X1,k3_orders_2(esk3_0,esk7_0,esk5_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk2_3(esk3_0,esk6_0,esk7_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_45])])).

cnf(c_0_52,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,k3_orders_2(esk3_0,esk7_0,esk4_0)),esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_28]),c_0_40])).

cnf(c_0_54,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_55,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | m1_subset_1(esk2_3(esk3_0,esk6_0,esk7_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( ~ r1_tarski(esk6_0,esk1_2(esk6_0,k3_orders_2(esk3_0,esk7_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_orders_2(esk3_0,X1,esk2_3(esk3_0,esk6_0,esk7_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,k3_orders_2(esk3_0,X2,esk2_3(esk3_0,esk6_0,esk7_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_13]),c_0_14]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_58,plain,
    ( X1 = k3_orders_2(X2,X3,esk2_3(X2,X3,X1))
    | X3 = k1_xboole_0
    | v2_struct_0(X2)
    | ~ m1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,esk1_2(esk6_0,k3_orders_2(esk3_0,esk7_0,esk4_0))),esk6_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_23])).

cnf(c_0_60,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_orders_2(esk3_0,esk5_0,esk2_3(esk3_0,esk6_0,esk7_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(esk5_0,k3_orders_2(esk3_0,X1,esk2_3(esk3_0,esk6_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_12])).

cnf(c_0_61,negated_conjecture,
    ( k3_orders_2(esk3_0,esk6_0,esk2_3(esk3_0,esk6_0,X1)) = X1
    | esk6_0 = k1_xboole_0
    | ~ m1_orders_2(X1,esk3_0,esk6_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_45]),c_0_13]),c_0_14]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_62,negated_conjecture,
    ( ~ r1_tarski(esk6_0,esk1_2(esk6_0,esk1_2(esk6_0,k3_orders_2(esk3_0,esk7_0,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_orders_2(esk3_0,esk5_0,esk2_3(esk3_0,esk6_0,esk7_0))
    | ~ r2_hidden(esk5_0,k3_orders_2(esk3_0,esk6_0,esk2_3(esk3_0,esk6_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_45])).

cnf(c_0_64,negated_conjecture,
    ( k3_orders_2(esk3_0,esk6_0,esk2_3(esk3_0,esk6_0,esk7_0)) = esk7_0
    | esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_47]),c_0_26])])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,esk1_2(esk6_0,esk1_2(esk6_0,k3_orders_2(esk3_0,esk7_0,esk4_0)))),esk6_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_23])).

cnf(c_0_67,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r1_tarski(k3_orders_2(esk3_0,X1,X2),k3_orders_2(esk3_0,X1,esk2_3(esk3_0,esk6_0,esk7_0)))
    | ~ r2_orders_2(esk3_0,X2,esk2_3(esk3_0,esk6_0,esk7_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_55]),c_0_13]),c_0_14]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_68,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_orders_2(esk3_0,esk5_0,esk2_3(esk3_0,esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])])).

cnf(c_0_69,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_70,negated_conjecture,
    ( ~ r1_tarski(esk6_0,esk1_2(esk6_0,esk1_2(esk6_0,esk1_2(esk6_0,k3_orders_2(esk3_0,esk7_0,esk4_0))))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r1_tarski(k3_orders_2(esk3_0,X1,esk5_0),k3_orders_2(esk3_0,X1,esk2_3(esk3_0,esk6_0,esk7_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_12]),c_0_68])).

cnf(c_0_72,plain,
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
    inference(csr,[status(thm)],[c_0_69,c_0_44])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,esk1_2(esk6_0,esk1_2(esk6_0,esk1_2(esk6_0,k3_orders_2(esk3_0,esk7_0,esk4_0))))),esk6_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_23])).

cnf(c_0_74,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r1_tarski(k3_orders_2(esk3_0,esk6_0,esk5_0),k3_orders_2(esk3_0,esk6_0,esk2_3(esk3_0,esk6_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_45])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(X1,k3_orders_2(esk3_0,X2,esk5_0))
    | ~ r2_orders_2(esk3_0,X1,esk5_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(X1,X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_12]),c_0_13]),c_0_14]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_76,negated_conjecture,
    ( ~ r1_tarski(esk6_0,esk1_2(esk6_0,esk1_2(esk6_0,esk1_2(esk6_0,esk1_2(esk6_0,k3_orders_2(esk3_0,esk7_0,esk4_0)))))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_73])).

cnf(c_0_77,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r1_tarski(k3_orders_2(esk3_0,esk6_0,esk5_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_64])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk4_0,k3_orders_2(esk3_0,X1,esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_20])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,esk1_2(esk6_0,esk1_2(esk6_0,esk1_2(esk6_0,esk1_2(esk6_0,k3_orders_2(esk3_0,esk7_0,esk4_0)))))),esk6_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_23])).

cnf(c_0_80,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,k3_orders_2(esk3_0,esk6_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_77])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk4_0,k3_orders_2(esk3_0,esk6_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_28]),c_0_45])])).

fof(c_0_82,plain,(
    ! [X12] : r1_tarski(k1_xboole_0,X12) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_83,negated_conjecture,
    ( ~ r1_tarski(esk6_0,esk1_2(esk6_0,esk1_2(esk6_0,esk1_2(esk6_0,esk1_2(esk6_0,esk1_2(esk6_0,k3_orders_2(esk3_0,esk7_0,esk4_0))))))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_79])).

cnf(c_0_84,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_36])).

cnf(c_0_85,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_86,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_84]),c_0_84]),c_0_84]),c_0_84]),c_0_84]),c_0_84]),c_0_85])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:11:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 5.64/5.83  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 5.64/5.83  # and selection function SelectNewComplexAHP.
% 5.64/5.83  #
% 5.64/5.83  # Preprocessing time       : 0.028 s
% 5.64/5.83  # Presaturation interreduction done
% 5.64/5.83  
% 5.64/5.83  # Proof found!
% 5.64/5.83  # SZS status Theorem
% 5.64/5.83  # SZS output start CNFRefutation
% 5.64/5.83  fof(t70_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))=>((((r2_orders_2(X1,X2,X3)&r2_hidden(X2,X4))&r2_hidden(X3,X5))&m1_orders_2(X5,X1,X4))=>r2_hidden(X2,X5))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_orders_2)).
% 5.64/5.83  fof(t64_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_orders_2(X1,X2,X3)=>r1_tarski(k3_orders_2(X1,X4,X2),k3_orders_2(X1,X4,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_orders_2)).
% 5.64/5.83  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.64/5.83  fof(t57_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,k3_orders_2(X1,X4,X3))<=>(r2_orders_2(X1,X2,X3)&r2_hidden(X2,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_orders_2)).
% 5.64/5.83  fof(d15_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((X2!=k1_xboole_0=>(m1_orders_2(X3,X1,X2)<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X1))&r2_hidden(X4,X2))&X3=k3_orders_2(X1,X2,X4))))&(X2=k1_xboole_0=>(m1_orders_2(X3,X1,X2)<=>X3=k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d15_orders_2)).
% 5.64/5.83  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 5.64/5.83  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.64/5.83  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.64/5.83  fof(c_0_8, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))=>((((r2_orders_2(X1,X2,X3)&r2_hidden(X2,X4))&r2_hidden(X3,X5))&m1_orders_2(X5,X1,X4))=>r2_hidden(X2,X5)))))))), inference(assume_negation,[status(cth)],[t70_orders_2])).
% 5.64/5.83  fof(c_0_9, plain, ![X27, X28, X29, X30]:(v2_struct_0(X27)|~v3_orders_2(X27)|~v4_orders_2(X27)|~v5_orders_2(X27)|~l1_orders_2(X27)|(~m1_subset_1(X28,u1_struct_0(X27))|(~m1_subset_1(X29,u1_struct_0(X27))|(~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X27)))|(~r2_orders_2(X27,X28,X29)|r1_tarski(k3_orders_2(X27,X30,X28),k3_orders_2(X27,X30,X29))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t64_orders_2])])])])).
% 5.64/5.83  fof(c_0_10, negated_conjecture, (((((~v2_struct_0(esk3_0)&v3_orders_2(esk3_0))&v4_orders_2(esk3_0))&v5_orders_2(esk3_0))&l1_orders_2(esk3_0))&(m1_subset_1(esk4_0,u1_struct_0(esk3_0))&(m1_subset_1(esk5_0,u1_struct_0(esk3_0))&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&((((r2_orders_2(esk3_0,esk4_0,esk5_0)&r2_hidden(esk4_0,esk6_0))&r2_hidden(esk5_0,esk7_0))&m1_orders_2(esk7_0,esk3_0,esk6_0))&~r2_hidden(esk4_0,esk7_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).
% 5.64/5.83  cnf(c_0_11, plain, (v2_struct_0(X1)|r1_tarski(k3_orders_2(X1,X4,X2),k3_orders_2(X1,X4,X3))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~r2_orders_2(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 5.64/5.83  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 5.64/5.83  cnf(c_0_13, negated_conjecture, (l1_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 5.64/5.83  cnf(c_0_14, negated_conjecture, (v5_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 5.64/5.83  cnf(c_0_15, negated_conjecture, (v4_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 5.64/5.83  cnf(c_0_16, negated_conjecture, (v3_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 5.64/5.83  cnf(c_0_17, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 5.64/5.83  fof(c_0_18, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 5.64/5.83  cnf(c_0_19, negated_conjecture, (r1_tarski(k3_orders_2(esk3_0,X1,X2),k3_orders_2(esk3_0,X1,esk5_0))|~r2_orders_2(esk3_0,X2,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13]), c_0_14]), c_0_15]), c_0_16])]), c_0_17])).
% 5.64/5.83  cnf(c_0_20, negated_conjecture, (r2_orders_2(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 5.64/5.83  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 5.64/5.83  cnf(c_0_22, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 5.64/5.83  cnf(c_0_23, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 5.64/5.83  fof(c_0_24, plain, ![X23, X24, X25, X26]:(((r2_orders_2(X23,X24,X25)|~r2_hidden(X24,k3_orders_2(X23,X26,X25))|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X23)))|~m1_subset_1(X25,u1_struct_0(X23))|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~v3_orders_2(X23)|~v4_orders_2(X23)|~v5_orders_2(X23)|~l1_orders_2(X23)))&(r2_hidden(X24,X26)|~r2_hidden(X24,k3_orders_2(X23,X26,X25))|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X23)))|~m1_subset_1(X25,u1_struct_0(X23))|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~v3_orders_2(X23)|~v4_orders_2(X23)|~v5_orders_2(X23)|~l1_orders_2(X23))))&(~r2_orders_2(X23,X24,X25)|~r2_hidden(X24,X26)|r2_hidden(X24,k3_orders_2(X23,X26,X25))|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X23)))|~m1_subset_1(X25,u1_struct_0(X23))|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~v3_orders_2(X23)|~v4_orders_2(X23)|~v5_orders_2(X23)|~l1_orders_2(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_orders_2])])])])])).
% 5.64/5.83  cnf(c_0_25, negated_conjecture, (r1_tarski(k3_orders_2(esk3_0,X1,esk4_0),k3_orders_2(esk3_0,X1,esk5_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])).
% 5.64/5.83  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 5.64/5.83  cnf(c_0_27, plain, (r2_hidden(esk1_2(X1,X2),X1)|r2_hidden(X3,X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 5.64/5.83  cnf(c_0_28, negated_conjecture, (r2_hidden(esk4_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 5.64/5.83  cnf(c_0_29, plain, (r2_hidden(X1,X2)|v2_struct_0(X3)|~r2_hidden(X1,k3_orders_2(X3,X2,X4))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X4,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~v3_orders_2(X3)|~v4_orders_2(X3)|~v5_orders_2(X3)|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 5.64/5.83  cnf(c_0_30, negated_conjecture, (r1_tarski(k3_orders_2(esk3_0,esk7_0,esk4_0),k3_orders_2(esk3_0,esk7_0,esk5_0))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 5.64/5.83  cnf(c_0_31, negated_conjecture, (r2_hidden(esk1_2(esk6_0,X1),esk6_0)|r2_hidden(esk4_0,X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 5.64/5.83  cnf(c_0_32, negated_conjecture, (r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,k3_orders_2(esk3_0,X2,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_12]), c_0_13]), c_0_14]), c_0_15]), c_0_16])]), c_0_17])).
% 5.64/5.83  cnf(c_0_33, negated_conjecture, (r2_hidden(X1,k3_orders_2(esk3_0,esk7_0,esk5_0))|~r2_hidden(X1,k3_orders_2(esk3_0,esk7_0,esk4_0))), inference(spm,[status(thm)],[c_0_22, c_0_30])).
% 5.64/5.83  cnf(c_0_34, negated_conjecture, (r2_hidden(esk1_2(esk6_0,X1),esk6_0)|r2_hidden(esk1_2(esk6_0,X2),X1)|r2_hidden(esk4_0,X2)), inference(spm,[status(thm)],[c_0_27, c_0_31])).
% 5.64/5.83  cnf(c_0_35, negated_conjecture, (r2_hidden(esk4_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(esk4_0,k3_orders_2(esk3_0,X1,esk5_0))), inference(spm,[status(thm)],[c_0_32, c_0_21])).
% 5.64/5.83  cnf(c_0_36, negated_conjecture, (~r2_hidden(esk4_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 5.64/5.83  fof(c_0_37, plain, ![X18, X19, X20, X22]:(((((m1_subset_1(esk2_3(X18,X19,X20),u1_struct_0(X18))|~m1_orders_2(X20,X18,X19)|X19=k1_xboole_0|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|(v2_struct_0(X18)|~v3_orders_2(X18)|~v4_orders_2(X18)|~v5_orders_2(X18)|~l1_orders_2(X18)))&(r2_hidden(esk2_3(X18,X19,X20),X19)|~m1_orders_2(X20,X18,X19)|X19=k1_xboole_0|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|(v2_struct_0(X18)|~v3_orders_2(X18)|~v4_orders_2(X18)|~v5_orders_2(X18)|~l1_orders_2(X18))))&(X20=k3_orders_2(X18,X19,esk2_3(X18,X19,X20))|~m1_orders_2(X20,X18,X19)|X19=k1_xboole_0|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|(v2_struct_0(X18)|~v3_orders_2(X18)|~v4_orders_2(X18)|~v5_orders_2(X18)|~l1_orders_2(X18))))&(~m1_subset_1(X22,u1_struct_0(X18))|~r2_hidden(X22,X19)|X20!=k3_orders_2(X18,X19,X22)|m1_orders_2(X20,X18,X19)|X19=k1_xboole_0|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|(v2_struct_0(X18)|~v3_orders_2(X18)|~v4_orders_2(X18)|~v5_orders_2(X18)|~l1_orders_2(X18))))&((~m1_orders_2(X20,X18,X19)|X20=k1_xboole_0|X19!=k1_xboole_0|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|(v2_struct_0(X18)|~v3_orders_2(X18)|~v4_orders_2(X18)|~v5_orders_2(X18)|~l1_orders_2(X18)))&(X20!=k1_xboole_0|m1_orders_2(X20,X18,X19)|X19!=k1_xboole_0|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|(v2_struct_0(X18)|~v3_orders_2(X18)|~v4_orders_2(X18)|~v5_orders_2(X18)|~l1_orders_2(X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d15_orders_2])])])])])])).
% 5.64/5.83  cnf(c_0_38, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 5.64/5.83  cnf(c_0_39, negated_conjecture, (r2_hidden(esk1_2(esk6_0,k3_orders_2(esk3_0,esk7_0,esk4_0)),esk6_0)|r2_hidden(esk1_2(esk6_0,X1),k3_orders_2(esk3_0,esk7_0,esk5_0))|r2_hidden(esk4_0,X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 5.64/5.83  cnf(c_0_40, negated_conjecture, (~r2_hidden(esk4_0,k3_orders_2(esk3_0,esk7_0,esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_26]), c_0_36])).
% 5.64/5.83  fof(c_0_41, plain, ![X13, X14, X15]:(~r2_hidden(X13,X14)|~m1_subset_1(X14,k1_zfmisc_1(X15))|m1_subset_1(X13,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 5.64/5.83  cnf(c_0_42, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|X2=k1_xboole_0|v2_struct_0(X1)|~m1_orders_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 5.64/5.83  cnf(c_0_43, negated_conjecture, (r2_hidden(esk1_2(esk6_0,k3_orders_2(esk3_0,esk7_0,esk4_0)),esk6_0)|r1_tarski(esk6_0,k3_orders_2(esk3_0,esk7_0,esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])).
% 5.64/5.83  cnf(c_0_44, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 5.64/5.83  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 5.64/5.83  cnf(c_0_46, negated_conjecture, (X1=k1_xboole_0|r2_hidden(esk2_3(esk3_0,X1,esk7_0),X1)|~m1_orders_2(esk7_0,esk3_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_26]), c_0_13]), c_0_14]), c_0_15]), c_0_16])]), c_0_17])).
% 5.64/5.83  cnf(c_0_47, negated_conjecture, (m1_orders_2(esk7_0,esk3_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 5.64/5.83  fof(c_0_48, plain, ![X16, X17]:(~r2_hidden(X16,X17)|~r1_tarski(X17,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 5.64/5.83  cnf(c_0_49, negated_conjecture, (r2_hidden(esk1_2(esk6_0,k3_orders_2(esk3_0,esk7_0,esk4_0)),esk6_0)|r2_hidden(X1,k3_orders_2(esk3_0,esk7_0,esk5_0))|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_22, c_0_43])).
% 5.64/5.83  cnf(c_0_50, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 5.64/5.83  cnf(c_0_51, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk2_3(esk3_0,esk6_0,esk7_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_45])])).
% 5.64/5.83  cnf(c_0_52, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 5.64/5.83  cnf(c_0_53, negated_conjecture, (r2_hidden(esk1_2(esk6_0,k3_orders_2(esk3_0,esk7_0,esk4_0)),esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_28]), c_0_40])).
% 5.64/5.83  cnf(c_0_54, plain, (r2_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r2_hidden(X2,k3_orders_2(X1,X4,X3))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 5.64/5.83  cnf(c_0_55, negated_conjecture, (esk6_0=k1_xboole_0|m1_subset_1(esk2_3(esk3_0,esk6_0,esk7_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 5.64/5.83  cnf(c_0_56, negated_conjecture, (~r1_tarski(esk6_0,esk1_2(esk6_0,k3_orders_2(esk3_0,esk7_0,esk4_0)))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 5.64/5.83  cnf(c_0_57, negated_conjecture, (esk6_0=k1_xboole_0|r2_orders_2(esk3_0,X1,esk2_3(esk3_0,esk6_0,esk7_0))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,k3_orders_2(esk3_0,X2,esk2_3(esk3_0,esk6_0,esk7_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_13]), c_0_14]), c_0_15]), c_0_16])]), c_0_17])).
% 5.64/5.83  cnf(c_0_58, plain, (X1=k3_orders_2(X2,X3,esk2_3(X2,X3,X1))|X3=k1_xboole_0|v2_struct_0(X2)|~m1_orders_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 5.64/5.83  cnf(c_0_59, negated_conjecture, (r2_hidden(esk1_2(esk6_0,esk1_2(esk6_0,k3_orders_2(esk3_0,esk7_0,esk4_0))),esk6_0)), inference(spm,[status(thm)],[c_0_56, c_0_23])).
% 5.64/5.83  cnf(c_0_60, negated_conjecture, (esk6_0=k1_xboole_0|r2_orders_2(esk3_0,esk5_0,esk2_3(esk3_0,esk6_0,esk7_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(esk5_0,k3_orders_2(esk3_0,X1,esk2_3(esk3_0,esk6_0,esk7_0)))), inference(spm,[status(thm)],[c_0_57, c_0_12])).
% 5.64/5.83  cnf(c_0_61, negated_conjecture, (k3_orders_2(esk3_0,esk6_0,esk2_3(esk3_0,esk6_0,X1))=X1|esk6_0=k1_xboole_0|~m1_orders_2(X1,esk3_0,esk6_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_45]), c_0_13]), c_0_14]), c_0_15]), c_0_16])]), c_0_17])).
% 5.64/5.83  cnf(c_0_62, negated_conjecture, (~r1_tarski(esk6_0,esk1_2(esk6_0,esk1_2(esk6_0,k3_orders_2(esk3_0,esk7_0,esk4_0))))), inference(spm,[status(thm)],[c_0_52, c_0_59])).
% 5.64/5.83  cnf(c_0_63, negated_conjecture, (esk6_0=k1_xboole_0|r2_orders_2(esk3_0,esk5_0,esk2_3(esk3_0,esk6_0,esk7_0))|~r2_hidden(esk5_0,k3_orders_2(esk3_0,esk6_0,esk2_3(esk3_0,esk6_0,esk7_0)))), inference(spm,[status(thm)],[c_0_60, c_0_45])).
% 5.64/5.83  cnf(c_0_64, negated_conjecture, (k3_orders_2(esk3_0,esk6_0,esk2_3(esk3_0,esk6_0,esk7_0))=esk7_0|esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_47]), c_0_26])])).
% 5.64/5.83  cnf(c_0_65, negated_conjecture, (r2_hidden(esk5_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 5.64/5.83  cnf(c_0_66, negated_conjecture, (r2_hidden(esk1_2(esk6_0,esk1_2(esk6_0,esk1_2(esk6_0,k3_orders_2(esk3_0,esk7_0,esk4_0)))),esk6_0)), inference(spm,[status(thm)],[c_0_62, c_0_23])).
% 5.64/5.83  cnf(c_0_67, negated_conjecture, (esk6_0=k1_xboole_0|r1_tarski(k3_orders_2(esk3_0,X1,X2),k3_orders_2(esk3_0,X1,esk2_3(esk3_0,esk6_0,esk7_0)))|~r2_orders_2(esk3_0,X2,esk2_3(esk3_0,esk6_0,esk7_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_55]), c_0_13]), c_0_14]), c_0_15]), c_0_16])]), c_0_17])).
% 5.64/5.83  cnf(c_0_68, negated_conjecture, (esk6_0=k1_xboole_0|r2_orders_2(esk3_0,esk5_0,esk2_3(esk3_0,esk6_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65])])).
% 5.64/5.83  cnf(c_0_69, plain, (r2_hidden(X2,k3_orders_2(X1,X4,X3))|v2_struct_0(X1)|~r2_orders_2(X1,X2,X3)|~r2_hidden(X2,X4)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 5.64/5.83  cnf(c_0_70, negated_conjecture, (~r1_tarski(esk6_0,esk1_2(esk6_0,esk1_2(esk6_0,esk1_2(esk6_0,k3_orders_2(esk3_0,esk7_0,esk4_0)))))), inference(spm,[status(thm)],[c_0_52, c_0_66])).
% 5.64/5.83  cnf(c_0_71, negated_conjecture, (esk6_0=k1_xboole_0|r1_tarski(k3_orders_2(esk3_0,X1,esk5_0),k3_orders_2(esk3_0,X1,esk2_3(esk3_0,esk6_0,esk7_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_12]), c_0_68])).
% 5.64/5.83  cnf(c_0_72, plain, (v2_struct_0(X1)|r2_hidden(X2,k3_orders_2(X1,X3,X4))|~r2_orders_2(X1,X2,X4)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X2,X3)), inference(csr,[status(thm)],[c_0_69, c_0_44])).
% 5.64/5.83  cnf(c_0_73, negated_conjecture, (r2_hidden(esk1_2(esk6_0,esk1_2(esk6_0,esk1_2(esk6_0,esk1_2(esk6_0,k3_orders_2(esk3_0,esk7_0,esk4_0))))),esk6_0)), inference(spm,[status(thm)],[c_0_70, c_0_23])).
% 5.64/5.83  cnf(c_0_74, negated_conjecture, (esk6_0=k1_xboole_0|r1_tarski(k3_orders_2(esk3_0,esk6_0,esk5_0),k3_orders_2(esk3_0,esk6_0,esk2_3(esk3_0,esk6_0,esk7_0)))), inference(spm,[status(thm)],[c_0_71, c_0_45])).
% 5.64/5.83  cnf(c_0_75, negated_conjecture, (r2_hidden(X1,k3_orders_2(esk3_0,X2,esk5_0))|~r2_orders_2(esk3_0,X1,esk5_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(X1,X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_12]), c_0_13]), c_0_14]), c_0_15]), c_0_16])]), c_0_17])).
% 5.64/5.83  cnf(c_0_76, negated_conjecture, (~r1_tarski(esk6_0,esk1_2(esk6_0,esk1_2(esk6_0,esk1_2(esk6_0,esk1_2(esk6_0,k3_orders_2(esk3_0,esk7_0,esk4_0))))))), inference(spm,[status(thm)],[c_0_52, c_0_73])).
% 5.64/5.83  cnf(c_0_77, negated_conjecture, (esk6_0=k1_xboole_0|r1_tarski(k3_orders_2(esk3_0,esk6_0,esk5_0),esk7_0)), inference(spm,[status(thm)],[c_0_74, c_0_64])).
% 5.64/5.83  cnf(c_0_78, negated_conjecture, (r2_hidden(esk4_0,k3_orders_2(esk3_0,X1,esk5_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(esk4_0,X1)), inference(spm,[status(thm)],[c_0_75, c_0_20])).
% 5.64/5.83  cnf(c_0_79, negated_conjecture, (r2_hidden(esk1_2(esk6_0,esk1_2(esk6_0,esk1_2(esk6_0,esk1_2(esk6_0,esk1_2(esk6_0,k3_orders_2(esk3_0,esk7_0,esk4_0)))))),esk6_0)), inference(spm,[status(thm)],[c_0_76, c_0_23])).
% 5.64/5.83  cnf(c_0_80, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(X1,esk7_0)|~r2_hidden(X1,k3_orders_2(esk3_0,esk6_0,esk5_0))), inference(spm,[status(thm)],[c_0_22, c_0_77])).
% 5.64/5.83  cnf(c_0_81, negated_conjecture, (r2_hidden(esk4_0,k3_orders_2(esk3_0,esk6_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_28]), c_0_45])])).
% 5.64/5.83  fof(c_0_82, plain, ![X12]:r1_tarski(k1_xboole_0,X12), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 5.64/5.83  cnf(c_0_83, negated_conjecture, (~r1_tarski(esk6_0,esk1_2(esk6_0,esk1_2(esk6_0,esk1_2(esk6_0,esk1_2(esk6_0,esk1_2(esk6_0,k3_orders_2(esk3_0,esk7_0,esk4_0)))))))), inference(spm,[status(thm)],[c_0_52, c_0_79])).
% 5.64/5.83  cnf(c_0_84, negated_conjecture, (esk6_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_36])).
% 5.64/5.83  cnf(c_0_85, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 5.64/5.83  cnf(c_0_86, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_84]), c_0_84]), c_0_84]), c_0_84]), c_0_84]), c_0_84]), c_0_85])]), ['proof']).
% 5.64/5.83  # SZS output end CNFRefutation
% 5.64/5.83  # Proof object total steps             : 87
% 5.64/5.83  # Proof object clause steps            : 70
% 5.64/5.83  # Proof object formula steps           : 17
% 5.64/5.83  # Proof object conjectures             : 59
% 5.64/5.83  # Proof object clause conjectures      : 56
% 5.64/5.83  # Proof object formula conjectures     : 3
% 5.64/5.83  # Proof object initial clauses used    : 26
% 5.64/5.83  # Proof object initial formulas used   : 8
% 5.64/5.83  # Proof object generating inferences   : 42
% 5.64/5.83  # Proof object simplifying inferences  : 66
% 5.64/5.83  # Training examples: 0 positive, 0 negative
% 5.64/5.83  # Parsed axioms                        : 8
% 5.64/5.83  # Removed by relevancy pruning/SinE    : 0
% 5.64/5.83  # Initial clauses                      : 30
% 5.64/5.83  # Removed in clause preprocessing      : 0
% 5.64/5.83  # Initial clauses in saturation        : 30
% 5.64/5.83  # Processed clauses                    : 18209
% 5.64/5.83  # ...of these trivial                  : 188
% 5.64/5.83  # ...subsumed                          : 4737
% 5.64/5.83  # ...remaining for further processing  : 13284
% 5.64/5.83  # Other redundant clauses eliminated   : 4
% 5.64/5.83  # Clauses deleted for lack of memory   : 0
% 5.64/5.83  # Backward-subsumed                    : 383
% 5.64/5.83  # Backward-rewritten                   : 11936
% 5.64/5.83  # Generated clauses                    : 264377
% 5.64/5.83  # ...of the previous two non-trivial   : 241998
% 5.64/5.83  # Contextual simplify-reflections      : 16
% 5.64/5.83  # Paramodulations                      : 264274
% 5.64/5.83  # Factorizations                       : 100
% 5.64/5.83  # Equation resolutions                 : 4
% 5.64/5.83  # Propositional unsat checks           : 0
% 5.64/5.83  #    Propositional check models        : 0
% 5.64/5.83  #    Propositional check unsatisfiable : 0
% 5.64/5.83  #    Propositional clauses             : 0
% 5.64/5.83  #    Propositional clauses after purity: 0
% 5.64/5.83  #    Propositional unsat core size     : 0
% 5.64/5.83  #    Propositional preprocessing time  : 0.000
% 5.64/5.83  #    Propositional encoding time       : 0.000
% 5.64/5.83  #    Propositional solver time         : 0.000
% 5.64/5.83  #    Success case prop preproc time    : 0.000
% 5.64/5.83  #    Success case prop encoding time   : 0.000
% 5.64/5.83  #    Success case prop solver time     : 0.000
% 5.64/5.83  # Current number of processed clauses  : 932
% 5.64/5.83  #    Positive orientable unit clauses  : 35
% 5.64/5.83  #    Positive unorientable unit clauses: 0
% 5.64/5.83  #    Negative unit clauses             : 28
% 5.64/5.83  #    Non-unit-clauses                  : 869
% 5.64/5.83  # Current number of unprocessed clauses: 222899
% 5.64/5.83  # ...number of literals in the above   : 825425
% 5.64/5.83  # Current number of archived formulas  : 0
% 5.64/5.83  # Current number of archived clauses   : 12349
% 5.64/5.83  # Clause-clause subsumption calls (NU) : 10669115
% 5.64/5.83  # Rec. Clause-clause subsumption calls : 6289712
% 5.64/5.83  # Non-unit clause-clause subsumptions  : 5052
% 5.64/5.83  # Unit Clause-clause subsumption calls : 49957
% 5.64/5.83  # Rewrite failures with RHS unbound    : 0
% 5.64/5.83  # BW rewrite match attempts            : 4452
% 5.64/5.83  # BW rewrite match successes           : 43
% 5.64/5.83  # Condensation attempts                : 0
% 5.64/5.83  # Condensation successes               : 0
% 5.64/5.83  # Termbank termtop insertions          : 7637801
% 5.67/5.84  
% 5.67/5.84  # -------------------------------------------------
% 5.67/5.84  # User time                : 5.396 s
% 5.67/5.84  # System time              : 0.096 s
% 5.67/5.84  # Total time               : 5.491 s
% 5.67/5.84  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
