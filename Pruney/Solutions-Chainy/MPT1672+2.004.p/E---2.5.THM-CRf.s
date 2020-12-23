%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:26 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :  197 (21852410 expanded)
%              Number of clauses        :  170 (7123295 expanded)
%              Number of leaves         :   13 (7324185 expanded)
%              Depth                    :   52
%              Number of atoms          :  857 (224904979 expanded)
%              Number of equality atoms :  222 (19346047 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   30 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t52_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( ! [X4] :
                      ( ( v1_finset_1(X4)
                        & m1_subset_1(X4,k1_zfmisc_1(X2)) )
                     => ( X4 != k1_xboole_0
                       => r1_yellow_0(X1,X4) ) )
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ~ ( r2_hidden(X4,X3)
                          & ! [X5] :
                              ( ( v1_finset_1(X5)
                                & m1_subset_1(X5,k1_zfmisc_1(X2)) )
                             => ~ ( r1_yellow_0(X1,X5)
                                  & X4 = k1_yellow_0(X1,X5) ) ) ) )
                  & ! [X4] :
                      ( ( v1_finset_1(X4)
                        & m1_subset_1(X4,k1_zfmisc_1(X2)) )
                     => ( X4 != k1_xboole_0
                       => r2_hidden(k1_yellow_0(X1,X4),X3) ) ) )
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r2_lattice3(X1,X2,X4)
                    <=> r2_lattice3(X1,X3,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_waybel_0)).

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

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(reflexivity_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => r3_orders_2(X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

fof(redefinition_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_orders_2(X1,X2,X3)
      <=> r1_orders_2(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(fc1_finset_1,axiom,(
    ! [X1] : v1_finset_1(k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_finset_1)).

fof(t7_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ( r1_lattice3(X1,k1_tarski(X3),X2)
                 => r1_orders_2(X1,X2,X3) )
                & ( r1_orders_2(X1,X2,X3)
                 => r1_lattice3(X1,k1_tarski(X3),X2) )
                & ( r2_lattice3(X1,k1_tarski(X3),X2)
                 => r1_orders_2(X1,X3,X2) )
                & ( r1_orders_2(X1,X3,X2)
                 => r2_lattice3(X1,k1_tarski(X3),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_0)).

fof(d9_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r1_yellow_0(X1,X2)
           => ( X3 = k1_yellow_0(X1,X2)
            <=> ( r2_lattice3(X1,X2,X3)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r2_lattice3(X1,X2,X4)
                     => r1_orders_2(X1,X3,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).

fof(t9_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( r1_tarski(X2,X3)
         => ! [X4] :
              ( m1_subset_1(X4,u1_struct_0(X1))
             => ( ( r1_lattice3(X1,X3,X4)
                 => r1_lattice3(X1,X2,X4) )
                & ( r2_lattice3(X1,X3,X4)
                 => r2_lattice3(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_0)).

fof(fc2_xboole_0,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_12,plain,(
    ! [X1,X2,X3] :
      ( epred1_3(X3,X2,X1)
    <=> ( ! [X4] :
            ( ( v1_finset_1(X4)
              & m1_subset_1(X4,k1_zfmisc_1(X2)) )
           => ( X4 != k1_xboole_0
             => r1_yellow_0(X1,X4) ) )
        & ! [X4] :
            ( m1_subset_1(X4,u1_struct_0(X1))
           => ~ ( r2_hidden(X4,X3)
                & ! [X5] :
                    ( ( v1_finset_1(X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X2)) )
                   => ~ ( r1_yellow_0(X1,X5)
                        & X4 = k1_yellow_0(X1,X5) ) ) ) )
        & ! [X4] :
            ( ( v1_finset_1(X4)
              & m1_subset_1(X4,k1_zfmisc_1(X2)) )
           => ( X4 != k1_xboole_0
             => r2_hidden(k1_yellow_0(X1,X4),X3) ) ) ) ) ),
    introduced(definition)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( epred1_3(X3,X2,X1)
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r2_lattice3(X1,X2,X4)
                      <=> r2_lattice3(X1,X3,X4) ) ) ) ) ) ) ),
    inference(apply_def,[status(thm)],[inference(assume_negation,[status(cth)],[t52_waybel_0]),c_0_12])).

fof(c_0_14,plain,(
    ! [X18,X19,X20,X21] :
      ( ( ~ r2_lattice3(X18,X19,X20)
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ r2_hidden(X21,X19)
        | r1_orders_2(X18,X21,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ l1_orders_2(X18) )
      & ( m1_subset_1(esk1_3(X18,X19,X20),u1_struct_0(X18))
        | r2_lattice3(X18,X19,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ l1_orders_2(X18) )
      & ( r2_hidden(esk1_3(X18,X19,X20),X19)
        | r2_lattice3(X18,X19,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ l1_orders_2(X18) )
      & ( ~ r1_orders_2(X18,esk1_3(X18,X19,X20),X20)
        | r2_lattice3(X18,X19,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ l1_orders_2(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

fof(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v3_orders_2(esk3_0)
    & v4_orders_2(esk3_0)
    & l1_orders_2(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & epred1_3(esk5_0,esk4_0,esk3_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk3_0))
    & ( ~ r2_lattice3(esk3_0,esk4_0,esk6_0)
      | ~ r2_lattice3(esk3_0,esk5_0,esk6_0) )
    & ( r2_lattice3(esk3_0,esk4_0,esk6_0)
      | r2_lattice3(esk3_0,esk5_0,esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_16,plain,(
    ! [X7,X8] :
      ( ( ~ r1_tarski(k1_tarski(X7),X8)
        | r2_hidden(X7,X8) )
      & ( ~ r2_hidden(X7,X8)
        | r1_tarski(k1_tarski(X7),X8) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

cnf(c_0_17,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X9,X10] :
      ( ( ~ m1_subset_1(X9,k1_zfmisc_1(X10))
        | r1_tarski(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | m1_subset_1(X9,k1_zfmisc_1(X10)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_21,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | r2_hidden(esk1_3(esk3_0,X1,esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

cnf(c_0_23,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | r1_tarski(k1_tarski(esk1_3(esk3_0,X1,esk6_0)),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( ~ r2_lattice3(esk3_0,esk4_0,esk6_0)
    | ~ r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_18]),c_0_19])])).

fof(c_0_28,plain,(
    ! [X15,X16,X17] :
      ( v2_struct_0(X15)
      | ~ v3_orders_2(X15)
      | ~ l1_orders_2(X15)
      | ~ m1_subset_1(X16,u1_struct_0(X15))
      | ~ m1_subset_1(X17,u1_struct_0(X15))
      | r3_orders_2(X15,X16,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).

fof(c_0_29,plain,(
    ! [X1,X2,X3] :
      ( epred1_3(X3,X2,X1)
     => ( ! [X4] :
            ( ( v1_finset_1(X4)
              & m1_subset_1(X4,k1_zfmisc_1(X2)) )
           => ( X4 != k1_xboole_0
             => r1_yellow_0(X1,X4) ) )
        & ! [X4] :
            ( m1_subset_1(X4,u1_struct_0(X1))
           => ~ ( r2_hidden(X4,X3)
                & ! [X5] :
                    ( ( v1_finset_1(X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X2)) )
                   => ~ ( r1_yellow_0(X1,X5)
                        & X4 = k1_yellow_0(X1,X5) ) ) ) )
        & ! [X4] :
            ( ( v1_finset_1(X4)
              & m1_subset_1(X4,k1_zfmisc_1(X2)) )
           => ( X4 != k1_xboole_0
             => r2_hidden(k1_yellow_0(X1,X4),X3) ) ) ) ) ),
    inference(split_equiv,[status(thm)],[c_0_12])).

cnf(c_0_30,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,X1,esk6_0)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_31,plain,(
    ! [X12,X13,X14] :
      ( ( ~ r3_orders_2(X12,X13,X14)
        | r1_orders_2(X12,X13,X14)
        | v2_struct_0(X12)
        | ~ v3_orders_2(X12)
        | ~ l1_orders_2(X12)
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ m1_subset_1(X14,u1_struct_0(X12)) )
      & ( ~ r1_orders_2(X12,X13,X14)
        | r3_orders_2(X12,X13,X14)
        | v2_struct_0(X12)
        | ~ v3_orders_2(X12)
        | ~ l1_orders_2(X12)
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ m1_subset_1(X14,u1_struct_0(X12)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,plain,
    ( v2_struct_0(X1)
    | r3_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( v3_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_35,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_36,plain,(
    ! [X39,X40,X41,X42,X43,X45] :
      ( ( ~ v1_finset_1(X42)
        | ~ m1_subset_1(X42,k1_zfmisc_1(X40))
        | X42 = k1_xboole_0
        | r1_yellow_0(X39,X42)
        | ~ epred1_3(X41,X40,X39) )
      & ( v1_finset_1(esk7_4(X39,X40,X41,X43))
        | ~ r2_hidden(X43,X41)
        | ~ m1_subset_1(X43,u1_struct_0(X39))
        | ~ epred1_3(X41,X40,X39) )
      & ( m1_subset_1(esk7_4(X39,X40,X41,X43),k1_zfmisc_1(X40))
        | ~ r2_hidden(X43,X41)
        | ~ m1_subset_1(X43,u1_struct_0(X39))
        | ~ epred1_3(X41,X40,X39) )
      & ( r1_yellow_0(X39,esk7_4(X39,X40,X41,X43))
        | ~ r2_hidden(X43,X41)
        | ~ m1_subset_1(X43,u1_struct_0(X39))
        | ~ epred1_3(X41,X40,X39) )
      & ( X43 = k1_yellow_0(X39,esk7_4(X39,X40,X41,X43))
        | ~ r2_hidden(X43,X41)
        | ~ m1_subset_1(X43,u1_struct_0(X39))
        | ~ epred1_3(X41,X40,X39) )
      & ( ~ v1_finset_1(X45)
        | ~ m1_subset_1(X45,k1_zfmisc_1(X40))
        | X45 = k1_xboole_0
        | r2_hidden(k1_yellow_0(X39,X45),X41)
        | ~ epred1_3(X41,X40,X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])])])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | ~ r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_30])).

fof(c_0_38,plain,(
    ! [X11] : v1_finset_1(k1_tarski(X11)) ),
    inference(variable_rename,[status(thm)],[fc1_finset_1])).

fof(c_0_39,plain,(
    ! [X28,X29,X30] :
      ( ( ~ r1_lattice3(X28,k1_tarski(X30),X29)
        | r1_orders_2(X28,X29,X30)
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | ~ l1_orders_2(X28) )
      & ( ~ r1_orders_2(X28,X29,X30)
        | r1_lattice3(X28,k1_tarski(X30),X29)
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | ~ l1_orders_2(X28) )
      & ( ~ r2_lattice3(X28,k1_tarski(X30),X29)
        | r1_orders_2(X28,X30,X29)
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | ~ l1_orders_2(X28) )
      & ( ~ r1_orders_2(X28,X30,X29)
        | r2_lattice3(X28,k1_tarski(X30),X29)
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | ~ l1_orders_2(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_yellow_0])])])])).

cnf(c_0_40,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_27])).

cnf(c_0_42,negated_conjecture,
    ( r3_orders_2(esk3_0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_18]),c_0_19]),c_0_34])]),c_0_35])).

fof(c_0_43,plain,(
    ! [X23,X24,X25,X26] :
      ( ( r2_lattice3(X23,X24,X25)
        | X25 != k1_yellow_0(X23,X24)
        | ~ r1_yellow_0(X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ l1_orders_2(X23) )
      & ( ~ m1_subset_1(X26,u1_struct_0(X23))
        | ~ r2_lattice3(X23,X24,X26)
        | r1_orders_2(X23,X25,X26)
        | X25 != k1_yellow_0(X23,X24)
        | ~ r1_yellow_0(X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ l1_orders_2(X23) )
      & ( m1_subset_1(esk2_3(X23,X24,X25),u1_struct_0(X23))
        | ~ r2_lattice3(X23,X24,X25)
        | X25 = k1_yellow_0(X23,X24)
        | ~ r1_yellow_0(X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ l1_orders_2(X23) )
      & ( r2_lattice3(X23,X24,esk2_3(X23,X24,X25))
        | ~ r2_lattice3(X23,X24,X25)
        | X25 = k1_yellow_0(X23,X24)
        | ~ r1_yellow_0(X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ l1_orders_2(X23) )
      & ( ~ r1_orders_2(X23,X25,esk2_3(X23,X24,X25))
        | ~ r2_lattice3(X23,X24,X25)
        | X25 = k1_yellow_0(X23,X24)
        | ~ r1_yellow_0(X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ l1_orders_2(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).

cnf(c_0_44,plain,
    ( X1 = k1_xboole_0
    | r1_yellow_0(X3,X1)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ epred1_3(X4,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_27])).

cnf(c_0_46,plain,
    ( v1_finset_1(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,plain,
    ( r2_lattice3(X1,k1_tarski(X2),X3)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r3_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_19]),c_0_34])]),c_0_35])).

cnf(c_0_49,negated_conjecture,
    ( r3_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_41])).

cnf(c_0_50,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | X3 = k1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,plain,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ epred1_3(X2,esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])])).

cnf(c_0_52,negated_conjecture,
    ( epred1_3(esk5_0,esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_53,negated_conjecture,
    ( r2_lattice3(esk3_0,k1_tarski(X1),esk1_3(esk3_0,esk4_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_41]),c_0_19])])).

cnf(c_0_54,negated_conjecture,
    ( r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_41]),c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( esk1_3(esk3_0,esk4_0,esk6_0) = k1_yellow_0(esk3_0,X1)
    | m1_subset_1(esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_yellow_0(esk3_0,X1)
    | ~ r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_41]),c_0_19])])).

cnf(c_0_56,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_41]),c_0_54])).

cnf(c_0_58,plain,
    ( r2_lattice3(X1,X2,esk2_3(X1,X2,X3))
    | X3 = k1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_59,plain,
    ( X2 = k1_yellow_0(X1,X3)
    | ~ r1_orders_2(X1,X2,esk2_3(X1,X3,X2))
    | ~ r2_lattice3(X1,X3,X2)
    | ~ r1_yellow_0(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_60,plain,
    ( r1_orders_2(X1,X2,X3)
    | ~ r2_lattice3(X1,k1_tarski(X2),X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_61,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( esk1_3(esk3_0,esk4_0,esk6_0) = k1_yellow_0(esk3_0,X1)
    | r2_lattice3(esk3_0,X1,esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_yellow_0(esk3_0,X1)
    | ~ r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_41]),c_0_19])])).

cnf(c_0_63,negated_conjecture,
    ( esk1_3(esk3_0,esk4_0,esk6_0) = k1_yellow_0(esk3_0,X1)
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_yellow_0(esk3_0,X1)
    | ~ r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_41]),c_0_19])])).

cnf(c_0_64,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,X1,esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r2_lattice3(esk3_0,k1_tarski(X1),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_19])])).

cnf(c_0_65,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_56]),c_0_57])).

cnf(c_0_66,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_56]),c_0_57])).

cnf(c_0_67,plain,
    ( X1 = k1_yellow_0(X2,esk7_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ epred1_3(X4,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_68,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_41]),c_0_65]),c_0_66])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_30])).

cnf(c_0_71,plain,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | ~ epred1_3(X2,X1,esk3_0)
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_72,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))
    | r1_tarski(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_52])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))
    | r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_76,plain,
    ( m1_subset_1(esk7_4(X1,X2,X3,X4),k1_zfmisc_1(X2))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_77,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_22])).

cnf(c_0_78,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_79,plain,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(X1))
    | ~ epred1_3(X2,X1,esk3_0)
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2) ),
    inference(spm,[status(thm)],[c_0_76,c_0_68])).

cnf(c_0_80,plain,
    ( r1_yellow_0(X1,esk7_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_81,plain,(
    ! [X31,X32,X33,X34] :
      ( ( ~ r1_lattice3(X31,X33,X34)
        | r1_lattice3(X31,X32,X34)
        | ~ m1_subset_1(X34,u1_struct_0(X31))
        | ~ r1_tarski(X32,X33)
        | ~ l1_orders_2(X31) )
      & ( ~ r2_lattice3(X31,X33,X34)
        | r2_lattice3(X31,X32,X34)
        | ~ m1_subset_1(X34,u1_struct_0(X31))
        | ~ r1_tarski(X32,X33)
        | ~ l1_orders_2(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_yellow_0])])])])).

cnf(c_0_82,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_77])).

cnf(c_0_83,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ r3_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_78]),c_0_19]),c_0_34])]),c_0_35])).

cnf(c_0_84,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r3_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_78])).

cnf(c_0_85,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_52])).

cnf(c_0_86,plain,
    ( r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | X4 != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_87,plain,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)))
    | ~ epred1_3(X2,X1,esk3_0)
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2) ),
    inference(spm,[status(thm)],[c_0_80,c_0_68])).

cnf(c_0_88,plain,
    ( r2_lattice3(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_tarski(X4,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_89,plain,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))
    | ~ epred1_3(X2,esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_82]),c_0_46])])).

cnf(c_0_90,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,k1_tarski(X1),esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_78]),c_0_19])])).

cnf(c_0_91,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_78]),c_0_84])).

cnf(c_0_92,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk5_0,esk6_0)
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_22])).

cnf(c_0_93,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_86])).

cnf(c_0_94,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_52])).

cnf(c_0_95,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | ~ r2_lattice3(esk3_0,X2,esk6_0)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_18]),c_0_19])])).

cnf(c_0_96,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_75])).

cnf(c_0_97,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | esk1_3(esk3_0,esk4_0,esk6_0) = k1_yellow_0(esk3_0,X1)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0))
    | ~ r1_yellow_0(esk3_0,X1)
    | ~ r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_78]),c_0_19])])).

cnf(c_0_98,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_52])).

cnf(c_0_99,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_78]),c_0_91])).

cnf(c_0_100,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_92])).

cnf(c_0_101,negated_conjecture,
    ( r1_orders_2(esk3_0,k1_yellow_0(esk3_0,X1),esk6_0)
    | ~ r1_yellow_0(esk3_0,X1)
    | ~ r2_lattice3(esk3_0,X1,esk6_0)
    | ~ m1_subset_1(k1_yellow_0(esk3_0,X1),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_18]),c_0_19])])).

cnf(c_0_102,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))
    | r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_22])).

cnf(c_0_103,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,X2,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_95,c_0_27])).

cnf(c_0_104,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))
    | r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_96])).

cnf(c_0_105,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_99])).

cnf(c_0_106,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | esk1_3(esk3_0,esk4_0,esk6_0) = k1_yellow_0(esk3_0,X1)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,X1,esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)))
    | ~ r1_yellow_0(esk3_0,X1)
    | ~ r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_78]),c_0_19])])).

cnf(c_0_107,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | esk1_3(esk3_0,esk4_0,esk6_0) = k1_yellow_0(esk3_0,X1)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | ~ r1_yellow_0(esk3_0,X1)
    | ~ r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_78]),c_0_19])])).

cnf(c_0_108,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,X2,esk6_0)),k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_95,c_0_30])).

cnf(c_0_109,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_100])).

cnf(c_0_110,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk5_0,esk6_0)
    | r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)
    | ~ r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)
    | ~ m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_111,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_112,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,X1,esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))
    | ~ r2_lattice3(esk3_0,k1_tarski(X1),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_105]),c_0_19])])).

cnf(c_0_113,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_98]),c_0_99])).

cnf(c_0_114,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | ~ r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_98]),c_0_99])).

cnf(c_0_115,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_116,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk1_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_117,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))
    | ~ m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_32])).

cnf(c_0_118,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_78]),c_0_113]),c_0_114])).

cnf(c_0_119,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | ~ m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_115]),c_0_37])).

cnf(c_0_120,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | ~ r1_orders_2(esk3_0,esk1_3(esk3_0,X1,esk6_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_18]),c_0_19])])).

cnf(c_0_121,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk1_3(esk3_0,esk5_0,esk6_0),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_118]),c_0_41])).

cnf(c_0_122,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk1_3(esk3_0,esk5_0,esk6_0),esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_118]),c_0_45])).

cnf(c_0_123,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_121]),c_0_32])).

cnf(c_0_124,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_122]),c_0_37])).

cnf(c_0_125,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ r3_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_123]),c_0_19]),c_0_34])]),c_0_35])).

cnf(c_0_126,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r3_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_123])).

cnf(c_0_127,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(k1_yellow_0(X3,X1),X4)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ epred1_3(X4,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_128,negated_conjecture,
    ( m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_30])).

cnf(c_0_129,plain,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))
    | ~ epred1_3(X2,esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_124]),c_0_46])])).

cnf(c_0_130,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,k1_tarski(X1),esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_123]),c_0_19])])).

cnf(c_0_131,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_123]),c_0_126])).

cnf(c_0_132,plain,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))
    | r2_hidden(k1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)
    | ~ epred1_3(X2,esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_128]),c_0_46])])).

cnf(c_0_133,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | esk1_3(esk3_0,esk4_0,esk6_0) = k1_yellow_0(esk3_0,X1)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0))
    | ~ r1_yellow_0(esk3_0,X1)
    | ~ r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_123]),c_0_19])])).

cnf(c_0_134,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_129,c_0_52])).

cnf(c_0_135,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_123]),c_0_131])).

cnf(c_0_136,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))
    | r2_hidden(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_132,c_0_52])).

cnf(c_0_137,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_134]),c_0_135])).

cnf(c_0_138,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | esk1_3(esk3_0,esk4_0,esk6_0) = k1_yellow_0(esk3_0,X1)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,X1,esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)))
    | ~ r1_yellow_0(esk3_0,X1)
    | ~ r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_123]),c_0_19])])).

cnf(c_0_139,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | esk1_3(esk3_0,esk4_0,esk6_0) = k1_yellow_0(esk3_0,X1)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | ~ r1_yellow_0(esk3_0,X1)
    | ~ r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_123]),c_0_19])])).

cnf(c_0_140,plain,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))
    | ~ epred1_3(X2,esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_128]),c_0_46])])).

cnf(c_0_141,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))
    | r1_tarski(k1_tarski(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_136])).

cnf(c_0_142,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,X1,esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))
    | ~ r2_lattice3(esk3_0,k1_tarski(X1),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_137]),c_0_19])])).

cnf(c_0_143,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_134]),c_0_135])).

cnf(c_0_144,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | ~ r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_134]),c_0_135])).

cnf(c_0_145,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_146,plain,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | r2_hidden(k1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)
    | ~ epred1_3(X2,esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_45]),c_0_46])])).

cnf(c_0_147,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_140,c_0_52])).

cnf(c_0_148,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,k1_tarski(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))),esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_108,c_0_141])).

cnf(c_0_149,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_123]),c_0_143]),c_0_144])).

cnf(c_0_150,negated_conjecture,
    ( r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),X1)
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r2_lattice3(esk3_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_41]),c_0_19])])).

cnf(c_0_151,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | r2_hidden(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_146,c_0_52])).

cnf(c_0_152,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))
    | ~ r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0)
    | ~ m1_subset_1(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_101,c_0_147])).

cnf(c_0_153,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_148,c_0_149])).

cnf(c_0_154,negated_conjecture,
    ( r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0))
    | ~ r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150,c_0_27]),c_0_18])])).

cnf(c_0_155,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_151,c_0_149])).

cnf(c_0_156,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))
    | ~ m1_subset_1(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_152,c_0_153])).

cnf(c_0_157,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_154,c_0_155])).

cnf(c_0_158,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_156,c_0_149]),c_0_70])).

cnf(c_0_159,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk4_0,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_120,c_0_157])).

cnf(c_0_160,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk4_0,esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_120,c_0_158])).

cnf(c_0_161,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_159]),c_0_27])).

cnf(c_0_162,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_160]),c_0_30])).

cnf(c_0_163,plain,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(X1))
    | ~ epred1_3(X2,X1,esk3_0)
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2) ),
    inference(spm,[status(thm)],[c_0_76,c_0_161])).

cnf(c_0_164,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_tarski(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_162])).

cnf(c_0_165,plain,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)))
    | ~ epred1_3(X2,X1,esk3_0)
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2) ),
    inference(spm,[status(thm)],[c_0_80,c_0_161])).

cnf(c_0_166,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_163,c_0_52])).

cnf(c_0_167,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_164])).

cnf(c_0_168,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_165,c_0_52])).

cnf(c_0_169,negated_conjecture,
    ( r2_lattice3(esk3_0,esk4_0,esk6_0)
    | r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_170,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_166,c_0_167])).

cnf(c_0_171,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_168,c_0_167])).

cnf(c_0_172,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0)
    | r2_lattice3(esk3_0,X1,esk6_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_95,c_0_169])).

cnf(c_0_173,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_170])).

cnf(c_0_174,plain,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | ~ epred1_3(X2,X1,esk3_0)
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2) ),
    inference(spm,[status(thm)],[c_0_67,c_0_161])).

cnf(c_0_175,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)
    | ~ r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)
    | ~ m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_101,c_0_171])).

cnf(c_0_176,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)
    | r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_172,c_0_173])).

cnf(c_0_177,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_174,c_0_52])).

cnf(c_0_178,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk5_0,esk6_0)
    | r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)
    | ~ m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_175,c_0_176])).

cnf(c_0_179,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_177,c_0_167])).

cnf(c_0_180,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_178,c_0_179]),c_0_27]),c_0_120])).

cnf(c_0_181,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_180])).

cnf(c_0_182,plain,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_hidden(k1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)
    | ~ epred1_3(X2,esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_181]),c_0_46])])).

cnf(c_0_183,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_hidden(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_182,c_0_52])).

cnf(c_0_184,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_183,c_0_149])).

cnf(c_0_185,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,X1,esk6_0)
    | ~ r1_tarski(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_95,c_0_180])).

cnf(c_0_186,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_tarski(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_184])).

cnf(c_0_187,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk6_0)
    | ~ r2_lattice3(esk3_0,k1_tarski(X1),esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_18]),c_0_19])])).

cnf(c_0_188,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_180])).

cnf(c_0_189,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_185,c_0_186])).

cnf(c_0_190,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_187,c_0_188]),c_0_189])).

fof(c_0_191,plain,(
    ! [X6] : ~ v1_xboole_0(k1_tarski(X6)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

cnf(c_0_192,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_120,c_0_190])).

cnf(c_0_193,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_191])).

cnf(c_0_194,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_192]),c_0_180])).

cnf(c_0_195,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_196,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_193,c_0_194]),c_0_195])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:59:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 3.85/4.08  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 3.85/4.08  # and selection function SelectNewComplexAHP.
% 3.85/4.08  #
% 3.85/4.08  # Preprocessing time       : 0.029 s
% 3.85/4.08  # Presaturation interreduction done
% 3.85/4.08  
% 3.85/4.08  # Proof found!
% 3.85/4.08  # SZS status Theorem
% 3.85/4.08  # SZS output start CNFRefutation
% 3.85/4.08  fof(t52_waybel_0, conjecture, ![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(((![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r1_yellow_0(X1,X4)))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X3)&![X5]:((v1_finset_1(X5)&m1_subset_1(X5,k1_zfmisc_1(X2)))=>~((r1_yellow_0(X1,X5)&X4=k1_yellow_0(X1,X5))))))))&![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_hidden(k1_yellow_0(X1,X4),X3))))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)<=>r2_lattice3(X1,X3,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_waybel_0)).
% 3.85/4.08  fof(d9_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 3.85/4.08  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.85/4.08  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.85/4.08  fof(reflexivity_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>r3_orders_2(X1,X2,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r3_orders_2)).
% 3.85/4.08  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 3.85/4.08  fof(fc1_finset_1, axiom, ![X1]:v1_finset_1(k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_finset_1)).
% 3.85/4.08  fof(t7_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((((r1_lattice3(X1,k1_tarski(X3),X2)=>r1_orders_2(X1,X2,X3))&(r1_orders_2(X1,X2,X3)=>r1_lattice3(X1,k1_tarski(X3),X2)))&(r2_lattice3(X1,k1_tarski(X3),X2)=>r1_orders_2(X1,X3,X2)))&(r1_orders_2(X1,X3,X2)=>r2_lattice3(X1,k1_tarski(X3),X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_yellow_0)).
% 3.85/4.08  fof(d9_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_yellow_0(X1,X2)=>(X3=k1_yellow_0(X1,X2)<=>(r2_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)=>r1_orders_2(X1,X3,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_yellow_0)).
% 3.85/4.08  fof(t9_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r1_lattice3(X1,X3,X4)=>r1_lattice3(X1,X2,X4))&(r2_lattice3(X1,X3,X4)=>r2_lattice3(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_yellow_0)).
% 3.85/4.08  fof(fc2_xboole_0, axiom, ![X1]:~(v1_xboole_0(k1_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 3.85/4.08  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.85/4.08  fof(c_0_12, plain, ![X1, X2, X3]:(epred1_3(X3,X2,X1)<=>((![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r1_yellow_0(X1,X4)))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X3)&![X5]:((v1_finset_1(X5)&m1_subset_1(X5,k1_zfmisc_1(X2)))=>~((r1_yellow_0(X1,X5)&X4=k1_yellow_0(X1,X5))))))))&![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_hidden(k1_yellow_0(X1,X4),X3))))), introduced(definition)).
% 3.85/4.08  fof(c_0_13, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(epred1_3(X3,X2,X1)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)<=>r2_lattice3(X1,X3,X4)))))))), inference(apply_def,[status(thm)],[inference(assume_negation,[status(cth)],[t52_waybel_0]), c_0_12])).
% 3.85/4.08  fof(c_0_14, plain, ![X18, X19, X20, X21]:((~r2_lattice3(X18,X19,X20)|(~m1_subset_1(X21,u1_struct_0(X18))|(~r2_hidden(X21,X19)|r1_orders_2(X18,X21,X20)))|~m1_subset_1(X20,u1_struct_0(X18))|~l1_orders_2(X18))&((m1_subset_1(esk1_3(X18,X19,X20),u1_struct_0(X18))|r2_lattice3(X18,X19,X20)|~m1_subset_1(X20,u1_struct_0(X18))|~l1_orders_2(X18))&((r2_hidden(esk1_3(X18,X19,X20),X19)|r2_lattice3(X18,X19,X20)|~m1_subset_1(X20,u1_struct_0(X18))|~l1_orders_2(X18))&(~r1_orders_2(X18,esk1_3(X18,X19,X20),X20)|r2_lattice3(X18,X19,X20)|~m1_subset_1(X20,u1_struct_0(X18))|~l1_orders_2(X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).
% 3.85/4.08  fof(c_0_15, negated_conjecture, ((((~v2_struct_0(esk3_0)&v3_orders_2(esk3_0))&v4_orders_2(esk3_0))&l1_orders_2(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(epred1_3(esk5_0,esk4_0,esk3_0)&(m1_subset_1(esk6_0,u1_struct_0(esk3_0))&((~r2_lattice3(esk3_0,esk4_0,esk6_0)|~r2_lattice3(esk3_0,esk5_0,esk6_0))&(r2_lattice3(esk3_0,esk4_0,esk6_0)|r2_lattice3(esk3_0,esk5_0,esk6_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 3.85/4.08  fof(c_0_16, plain, ![X7, X8]:((~r1_tarski(k1_tarski(X7),X8)|r2_hidden(X7,X8))&(~r2_hidden(X7,X8)|r1_tarski(k1_tarski(X7),X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 3.85/4.08  cnf(c_0_17, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.85/4.08  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 3.85/4.08  cnf(c_0_19, negated_conjecture, (l1_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 3.85/4.08  fof(c_0_20, plain, ![X9, X10]:((~m1_subset_1(X9,k1_zfmisc_1(X10))|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|m1_subset_1(X9,k1_zfmisc_1(X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 3.85/4.08  cnf(c_0_21, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 3.85/4.08  cnf(c_0_22, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|r2_hidden(esk1_3(esk3_0,X1,esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])])).
% 3.85/4.08  cnf(c_0_23, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.85/4.08  cnf(c_0_24, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 3.85/4.08  cnf(c_0_25, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|r1_tarski(k1_tarski(esk1_3(esk3_0,X1,esk6_0)),X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 3.85/4.08  cnf(c_0_26, negated_conjecture, (~r2_lattice3(esk3_0,esk4_0,esk6_0)|~r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 3.85/4.08  cnf(c_0_27, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk1_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_18]), c_0_19])])).
% 3.85/4.08  fof(c_0_28, plain, ![X15, X16, X17]:(v2_struct_0(X15)|~v3_orders_2(X15)|~l1_orders_2(X15)|~m1_subset_1(X16,u1_struct_0(X15))|~m1_subset_1(X17,u1_struct_0(X15))|r3_orders_2(X15,X16,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).
% 3.85/4.08  fof(c_0_29, plain, ![X1, X2, X3]:(epred1_3(X3,X2,X1)=>((![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r1_yellow_0(X1,X4)))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X3)&![X5]:((v1_finset_1(X5)&m1_subset_1(X5,k1_zfmisc_1(X2)))=>~((r1_yellow_0(X1,X5)&X4=k1_yellow_0(X1,X5))))))))&![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_hidden(k1_yellow_0(X1,X4),X3))))), inference(split_equiv,[status(thm)],[c_0_12])).
% 3.85/4.08  cnf(c_0_30, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,X1,esk6_0)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 3.85/4.08  fof(c_0_31, plain, ![X12, X13, X14]:((~r3_orders_2(X12,X13,X14)|r1_orders_2(X12,X13,X14)|(v2_struct_0(X12)|~v3_orders_2(X12)|~l1_orders_2(X12)|~m1_subset_1(X13,u1_struct_0(X12))|~m1_subset_1(X14,u1_struct_0(X12))))&(~r1_orders_2(X12,X13,X14)|r3_orders_2(X12,X13,X14)|(v2_struct_0(X12)|~v3_orders_2(X12)|~l1_orders_2(X12)|~m1_subset_1(X13,u1_struct_0(X12))|~m1_subset_1(X14,u1_struct_0(X12))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 3.85/4.08  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))|~r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 3.85/4.08  cnf(c_0_33, plain, (v2_struct_0(X1)|r3_orders_2(X1,X2,X2)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 3.85/4.08  cnf(c_0_34, negated_conjecture, (v3_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 3.85/4.08  cnf(c_0_35, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 3.85/4.08  fof(c_0_36, plain, ![X39, X40, X41, X42, X43, X45]:(((~v1_finset_1(X42)|~m1_subset_1(X42,k1_zfmisc_1(X40))|(X42=k1_xboole_0|r1_yellow_0(X39,X42))|~epred1_3(X41,X40,X39))&(((v1_finset_1(esk7_4(X39,X40,X41,X43))|~r2_hidden(X43,X41)|~m1_subset_1(X43,u1_struct_0(X39))|~epred1_3(X41,X40,X39))&(m1_subset_1(esk7_4(X39,X40,X41,X43),k1_zfmisc_1(X40))|~r2_hidden(X43,X41)|~m1_subset_1(X43,u1_struct_0(X39))|~epred1_3(X41,X40,X39)))&((r1_yellow_0(X39,esk7_4(X39,X40,X41,X43))|~r2_hidden(X43,X41)|~m1_subset_1(X43,u1_struct_0(X39))|~epred1_3(X41,X40,X39))&(X43=k1_yellow_0(X39,esk7_4(X39,X40,X41,X43))|~r2_hidden(X43,X41)|~m1_subset_1(X43,u1_struct_0(X39))|~epred1_3(X41,X40,X39)))))&(~v1_finset_1(X45)|~m1_subset_1(X45,k1_zfmisc_1(X40))|(X45=k1_xboole_0|r2_hidden(k1_yellow_0(X39,X45),X41))|~epred1_3(X41,X40,X39))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])])])).
% 3.85/4.08  cnf(c_0_37, negated_conjecture, (m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))|~r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_26, c_0_30])).
% 3.85/4.08  fof(c_0_38, plain, ![X11]:v1_finset_1(k1_tarski(X11)), inference(variable_rename,[status(thm)],[fc1_finset_1])).
% 3.85/4.08  fof(c_0_39, plain, ![X28, X29, X30]:((((~r1_lattice3(X28,k1_tarski(X30),X29)|r1_orders_2(X28,X29,X30)|~m1_subset_1(X30,u1_struct_0(X28))|~m1_subset_1(X29,u1_struct_0(X28))|~l1_orders_2(X28))&(~r1_orders_2(X28,X29,X30)|r1_lattice3(X28,k1_tarski(X30),X29)|~m1_subset_1(X30,u1_struct_0(X28))|~m1_subset_1(X29,u1_struct_0(X28))|~l1_orders_2(X28)))&(~r2_lattice3(X28,k1_tarski(X30),X29)|r1_orders_2(X28,X30,X29)|~m1_subset_1(X30,u1_struct_0(X28))|~m1_subset_1(X29,u1_struct_0(X28))|~l1_orders_2(X28)))&(~r1_orders_2(X28,X30,X29)|r2_lattice3(X28,k1_tarski(X30),X29)|~m1_subset_1(X30,u1_struct_0(X28))|~m1_subset_1(X29,u1_struct_0(X28))|~l1_orders_2(X28))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_yellow_0])])])])).
% 3.85/4.08  cnf(c_0_40, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r3_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 3.85/4.08  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_32, c_0_27])).
% 3.85/4.08  cnf(c_0_42, negated_conjecture, (r3_orders_2(esk3_0,X1,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_18]), c_0_19]), c_0_34])]), c_0_35])).
% 3.85/4.08  fof(c_0_43, plain, ![X23, X24, X25, X26]:(((r2_lattice3(X23,X24,X25)|X25!=k1_yellow_0(X23,X24)|~r1_yellow_0(X23,X24)|~m1_subset_1(X25,u1_struct_0(X23))|~l1_orders_2(X23))&(~m1_subset_1(X26,u1_struct_0(X23))|(~r2_lattice3(X23,X24,X26)|r1_orders_2(X23,X25,X26))|X25!=k1_yellow_0(X23,X24)|~r1_yellow_0(X23,X24)|~m1_subset_1(X25,u1_struct_0(X23))|~l1_orders_2(X23)))&((m1_subset_1(esk2_3(X23,X24,X25),u1_struct_0(X23))|~r2_lattice3(X23,X24,X25)|X25=k1_yellow_0(X23,X24)|~r1_yellow_0(X23,X24)|~m1_subset_1(X25,u1_struct_0(X23))|~l1_orders_2(X23))&((r2_lattice3(X23,X24,esk2_3(X23,X24,X25))|~r2_lattice3(X23,X24,X25)|X25=k1_yellow_0(X23,X24)|~r1_yellow_0(X23,X24)|~m1_subset_1(X25,u1_struct_0(X23))|~l1_orders_2(X23))&(~r1_orders_2(X23,X25,esk2_3(X23,X24,X25))|~r2_lattice3(X23,X24,X25)|X25=k1_yellow_0(X23,X24)|~r1_yellow_0(X23,X24)|~m1_subset_1(X25,u1_struct_0(X23))|~l1_orders_2(X23))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).
% 3.85/4.08  cnf(c_0_44, plain, (X1=k1_xboole_0|r1_yellow_0(X3,X1)|~v1_finset_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~epred1_3(X4,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 3.85/4.08  cnf(c_0_45, negated_conjecture, (m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_37, c_0_27])).
% 3.85/4.08  cnf(c_0_46, plain, (v1_finset_1(k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 3.85/4.08  cnf(c_0_47, plain, (r2_lattice3(X1,k1_tarski(X2),X3)|~r1_orders_2(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 3.85/4.08  cnf(c_0_48, negated_conjecture, (r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r3_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_19]), c_0_34])]), c_0_35])).
% 3.85/4.08  cnf(c_0_49, negated_conjecture, (r3_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_42, c_0_41])).
% 3.85/4.08  cnf(c_0_50, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))|X3=k1_yellow_0(X1,X2)|~r2_lattice3(X1,X2,X3)|~r1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 3.85/4.08  cnf(c_0_51, plain, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~epred1_3(X2,esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])])).
% 3.85/4.08  cnf(c_0_52, negated_conjecture, (epred1_3(esk5_0,esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 3.85/4.08  cnf(c_0_53, negated_conjecture, (r2_lattice3(esk3_0,k1_tarski(X1),esk1_3(esk3_0,esk4_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_41]), c_0_19])])).
% 3.85/4.08  cnf(c_0_54, negated_conjecture, (r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_41]), c_0_49])).
% 3.85/4.08  cnf(c_0_55, negated_conjecture, (esk1_3(esk3_0,esk4_0,esk6_0)=k1_yellow_0(esk3_0,X1)|m1_subset_1(esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r1_yellow_0(esk3_0,X1)|~r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_41]), c_0_19])])).
% 3.85/4.08  cnf(c_0_56, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 3.85/4.08  cnf(c_0_57, negated_conjecture, (r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_41]), c_0_54])).
% 3.85/4.08  cnf(c_0_58, plain, (r2_lattice3(X1,X2,esk2_3(X1,X2,X3))|X3=k1_yellow_0(X1,X2)|~r2_lattice3(X1,X2,X3)|~r1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 3.85/4.08  cnf(c_0_59, plain, (X2=k1_yellow_0(X1,X3)|~r1_orders_2(X1,X2,esk2_3(X1,X3,X2))|~r2_lattice3(X1,X3,X2)|~r1_yellow_0(X1,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 3.85/4.08  cnf(c_0_60, plain, (r1_orders_2(X1,X2,X3)|~r2_lattice3(X1,k1_tarski(X2),X3)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 3.85/4.08  cnf(c_0_61, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])).
% 3.85/4.08  cnf(c_0_62, negated_conjecture, (esk1_3(esk3_0,esk4_0,esk6_0)=k1_yellow_0(esk3_0,X1)|r2_lattice3(esk3_0,X1,esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r1_yellow_0(esk3_0,X1)|~r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_41]), c_0_19])])).
% 3.85/4.08  cnf(c_0_63, negated_conjecture, (esk1_3(esk3_0,esk4_0,esk6_0)=k1_yellow_0(esk3_0,X1)|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r1_yellow_0(esk3_0,X1)|~r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))|~r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_41]), c_0_19])])).
% 3.85/4.08  cnf(c_0_64, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,X1,esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r2_lattice3(esk3_0,k1_tarski(X1),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_19])])).
% 3.85/4.08  cnf(c_0_65, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_56]), c_0_57])).
% 3.85/4.08  cnf(c_0_66, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_56]), c_0_57])).
% 3.85/4.08  cnf(c_0_67, plain, (X1=k1_yellow_0(X2,esk7_4(X2,X3,X4,X1))|~r2_hidden(X1,X4)|~m1_subset_1(X1,u1_struct_0(X2))|~epred1_3(X4,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 3.85/4.08  cnf(c_0_68, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_41]), c_0_65]), c_0_66])).
% 3.85/4.08  cnf(c_0_69, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 3.85/4.08  cnf(c_0_70, negated_conjecture, (m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_32, c_0_30])).
% 3.85/4.08  cnf(c_0_71, plain, (k1_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|~epred1_3(X2,X1,esk3_0)|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 3.85/4.08  cnf(c_0_72, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 3.85/4.08  cnf(c_0_73, negated_conjecture, (m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))|r1_tarski(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),esk5_0)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 3.85/4.08  cnf(c_0_74, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_71, c_0_52])).
% 3.85/4.08  cnf(c_0_75, negated_conjecture, (m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))|r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 3.85/4.08  cnf(c_0_76, plain, (m1_subset_1(esk7_4(X1,X2,X3,X4),k1_zfmisc_1(X2))|~r2_hidden(X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~epred1_3(X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 3.85/4.08  cnf(c_0_77, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_74, c_0_22])).
% 3.85/4.08  cnf(c_0_78, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 3.85/4.08  cnf(c_0_79, plain, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(X1))|~epred1_3(X2,X1,esk3_0)|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2)), inference(spm,[status(thm)],[c_0_76, c_0_68])).
% 3.85/4.08  cnf(c_0_80, plain, (r1_yellow_0(X1,esk7_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~epred1_3(X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 3.85/4.08  fof(c_0_81, plain, ![X31, X32, X33, X34]:((~r1_lattice3(X31,X33,X34)|r1_lattice3(X31,X32,X34)|~m1_subset_1(X34,u1_struct_0(X31))|~r1_tarski(X32,X33)|~l1_orders_2(X31))&(~r2_lattice3(X31,X33,X34)|r2_lattice3(X31,X32,X34)|~m1_subset_1(X34,u1_struct_0(X31))|~r1_tarski(X32,X33)|~l1_orders_2(X31))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_yellow_0])])])])).
% 3.85/4.08  cnf(c_0_82, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_37, c_0_77])).
% 3.85/4.08  cnf(c_0_83, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))|~r3_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_78]), c_0_19]), c_0_34])]), c_0_35])).
% 3.85/4.08  cnf(c_0_84, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r3_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_42, c_0_78])).
% 3.85/4.08  cnf(c_0_85, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_79, c_0_52])).
% 3.85/4.08  cnf(c_0_86, plain, (r1_orders_2(X2,X4,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|X4!=k1_yellow_0(X2,X3)|~r1_yellow_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 3.85/4.08  cnf(c_0_87, plain, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)))|~epred1_3(X2,X1,esk3_0)|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2)), inference(spm,[status(thm)],[c_0_80, c_0_68])).
% 3.85/4.08  cnf(c_0_88, plain, (r2_lattice3(X1,X4,X3)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~r1_tarski(X4,X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 3.85/4.08  cnf(c_0_89, plain, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))|~epred1_3(X2,esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_82]), c_0_46])])).
% 3.85/4.08  cnf(c_0_90, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,k1_tarski(X1),esk1_3(esk3_0,esk4_0,esk6_0))|~r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_78]), c_0_19])])).
% 3.85/4.08  cnf(c_0_91, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_78]), c_0_84])).
% 3.85/4.08  cnf(c_0_92, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk5_0,esk6_0)|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_85, c_0_22])).
% 3.85/4.08  cnf(c_0_93, plain, (r1_orders_2(X1,k1_yellow_0(X1,X2),X3)|~r1_yellow_0(X1,X2)|~r2_lattice3(X1,X2,X3)|~l1_orders_2(X1)|~m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_86])).
% 3.85/4.08  cnf(c_0_94, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_87, c_0_52])).
% 3.85/4.08  cnf(c_0_95, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|~r2_lattice3(esk3_0,X2,esk6_0)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_18]), c_0_19])])).
% 3.85/4.08  cnf(c_0_96, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_85, c_0_75])).
% 3.85/4.08  cnf(c_0_97, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|esk1_3(esk3_0,esk4_0,esk6_0)=k1_yellow_0(esk3_0,X1)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0))|~r1_yellow_0(esk3_0,X1)|~r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_78]), c_0_19])])).
% 3.85/4.08  cnf(c_0_98, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))), inference(spm,[status(thm)],[c_0_89, c_0_52])).
% 3.85/4.08  cnf(c_0_99, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_78]), c_0_91])).
% 3.85/4.08  cnf(c_0_100, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_37, c_0_92])).
% 3.85/4.08  cnf(c_0_101, negated_conjecture, (r1_orders_2(esk3_0,k1_yellow_0(esk3_0,X1),esk6_0)|~r1_yellow_0(esk3_0,X1)|~r2_lattice3(esk3_0,X1,esk6_0)|~m1_subset_1(k1_yellow_0(esk3_0,X1),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_18]), c_0_19])])).
% 3.85/4.08  cnf(c_0_102, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))|r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_94, c_0_22])).
% 3.85/4.08  cnf(c_0_103, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk1_3(esk3_0,X2,esk6_0),u1_struct_0(esk3_0))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_95, c_0_27])).
% 3.85/4.08  cnf(c_0_104, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))|r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0)), inference(spm,[status(thm)],[c_0_69, c_0_96])).
% 3.85/4.08  cnf(c_0_105, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_99])).
% 3.85/4.08  cnf(c_0_106, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|esk1_3(esk3_0,esk4_0,esk6_0)=k1_yellow_0(esk3_0,X1)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,X1,esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)))|~r1_yellow_0(esk3_0,X1)|~r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_78]), c_0_19])])).
% 3.85/4.08  cnf(c_0_107, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|esk1_3(esk3_0,esk4_0,esk6_0)=k1_yellow_0(esk3_0,X1)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|~r1_yellow_0(esk3_0,X1)|~r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))|~r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_78]), c_0_19])])).
% 3.85/4.08  cnf(c_0_108, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,X2,esk6_0)),k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_95, c_0_30])).
% 3.85/4.08  cnf(c_0_109, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))|r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0)), inference(spm,[status(thm)],[c_0_69, c_0_100])).
% 3.85/4.08  cnf(c_0_110, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk5_0,esk6_0)|r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)|~r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)|~m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_101, c_0_102])).
% 3.85/4.08  cnf(c_0_111, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 3.85/4.08  cnf(c_0_112, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,X1,esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))|~r2_lattice3(esk3_0,k1_tarski(X1),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_105]), c_0_19])])).
% 3.85/4.08  cnf(c_0_113, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_98]), c_0_99])).
% 3.85/4.08  cnf(c_0_114, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|~r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_98]), c_0_99])).
% 3.85/4.08  cnf(c_0_115, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_108, c_0_109])).
% 3.85/4.08  cnf(c_0_116, plain, (r2_lattice3(X1,X2,X3)|~r1_orders_2(X1,esk1_3(X1,X2,X3),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.85/4.08  cnf(c_0_117, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))|~m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_32])).
% 3.85/4.08  cnf(c_0_118, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_78]), c_0_113]), c_0_114])).
% 3.85/4.08  cnf(c_0_119, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))|~m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_115]), c_0_37])).
% 3.85/4.08  cnf(c_0_120, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|~r1_orders_2(esk3_0,esk1_3(esk3_0,X1,esk6_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_18]), c_0_19])])).
% 3.85/4.08  cnf(c_0_121, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk1_3(esk3_0,esk5_0,esk6_0),esk6_0)|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_118]), c_0_41])).
% 3.85/4.08  cnf(c_0_122, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk1_3(esk3_0,esk5_0,esk6_0),esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_118]), c_0_45])).
% 3.85/4.08  cnf(c_0_123, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_121]), c_0_32])).
% 3.85/4.08  cnf(c_0_124, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_122]), c_0_37])).
% 3.85/4.08  cnf(c_0_125, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))|~r3_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_123]), c_0_19]), c_0_34])]), c_0_35])).
% 3.85/4.08  cnf(c_0_126, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r3_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_42, c_0_123])).
% 3.85/4.08  cnf(c_0_127, plain, (X1=k1_xboole_0|r2_hidden(k1_yellow_0(X3,X1),X4)|~v1_finset_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~epred1_3(X4,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 3.85/4.08  cnf(c_0_128, negated_conjecture, (m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_37, c_0_30])).
% 3.85/4.08  cnf(c_0_129, plain, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))|~epred1_3(X2,esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_124]), c_0_46])])).
% 3.85/4.08  cnf(c_0_130, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,k1_tarski(X1),esk1_3(esk3_0,esk4_0,esk6_0))|~r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_123]), c_0_19])])).
% 3.85/4.08  cnf(c_0_131, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_123]), c_0_126])).
% 3.85/4.08  cnf(c_0_132, plain, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))|r2_hidden(k1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)|~epred1_3(X2,esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_128]), c_0_46])])).
% 3.85/4.08  cnf(c_0_133, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|esk1_3(esk3_0,esk4_0,esk6_0)=k1_yellow_0(esk3_0,X1)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0))|~r1_yellow_0(esk3_0,X1)|~r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_123]), c_0_19])])).
% 3.85/4.08  cnf(c_0_134, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))), inference(spm,[status(thm)],[c_0_129, c_0_52])).
% 3.85/4.08  cnf(c_0_135, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_123]), c_0_131])).
% 3.85/4.08  cnf(c_0_136, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))|r2_hidden(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0)), inference(spm,[status(thm)],[c_0_132, c_0_52])).
% 3.85/4.08  cnf(c_0_137, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_133, c_0_134]), c_0_135])).
% 3.85/4.08  cnf(c_0_138, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|esk1_3(esk3_0,esk4_0,esk6_0)=k1_yellow_0(esk3_0,X1)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,X1,esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)))|~r1_yellow_0(esk3_0,X1)|~r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_123]), c_0_19])])).
% 3.85/4.08  cnf(c_0_139, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|esk1_3(esk3_0,esk4_0,esk6_0)=k1_yellow_0(esk3_0,X1)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|~r1_yellow_0(esk3_0,X1)|~r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))|~r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_123]), c_0_19])])).
% 3.85/4.08  cnf(c_0_140, plain, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))|~epred1_3(X2,esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_128]), c_0_46])])).
% 3.85/4.08  cnf(c_0_141, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))|r1_tarski(k1_tarski(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))),esk5_0)), inference(spm,[status(thm)],[c_0_21, c_0_136])).
% 3.85/4.08  cnf(c_0_142, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,X1,esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))|~r2_lattice3(esk3_0,k1_tarski(X1),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_137]), c_0_19])])).
% 3.85/4.08  cnf(c_0_143, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_134]), c_0_135])).
% 3.85/4.08  cnf(c_0_144, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|~r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_139, c_0_134]), c_0_135])).
% 3.85/4.08  cnf(c_0_145, plain, (r1_orders_2(X1,X4,X3)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.85/4.08  cnf(c_0_146, plain, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|r2_hidden(k1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)|~epred1_3(X2,esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_45]), c_0_46])])).
% 3.85/4.08  cnf(c_0_147, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_140, c_0_52])).
% 3.85/4.08  cnf(c_0_148, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,k1_tarski(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))),esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_108, c_0_141])).
% 3.85/4.08  cnf(c_0_149, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_142, c_0_123]), c_0_143]), c_0_144])).
% 3.85/4.08  cnf(c_0_150, negated_conjecture, (r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),X1)|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r2_lattice3(esk3_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145, c_0_41]), c_0_19])])).
% 3.85/4.08  cnf(c_0_151, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|r2_hidden(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0)), inference(spm,[status(thm)],[c_0_146, c_0_52])).
% 3.85/4.08  cnf(c_0_152, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))|~r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0)|~m1_subset_1(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_101, c_0_147])).
% 3.85/4.08  cnf(c_0_153, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_148, c_0_149])).
% 3.85/4.08  cnf(c_0_154, negated_conjecture, (r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0)|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0))|~r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150, c_0_27]), c_0_18])])).
% 3.85/4.08  cnf(c_0_155, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_151, c_0_149])).
% 3.85/4.08  cnf(c_0_156, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))|~m1_subset_1(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_152, c_0_153])).
% 3.85/4.08  cnf(c_0_157, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0)|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_154, c_0_155])).
% 3.85/4.08  cnf(c_0_158, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_156, c_0_149]), c_0_70])).
% 3.85/4.08  cnf(c_0_159, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk4_0,esk6_0)|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_120, c_0_157])).
% 3.85/4.08  cnf(c_0_160, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk4_0,esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_120, c_0_158])).
% 3.85/4.08  cnf(c_0_161, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_159]), c_0_27])).
% 3.85/4.08  cnf(c_0_162, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_160]), c_0_30])).
% 3.85/4.08  cnf(c_0_163, plain, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(X1))|~epred1_3(X2,X1,esk3_0)|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2)), inference(spm,[status(thm)],[c_0_76, c_0_161])).
% 3.85/4.08  cnf(c_0_164, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_tarski(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),esk5_0)), inference(spm,[status(thm)],[c_0_69, c_0_162])).
% 3.85/4.08  cnf(c_0_165, plain, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)))|~epred1_3(X2,X1,esk3_0)|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2)), inference(spm,[status(thm)],[c_0_80, c_0_161])).
% 3.85/4.08  cnf(c_0_166, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_163, c_0_52])).
% 3.85/4.08  cnf(c_0_167, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_72, c_0_164])).
% 3.85/4.08  cnf(c_0_168, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_165, c_0_52])).
% 3.85/4.08  cnf(c_0_169, negated_conjecture, (r2_lattice3(esk3_0,esk4_0,esk6_0)|r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 3.85/4.08  cnf(c_0_170, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_166, c_0_167])).
% 3.85/4.08  cnf(c_0_171, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))), inference(spm,[status(thm)],[c_0_168, c_0_167])).
% 3.85/4.08  cnf(c_0_172, negated_conjecture, (r2_lattice3(esk3_0,esk5_0,esk6_0)|r2_lattice3(esk3_0,X1,esk6_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_95, c_0_169])).
% 3.85/4.08  cnf(c_0_173, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0)), inference(spm,[status(thm)],[c_0_69, c_0_170])).
% 3.85/4.08  cnf(c_0_174, plain, (k1_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|~epred1_3(X2,X1,esk3_0)|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2)), inference(spm,[status(thm)],[c_0_67, c_0_161])).
% 3.85/4.08  cnf(c_0_175, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)|~r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)|~m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_101, c_0_171])).
% 3.85/4.08  cnf(c_0_176, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)|r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_172, c_0_173])).
% 3.85/4.08  cnf(c_0_177, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_174, c_0_52])).
% 3.85/4.08  cnf(c_0_178, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk5_0,esk6_0)|r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)|~m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_175, c_0_176])).
% 3.85/4.08  cnf(c_0_179, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_177, c_0_167])).
% 3.85/4.08  cnf(c_0_180, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_178, c_0_179]), c_0_27]), c_0_120])).
% 3.85/4.08  cnf(c_0_181, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_37, c_0_180])).
% 3.85/4.08  cnf(c_0_182, plain, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_hidden(k1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)|~epred1_3(X2,esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_181]), c_0_46])])).
% 3.85/4.08  cnf(c_0_183, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_hidden(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0)), inference(spm,[status(thm)],[c_0_182, c_0_52])).
% 3.85/4.08  cnf(c_0_184, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_183, c_0_149])).
% 3.85/4.08  cnf(c_0_185, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,X1,esk6_0)|~r1_tarski(X1,esk5_0)), inference(spm,[status(thm)],[c_0_95, c_0_180])).
% 3.85/4.08  cnf(c_0_186, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_tarski(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk5_0)), inference(spm,[status(thm)],[c_0_21, c_0_184])).
% 3.85/4.08  cnf(c_0_187, negated_conjecture, (r1_orders_2(esk3_0,X1,esk6_0)|~r2_lattice3(esk3_0,k1_tarski(X1),esk6_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_18]), c_0_19])])).
% 3.85/4.08  cnf(c_0_188, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_32, c_0_180])).
% 3.85/4.08  cnf(c_0_189, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0)), inference(spm,[status(thm)],[c_0_185, c_0_186])).
% 3.85/4.08  cnf(c_0_190, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_187, c_0_188]), c_0_189])).
% 3.85/4.08  fof(c_0_191, plain, ![X6]:~v1_xboole_0(k1_tarski(X6)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).
% 3.85/4.08  cnf(c_0_192, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk4_0,esk6_0)), inference(spm,[status(thm)],[c_0_120, c_0_190])).
% 3.85/4.08  cnf(c_0_193, plain, (~v1_xboole_0(k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_191])).
% 3.85/4.08  cnf(c_0_194, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_192]), c_0_180])).
% 3.85/4.08  cnf(c_0_195, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 3.85/4.08  cnf(c_0_196, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_193, c_0_194]), c_0_195])]), ['proof']).
% 3.85/4.08  # SZS output end CNFRefutation
% 3.85/4.08  # Proof object total steps             : 197
% 3.85/4.08  # Proof object clause steps            : 170
% 3.85/4.08  # Proof object formula steps           : 27
% 3.85/4.08  # Proof object conjectures             : 134
% 3.85/4.08  # Proof object clause conjectures      : 131
% 3.85/4.08  # Proof object formula conjectures     : 3
% 3.85/4.08  # Proof object initial clauses used    : 32
% 3.85/4.08  # Proof object initial formulas used   : 12
% 3.85/4.08  # Proof object generating inferences   : 137
% 3.85/4.08  # Proof object simplifying inferences  : 113
% 3.85/4.08  # Training examples: 0 positive, 0 negative
% 3.85/4.08  # Parsed axioms                        : 12
% 3.85/4.08  # Removed by relevancy pruning/SinE    : 0
% 3.85/4.08  # Initial clauses                      : 41
% 3.85/4.08  # Removed in clause preprocessing      : 0
% 3.85/4.08  # Initial clauses in saturation        : 41
% 3.85/4.08  # Processed clauses                    : 10853
% 3.85/4.08  # ...of these trivial                  : 166
% 3.85/4.08  # ...subsumed                          : 4146
% 3.85/4.08  # ...remaining for further processing  : 6541
% 3.85/4.08  # Other redundant clauses eliminated   : 2
% 3.85/4.08  # Clauses deleted for lack of memory   : 0
% 3.85/4.08  # Backward-subsumed                    : 2809
% 3.85/4.08  # Backward-rewritten                   : 2227
% 3.85/4.08  # Generated clauses                    : 62152
% 3.85/4.08  # ...of the previous two non-trivial   : 60574
% 3.85/4.08  # Contextual simplify-reflections      : 454
% 3.85/4.08  # Paramodulations                      : 62150
% 3.85/4.08  # Factorizations                       : 0
% 3.85/4.08  # Equation resolutions                 : 2
% 3.85/4.08  # Propositional unsat checks           : 0
% 3.85/4.08  #    Propositional check models        : 0
% 3.85/4.08  #    Propositional check unsatisfiable : 0
% 3.85/4.08  #    Propositional clauses             : 0
% 3.85/4.08  #    Propositional clauses after purity: 0
% 3.85/4.08  #    Propositional unsat core size     : 0
% 3.85/4.08  #    Propositional preprocessing time  : 0.000
% 3.85/4.08  #    Propositional encoding time       : 0.000
% 3.85/4.08  #    Propositional solver time         : 0.000
% 3.85/4.08  #    Success case prop preproc time    : 0.000
% 3.85/4.08  #    Success case prop encoding time   : 0.000
% 3.85/4.08  #    Success case prop solver time     : 0.000
% 3.85/4.08  # Current number of processed clauses  : 1462
% 3.85/4.08  #    Positive orientable unit clauses  : 97
% 3.85/4.08  #    Positive unorientable unit clauses: 0
% 3.85/4.08  #    Negative unit clauses             : 2
% 3.85/4.08  #    Non-unit-clauses                  : 1363
% 3.85/4.08  # Current number of unprocessed clauses: 47225
% 3.85/4.08  # ...number of literals in the above   : 293518
% 3.85/4.08  # Current number of archived formulas  : 0
% 3.85/4.08  # Current number of archived clauses   : 5077
% 3.85/4.08  # Clause-clause subsumption calls (NU) : 6556049
% 3.85/4.08  # Rec. Clause-clause subsumption calls : 451659
% 3.85/4.08  # Non-unit clause-clause subsumptions  : 7407
% 3.85/4.08  # Unit Clause-clause subsumption calls : 28043
% 3.85/4.08  # Rewrite failures with RHS unbound    : 0
% 3.85/4.08  # BW rewrite match attempts            : 3130
% 3.85/4.08  # BW rewrite match successes           : 27
% 3.85/4.08  # Condensation attempts                : 0
% 3.85/4.08  # Condensation successes               : 0
% 3.85/4.08  # Termbank termtop insertions          : 3947780
% 3.85/4.08  
% 3.85/4.08  # -------------------------------------------------
% 3.85/4.08  # User time                : 3.711 s
% 3.85/4.08  # System time              : 0.034 s
% 3.85/4.08  # Total time               : 3.744 s
% 3.85/4.08  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
