%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:27 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :  200 (35195804 expanded)
%              Number of clauses        :  173 (11327739 expanded)
%              Number of leaves         :   13 (11867457 expanded)
%              Depth                    :   63
%              Number of atoms          :  880 (368584273 expanded)
%              Number of equality atoms :  244 (31976371 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   30 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_waybel_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

fof(t63_subset_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(reflexivity_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => r3_orders_2(X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

fof(redefinition_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_orders_2(X1,X2,X3)
      <=> r1_orders_2(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(fc1_finset_1,axiom,(
    ! [X1] : v1_finset_1(k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_finset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_yellow_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_yellow_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(fc2_xboole_0,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

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
      ( ~ r2_hidden(X7,X8)
      | m1_subset_1(k1_tarski(X7),k1_zfmisc_1(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).

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

cnf(c_0_20,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | r2_hidden(esk1_3(esk3_0,X1,esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

cnf(c_0_23,negated_conjecture,
    ( ~ r2_lattice3(esk3_0,esk4_0,esk6_0)
    | ~ r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_18]),c_0_19])])).

fof(c_0_25,plain,(
    ! [X15,X16,X17] :
      ( v2_struct_0(X15)
      | ~ v3_orders_2(X15)
      | ~ l1_orders_2(X15)
      | ~ m1_subset_1(X16,u1_struct_0(X15))
      | ~ m1_subset_1(X17,u1_struct_0(X15))
      | r3_orders_2(X15,X16,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).

fof(c_0_26,plain,(
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

cnf(c_0_27,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,X1,esk6_0)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_28,plain,(
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

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( v2_struct_0(X1)
    | r3_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( v3_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_32,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_33,plain,(
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
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])])])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | ~ r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_27])).

fof(c_0_35,plain,(
    ! [X11] : v1_finset_1(k1_tarski(X11)) ),
    inference(variable_rename,[status(thm)],[fc1_finset_1])).

fof(c_0_36,plain,(
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

cnf(c_0_37,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_24])).

cnf(c_0_39,negated_conjecture,
    ( r3_orders_2(esk3_0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_18]),c_0_19]),c_0_31])]),c_0_32])).

fof(c_0_40,plain,(
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

cnf(c_0_41,plain,
    ( X1 = k1_xboole_0
    | r1_yellow_0(X3,X1)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ epred1_3(X4,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_24])).

cnf(c_0_43,plain,
    ( v1_finset_1(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( r2_lattice3(X1,k1_tarski(X2),X3)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r3_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_19]),c_0_31])]),c_0_32])).

cnf(c_0_46,negated_conjecture,
    ( r3_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_38])).

cnf(c_0_47,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | X3 = k1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ epred1_3(X2,esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])])).

cnf(c_0_49,negated_conjecture,
    ( epred1_3(esk5_0,esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_50,negated_conjecture,
    ( r2_lattice3(esk3_0,k1_tarski(X1),esk1_3(esk3_0,esk4_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_38]),c_0_19])])).

cnf(c_0_51,negated_conjecture,
    ( r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_38]),c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( esk1_3(esk3_0,esk4_0,esk6_0) = k1_yellow_0(esk3_0,X1)
    | m1_subset_1(esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_yellow_0(esk3_0,X1)
    | ~ r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_38]),c_0_19])])).

cnf(c_0_53,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_38]),c_0_51])).

cnf(c_0_55,plain,
    ( r2_lattice3(X1,X2,esk2_3(X1,X2,X3))
    | X3 = k1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_56,plain,
    ( X2 = k1_yellow_0(X1,X3)
    | ~ r1_orders_2(X1,X2,esk2_3(X1,X3,X2))
    | ~ r2_lattice3(X1,X3,X2)
    | ~ r1_yellow_0(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_57,plain,
    ( r1_orders_2(X1,X2,X3)
    | ~ r2_lattice3(X1,k1_tarski(X2),X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_58,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( esk1_3(esk3_0,esk4_0,esk6_0) = k1_yellow_0(esk3_0,X1)
    | r2_lattice3(esk3_0,X1,esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_yellow_0(esk3_0,X1)
    | ~ r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_38]),c_0_19])])).

cnf(c_0_60,negated_conjecture,
    ( esk1_3(esk3_0,esk4_0,esk6_0) = k1_yellow_0(esk3_0,X1)
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_yellow_0(esk3_0,X1)
    | ~ r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_38]),c_0_19])])).

cnf(c_0_61,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,X1,esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r2_lattice3(esk3_0,k1_tarski(X1),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_19])])).

cnf(c_0_62,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_53]),c_0_54])).

cnf(c_0_63,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_53]),c_0_54])).

cnf(c_0_64,plain,
    ( X1 = k1_yellow_0(X2,esk7_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ epred1_3(X4,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_65,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_38]),c_0_62]),c_0_63])).

cnf(c_0_66,plain,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | ~ epred1_3(X2,X1,esk3_0)
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_67,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_49])).

cnf(c_0_68,plain,
    ( m1_subset_1(esk7_4(X1,X2,X3,X4),k1_zfmisc_1(X2))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_69,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_22])).

cnf(c_0_70,plain,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(X1))
    | ~ epred1_3(X2,X1,esk3_0)
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2) ),
    inference(spm,[status(thm)],[c_0_68,c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_69])).

cnf(c_0_72,plain,
    ( r1_yellow_0(X1,esk7_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_73,plain,(
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

cnf(c_0_74,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_49])).

cnf(c_0_75,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_69])).

cnf(c_0_76,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ r3_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_71]),c_0_19]),c_0_31])]),c_0_32])).

cnf(c_0_77,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r3_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_71])).

cnf(c_0_78,plain,
    ( r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | X4 != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_79,plain,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)))
    | ~ epred1_3(X2,X1,esk3_0)
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2) ),
    inference(spm,[status(thm)],[c_0_72,c_0_65])).

cnf(c_0_80,plain,
    ( r2_lattice3(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_tarski(X4,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

fof(c_0_81,plain,(
    ! [X9,X10] :
      ( ( ~ m1_subset_1(X9,k1_zfmisc_1(X10))
        | r1_tarski(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | m1_subset_1(X9,k1_zfmisc_1(X10)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_82,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk5_0,esk6_0)
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_22])).

cnf(c_0_83,plain,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))
    | ~ epred1_3(X2,esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_75]),c_0_43])])).

cnf(c_0_84,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,k1_tarski(X1),esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_71]),c_0_19])])).

cnf(c_0_85,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_71]),c_0_77])).

cnf(c_0_86,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_78])).

cnf(c_0_87,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_49])).

cnf(c_0_88,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | ~ r2_lattice3(esk3_0,X2,esk6_0)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_18]),c_0_19])])).

cnf(c_0_89,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_90,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_82])).

cnf(c_0_91,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | esk1_3(esk3_0,esk4_0,esk6_0) = k1_yellow_0(esk3_0,X1)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0))
    | ~ r1_yellow_0(esk3_0,X1)
    | ~ r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_71]),c_0_19])])).

cnf(c_0_92,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_83,c_0_49])).

cnf(c_0_93,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_71]),c_0_85])).

cnf(c_0_94,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_82])).

cnf(c_0_95,negated_conjecture,
    ( r1_orders_2(esk3_0,k1_yellow_0(esk3_0,X1),esk6_0)
    | ~ r1_yellow_0(esk3_0,X1)
    | ~ r2_lattice3(esk3_0,X1,esk6_0)
    | ~ m1_subset_1(k1_yellow_0(esk3_0,X1),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_18]),c_0_19])])).

cnf(c_0_96,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))
    | r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_22])).

cnf(c_0_97,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,X2,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_88,c_0_24])).

cnf(c_0_98,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_99,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_93])).

cnf(c_0_100,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | esk1_3(esk3_0,esk4_0,esk6_0) = k1_yellow_0(esk3_0,X1)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,X1,esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)))
    | ~ r1_yellow_0(esk3_0,X1)
    | ~ r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_71]),c_0_19])])).

cnf(c_0_101,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | esk1_3(esk3_0,esk4_0,esk6_0) = k1_yellow_0(esk3_0,X1)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | ~ r1_yellow_0(esk3_0,X1)
    | ~ r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_71]),c_0_19])])).

cnf(c_0_102,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,X2,esk6_0)),k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_88,c_0_27])).

cnf(c_0_103,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_94])).

cnf(c_0_104,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk5_0,esk6_0)
    | r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)
    | ~ r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)
    | ~ m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_105,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_106,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,X1,esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))
    | ~ r2_lattice3(esk3_0,k1_tarski(X1),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_99]),c_0_19])])).

cnf(c_0_107,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_92]),c_0_93])).

cnf(c_0_108,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | ~ r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_92]),c_0_93])).

cnf(c_0_109,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_110,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk1_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_111,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))
    | ~ m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_29])).

cnf(c_0_112,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_71]),c_0_107]),c_0_108])).

cnf(c_0_113,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | ~ m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_109]),c_0_34])).

cnf(c_0_114,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | ~ r1_orders_2(esk3_0,esk1_3(esk3_0,X1,esk6_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_18]),c_0_19])])).

cnf(c_0_115,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk1_3(esk3_0,esk5_0,esk6_0),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_38])).

cnf(c_0_116,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk1_3(esk3_0,esk5_0,esk6_0),esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_112]),c_0_42])).

cnf(c_0_117,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_115]),c_0_29])).

cnf(c_0_118,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_116]),c_0_34])).

cnf(c_0_119,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ r3_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_117]),c_0_19]),c_0_31])]),c_0_32])).

cnf(c_0_120,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r3_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_117])).

cnf(c_0_121,plain,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))
    | ~ epred1_3(X2,esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_118]),c_0_43])])).

cnf(c_0_122,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,k1_tarski(X1),esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_117]),c_0_19])])).

cnf(c_0_123,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_117]),c_0_120])).

cnf(c_0_124,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | esk1_3(esk3_0,esk4_0,esk6_0) = k1_yellow_0(esk3_0,X1)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0))
    | ~ r1_yellow_0(esk3_0,X1)
    | ~ r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_117]),c_0_19])])).

cnf(c_0_125,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_121,c_0_49])).

cnf(c_0_126,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_117]),c_0_123])).

cnf(c_0_127,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(k1_yellow_0(X3,X1),X4)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ epred1_3(X4,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_128,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_125]),c_0_126])).

cnf(c_0_129,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | esk1_3(esk3_0,esk4_0,esk6_0) = k1_yellow_0(esk3_0,X1)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,X1,esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)))
    | ~ r1_yellow_0(esk3_0,X1)
    | ~ r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_117]),c_0_19])])).

cnf(c_0_130,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | esk1_3(esk3_0,esk4_0,esk6_0) = k1_yellow_0(esk3_0,X1)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | ~ r1_yellow_0(esk3_0,X1)
    | ~ r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_117]),c_0_19])])).

cnf(c_0_131,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_132,plain,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | r2_hidden(k1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)
    | ~ epred1_3(X2,esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_42]),c_0_43])])).

cnf(c_0_133,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,X1,esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))
    | ~ r2_lattice3(esk3_0,k1_tarski(X1),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_128]),c_0_19])])).

cnf(c_0_134,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_125]),c_0_126])).

cnf(c_0_135,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | ~ r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_125]),c_0_126])).

cnf(c_0_136,negated_conjecture,
    ( r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),X1)
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r2_lattice3(esk3_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_38]),c_0_19])])).

cnf(c_0_137,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | r2_hidden(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_132,c_0_49])).

cnf(c_0_138,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_117]),c_0_134]),c_0_135])).

cnf(c_0_139,negated_conjecture,
    ( r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0))
    | ~ r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_24]),c_0_18])])).

cnf(c_0_140,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_137,c_0_138])).

cnf(c_0_141,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_139,c_0_140])).

cnf(c_0_142,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk4_0,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_114,c_0_141])).

cnf(c_0_143,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_142]),c_0_24])).

cnf(c_0_144,plain,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | ~ epred1_3(X2,X1,esk3_0)
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2) ),
    inference(spm,[status(thm)],[c_0_64,c_0_143])).

cnf(c_0_145,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_144,c_0_49])).

cnf(c_0_146,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_145,c_0_22])).

cnf(c_0_147,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_146])).

cnf(c_0_148,plain,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_hidden(k1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)
    | ~ epred1_3(X2,esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_147]),c_0_43])])).

cnf(c_0_149,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_hidden(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_148,c_0_49])).

cnf(c_0_150,plain,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(X1))
    | ~ epred1_3(X2,X1,esk3_0)
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2) ),
    inference(spm,[status(thm)],[c_0_68,c_0_143])).

cnf(c_0_151,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_149,c_0_138])).

cnf(c_0_152,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_150,c_0_49])).

cnf(c_0_153,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_151])).

cnf(c_0_154,plain,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)))
    | ~ epred1_3(X2,X1,esk3_0)
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2) ),
    inference(spm,[status(thm)],[c_0_72,c_0_143])).

cnf(c_0_155,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk5_0,esk6_0)
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_152,c_0_22])).

cnf(c_0_156,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,X1,esk6_0)
    | ~ r1_tarski(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_88,c_0_146])).

cnf(c_0_157,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_tarski(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_153])).

cnf(c_0_158,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_154,c_0_49])).

cnf(c_0_159,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_155])).

cnf(c_0_160,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk6_0)
    | ~ r2_lattice3(esk3_0,k1_tarski(X1),esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_18]),c_0_19])])).

cnf(c_0_161,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_146])).

cnf(c_0_162,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_156,c_0_157])).

cnf(c_0_163,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_155])).

cnf(c_0_164,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))
    | r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_158,c_0_22])).

cnf(c_0_165,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_159])).

cnf(c_0_166,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_160,c_0_161]),c_0_162])).

cnf(c_0_167,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_163])).

cnf(c_0_168,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk5_0,esk6_0)
    | r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)
    | ~ r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)
    | ~ m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_164])).

cnf(c_0_169,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_102,c_0_165])).

cnf(c_0_170,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_114,c_0_166])).

cnf(c_0_171,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_97,c_0_167])).

cnf(c_0_172,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | ~ m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_168,c_0_169]),c_0_34])).

cnf(c_0_173,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_170]),c_0_146])).

cnf(c_0_174,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))
    | ~ m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_168,c_0_171]),c_0_29])).

cnf(c_0_175,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk1_3(esk3_0,esk5_0,esk6_0),esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_172,c_0_173]),c_0_42])).

cnf(c_0_176,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk1_3(esk3_0,esk5_0,esk6_0),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_174,c_0_173]),c_0_38])).

cnf(c_0_177,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_175]),c_0_34])).

cnf(c_0_178,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_176]),c_0_29])).

cnf(c_0_179,plain,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_hidden(k1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)
    | ~ epred1_3(X2,esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_177]),c_0_43])])).

cnf(c_0_180,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),X1)
    | ~ r2_lattice3(esk3_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_178]),c_0_19])])).

cnf(c_0_181,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_hidden(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_179,c_0_49])).

cnf(c_0_182,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0)
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | ~ r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_180,c_0_155]),c_0_18])])).

cnf(c_0_183,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_181,c_0_138])).

cnf(c_0_184,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0)
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_182,c_0_183])).

cnf(c_0_185,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk4_0,esk6_0)
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_114,c_0_184])).

cnf(c_0_186,negated_conjecture,
    ( r2_lattice3(esk3_0,esk4_0,esk6_0)
    | r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_187,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_185]),c_0_155])).

cnf(c_0_188,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0)
    | r2_lattice3(esk3_0,X1,esk6_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_88,c_0_186])).

cnf(c_0_189,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_187])).

cnf(c_0_190,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)
    | r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_188,c_0_189])).

cnf(c_0_191,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk5_0,esk6_0)
    | r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)
    | ~ m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_168,c_0_190])).

cnf(c_0_192,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_191,c_0_173]),c_0_24]),c_0_114])).

cnf(c_0_193,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_180,c_0_192]),c_0_18])]),c_0_183])).

fof(c_0_194,plain,(
    ! [X6] : ~ v1_xboole_0(k1_tarski(X6)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

cnf(c_0_195,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_114,c_0_193])).

cnf(c_0_196,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_194])).

cnf(c_0_197,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_195]),c_0_192])).

cnf(c_0_198,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_199,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_196,c_0_197]),c_0_198])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:48:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 2.77/2.93  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 2.77/2.93  # and selection function SelectNewComplexAHP.
% 2.77/2.93  #
% 2.77/2.93  # Preprocessing time       : 0.030 s
% 2.77/2.93  # Presaturation interreduction done
% 2.77/2.93  
% 2.77/2.93  # Proof found!
% 2.77/2.93  # SZS status Theorem
% 2.77/2.93  # SZS output start CNFRefutation
% 2.77/2.93  fof(t52_waybel_0, conjecture, ![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(((![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r1_yellow_0(X1,X4)))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X3)&![X5]:((v1_finset_1(X5)&m1_subset_1(X5,k1_zfmisc_1(X2)))=>~((r1_yellow_0(X1,X5)&X4=k1_yellow_0(X1,X5))))))))&![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_hidden(k1_yellow_0(X1,X4),X3))))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)<=>r2_lattice3(X1,X3,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_waybel_0)).
% 2.77/2.93  fof(d9_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattice3)).
% 2.77/2.93  fof(t63_subset_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 2.77/2.93  fof(reflexivity_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>r3_orders_2(X1,X2,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r3_orders_2)).
% 2.77/2.93  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 2.77/2.93  fof(fc1_finset_1, axiom, ![X1]:v1_finset_1(k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_finset_1)).
% 2.77/2.93  fof(t7_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((((r1_lattice3(X1,k1_tarski(X3),X2)=>r1_orders_2(X1,X2,X3))&(r1_orders_2(X1,X2,X3)=>r1_lattice3(X1,k1_tarski(X3),X2)))&(r2_lattice3(X1,k1_tarski(X3),X2)=>r1_orders_2(X1,X3,X2)))&(r1_orders_2(X1,X3,X2)=>r2_lattice3(X1,k1_tarski(X3),X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_yellow_0)).
% 2.77/2.93  fof(d9_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_yellow_0(X1,X2)=>(X3=k1_yellow_0(X1,X2)<=>(r2_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)=>r1_orders_2(X1,X3,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_yellow_0)).
% 2.77/2.93  fof(t9_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r1_lattice3(X1,X3,X4)=>r1_lattice3(X1,X2,X4))&(r2_lattice3(X1,X3,X4)=>r2_lattice3(X1,X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_yellow_0)).
% 2.77/2.93  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.77/2.93  fof(fc2_xboole_0, axiom, ![X1]:~(v1_xboole_0(k1_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 2.77/2.93  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.77/2.93  fof(c_0_12, plain, ![X1, X2, X3]:(epred1_3(X3,X2,X1)<=>((![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r1_yellow_0(X1,X4)))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X3)&![X5]:((v1_finset_1(X5)&m1_subset_1(X5,k1_zfmisc_1(X2)))=>~((r1_yellow_0(X1,X5)&X4=k1_yellow_0(X1,X5))))))))&![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_hidden(k1_yellow_0(X1,X4),X3))))), introduced(definition)).
% 2.77/2.93  fof(c_0_13, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(epred1_3(X3,X2,X1)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)<=>r2_lattice3(X1,X3,X4)))))))), inference(apply_def,[status(thm)],[inference(assume_negation,[status(cth)],[t52_waybel_0]), c_0_12])).
% 2.77/2.93  fof(c_0_14, plain, ![X18, X19, X20, X21]:((~r2_lattice3(X18,X19,X20)|(~m1_subset_1(X21,u1_struct_0(X18))|(~r2_hidden(X21,X19)|r1_orders_2(X18,X21,X20)))|~m1_subset_1(X20,u1_struct_0(X18))|~l1_orders_2(X18))&((m1_subset_1(esk1_3(X18,X19,X20),u1_struct_0(X18))|r2_lattice3(X18,X19,X20)|~m1_subset_1(X20,u1_struct_0(X18))|~l1_orders_2(X18))&((r2_hidden(esk1_3(X18,X19,X20),X19)|r2_lattice3(X18,X19,X20)|~m1_subset_1(X20,u1_struct_0(X18))|~l1_orders_2(X18))&(~r1_orders_2(X18,esk1_3(X18,X19,X20),X20)|r2_lattice3(X18,X19,X20)|~m1_subset_1(X20,u1_struct_0(X18))|~l1_orders_2(X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).
% 2.77/2.93  fof(c_0_15, negated_conjecture, ((((~v2_struct_0(esk3_0)&v3_orders_2(esk3_0))&v4_orders_2(esk3_0))&l1_orders_2(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(epred1_3(esk5_0,esk4_0,esk3_0)&(m1_subset_1(esk6_0,u1_struct_0(esk3_0))&((~r2_lattice3(esk3_0,esk4_0,esk6_0)|~r2_lattice3(esk3_0,esk5_0,esk6_0))&(r2_lattice3(esk3_0,esk4_0,esk6_0)|r2_lattice3(esk3_0,esk5_0,esk6_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 2.77/2.93  fof(c_0_16, plain, ![X7, X8]:(~r2_hidden(X7,X8)|m1_subset_1(k1_tarski(X7),k1_zfmisc_1(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).
% 2.77/2.93  cnf(c_0_17, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.77/2.93  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.77/2.93  cnf(c_0_19, negated_conjecture, (l1_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.77/2.93  cnf(c_0_20, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.77/2.93  cnf(c_0_21, plain, (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.77/2.93  cnf(c_0_22, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|r2_hidden(esk1_3(esk3_0,X1,esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])])).
% 2.77/2.93  cnf(c_0_23, negated_conjecture, (~r2_lattice3(esk3_0,esk4_0,esk6_0)|~r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.77/2.93  cnf(c_0_24, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk1_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_18]), c_0_19])])).
% 2.77/2.93  fof(c_0_25, plain, ![X15, X16, X17]:(v2_struct_0(X15)|~v3_orders_2(X15)|~l1_orders_2(X15)|~m1_subset_1(X16,u1_struct_0(X15))|~m1_subset_1(X17,u1_struct_0(X15))|r3_orders_2(X15,X16,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).
% 2.77/2.93  fof(c_0_26, plain, ![X1, X2, X3]:(epred1_3(X3,X2,X1)=>((![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r1_yellow_0(X1,X4)))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X3)&![X5]:((v1_finset_1(X5)&m1_subset_1(X5,k1_zfmisc_1(X2)))=>~((r1_yellow_0(X1,X5)&X4=k1_yellow_0(X1,X5))))))))&![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_hidden(k1_yellow_0(X1,X4),X3))))), inference(split_equiv,[status(thm)],[c_0_12])).
% 2.77/2.93  cnf(c_0_27, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,X1,esk6_0)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 2.77/2.93  fof(c_0_28, plain, ![X12, X13, X14]:((~r3_orders_2(X12,X13,X14)|r1_orders_2(X12,X13,X14)|(v2_struct_0(X12)|~v3_orders_2(X12)|~l1_orders_2(X12)|~m1_subset_1(X13,u1_struct_0(X12))|~m1_subset_1(X14,u1_struct_0(X12))))&(~r1_orders_2(X12,X13,X14)|r3_orders_2(X12,X13,X14)|(v2_struct_0(X12)|~v3_orders_2(X12)|~l1_orders_2(X12)|~m1_subset_1(X13,u1_struct_0(X12))|~m1_subset_1(X14,u1_struct_0(X12))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 2.77/2.93  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))|~r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 2.77/2.93  cnf(c_0_30, plain, (v2_struct_0(X1)|r3_orders_2(X1,X2,X2)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 2.77/2.93  cnf(c_0_31, negated_conjecture, (v3_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.77/2.93  cnf(c_0_32, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.77/2.93  fof(c_0_33, plain, ![X39, X40, X41, X42, X43, X45]:(((~v1_finset_1(X42)|~m1_subset_1(X42,k1_zfmisc_1(X40))|(X42=k1_xboole_0|r1_yellow_0(X39,X42))|~epred1_3(X41,X40,X39))&(((v1_finset_1(esk7_4(X39,X40,X41,X43))|~r2_hidden(X43,X41)|~m1_subset_1(X43,u1_struct_0(X39))|~epred1_3(X41,X40,X39))&(m1_subset_1(esk7_4(X39,X40,X41,X43),k1_zfmisc_1(X40))|~r2_hidden(X43,X41)|~m1_subset_1(X43,u1_struct_0(X39))|~epred1_3(X41,X40,X39)))&((r1_yellow_0(X39,esk7_4(X39,X40,X41,X43))|~r2_hidden(X43,X41)|~m1_subset_1(X43,u1_struct_0(X39))|~epred1_3(X41,X40,X39))&(X43=k1_yellow_0(X39,esk7_4(X39,X40,X41,X43))|~r2_hidden(X43,X41)|~m1_subset_1(X43,u1_struct_0(X39))|~epred1_3(X41,X40,X39)))))&(~v1_finset_1(X45)|~m1_subset_1(X45,k1_zfmisc_1(X40))|(X45=k1_xboole_0|r2_hidden(k1_yellow_0(X39,X45),X41))|~epred1_3(X41,X40,X39))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])])])).
% 2.77/2.93  cnf(c_0_34, negated_conjecture, (m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))|~r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_23, c_0_27])).
% 2.77/2.93  fof(c_0_35, plain, ![X11]:v1_finset_1(k1_tarski(X11)), inference(variable_rename,[status(thm)],[fc1_finset_1])).
% 2.77/2.93  fof(c_0_36, plain, ![X28, X29, X30]:((((~r1_lattice3(X28,k1_tarski(X30),X29)|r1_orders_2(X28,X29,X30)|~m1_subset_1(X30,u1_struct_0(X28))|~m1_subset_1(X29,u1_struct_0(X28))|~l1_orders_2(X28))&(~r1_orders_2(X28,X29,X30)|r1_lattice3(X28,k1_tarski(X30),X29)|~m1_subset_1(X30,u1_struct_0(X28))|~m1_subset_1(X29,u1_struct_0(X28))|~l1_orders_2(X28)))&(~r2_lattice3(X28,k1_tarski(X30),X29)|r1_orders_2(X28,X30,X29)|~m1_subset_1(X30,u1_struct_0(X28))|~m1_subset_1(X29,u1_struct_0(X28))|~l1_orders_2(X28)))&(~r1_orders_2(X28,X30,X29)|r2_lattice3(X28,k1_tarski(X30),X29)|~m1_subset_1(X30,u1_struct_0(X28))|~m1_subset_1(X29,u1_struct_0(X28))|~l1_orders_2(X28))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_yellow_0])])])])).
% 2.77/2.93  cnf(c_0_37, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r3_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 2.77/2.93  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_29, c_0_24])).
% 2.77/2.93  cnf(c_0_39, negated_conjecture, (r3_orders_2(esk3_0,X1,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_18]), c_0_19]), c_0_31])]), c_0_32])).
% 2.77/2.93  fof(c_0_40, plain, ![X23, X24, X25, X26]:(((r2_lattice3(X23,X24,X25)|X25!=k1_yellow_0(X23,X24)|~r1_yellow_0(X23,X24)|~m1_subset_1(X25,u1_struct_0(X23))|~l1_orders_2(X23))&(~m1_subset_1(X26,u1_struct_0(X23))|(~r2_lattice3(X23,X24,X26)|r1_orders_2(X23,X25,X26))|X25!=k1_yellow_0(X23,X24)|~r1_yellow_0(X23,X24)|~m1_subset_1(X25,u1_struct_0(X23))|~l1_orders_2(X23)))&((m1_subset_1(esk2_3(X23,X24,X25),u1_struct_0(X23))|~r2_lattice3(X23,X24,X25)|X25=k1_yellow_0(X23,X24)|~r1_yellow_0(X23,X24)|~m1_subset_1(X25,u1_struct_0(X23))|~l1_orders_2(X23))&((r2_lattice3(X23,X24,esk2_3(X23,X24,X25))|~r2_lattice3(X23,X24,X25)|X25=k1_yellow_0(X23,X24)|~r1_yellow_0(X23,X24)|~m1_subset_1(X25,u1_struct_0(X23))|~l1_orders_2(X23))&(~r1_orders_2(X23,X25,esk2_3(X23,X24,X25))|~r2_lattice3(X23,X24,X25)|X25=k1_yellow_0(X23,X24)|~r1_yellow_0(X23,X24)|~m1_subset_1(X25,u1_struct_0(X23))|~l1_orders_2(X23))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).
% 2.77/2.93  cnf(c_0_41, plain, (X1=k1_xboole_0|r1_yellow_0(X3,X1)|~v1_finset_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~epred1_3(X4,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 2.77/2.93  cnf(c_0_42, negated_conjecture, (m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_34, c_0_24])).
% 2.77/2.93  cnf(c_0_43, plain, (v1_finset_1(k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 2.77/2.93  cnf(c_0_44, plain, (r2_lattice3(X1,k1_tarski(X2),X3)|~r1_orders_2(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 2.77/2.93  cnf(c_0_45, negated_conjecture, (r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r3_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_19]), c_0_31])]), c_0_32])).
% 2.77/2.93  cnf(c_0_46, negated_conjecture, (r3_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_39, c_0_38])).
% 2.77/2.93  cnf(c_0_47, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))|X3=k1_yellow_0(X1,X2)|~r2_lattice3(X1,X2,X3)|~r1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 2.77/2.93  cnf(c_0_48, plain, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~epred1_3(X2,esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])])).
% 2.77/2.93  cnf(c_0_49, negated_conjecture, (epred1_3(esk5_0,esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.77/2.93  cnf(c_0_50, negated_conjecture, (r2_lattice3(esk3_0,k1_tarski(X1),esk1_3(esk3_0,esk4_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_38]), c_0_19])])).
% 2.77/2.93  cnf(c_0_51, negated_conjecture, (r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_38]), c_0_46])).
% 2.77/2.93  cnf(c_0_52, negated_conjecture, (esk1_3(esk3_0,esk4_0,esk6_0)=k1_yellow_0(esk3_0,X1)|m1_subset_1(esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r1_yellow_0(esk3_0,X1)|~r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_38]), c_0_19])])).
% 2.77/2.93  cnf(c_0_53, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 2.77/2.93  cnf(c_0_54, negated_conjecture, (r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_38]), c_0_51])).
% 2.77/2.93  cnf(c_0_55, plain, (r2_lattice3(X1,X2,esk2_3(X1,X2,X3))|X3=k1_yellow_0(X1,X2)|~r2_lattice3(X1,X2,X3)|~r1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 2.77/2.93  cnf(c_0_56, plain, (X2=k1_yellow_0(X1,X3)|~r1_orders_2(X1,X2,esk2_3(X1,X3,X2))|~r2_lattice3(X1,X3,X2)|~r1_yellow_0(X1,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 2.77/2.93  cnf(c_0_57, plain, (r1_orders_2(X1,X2,X3)|~r2_lattice3(X1,k1_tarski(X2),X3)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 2.77/2.93  cnf(c_0_58, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])).
% 2.77/2.93  cnf(c_0_59, negated_conjecture, (esk1_3(esk3_0,esk4_0,esk6_0)=k1_yellow_0(esk3_0,X1)|r2_lattice3(esk3_0,X1,esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r1_yellow_0(esk3_0,X1)|~r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_38]), c_0_19])])).
% 2.77/2.93  cnf(c_0_60, negated_conjecture, (esk1_3(esk3_0,esk4_0,esk6_0)=k1_yellow_0(esk3_0,X1)|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r1_yellow_0(esk3_0,X1)|~r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))|~r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_38]), c_0_19])])).
% 2.77/2.93  cnf(c_0_61, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,X1,esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r2_lattice3(esk3_0,k1_tarski(X1),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_19])])).
% 2.77/2.93  cnf(c_0_62, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_53]), c_0_54])).
% 2.77/2.93  cnf(c_0_63, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_53]), c_0_54])).
% 2.77/2.93  cnf(c_0_64, plain, (X1=k1_yellow_0(X2,esk7_4(X2,X3,X4,X1))|~r2_hidden(X1,X4)|~m1_subset_1(X1,u1_struct_0(X2))|~epred1_3(X4,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 2.77/2.93  cnf(c_0_65, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_38]), c_0_62]), c_0_63])).
% 2.77/2.93  cnf(c_0_66, plain, (k1_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|~epred1_3(X2,X1,esk3_0)|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 2.77/2.93  cnf(c_0_67, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_66, c_0_49])).
% 2.77/2.93  cnf(c_0_68, plain, (m1_subset_1(esk7_4(X1,X2,X3,X4),k1_zfmisc_1(X2))|~r2_hidden(X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~epred1_3(X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 2.77/2.93  cnf(c_0_69, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_67, c_0_22])).
% 2.77/2.93  cnf(c_0_70, plain, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(X1))|~epred1_3(X2,X1,esk3_0)|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2)), inference(spm,[status(thm)],[c_0_68, c_0_65])).
% 2.77/2.93  cnf(c_0_71, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_29, c_0_69])).
% 2.77/2.93  cnf(c_0_72, plain, (r1_yellow_0(X1,esk7_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~epred1_3(X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 2.77/2.93  fof(c_0_73, plain, ![X31, X32, X33, X34]:((~r1_lattice3(X31,X33,X34)|r1_lattice3(X31,X32,X34)|~m1_subset_1(X34,u1_struct_0(X31))|~r1_tarski(X32,X33)|~l1_orders_2(X31))&(~r2_lattice3(X31,X33,X34)|r2_lattice3(X31,X32,X34)|~m1_subset_1(X34,u1_struct_0(X31))|~r1_tarski(X32,X33)|~l1_orders_2(X31))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_yellow_0])])])])).
% 2.77/2.93  cnf(c_0_74, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_70, c_0_49])).
% 2.77/2.93  cnf(c_0_75, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_34, c_0_69])).
% 2.77/2.93  cnf(c_0_76, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))|~r3_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_71]), c_0_19]), c_0_31])]), c_0_32])).
% 2.77/2.93  cnf(c_0_77, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r3_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_39, c_0_71])).
% 2.77/2.93  cnf(c_0_78, plain, (r1_orders_2(X2,X4,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|X4!=k1_yellow_0(X2,X3)|~r1_yellow_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 2.77/2.93  cnf(c_0_79, plain, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)))|~epred1_3(X2,X1,esk3_0)|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2)), inference(spm,[status(thm)],[c_0_72, c_0_65])).
% 2.77/2.93  cnf(c_0_80, plain, (r2_lattice3(X1,X4,X3)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~r1_tarski(X4,X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 2.77/2.93  fof(c_0_81, plain, ![X9, X10]:((~m1_subset_1(X9,k1_zfmisc_1(X10))|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|m1_subset_1(X9,k1_zfmisc_1(X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 2.77/2.93  cnf(c_0_82, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk5_0,esk6_0)|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_74, c_0_22])).
% 2.77/2.93  cnf(c_0_83, plain, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))|~epred1_3(X2,esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_75]), c_0_43])])).
% 2.77/2.93  cnf(c_0_84, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,k1_tarski(X1),esk1_3(esk3_0,esk4_0,esk6_0))|~r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_71]), c_0_19])])).
% 2.77/2.93  cnf(c_0_85, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_71]), c_0_77])).
% 2.77/2.93  cnf(c_0_86, plain, (r1_orders_2(X1,k1_yellow_0(X1,X2),X3)|~r1_yellow_0(X1,X2)|~r2_lattice3(X1,X2,X3)|~l1_orders_2(X1)|~m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_78])).
% 2.77/2.93  cnf(c_0_87, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_79, c_0_49])).
% 2.77/2.93  cnf(c_0_88, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|~r2_lattice3(esk3_0,X2,esk6_0)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_18]), c_0_19])])).
% 2.77/2.93  cnf(c_0_89, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_81])).
% 2.77/2.93  cnf(c_0_90, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_29, c_0_82])).
% 2.77/2.93  cnf(c_0_91, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|esk1_3(esk3_0,esk4_0,esk6_0)=k1_yellow_0(esk3_0,X1)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0))|~r1_yellow_0(esk3_0,X1)|~r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_71]), c_0_19])])).
% 2.77/2.93  cnf(c_0_92, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))), inference(spm,[status(thm)],[c_0_83, c_0_49])).
% 2.77/2.93  cnf(c_0_93, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_71]), c_0_85])).
% 2.77/2.93  cnf(c_0_94, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_34, c_0_82])).
% 2.77/2.93  cnf(c_0_95, negated_conjecture, (r1_orders_2(esk3_0,k1_yellow_0(esk3_0,X1),esk6_0)|~r1_yellow_0(esk3_0,X1)|~r2_lattice3(esk3_0,X1,esk6_0)|~m1_subset_1(k1_yellow_0(esk3_0,X1),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_18]), c_0_19])])).
% 2.77/2.93  cnf(c_0_96, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))|r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_87, c_0_22])).
% 2.77/2.93  cnf(c_0_97, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk1_3(esk3_0,X2,esk6_0),u1_struct_0(esk3_0))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_88, c_0_24])).
% 2.77/2.93  cnf(c_0_98, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0)|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 2.77/2.93  cnf(c_0_99, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_93])).
% 2.77/2.93  cnf(c_0_100, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|esk1_3(esk3_0,esk4_0,esk6_0)=k1_yellow_0(esk3_0,X1)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,X1,esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)))|~r1_yellow_0(esk3_0,X1)|~r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_71]), c_0_19])])).
% 2.77/2.93  cnf(c_0_101, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|esk1_3(esk3_0,esk4_0,esk6_0)=k1_yellow_0(esk3_0,X1)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|~r1_yellow_0(esk3_0,X1)|~r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))|~r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_71]), c_0_19])])).
% 2.77/2.93  cnf(c_0_102, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,X2,esk6_0)),k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_88, c_0_27])).
% 2.77/2.93  cnf(c_0_103, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_89, c_0_94])).
% 2.77/2.93  cnf(c_0_104, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk5_0,esk6_0)|r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)|~r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)|~m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 2.77/2.93  cnf(c_0_105, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 2.77/2.93  cnf(c_0_106, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,X1,esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))|~r2_lattice3(esk3_0,k1_tarski(X1),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_99]), c_0_19])])).
% 2.77/2.93  cnf(c_0_107, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_92]), c_0_93])).
% 2.77/2.93  cnf(c_0_108, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|~r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_92]), c_0_93])).
% 2.77/2.93  cnf(c_0_109, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_102, c_0_103])).
% 2.77/2.93  cnf(c_0_110, plain, (r2_lattice3(X1,X2,X3)|~r1_orders_2(X1,esk1_3(X1,X2,X3),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.77/2.93  cnf(c_0_111, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))|~m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_29])).
% 2.77/2.93  cnf(c_0_112, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_71]), c_0_107]), c_0_108])).
% 2.77/2.93  cnf(c_0_113, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))|~m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_109]), c_0_34])).
% 2.77/2.93  cnf(c_0_114, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|~r1_orders_2(esk3_0,esk1_3(esk3_0,X1,esk6_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_18]), c_0_19])])).
% 2.77/2.93  cnf(c_0_115, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk1_3(esk3_0,esk5_0,esk6_0),esk6_0)|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_38])).
% 2.77/2.93  cnf(c_0_116, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk1_3(esk3_0,esk5_0,esk6_0),esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_112]), c_0_42])).
% 2.77/2.93  cnf(c_0_117, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_115]), c_0_29])).
% 2.77/2.93  cnf(c_0_118, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_116]), c_0_34])).
% 2.77/2.93  cnf(c_0_119, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))|~r3_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_117]), c_0_19]), c_0_31])]), c_0_32])).
% 2.77/2.93  cnf(c_0_120, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r3_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_39, c_0_117])).
% 2.77/2.93  cnf(c_0_121, plain, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))|~epred1_3(X2,esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_118]), c_0_43])])).
% 2.77/2.93  cnf(c_0_122, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,k1_tarski(X1),esk1_3(esk3_0,esk4_0,esk6_0))|~r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_117]), c_0_19])])).
% 2.77/2.93  cnf(c_0_123, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_117]), c_0_120])).
% 2.77/2.93  cnf(c_0_124, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|esk1_3(esk3_0,esk4_0,esk6_0)=k1_yellow_0(esk3_0,X1)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0))|~r1_yellow_0(esk3_0,X1)|~r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_117]), c_0_19])])).
% 2.77/2.93  cnf(c_0_125, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))), inference(spm,[status(thm)],[c_0_121, c_0_49])).
% 2.77/2.93  cnf(c_0_126, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_117]), c_0_123])).
% 2.77/2.93  cnf(c_0_127, plain, (X1=k1_xboole_0|r2_hidden(k1_yellow_0(X3,X1),X4)|~v1_finset_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~epred1_3(X4,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 2.77/2.93  cnf(c_0_128, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_125]), c_0_126])).
% 2.77/2.93  cnf(c_0_129, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|esk1_3(esk3_0,esk4_0,esk6_0)=k1_yellow_0(esk3_0,X1)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,X1,esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)))|~r1_yellow_0(esk3_0,X1)|~r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_117]), c_0_19])])).
% 2.77/2.93  cnf(c_0_130, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|esk1_3(esk3_0,esk4_0,esk6_0)=k1_yellow_0(esk3_0,X1)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|~r1_yellow_0(esk3_0,X1)|~r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))|~r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_117]), c_0_19])])).
% 2.77/2.93  cnf(c_0_131, plain, (r1_orders_2(X1,X4,X3)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.77/2.93  cnf(c_0_132, plain, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|r2_hidden(k1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)|~epred1_3(X2,esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_42]), c_0_43])])).
% 2.77/2.93  cnf(c_0_133, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,X1,esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))|~r2_lattice3(esk3_0,k1_tarski(X1),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_128]), c_0_19])])).
% 2.77/2.93  cnf(c_0_134, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_125]), c_0_126])).
% 2.77/2.93  cnf(c_0_135, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|~r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_125]), c_0_126])).
% 2.77/2.93  cnf(c_0_136, negated_conjecture, (r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),X1)|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r2_lattice3(esk3_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_38]), c_0_19])])).
% 2.77/2.93  cnf(c_0_137, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|r2_hidden(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0)), inference(spm,[status(thm)],[c_0_132, c_0_49])).
% 2.77/2.93  cnf(c_0_138, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_133, c_0_117]), c_0_134]), c_0_135])).
% 2.77/2.93  cnf(c_0_139, negated_conjecture, (r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0)|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0))|~r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136, c_0_24]), c_0_18])])).
% 2.77/2.93  cnf(c_0_140, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_137, c_0_138])).
% 2.77/2.93  cnf(c_0_141, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0)|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_139, c_0_140])).
% 2.77/2.93  cnf(c_0_142, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk4_0,esk6_0)|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_114, c_0_141])).
% 2.77/2.93  cnf(c_0_143, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_142]), c_0_24])).
% 2.77/2.93  cnf(c_0_144, plain, (k1_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|~epred1_3(X2,X1,esk3_0)|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2)), inference(spm,[status(thm)],[c_0_64, c_0_143])).
% 2.77/2.93  cnf(c_0_145, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_144, c_0_49])).
% 2.77/2.93  cnf(c_0_146, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_145, c_0_22])).
% 2.77/2.93  cnf(c_0_147, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_34, c_0_146])).
% 2.77/2.93  cnf(c_0_148, plain, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_hidden(k1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)|~epred1_3(X2,esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_147]), c_0_43])])).
% 2.77/2.93  cnf(c_0_149, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_hidden(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0)), inference(spm,[status(thm)],[c_0_148, c_0_49])).
% 2.77/2.93  cnf(c_0_150, plain, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(X1))|~epred1_3(X2,X1,esk3_0)|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2)), inference(spm,[status(thm)],[c_0_68, c_0_143])).
% 2.77/2.93  cnf(c_0_151, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_149, c_0_138])).
% 2.77/2.93  cnf(c_0_152, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_150, c_0_49])).
% 2.77/2.93  cnf(c_0_153, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_21, c_0_151])).
% 2.77/2.93  cnf(c_0_154, plain, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)))|~epred1_3(X2,X1,esk3_0)|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2)), inference(spm,[status(thm)],[c_0_72, c_0_143])).
% 2.77/2.93  cnf(c_0_155, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk5_0,esk6_0)|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_152, c_0_22])).
% 2.77/2.93  cnf(c_0_156, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,X1,esk6_0)|~r1_tarski(X1,esk5_0)), inference(spm,[status(thm)],[c_0_88, c_0_146])).
% 2.77/2.93  cnf(c_0_157, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_tarski(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk5_0)), inference(spm,[status(thm)],[c_0_89, c_0_153])).
% 2.77/2.93  cnf(c_0_158, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_154, c_0_49])).
% 2.77/2.93  cnf(c_0_159, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_34, c_0_155])).
% 2.77/2.93  cnf(c_0_160, negated_conjecture, (r1_orders_2(esk3_0,X1,esk6_0)|~r2_lattice3(esk3_0,k1_tarski(X1),esk6_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_18]), c_0_19])])).
% 2.77/2.93  cnf(c_0_161, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_29, c_0_146])).
% 2.77/2.93  cnf(c_0_162, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0)), inference(spm,[status(thm)],[c_0_156, c_0_157])).
% 2.77/2.93  cnf(c_0_163, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_29, c_0_155])).
% 2.77/2.93  cnf(c_0_164, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))|r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_158, c_0_22])).
% 2.77/2.93  cnf(c_0_165, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_89, c_0_159])).
% 2.77/2.93  cnf(c_0_166, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_160, c_0_161]), c_0_162])).
% 2.77/2.93  cnf(c_0_167, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0)|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_89, c_0_163])).
% 2.77/2.93  cnf(c_0_168, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk5_0,esk6_0)|r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)|~r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)|~m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_95, c_0_164])).
% 2.77/2.93  cnf(c_0_169, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_102, c_0_165])).
% 2.77/2.93  cnf(c_0_170, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk4_0,esk6_0)), inference(spm,[status(thm)],[c_0_114, c_0_166])).
% 2.77/2.93  cnf(c_0_171, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_97, c_0_167])).
% 2.77/2.93  cnf(c_0_172, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))|~m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_168, c_0_169]), c_0_34])).
% 2.77/2.93  cnf(c_0_173, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_170]), c_0_146])).
% 2.77/2.93  cnf(c_0_174, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))|~m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_168, c_0_171]), c_0_29])).
% 2.77/2.93  cnf(c_0_175, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk1_3(esk3_0,esk5_0,esk6_0),esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_172, c_0_173]), c_0_42])).
% 2.77/2.93  cnf(c_0_176, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk1_3(esk3_0,esk5_0,esk6_0),esk6_0)|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_174, c_0_173]), c_0_38])).
% 2.77/2.93  cnf(c_0_177, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_175]), c_0_34])).
% 2.77/2.93  cnf(c_0_178, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_176]), c_0_29])).
% 2.77/2.93  cnf(c_0_179, plain, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_hidden(k1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)|~epred1_3(X2,esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_177]), c_0_43])])).
% 2.77/2.93  cnf(c_0_180, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),X1)|~r2_lattice3(esk3_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_178]), c_0_19])])).
% 2.77/2.93  cnf(c_0_181, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_hidden(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0)), inference(spm,[status(thm)],[c_0_179, c_0_49])).
% 2.77/2.93  cnf(c_0_182, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0)|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))|~r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_180, c_0_155]), c_0_18])])).
% 2.77/2.93  cnf(c_0_183, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_181, c_0_138])).
% 2.77/2.93  cnf(c_0_184, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0)|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_182, c_0_183])).
% 2.77/2.93  cnf(c_0_185, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk4_0,esk6_0)|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_114, c_0_184])).
% 2.77/2.93  cnf(c_0_186, negated_conjecture, (r2_lattice3(esk3_0,esk4_0,esk6_0)|r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.77/2.93  cnf(c_0_187, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_185]), c_0_155])).
% 2.77/2.93  cnf(c_0_188, negated_conjecture, (r2_lattice3(esk3_0,esk5_0,esk6_0)|r2_lattice3(esk3_0,X1,esk6_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_88, c_0_186])).
% 2.77/2.93  cnf(c_0_189, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0)), inference(spm,[status(thm)],[c_0_89, c_0_187])).
% 2.77/2.93  cnf(c_0_190, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)|r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_188, c_0_189])).
% 2.77/2.93  cnf(c_0_191, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk5_0,esk6_0)|r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)|~m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_168, c_0_190])).
% 2.77/2.93  cnf(c_0_192, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_191, c_0_173]), c_0_24]), c_0_114])).
% 2.77/2.93  cnf(c_0_193, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_180, c_0_192]), c_0_18])]), c_0_183])).
% 2.77/2.93  fof(c_0_194, plain, ![X6]:~v1_xboole_0(k1_tarski(X6)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).
% 2.77/2.93  cnf(c_0_195, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk4_0,esk6_0)), inference(spm,[status(thm)],[c_0_114, c_0_193])).
% 2.77/2.93  cnf(c_0_196, plain, (~v1_xboole_0(k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_194])).
% 2.77/2.93  cnf(c_0_197, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_195]), c_0_192])).
% 2.77/2.93  cnf(c_0_198, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 2.77/2.93  cnf(c_0_199, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_196, c_0_197]), c_0_198])]), ['proof']).
% 2.77/2.93  # SZS output end CNFRefutation
% 2.77/2.93  # Proof object total steps             : 200
% 2.77/2.93  # Proof object clause steps            : 173
% 2.77/2.93  # Proof object formula steps           : 27
% 2.77/2.93  # Proof object conjectures             : 140
% 2.77/2.93  # Proof object clause conjectures      : 137
% 2.77/2.93  # Proof object formula conjectures     : 3
% 2.77/2.93  # Proof object initial clauses used    : 30
% 2.77/2.93  # Proof object initial formulas used   : 12
% 2.77/2.93  # Proof object generating inferences   : 142
% 2.77/2.93  # Proof object simplifying inferences  : 124
% 2.77/2.93  # Training examples: 0 positive, 0 negative
% 2.77/2.93  # Parsed axioms                        : 12
% 2.77/2.93  # Removed by relevancy pruning/SinE    : 0
% 2.77/2.93  # Initial clauses                      : 40
% 2.77/2.93  # Removed in clause preprocessing      : 0
% 2.77/2.93  # Initial clauses in saturation        : 40
% 2.77/2.93  # Processed clauses                    : 9580
% 2.77/2.93  # ...of these trivial                  : 222
% 2.77/2.93  # ...subsumed                          : 3497
% 2.77/2.93  # ...remaining for further processing  : 5861
% 2.77/2.93  # Other redundant clauses eliminated   : 2
% 2.77/2.93  # Clauses deleted for lack of memory   : 0
% 2.77/2.93  # Backward-subsumed                    : 2728
% 2.77/2.93  # Backward-rewritten                   : 2180
% 2.77/2.93  # Generated clauses                    : 38417
% 2.77/2.93  # ...of the previous two non-trivial   : 38540
% 2.77/2.93  # Contextual simplify-reflections      : 446
% 2.77/2.93  # Paramodulations                      : 38415
% 2.77/2.93  # Factorizations                       : 0
% 2.77/2.93  # Equation resolutions                 : 2
% 2.77/2.93  # Propositional unsat checks           : 0
% 2.77/2.93  #    Propositional check models        : 0
% 2.77/2.93  #    Propositional check unsatisfiable : 0
% 2.77/2.93  #    Propositional clauses             : 0
% 2.77/2.93  #    Propositional clauses after purity: 0
% 2.77/2.93  #    Propositional unsat core size     : 0
% 2.77/2.93  #    Propositional preprocessing time  : 0.000
% 2.77/2.93  #    Propositional encoding time       : 0.000
% 2.77/2.93  #    Propositional solver time         : 0.000
% 2.77/2.93  #    Success case prop preproc time    : 0.000
% 2.77/2.93  #    Success case prop encoding time   : 0.000
% 2.77/2.93  #    Success case prop solver time     : 0.000
% 2.77/2.93  # Current number of processed clauses  : 911
% 2.77/2.93  #    Positive orientable unit clauses  : 93
% 2.77/2.93  #    Positive unorientable unit clauses: 0
% 2.77/2.93  #    Negative unit clauses             : 2
% 2.77/2.93  #    Non-unit-clauses                  : 816
% 2.77/2.93  # Current number of unprocessed clauses: 26641
% 2.77/2.93  # ...number of literals in the above   : 164329
% 2.77/2.93  # Current number of archived formulas  : 0
% 2.77/2.93  # Current number of archived clauses   : 4948
% 2.77/2.93  # Clause-clause subsumption calls (NU) : 4231009
% 2.77/2.93  # Rec. Clause-clause subsumption calls : 610360
% 2.77/2.93  # Non-unit clause-clause subsumptions  : 6667
% 2.77/2.93  # Unit Clause-clause subsumption calls : 21397
% 2.77/2.93  # Rewrite failures with RHS unbound    : 0
% 2.77/2.93  # BW rewrite match attempts            : 2220
% 2.77/2.93  # BW rewrite match successes           : 31
% 2.77/2.93  # Condensation attempts                : 0
% 2.77/2.93  # Condensation successes               : 0
% 2.77/2.93  # Termbank termtop insertions          : 2376897
% 2.77/2.93  
% 2.77/2.93  # -------------------------------------------------
% 2.77/2.93  # User time                : 2.560 s
% 2.77/2.93  # System time              : 0.025 s
% 2.77/2.93  # Total time               : 2.585 s
% 2.77/2.93  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
