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

% Result     : Theorem 1.36s
% Output     : CNFRefutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :  153 (12359 expanded)
%              Number of clauses        :  126 (4322 expanded)
%              Number of leaves         :   13 (3967 expanded)
%              Depth                    :   46
%              Number of atoms          :  620 (116652 expanded)
%              Number of equality atoms :  102 (10468 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t57_waybel_0,conjecture,(
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
                       => r2_yellow_0(X1,X4) ) )
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ~ ( r2_hidden(X4,X3)
                          & ! [X5] :
                              ( ( v1_finset_1(X5)
                                & m1_subset_1(X5,k1_zfmisc_1(X2)) )
                             => ~ ( r2_yellow_0(X1,X5)
                                  & X4 = k2_yellow_0(X1,X5) ) ) ) )
                  & ! [X4] :
                      ( ( v1_finset_1(X4)
                        & m1_subset_1(X4,k1_zfmisc_1(X2)) )
                     => ( X4 != k1_xboole_0
                       => r2_hidden(k2_yellow_0(X1,X4),X3) ) ) )
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r1_lattice3(X1,X2,X4)
                    <=> r1_lattice3(X1,X3,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_waybel_0)).

fof(d8_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r1_lattice3(X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r1_orders_2(X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

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

fof(dt_k2_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_0)).

fof(fc1_finset_1,axiom,(
    ! [X1] : v1_finset_1(k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_finset_1)).

fof(t4_yellow_0,axiom,(
    ! [X1] :
      ( ( v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_orders_2(X1,X2,X3)
               => ! [X4] :
                    ( ( r1_lattice3(X1,X4,X3)
                     => r1_lattice3(X1,X4,X2) )
                    & ( r2_lattice3(X1,X4,X2)
                     => r2_lattice3(X1,X4,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_0)).

fof(d10_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r2_yellow_0(X1,X2)
           => ( X3 = k2_yellow_0(X1,X2)
            <=> ( r1_lattice3(X1,X2,X3)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r1_lattice3(X1,X2,X4)
                     => r1_orders_2(X1,X4,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_yellow_0)).

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
             => r2_yellow_0(X1,X4) ) )
        & ! [X4] :
            ( m1_subset_1(X4,u1_struct_0(X1))
           => ~ ( r2_hidden(X4,X3)
                & ! [X5] :
                    ( ( v1_finset_1(X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X2)) )
                   => ~ ( r2_yellow_0(X1,X5)
                        & X4 = k2_yellow_0(X1,X5) ) ) ) )
        & ! [X4] :
            ( ( v1_finset_1(X4)
              & m1_subset_1(X4,k1_zfmisc_1(X2)) )
           => ( X4 != k1_xboole_0
             => r2_hidden(k2_yellow_0(X1,X4),X3) ) ) ) ) ),
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
                     => ( r1_lattice3(X1,X2,X4)
                      <=> r1_lattice3(X1,X3,X4) ) ) ) ) ) ) ),
    inference(apply_def,[status(thm)],[inference(assume_negation,[status(cth)],[t57_waybel_0]),c_0_12])).

fof(c_0_14,plain,(
    ! [X15,X16,X17,X18] :
      ( ( ~ r1_lattice3(X15,X16,X17)
        | ~ m1_subset_1(X18,u1_struct_0(X15))
        | ~ r2_hidden(X18,X16)
        | r1_orders_2(X15,X17,X18)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ l1_orders_2(X15) )
      & ( m1_subset_1(esk1_3(X15,X16,X17),u1_struct_0(X15))
        | r1_lattice3(X15,X16,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ l1_orders_2(X15) )
      & ( r2_hidden(esk1_3(X15,X16,X17),X16)
        | r1_lattice3(X15,X16,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ l1_orders_2(X15) )
      & ( ~ r1_orders_2(X15,X17,esk1_3(X15,X16,X17))
        | r1_lattice3(X15,X16,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ l1_orders_2(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).

fof(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v3_orders_2(esk3_0)
    & v4_orders_2(esk3_0)
    & l1_orders_2(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & epred1_3(esk5_0,esk4_0,esk3_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk3_0))
    & ( ~ r1_lattice3(esk3_0,esk4_0,esk6_0)
      | ~ r1_lattice3(esk3_0,esk5_0,esk6_0) )
    & ( r1_lattice3(esk3_0,esk4_0,esk6_0)
      | r1_lattice3(esk3_0,esk5_0,esk6_0) ) ),
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
    | r1_lattice3(X1,X2,X3)
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
    ( r1_lattice3(esk3_0,X1,esk6_0)
    | r2_hidden(esk1_3(esk3_0,X1,esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

cnf(c_0_23,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk6_0)
    | r1_tarski(k1_tarski(esk1_3(esk3_0,X1,esk6_0)),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_25,plain,(
    ! [X25,X26] :
      ( ~ l1_orders_2(X25)
      | m1_subset_1(k2_yellow_0(X25,X26),u1_struct_0(X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_yellow_0])])).

fof(c_0_26,plain,(
    ! [X1,X2,X3] :
      ( epred1_3(X3,X2,X1)
     => ( ! [X4] :
            ( ( v1_finset_1(X4)
              & m1_subset_1(X4,k1_zfmisc_1(X2)) )
           => ( X4 != k1_xboole_0
             => r2_yellow_0(X1,X4) ) )
        & ! [X4] :
            ( m1_subset_1(X4,u1_struct_0(X1))
           => ~ ( r2_hidden(X4,X3)
                & ! [X5] :
                    ( ( v1_finset_1(X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X2)) )
                   => ~ ( r2_yellow_0(X1,X5)
                        & X4 = k2_yellow_0(X1,X5) ) ) ) )
        & ! [X4] :
            ( ( v1_finset_1(X4)
              & m1_subset_1(X4,k1_zfmisc_1(X2)) )
           => ( X4 != k1_xboole_0
             => r2_hidden(k2_yellow_0(X1,X4),X3) ) ) ) ) ),
    inference(split_equiv,[status(thm)],[c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( ~ r1_lattice3(esk3_0,esk4_0,esk6_0)
    | ~ r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,X1,esk6_0)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_30,plain,
    ( m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_31,plain,(
    ! [X42,X43,X44,X45,X46,X48] :
      ( ( ~ v1_finset_1(X45)
        | ~ m1_subset_1(X45,k1_zfmisc_1(X43))
        | X45 = k1_xboole_0
        | r2_yellow_0(X42,X45)
        | ~ epred1_3(X44,X43,X42) )
      & ( v1_finset_1(esk7_4(X42,X43,X44,X46))
        | ~ r2_hidden(X46,X44)
        | ~ m1_subset_1(X46,u1_struct_0(X42))
        | ~ epred1_3(X44,X43,X42) )
      & ( m1_subset_1(esk7_4(X42,X43,X44,X46),k1_zfmisc_1(X43))
        | ~ r2_hidden(X46,X44)
        | ~ m1_subset_1(X46,u1_struct_0(X42))
        | ~ epred1_3(X44,X43,X42) )
      & ( r2_yellow_0(X42,esk7_4(X42,X43,X44,X46))
        | ~ r2_hidden(X46,X44)
        | ~ m1_subset_1(X46,u1_struct_0(X42))
        | ~ epred1_3(X44,X43,X42) )
      & ( X46 = k2_yellow_0(X42,esk7_4(X42,X43,X44,X46))
        | ~ r2_hidden(X46,X44)
        | ~ m1_subset_1(X46,u1_struct_0(X42))
        | ~ epred1_3(X44,X43,X42) )
      & ( ~ v1_finset_1(X48)
        | ~ m1_subset_1(X48,k1_zfmisc_1(X43))
        | X48 = k1_xboole_0
        | r2_hidden(k2_yellow_0(X42,X48),X44)
        | ~ epred1_3(X44,X43,X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])])])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | ~ r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_18]),c_0_19])])).

fof(c_0_34,plain,(
    ! [X14] : v1_finset_1(k1_tarski(X14)) ),
    inference(variable_rename,[status(thm)],[fc1_finset_1])).

cnf(c_0_35,plain,
    ( r1_orders_2(X1,X3,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(k2_yellow_0(esk3_0,X1),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_19])).

cnf(c_0_37,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(k2_yellow_0(X3,X1),X4)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ epred1_3(X4,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,plain,
    ( v1_finset_1(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_40,plain,(
    ! [X27,X28,X29,X30] :
      ( ( ~ r1_lattice3(X27,X30,X29)
        | r1_lattice3(X27,X30,X28)
        | ~ r1_orders_2(X27,X28,X29)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | ~ v4_orders_2(X27)
        | ~ l1_orders_2(X27) )
      & ( ~ r2_lattice3(X27,X30,X28)
        | r2_lattice3(X27,X30,X29)
        | ~ r1_orders_2(X27,X28,X29)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | ~ v4_orders_2(X27)
        | ~ l1_orders_2(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_yellow_0])])])])).

cnf(c_0_41,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,k2_yellow_0(esk3_0,X2))
    | ~ r1_lattice3(esk3_0,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(k2_yellow_0(esk3_0,X2),X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_19])])).

cnf(c_0_42,plain,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | r2_hidden(k2_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)
    | ~ epred1_3(X2,esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])])).

cnf(c_0_43,negated_conjecture,
    ( epred1_3(esk5_0,esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_44,plain,(
    ! [X20,X21,X22,X23] :
      ( ( r1_lattice3(X20,X21,X22)
        | X22 != k2_yellow_0(X20,X21)
        | ~ r2_yellow_0(X20,X21)
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | ~ l1_orders_2(X20) )
      & ( ~ m1_subset_1(X23,u1_struct_0(X20))
        | ~ r1_lattice3(X20,X21,X23)
        | r1_orders_2(X20,X23,X22)
        | X22 != k2_yellow_0(X20,X21)
        | ~ r2_yellow_0(X20,X21)
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | ~ l1_orders_2(X20) )
      & ( m1_subset_1(esk2_3(X20,X21,X22),u1_struct_0(X20))
        | ~ r1_lattice3(X20,X21,X22)
        | X22 = k2_yellow_0(X20,X21)
        | ~ r2_yellow_0(X20,X21)
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | ~ l1_orders_2(X20) )
      & ( r1_lattice3(X20,X21,esk2_3(X20,X21,X22))
        | ~ r1_lattice3(X20,X21,X22)
        | X22 = k2_yellow_0(X20,X21)
        | ~ r2_yellow_0(X20,X21)
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | ~ l1_orders_2(X20) )
      & ( ~ r1_orders_2(X20,esk2_3(X20,X21,X22),X22)
        | ~ r1_lattice3(X20,X21,X22)
        | X22 = k2_yellow_0(X20,X21)
        | ~ r2_yellow_0(X20,X21)
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | ~ l1_orders_2(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_yellow_0])])])])])).

cnf(c_0_45,plain,
    ( X1 = k1_xboole_0
    | r2_yellow_0(X3,X1)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ epred1_3(X4,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_46,plain,(
    ! [X31,X32,X33] :
      ( ( ~ r1_lattice3(X31,k1_tarski(X33),X32)
        | r1_orders_2(X31,X32,X33)
        | ~ m1_subset_1(X33,u1_struct_0(X31))
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | ~ l1_orders_2(X31) )
      & ( ~ r1_orders_2(X31,X32,X33)
        | r1_lattice3(X31,k1_tarski(X33),X32)
        | ~ m1_subset_1(X33,u1_struct_0(X31))
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | ~ l1_orders_2(X31) )
      & ( ~ r2_lattice3(X31,k1_tarski(X33),X32)
        | r1_orders_2(X31,X33,X32)
        | ~ m1_subset_1(X33,u1_struct_0(X31))
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | ~ l1_orders_2(X31) )
      & ( ~ r1_orders_2(X31,X33,X32)
        | r2_lattice3(X31,k1_tarski(X33),X32)
        | ~ m1_subset_1(X33,u1_struct_0(X31))
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | ~ l1_orders_2(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_yellow_0])])])])).

cnf(c_0_47,plain,
    ( r1_lattice3(X1,X2,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,X4,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( v4_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_49,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,X1))
    | m1_subset_1(esk1_3(esk3_0,X2,esk6_0),u1_struct_0(esk3_0))
    | ~ r2_hidden(k2_yellow_0(esk3_0,X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_33]),c_0_18])])).

cnf(c_0_50,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | r2_hidden(k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_51,plain,
    ( r1_lattice3(X1,X2,X3)
    | X3 != k2_yellow_0(X1,X2)
    | ~ r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,plain,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ epred1_3(X2,esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_38]),c_0_39])])).

cnf(c_0_53,plain,
    ( r1_orders_2(X1,X3,X2)
    | ~ r1_lattice3(X1,k1_tarski(X2),X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_33])).

cnf(c_0_55,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk6_0)
    | ~ r1_orders_2(esk3_0,esk6_0,X2)
    | ~ r1_lattice3(esk3_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_18]),c_0_48]),c_0_19])])).

cnf(c_0_56,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,plain,
    ( r1_lattice3(X1,X2,k2_yellow_0(X1,X2))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_51]),c_0_30])).

cnf(c_0_58,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_43])).

cnf(c_0_59,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,X1)
    | ~ r1_lattice3(esk3_0,k1_tarski(X1),esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_18]),c_0_19])])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_33])).

cnf(c_0_61,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_lattice3(esk3_0,X1,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_36])])).

cnf(c_0_62,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_19])])).

cnf(c_0_63,plain,
    ( r1_lattice3(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,esk1_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_64,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk6_0)
    | ~ r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,X1,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_18]),c_0_19])])).

cnf(c_0_67,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,esk4_0,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_28])).

cnf(c_0_70,plain,
    ( X1 = k2_yellow_0(X2,esk7_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ epred1_3(X4,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_71,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_68]),c_0_33])).

cnf(c_0_72,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_28])).

cnf(c_0_74,plain,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))
    | r2_hidden(k2_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)
    | ~ epred1_3(X2,esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_69]),c_0_39])])).

cnf(c_0_75,plain,
    ( k2_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | ~ epred1_3(X2,X1,esk3_0)
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_76,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))
    | r1_tarski(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_78,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,X1))
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,X2,esk6_0)),k1_zfmisc_1(X2))
    | ~ r2_hidden(k2_yellow_0(esk3_0,X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_28]),c_0_18])])).

cnf(c_0_79,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))
    | r2_hidden(k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_43])).

cnf(c_0_80,plain,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))
    | ~ epred1_3(X2,esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_69]),c_0_39])])).

cnf(c_0_81,negated_conjecture,
    ( k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_43])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))
    | r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_83,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_84,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_43])).

cnf(c_0_85,plain,
    ( m1_subset_1(esk7_4(X1,X2,X3,X4),k1_zfmisc_1(X2))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_86,negated_conjecture,
    ( k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_87,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))
    | ~ r1_lattice3(esk3_0,X1,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_83]),c_0_36])])).

cnf(c_0_88,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_84]),c_0_19])])).

cnf(c_0_89,plain,
    ( r2_yellow_0(X1,esk7_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_90,plain,(
    ! [X34,X35,X36,X37] :
      ( ( ~ r1_lattice3(X34,X36,X37)
        | r1_lattice3(X34,X35,X37)
        | ~ m1_subset_1(X37,u1_struct_0(X34))
        | ~ r1_tarski(X35,X36)
        | ~ l1_orders_2(X34) )
      & ( ~ r2_lattice3(X34,X36,X37)
        | r2_lattice3(X34,X35,X37)
        | ~ m1_subset_1(X37,u1_struct_0(X34))
        | ~ r1_tarski(X35,X36)
        | ~ l1_orders_2(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_yellow_0])])])])).

cnf(c_0_91,plain,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(X1))
    | ~ epred1_3(X2,X1,esk3_0)
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2) ),
    inference(spm,[status(thm)],[c_0_85,c_0_71])).

cnf(c_0_92,negated_conjecture,
    ( k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_86])).

cnf(c_0_93,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_94,plain,
    ( r1_orders_2(X2,X1,X4)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | X4 != k2_yellow_0(X2,X3)
    | ~ r2_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_95,plain,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)))
    | ~ epred1_3(X2,X1,esk3_0)
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2) ),
    inference(spm,[status(thm)],[c_0_89,c_0_71])).

cnf(c_0_96,plain,
    ( r1_lattice3(X1,X4,X3)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_tarski(X4,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_97,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_91,c_0_43])).

cnf(c_0_98,negated_conjecture,
    ( k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_99,plain,
    ( r1_orders_2(X1,X2,k2_yellow_0(X1,X3))
    | ~ r2_yellow_0(X1,X3)
    | ~ r1_lattice3(X1,X3,X2)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_94]),c_0_30])).

cnf(c_0_100,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_95,c_0_43])).

cnf(c_0_101,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk6_0)
    | ~ r1_lattice3(esk3_0,X2,esk6_0)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_18]),c_0_19])])).

cnf(c_0_102,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_97,c_0_82])).

cnf(c_0_103,negated_conjecture,
    ( k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,esk4_0,esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_98])).

cnf(c_0_104,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,X1))
    | ~ r2_yellow_0(esk3_0,X1)
    | ~ r1_lattice3(esk3_0,X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_18]),c_0_19])])).

cnf(c_0_105,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))
    | r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_100,c_0_22])).

cnf(c_0_106,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,X2,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_101,c_0_33])).

cnf(c_0_107,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))
    | r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_102])).

cnf(c_0_108,negated_conjecture,
    ( k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_103]),c_0_28])).

cnf(c_0_109,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))))
    | r1_lattice3(esk3_0,esk5_0,esk6_0)
    | ~ r1_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_110,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_111,negated_conjecture,
    ( k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_tarski(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_108])).

cnf(c_0_112,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_54])).

cnf(c_0_113,negated_conjecture,
    ( k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_111]),c_0_81])).

cnf(c_0_114,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_115,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_114]),c_0_54])).

cnf(c_0_116,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_115])).

cnf(c_0_117,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_116,c_0_93])).

cnf(c_0_118,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,esk4_0,esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_117])).

cnf(c_0_119,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_118]),c_0_28])).

cnf(c_0_120,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,esk5_0,esk6_0)
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_97,c_0_22])).

cnf(c_0_121,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_tarski(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_119])).

cnf(c_0_122,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_120])).

cnf(c_0_123,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_121])).

cnf(c_0_124,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,X2,esk6_0)),k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_101,c_0_28])).

cnf(c_0_125,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_122])).

cnf(c_0_126,negated_conjecture,
    ( r1_lattice3(esk3_0,esk4_0,esk6_0)
    | r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_127,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_97,c_0_123])).

cnf(c_0_128,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_124,c_0_125])).

cnf(c_0_129,negated_conjecture,
    ( r1_lattice3(esk3_0,esk5_0,esk6_0)
    | r1_lattice3(esk3_0,X1,esk6_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_101,c_0_126])).

cnf(c_0_130,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_127])).

cnf(c_0_131,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))))
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_128]),c_0_32])).

cnf(c_0_132,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)
    | r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_129,c_0_130])).

cnf(c_0_133,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_131,c_0_113])).

cnf(c_0_134,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))))
    | r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_109,c_0_132])).

cnf(c_0_135,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_133]),c_0_32])).

cnf(c_0_136,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_113]),c_0_66])).

cnf(c_0_137,plain,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_hidden(k2_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)
    | ~ epred1_3(X2,esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_135]),c_0_39])])).

cnf(c_0_138,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,X1))
    | ~ r2_hidden(k2_yellow_0(esk3_0,X1),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_136]),c_0_18])])).

cnf(c_0_139,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_hidden(k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_137,c_0_43])).

cnf(c_0_140,plain,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))
    | ~ epred1_3(X2,esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_135]),c_0_39])])).

cnf(c_0_141,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_138,c_0_139])).

cnf(c_0_142,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_140,c_0_43])).

cnf(c_0_143,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,X1,esk6_0)
    | ~ r1_lattice3(esk3_0,X1,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_141]),c_0_36])])).

cnf(c_0_144,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_142]),c_0_19])])).

cnf(c_0_145,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_143,c_0_144])).

cnf(c_0_146,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_116,c_0_145])).

fof(c_0_147,plain,(
    ! [X6] : ~ v1_xboole_0(k1_tarski(X6)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

cnf(c_0_148,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_146])).

cnf(c_0_149,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_147])).

cnf(c_0_150,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_148]),c_0_136])).

cnf(c_0_151,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_152,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149,c_0_150]),c_0_151])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:16:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.36/1.59  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 1.36/1.59  # and selection function SelectNewComplexAHP.
% 1.36/1.59  #
% 1.36/1.59  # Preprocessing time       : 0.029 s
% 1.36/1.59  # Presaturation interreduction done
% 1.36/1.59  
% 1.36/1.59  # Proof found!
% 1.36/1.59  # SZS status Theorem
% 1.36/1.59  # SZS output start CNFRefutation
% 1.36/1.59  fof(t57_waybel_0, conjecture, ![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(((![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_yellow_0(X1,X4)))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X3)&![X5]:((v1_finset_1(X5)&m1_subset_1(X5,k1_zfmisc_1(X2)))=>~((r2_yellow_0(X1,X5)&X4=k2_yellow_0(X1,X5))))))))&![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_hidden(k2_yellow_0(X1,X4),X3))))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X4)<=>r1_lattice3(X1,X3,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_waybel_0)).
% 1.36/1.59  fof(d8_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattice3)).
% 1.36/1.59  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.36/1.59  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.36/1.59  fof(dt_k2_yellow_0, axiom, ![X1, X2]:(l1_orders_2(X1)=>m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_0)).
% 1.36/1.59  fof(fc1_finset_1, axiom, ![X1]:v1_finset_1(k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_finset_1)).
% 1.36/1.59  fof(t4_yellow_0, axiom, ![X1]:((v4_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_orders_2(X1,X2,X3)=>![X4]:((r1_lattice3(X1,X4,X3)=>r1_lattice3(X1,X4,X2))&(r2_lattice3(X1,X4,X2)=>r2_lattice3(X1,X4,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_yellow_0)).
% 1.36/1.59  fof(d10_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_yellow_0(X1,X2)=>(X3=k2_yellow_0(X1,X2)<=>(r1_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X4)=>r1_orders_2(X1,X4,X3)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_yellow_0)).
% 1.36/1.59  fof(t7_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((((r1_lattice3(X1,k1_tarski(X3),X2)=>r1_orders_2(X1,X2,X3))&(r1_orders_2(X1,X2,X3)=>r1_lattice3(X1,k1_tarski(X3),X2)))&(r2_lattice3(X1,k1_tarski(X3),X2)=>r1_orders_2(X1,X3,X2)))&(r1_orders_2(X1,X3,X2)=>r2_lattice3(X1,k1_tarski(X3),X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_yellow_0)).
% 1.36/1.59  fof(t9_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r1_lattice3(X1,X3,X4)=>r1_lattice3(X1,X2,X4))&(r2_lattice3(X1,X3,X4)=>r2_lattice3(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_yellow_0)).
% 1.36/1.59  fof(fc2_xboole_0, axiom, ![X1]:~(v1_xboole_0(k1_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 1.36/1.59  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.36/1.59  fof(c_0_12, plain, ![X1, X2, X3]:(epred1_3(X3,X2,X1)<=>((![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_yellow_0(X1,X4)))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X3)&![X5]:((v1_finset_1(X5)&m1_subset_1(X5,k1_zfmisc_1(X2)))=>~((r2_yellow_0(X1,X5)&X4=k2_yellow_0(X1,X5))))))))&![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_hidden(k2_yellow_0(X1,X4),X3))))), introduced(definition)).
% 1.36/1.59  fof(c_0_13, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(epred1_3(X3,X2,X1)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X4)<=>r1_lattice3(X1,X3,X4)))))))), inference(apply_def,[status(thm)],[inference(assume_negation,[status(cth)],[t57_waybel_0]), c_0_12])).
% 1.36/1.59  fof(c_0_14, plain, ![X15, X16, X17, X18]:((~r1_lattice3(X15,X16,X17)|(~m1_subset_1(X18,u1_struct_0(X15))|(~r2_hidden(X18,X16)|r1_orders_2(X15,X17,X18)))|~m1_subset_1(X17,u1_struct_0(X15))|~l1_orders_2(X15))&((m1_subset_1(esk1_3(X15,X16,X17),u1_struct_0(X15))|r1_lattice3(X15,X16,X17)|~m1_subset_1(X17,u1_struct_0(X15))|~l1_orders_2(X15))&((r2_hidden(esk1_3(X15,X16,X17),X16)|r1_lattice3(X15,X16,X17)|~m1_subset_1(X17,u1_struct_0(X15))|~l1_orders_2(X15))&(~r1_orders_2(X15,X17,esk1_3(X15,X16,X17))|r1_lattice3(X15,X16,X17)|~m1_subset_1(X17,u1_struct_0(X15))|~l1_orders_2(X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).
% 1.36/1.59  fof(c_0_15, negated_conjecture, ((((~v2_struct_0(esk3_0)&v3_orders_2(esk3_0))&v4_orders_2(esk3_0))&l1_orders_2(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(epred1_3(esk5_0,esk4_0,esk3_0)&(m1_subset_1(esk6_0,u1_struct_0(esk3_0))&((~r1_lattice3(esk3_0,esk4_0,esk6_0)|~r1_lattice3(esk3_0,esk5_0,esk6_0))&(r1_lattice3(esk3_0,esk4_0,esk6_0)|r1_lattice3(esk3_0,esk5_0,esk6_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 1.36/1.59  fof(c_0_16, plain, ![X7, X8]:((~r1_tarski(k1_tarski(X7),X8)|r2_hidden(X7,X8))&(~r2_hidden(X7,X8)|r1_tarski(k1_tarski(X7),X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 1.36/1.59  cnf(c_0_17, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.36/1.59  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.36/1.59  cnf(c_0_19, negated_conjecture, (l1_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.36/1.59  fof(c_0_20, plain, ![X9, X10]:((~m1_subset_1(X9,k1_zfmisc_1(X10))|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|m1_subset_1(X9,k1_zfmisc_1(X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 1.36/1.59  cnf(c_0_21, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.36/1.59  cnf(c_0_22, negated_conjecture, (r1_lattice3(esk3_0,X1,esk6_0)|r2_hidden(esk1_3(esk3_0,X1,esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])])).
% 1.36/1.59  cnf(c_0_23, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.36/1.59  cnf(c_0_24, negated_conjecture, (r1_lattice3(esk3_0,X1,esk6_0)|r1_tarski(k1_tarski(esk1_3(esk3_0,X1,esk6_0)),X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 1.36/1.59  fof(c_0_25, plain, ![X25, X26]:(~l1_orders_2(X25)|m1_subset_1(k2_yellow_0(X25,X26),u1_struct_0(X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_yellow_0])])).
% 1.36/1.59  fof(c_0_26, plain, ![X1, X2, X3]:(epred1_3(X3,X2,X1)=>((![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_yellow_0(X1,X4)))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X3)&![X5]:((v1_finset_1(X5)&m1_subset_1(X5,k1_zfmisc_1(X2)))=>~((r2_yellow_0(X1,X5)&X4=k2_yellow_0(X1,X5))))))))&![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_hidden(k2_yellow_0(X1,X4),X3))))), inference(split_equiv,[status(thm)],[c_0_12])).
% 1.36/1.59  cnf(c_0_27, negated_conjecture, (~r1_lattice3(esk3_0,esk4_0,esk6_0)|~r1_lattice3(esk3_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.36/1.59  cnf(c_0_28, negated_conjecture, (r1_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,X1,esk6_0)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 1.36/1.59  cnf(c_0_29, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.36/1.59  cnf(c_0_30, plain, (m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.36/1.59  fof(c_0_31, plain, ![X42, X43, X44, X45, X46, X48]:(((~v1_finset_1(X45)|~m1_subset_1(X45,k1_zfmisc_1(X43))|(X45=k1_xboole_0|r2_yellow_0(X42,X45))|~epred1_3(X44,X43,X42))&(((v1_finset_1(esk7_4(X42,X43,X44,X46))|~r2_hidden(X46,X44)|~m1_subset_1(X46,u1_struct_0(X42))|~epred1_3(X44,X43,X42))&(m1_subset_1(esk7_4(X42,X43,X44,X46),k1_zfmisc_1(X43))|~r2_hidden(X46,X44)|~m1_subset_1(X46,u1_struct_0(X42))|~epred1_3(X44,X43,X42)))&((r2_yellow_0(X42,esk7_4(X42,X43,X44,X46))|~r2_hidden(X46,X44)|~m1_subset_1(X46,u1_struct_0(X42))|~epred1_3(X44,X43,X42))&(X46=k2_yellow_0(X42,esk7_4(X42,X43,X44,X46))|~r2_hidden(X46,X44)|~m1_subset_1(X46,u1_struct_0(X42))|~epred1_3(X44,X43,X42)))))&(~v1_finset_1(X48)|~m1_subset_1(X48,k1_zfmisc_1(X43))|(X48=k1_xboole_0|r2_hidden(k2_yellow_0(X42,X48),X44))|~epred1_3(X44,X43,X42))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])])])).
% 1.36/1.59  cnf(c_0_32, negated_conjecture, (m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))|~r1_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 1.36/1.59  cnf(c_0_33, negated_conjecture, (r1_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk1_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_18]), c_0_19])])).
% 1.36/1.59  fof(c_0_34, plain, ![X14]:v1_finset_1(k1_tarski(X14)), inference(variable_rename,[status(thm)],[fc1_finset_1])).
% 1.36/1.59  cnf(c_0_35, plain, (r1_orders_2(X1,X3,X4)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.36/1.59  cnf(c_0_36, negated_conjecture, (m1_subset_1(k2_yellow_0(esk3_0,X1),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_30, c_0_19])).
% 1.36/1.59  cnf(c_0_37, plain, (X1=k1_xboole_0|r2_hidden(k2_yellow_0(X3,X1),X4)|~v1_finset_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~epred1_3(X4,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.36/1.59  cnf(c_0_38, negated_conjecture, (m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 1.36/1.59  cnf(c_0_39, plain, (v1_finset_1(k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.36/1.59  fof(c_0_40, plain, ![X27, X28, X29, X30]:((~r1_lattice3(X27,X30,X29)|r1_lattice3(X27,X30,X28)|~r1_orders_2(X27,X28,X29)|~m1_subset_1(X29,u1_struct_0(X27))|~m1_subset_1(X28,u1_struct_0(X27))|(~v4_orders_2(X27)|~l1_orders_2(X27)))&(~r2_lattice3(X27,X30,X28)|r2_lattice3(X27,X30,X29)|~r1_orders_2(X27,X28,X29)|~m1_subset_1(X29,u1_struct_0(X27))|~m1_subset_1(X28,u1_struct_0(X27))|(~v4_orders_2(X27)|~l1_orders_2(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_yellow_0])])])])).
% 1.36/1.59  cnf(c_0_41, negated_conjecture, (r1_orders_2(esk3_0,X1,k2_yellow_0(esk3_0,X2))|~r1_lattice3(esk3_0,X3,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(k2_yellow_0(esk3_0,X2),X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_19])])).
% 1.36/1.59  cnf(c_0_42, plain, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|r2_hidden(k2_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)|~epred1_3(X2,esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])])).
% 1.36/1.59  cnf(c_0_43, negated_conjecture, (epred1_3(esk5_0,esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.36/1.59  fof(c_0_44, plain, ![X20, X21, X22, X23]:(((r1_lattice3(X20,X21,X22)|X22!=k2_yellow_0(X20,X21)|~r2_yellow_0(X20,X21)|~m1_subset_1(X22,u1_struct_0(X20))|~l1_orders_2(X20))&(~m1_subset_1(X23,u1_struct_0(X20))|(~r1_lattice3(X20,X21,X23)|r1_orders_2(X20,X23,X22))|X22!=k2_yellow_0(X20,X21)|~r2_yellow_0(X20,X21)|~m1_subset_1(X22,u1_struct_0(X20))|~l1_orders_2(X20)))&((m1_subset_1(esk2_3(X20,X21,X22),u1_struct_0(X20))|~r1_lattice3(X20,X21,X22)|X22=k2_yellow_0(X20,X21)|~r2_yellow_0(X20,X21)|~m1_subset_1(X22,u1_struct_0(X20))|~l1_orders_2(X20))&((r1_lattice3(X20,X21,esk2_3(X20,X21,X22))|~r1_lattice3(X20,X21,X22)|X22=k2_yellow_0(X20,X21)|~r2_yellow_0(X20,X21)|~m1_subset_1(X22,u1_struct_0(X20))|~l1_orders_2(X20))&(~r1_orders_2(X20,esk2_3(X20,X21,X22),X22)|~r1_lattice3(X20,X21,X22)|X22=k2_yellow_0(X20,X21)|~r2_yellow_0(X20,X21)|~m1_subset_1(X22,u1_struct_0(X20))|~l1_orders_2(X20))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_yellow_0])])])])])).
% 1.36/1.59  cnf(c_0_45, plain, (X1=k1_xboole_0|r2_yellow_0(X3,X1)|~v1_finset_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~epred1_3(X4,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.36/1.59  fof(c_0_46, plain, ![X31, X32, X33]:((((~r1_lattice3(X31,k1_tarski(X33),X32)|r1_orders_2(X31,X32,X33)|~m1_subset_1(X33,u1_struct_0(X31))|~m1_subset_1(X32,u1_struct_0(X31))|~l1_orders_2(X31))&(~r1_orders_2(X31,X32,X33)|r1_lattice3(X31,k1_tarski(X33),X32)|~m1_subset_1(X33,u1_struct_0(X31))|~m1_subset_1(X32,u1_struct_0(X31))|~l1_orders_2(X31)))&(~r2_lattice3(X31,k1_tarski(X33),X32)|r1_orders_2(X31,X33,X32)|~m1_subset_1(X33,u1_struct_0(X31))|~m1_subset_1(X32,u1_struct_0(X31))|~l1_orders_2(X31)))&(~r1_orders_2(X31,X33,X32)|r2_lattice3(X31,k1_tarski(X33),X32)|~m1_subset_1(X33,u1_struct_0(X31))|~m1_subset_1(X32,u1_struct_0(X31))|~l1_orders_2(X31))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_yellow_0])])])])).
% 1.36/1.59  cnf(c_0_47, plain, (r1_lattice3(X1,X2,X4)|~r1_lattice3(X1,X2,X3)|~r1_orders_2(X1,X4,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~v4_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 1.36/1.59  cnf(c_0_48, negated_conjecture, (v4_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.36/1.59  cnf(c_0_49, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,X1))|m1_subset_1(esk1_3(esk3_0,X2,esk6_0),u1_struct_0(esk3_0))|~r2_hidden(k2_yellow_0(esk3_0,X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_33]), c_0_18])])).
% 1.36/1.59  cnf(c_0_50, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|r2_hidden(k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 1.36/1.59  cnf(c_0_51, plain, (r1_lattice3(X1,X2,X3)|X3!=k2_yellow_0(X1,X2)|~r2_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 1.36/1.59  cnf(c_0_52, plain, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~epred1_3(X2,esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_38]), c_0_39])])).
% 1.36/1.59  cnf(c_0_53, plain, (r1_orders_2(X1,X3,X2)|~r1_lattice3(X1,k1_tarski(X2),X3)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 1.36/1.59  cnf(c_0_54, negated_conjecture, (m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))|~r1_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_27, c_0_33])).
% 1.36/1.59  cnf(c_0_55, negated_conjecture, (r1_lattice3(esk3_0,X1,esk6_0)|~r1_orders_2(esk3_0,esk6_0,X2)|~r1_lattice3(esk3_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_18]), c_0_48]), c_0_19])])).
% 1.36/1.59  cnf(c_0_56, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 1.36/1.59  cnf(c_0_57, plain, (r1_lattice3(X1,X2,k2_yellow_0(X1,X2))|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_51]), c_0_30])).
% 1.36/1.59  cnf(c_0_58, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_52, c_0_43])).
% 1.36/1.59  cnf(c_0_59, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,X1)|~r1_lattice3(esk3_0,k1_tarski(X1),esk6_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_18]), c_0_19])])).
% 1.36/1.59  cnf(c_0_60, negated_conjecture, (m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_54, c_0_33])).
% 1.36/1.59  cnf(c_0_61, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r1_lattice3(esk3_0,X1,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_36])])).
% 1.36/1.59  cnf(c_0_62, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_19])])).
% 1.36/1.59  cnf(c_0_63, plain, (r1_lattice3(X1,X3,X2)|~r1_orders_2(X1,X2,esk1_3(X1,X3,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.36/1.59  cnf(c_0_64, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 1.36/1.59  cnf(c_0_65, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0)|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 1.36/1.59  cnf(c_0_66, negated_conjecture, (r1_lattice3(esk3_0,X1,esk6_0)|~r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,X1,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_18]), c_0_19])])).
% 1.36/1.59  cnf(c_0_67, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 1.36/1.59  cnf(c_0_68, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,esk4_0,esk6_0)|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 1.36/1.59  cnf(c_0_69, negated_conjecture, (m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_32, c_0_28])).
% 1.36/1.59  cnf(c_0_70, plain, (X1=k2_yellow_0(X2,esk7_4(X2,X3,X4,X1))|~r2_hidden(X1,X4)|~m1_subset_1(X1,u1_struct_0(X2))|~epred1_3(X4,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.36/1.60  cnf(c_0_71, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_68]), c_0_33])).
% 1.36/1.60  cnf(c_0_72, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.36/1.60  cnf(c_0_73, negated_conjecture, (m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_54, c_0_28])).
% 1.36/1.60  cnf(c_0_74, plain, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))|r2_hidden(k2_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)|~epred1_3(X2,esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_69]), c_0_39])])).
% 1.36/1.60  cnf(c_0_75, plain, (k2_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|~epred1_3(X2,X1,esk3_0)|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 1.36/1.60  cnf(c_0_76, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.36/1.60  cnf(c_0_77, negated_conjecture, (m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))|r1_tarski(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),esk5_0)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 1.36/1.60  cnf(c_0_78, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,X1))|m1_subset_1(k1_tarski(esk1_3(esk3_0,X2,esk6_0)),k1_zfmisc_1(X2))|~r2_hidden(k2_yellow_0(esk3_0,X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_28]), c_0_18])])).
% 1.36/1.60  cnf(c_0_79, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))|r2_hidden(k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0)), inference(spm,[status(thm)],[c_0_74, c_0_43])).
% 1.36/1.60  cnf(c_0_80, plain, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))|~epred1_3(X2,esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_69]), c_0_39])])).
% 1.36/1.60  cnf(c_0_81, negated_conjecture, (k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_75, c_0_43])).
% 1.36/1.60  cnf(c_0_82, negated_conjecture, (m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))|r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 1.36/1.60  cnf(c_0_83, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 1.36/1.60  cnf(c_0_84, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_80, c_0_43])).
% 1.36/1.60  cnf(c_0_85, plain, (m1_subset_1(esk7_4(X1,X2,X3,X4),k1_zfmisc_1(X2))|~r2_hidden(X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~epred1_3(X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.36/1.60  cnf(c_0_86, negated_conjecture, (k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 1.36/1.60  cnf(c_0_87, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))|~r1_lattice3(esk3_0,X1,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_83]), c_0_36])])).
% 1.36/1.60  cnf(c_0_88, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_84]), c_0_19])])).
% 1.36/1.60  cnf(c_0_89, plain, (r2_yellow_0(X1,esk7_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~epred1_3(X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.36/1.60  fof(c_0_90, plain, ![X34, X35, X36, X37]:((~r1_lattice3(X34,X36,X37)|r1_lattice3(X34,X35,X37)|~m1_subset_1(X37,u1_struct_0(X34))|~r1_tarski(X35,X36)|~l1_orders_2(X34))&(~r2_lattice3(X34,X36,X37)|r2_lattice3(X34,X35,X37)|~m1_subset_1(X37,u1_struct_0(X34))|~r1_tarski(X35,X36)|~l1_orders_2(X34))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_yellow_0])])])])).
% 1.36/1.60  cnf(c_0_91, plain, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(X1))|~epred1_3(X2,X1,esk3_0)|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2)), inference(spm,[status(thm)],[c_0_85, c_0_71])).
% 1.36/1.60  cnf(c_0_92, negated_conjecture, (k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))|~r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0)), inference(spm,[status(thm)],[c_0_59, c_0_86])).
% 1.36/1.60  cnf(c_0_93, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 1.36/1.60  cnf(c_0_94, plain, (r1_orders_2(X2,X1,X4)|~m1_subset_1(X1,u1_struct_0(X2))|~r1_lattice3(X2,X3,X1)|X4!=k2_yellow_0(X2,X3)|~r2_yellow_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 1.36/1.60  cnf(c_0_95, plain, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)))|~epred1_3(X2,X1,esk3_0)|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2)), inference(spm,[status(thm)],[c_0_89, c_0_71])).
% 1.36/1.60  cnf(c_0_96, plain, (r1_lattice3(X1,X4,X3)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~r1_tarski(X4,X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_90])).
% 1.36/1.60  cnf(c_0_97, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_91, c_0_43])).
% 1.36/1.60  cnf(c_0_98, negated_conjecture, (k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 1.36/1.60  cnf(c_0_99, plain, (r1_orders_2(X1,X2,k2_yellow_0(X1,X3))|~r2_yellow_0(X1,X3)|~r1_lattice3(X1,X3,X2)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_94]), c_0_30])).
% 1.36/1.60  cnf(c_0_100, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_95, c_0_43])).
% 1.36/1.60  cnf(c_0_101, negated_conjecture, (r1_lattice3(esk3_0,X1,esk6_0)|~r1_lattice3(esk3_0,X2,esk6_0)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_18]), c_0_19])])).
% 1.36/1.60  cnf(c_0_102, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_97, c_0_82])).
% 1.36/1.60  cnf(c_0_103, negated_conjecture, (k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,esk4_0,esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_66, c_0_98])).
% 1.36/1.60  cnf(c_0_104, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,X1))|~r2_yellow_0(esk3_0,X1)|~r1_lattice3(esk3_0,X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_18]), c_0_19])])).
% 1.36/1.60  cnf(c_0_105, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))|r1_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_100, c_0_22])).
% 1.36/1.60  cnf(c_0_106, negated_conjecture, (r1_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk1_3(esk3_0,X2,esk6_0),u1_struct_0(esk3_0))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_101, c_0_33])).
% 1.36/1.60  cnf(c_0_107, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))|r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0)), inference(spm,[status(thm)],[c_0_72, c_0_102])).
% 1.36/1.60  cnf(c_0_108, negated_conjecture, (k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_103]), c_0_28])).
% 1.36/1.60  cnf(c_0_109, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))))|r1_lattice3(esk3_0,esk5_0,esk6_0)|~r1_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)), inference(spm,[status(thm)],[c_0_104, c_0_105])).
% 1.36/1.60  cnf(c_0_110, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_106, c_0_107])).
% 1.36/1.60  cnf(c_0_111, negated_conjecture, (k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_tarski(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),esk5_0)), inference(spm,[status(thm)],[c_0_72, c_0_108])).
% 1.36/1.60  cnf(c_0_112, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_110]), c_0_54])).
% 1.36/1.60  cnf(c_0_113, negated_conjecture, (k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_111]), c_0_81])).
% 1.36/1.60  cnf(c_0_114, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_112, c_0_113])).
% 1.36/1.60  cnf(c_0_115, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_114]), c_0_54])).
% 1.36/1.60  cnf(c_0_116, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))|~r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0)), inference(spm,[status(thm)],[c_0_59, c_0_115])).
% 1.36/1.60  cnf(c_0_117, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_116, c_0_93])).
% 1.36/1.60  cnf(c_0_118, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,esk4_0,esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_66, c_0_117])).
% 1.36/1.60  cnf(c_0_119, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_118]), c_0_28])).
% 1.36/1.60  cnf(c_0_120, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,esk5_0,esk6_0)|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_97, c_0_22])).
% 1.36/1.60  cnf(c_0_121, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_tarski(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),esk5_0)), inference(spm,[status(thm)],[c_0_72, c_0_119])).
% 1.36/1.60  cnf(c_0_122, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_32, c_0_120])).
% 1.36/1.60  cnf(c_0_123, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_76, c_0_121])).
% 1.36/1.60  cnf(c_0_124, negated_conjecture, (r1_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,X2,esk6_0)),k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_101, c_0_28])).
% 1.36/1.60  cnf(c_0_125, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))|r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0)), inference(spm,[status(thm)],[c_0_72, c_0_122])).
% 1.36/1.60  cnf(c_0_126, negated_conjecture, (r1_lattice3(esk3_0,esk4_0,esk6_0)|r1_lattice3(esk3_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.36/1.60  cnf(c_0_127, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_97, c_0_123])).
% 1.36/1.60  cnf(c_0_128, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_124, c_0_125])).
% 1.36/1.60  cnf(c_0_129, negated_conjecture, (r1_lattice3(esk3_0,esk5_0,esk6_0)|r1_lattice3(esk3_0,X1,esk6_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_101, c_0_126])).
% 1.36/1.60  cnf(c_0_130, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0)), inference(spm,[status(thm)],[c_0_72, c_0_127])).
% 1.36/1.60  cnf(c_0_131, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))))|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_128]), c_0_32])).
% 1.36/1.60  cnf(c_0_132, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)|r1_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_129, c_0_130])).
% 1.36/1.60  cnf(c_0_133, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_131, c_0_113])).
% 1.36/1.60  cnf(c_0_134, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))))|r1_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_109, c_0_132])).
% 1.36/1.60  cnf(c_0_135, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_133]), c_0_32])).
% 1.36/1.60  cnf(c_0_136, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,esk5_0,esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_113]), c_0_66])).
% 1.36/1.60  cnf(c_0_137, plain, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_hidden(k2_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)|~epred1_3(X2,esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_135]), c_0_39])])).
% 1.36/1.60  cnf(c_0_138, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,X1))|~r2_hidden(k2_yellow_0(esk3_0,X1),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_136]), c_0_18])])).
% 1.36/1.60  cnf(c_0_139, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_hidden(k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0)), inference(spm,[status(thm)],[c_0_137, c_0_43])).
% 1.36/1.60  cnf(c_0_140, plain, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))|~epred1_3(X2,esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_135]), c_0_39])])).
% 1.36/1.60  cnf(c_0_141, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))), inference(spm,[status(thm)],[c_0_138, c_0_139])).
% 1.36/1.60  cnf(c_0_142, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))), inference(spm,[status(thm)],[c_0_140, c_0_43])).
% 1.36/1.60  cnf(c_0_143, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,X1,esk6_0)|~r1_lattice3(esk3_0,X1,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_141]), c_0_36])])).
% 1.36/1.60  cnf(c_0_144, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_142]), c_0_19])])).
% 1.36/1.60  cnf(c_0_145, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0)), inference(spm,[status(thm)],[c_0_143, c_0_144])).
% 1.36/1.60  cnf(c_0_146, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_116, c_0_145])).
% 1.36/1.60  fof(c_0_147, plain, ![X6]:~v1_xboole_0(k1_tarski(X6)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).
% 1.36/1.60  cnf(c_0_148, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,esk4_0,esk6_0)), inference(spm,[status(thm)],[c_0_66, c_0_146])).
% 1.36/1.60  cnf(c_0_149, plain, (~v1_xboole_0(k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_147])).
% 1.36/1.60  cnf(c_0_150, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_148]), c_0_136])).
% 1.36/1.60  cnf(c_0_151, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 1.36/1.60  cnf(c_0_152, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149, c_0_150]), c_0_151])]), ['proof']).
% 1.36/1.60  # SZS output end CNFRefutation
% 1.36/1.60  # Proof object total steps             : 153
% 1.36/1.60  # Proof object clause steps            : 126
% 1.36/1.60  # Proof object formula steps           : 27
% 1.36/1.60  # Proof object conjectures             : 96
% 1.36/1.60  # Proof object clause conjectures      : 93
% 1.36/1.60  # Proof object formula conjectures     : 3
% 1.36/1.60  # Proof object initial clauses used    : 28
% 1.36/1.60  # Proof object initial formulas used   : 12
% 1.36/1.60  # Proof object generating inferences   : 96
% 1.36/1.60  # Proof object simplifying inferences  : 63
% 1.36/1.60  # Training examples: 0 positive, 0 negative
% 1.36/1.60  # Parsed axioms                        : 13
% 1.36/1.60  # Removed by relevancy pruning/SinE    : 0
% 1.36/1.60  # Initial clauses                      : 42
% 1.36/1.60  # Removed in clause preprocessing      : 0
% 1.36/1.60  # Initial clauses in saturation        : 42
% 1.36/1.60  # Processed clauses                    : 2951
% 1.36/1.60  # ...of these trivial                  : 0
% 1.36/1.60  # ...subsumed                          : 852
% 1.36/1.60  # ...remaining for further processing  : 2099
% 1.36/1.60  # Other redundant clauses eliminated   : 2
% 1.36/1.60  # Clauses deleted for lack of memory   : 0
% 1.36/1.60  # Backward-subsumed                    : 484
% 1.36/1.60  # Backward-rewritten                   : 523
% 1.36/1.60  # Generated clauses                    : 18015
% 1.36/1.60  # ...of the previous two non-trivial   : 17976
% 1.36/1.60  # Contextual simplify-reflections      : 91
% 1.36/1.60  # Paramodulations                      : 18011
% 1.36/1.60  # Factorizations                       : 2
% 1.36/1.60  # Equation resolutions                 : 2
% 1.36/1.60  # Propositional unsat checks           : 0
% 1.36/1.60  #    Propositional check models        : 0
% 1.36/1.60  #    Propositional check unsatisfiable : 0
% 1.36/1.60  #    Propositional clauses             : 0
% 1.36/1.60  #    Propositional clauses after purity: 0
% 1.36/1.60  #    Propositional unsat core size     : 0
% 1.36/1.60  #    Propositional preprocessing time  : 0.000
% 1.36/1.60  #    Propositional encoding time       : 0.000
% 1.36/1.60  #    Propositional solver time         : 0.000
% 1.36/1.60  #    Success case prop preproc time    : 0.000
% 1.36/1.60  #    Success case prop encoding time   : 0.000
% 1.36/1.60  #    Success case prop solver time     : 0.000
% 1.36/1.60  # Current number of processed clauses  : 1048
% 1.36/1.60  #    Positive orientable unit clauses  : 22
% 1.36/1.60  #    Positive unorientable unit clauses: 0
% 1.36/1.60  #    Negative unit clauses             : 2
% 1.36/1.60  #    Non-unit-clauses                  : 1024
% 1.36/1.60  # Current number of unprocessed clauses: 14619
% 1.36/1.60  # ...number of literals in the above   : 67132
% 1.36/1.60  # Current number of archived formulas  : 0
% 1.36/1.60  # Current number of archived clauses   : 1049
% 1.36/1.60  # Clause-clause subsumption calls (NU) : 422196
% 1.36/1.60  # Rec. Clause-clause subsumption calls : 138193
% 1.36/1.60  # Non-unit clause-clause subsumptions  : 1427
% 1.36/1.60  # Unit Clause-clause subsumption calls : 656
% 1.36/1.60  # Rewrite failures with RHS unbound    : 0
% 1.36/1.60  # BW rewrite match attempts            : 32
% 1.36/1.60  # BW rewrite match successes           : 6
% 1.36/1.60  # Condensation attempts                : 0
% 1.36/1.60  # Condensation successes               : 0
% 1.36/1.60  # Termbank termtop insertions          : 684721
% 1.36/1.60  
% 1.36/1.60  # -------------------------------------------------
% 1.36/1.60  # User time                : 1.238 s
% 1.36/1.60  # System time              : 0.016 s
% 1.36/1.60  # Total time               : 1.254 s
% 1.36/1.60  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
