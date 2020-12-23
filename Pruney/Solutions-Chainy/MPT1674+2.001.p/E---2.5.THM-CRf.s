%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:27 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  108 (1111 expanded)
%              Number of clauses        :   79 ( 384 expanded)
%              Number of leaves         :   14 ( 353 expanded)
%              Depth                    :   29
%              Number of atoms          :  553 (10252 expanded)
%              Number of equality atoms :   60 (1447 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   30 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t54_waybel_0,conjecture,(
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
                       => r2_hidden(k1_yellow_0(X1,X4),X3) ) )
                  & r1_yellow_0(X1,X2) )
               => k1_yellow_0(X1,X3) = k1_yellow_0(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_waybel_0)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

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

fof(t63_subset_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

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

fof(t24_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r1_orders_2(X1,X2,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

fof(fc1_finset_1,axiom,(
    ! [X1] : v1_finset_1(k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_finset_1)).

fof(t47_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2,X3] :
          ( ( r1_yellow_0(X1,X2)
            & ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_lattice3(X1,X2,X4)
                <=> r2_lattice3(X1,X3,X4) ) ) )
         => k1_yellow_0(X1,X2) = k1_yellow_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_yellow_0)).

fof(fc2_xboole_0,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

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

fof(c_0_13,plain,(
    ! [X1,X3,X2] :
      ( epred1_3(X2,X3,X1)
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
             => r2_hidden(k1_yellow_0(X1,X4),X3) ) )
        & r1_yellow_0(X1,X2) ) ) ),
    introduced(definition)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( epred1_3(X2,X3,X1)
                 => k1_yellow_0(X1,X3) = k1_yellow_0(X1,X2) ) ) ) ) ),
    inference(apply_def,[status(thm)],[inference(assume_negation,[status(cth)],[t54_waybel_0]),c_0_13])).

fof(c_0_15,plain,(
    ! [X1,X3,X2] :
      ( epred1_3(X2,X3,X1)
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
             => r2_hidden(k1_yellow_0(X1,X4),X3) ) )
        & r1_yellow_0(X1,X2) ) ) ),
    inference(split_equiv,[status(thm)],[c_0_13])).

fof(c_0_16,plain,(
    ! [X11,X12,X13] :
      ( ~ r2_hidden(X11,X12)
      | ~ m1_subset_1(X12,k1_zfmisc_1(X13))
      | m1_subset_1(X11,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v3_orders_2(esk4_0)
    & v4_orders_2(esk4_0)
    & l1_orders_2(esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & epred1_3(esk5_0,esk6_0,esk4_0)
    & k1_yellow_0(esk4_0,esk6_0) != k1_yellow_0(esk4_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

fof(c_0_18,plain,(
    ! [X41,X42,X43,X44,X45,X47] :
      ( ( ~ v1_finset_1(X44)
        | ~ m1_subset_1(X44,k1_zfmisc_1(X43))
        | X44 = k1_xboole_0
        | r1_yellow_0(X41,X44)
        | ~ epred1_3(X43,X42,X41) )
      & ( v1_finset_1(esk7_4(X41,X42,X43,X45))
        | ~ r2_hidden(X45,X42)
        | ~ m1_subset_1(X45,u1_struct_0(X41))
        | ~ epred1_3(X43,X42,X41) )
      & ( m1_subset_1(esk7_4(X41,X42,X43,X45),k1_zfmisc_1(X43))
        | ~ r2_hidden(X45,X42)
        | ~ m1_subset_1(X45,u1_struct_0(X41))
        | ~ epred1_3(X43,X42,X41) )
      & ( r1_yellow_0(X41,esk7_4(X41,X42,X43,X45))
        | ~ r2_hidden(X45,X42)
        | ~ m1_subset_1(X45,u1_struct_0(X41))
        | ~ epred1_3(X43,X42,X41) )
      & ( X45 = k1_yellow_0(X41,esk7_4(X41,X42,X43,X45))
        | ~ r2_hidden(X45,X42)
        | ~ m1_subset_1(X45,u1_struct_0(X41))
        | ~ epred1_3(X43,X42,X41) )
      & ( ~ v1_finset_1(X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(X43))
        | X47 = k1_xboole_0
        | r2_hidden(k1_yellow_0(X41,X47),X42)
        | ~ epred1_3(X43,X42,X41) )
      & ( r1_yellow_0(X41,X43)
        | ~ epred1_3(X43,X42,X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])])])).

fof(c_0_19,plain,(
    ! [X9,X10] :
      ( ( ~ m1_subset_1(X9,k1_zfmisc_1(X10))
        | r1_tarski(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | m1_subset_1(X9,k1_zfmisc_1(X10)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_20,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X17,X18,X19,X20] :
      ( ( ~ r2_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r2_hidden(X20,X18)
        | r1_orders_2(X17,X20,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ l1_orders_2(X17) )
      & ( m1_subset_1(esk1_3(X17,X18,X19),u1_struct_0(X17))
        | r2_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ l1_orders_2(X17) )
      & ( r2_hidden(esk1_3(X17,X18,X19),X18)
        | r2_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ l1_orders_2(X17) )
      & ( ~ r1_orders_2(X17,esk1_3(X17,X18,X19),X19)
        | r2_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ l1_orders_2(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

cnf(c_0_23,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(k1_yellow_0(X3,X1),X4)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ epred1_3(X2,X4,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X7,X8] :
      ( ~ r2_hidden(X7,X8)
      | m1_subset_1(k1_tarski(X7),k1_zfmisc_1(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).

fof(c_0_26,plain,(
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

fof(c_0_27,plain,(
    ! [X22,X23,X24,X25] :
      ( ( r2_lattice3(X22,X23,X24)
        | X24 != k1_yellow_0(X22,X23)
        | ~ r1_yellow_0(X22,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ l1_orders_2(X22) )
      & ( ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ r2_lattice3(X22,X23,X25)
        | r1_orders_2(X22,X24,X25)
        | X24 != k1_yellow_0(X22,X23)
        | ~ r1_yellow_0(X22,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ l1_orders_2(X22) )
      & ( m1_subset_1(esk2_3(X22,X23,X24),u1_struct_0(X22))
        | ~ r2_lattice3(X22,X23,X24)
        | X24 = k1_yellow_0(X22,X23)
        | ~ r1_yellow_0(X22,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ l1_orders_2(X22) )
      & ( r2_lattice3(X22,X23,esk2_3(X22,X23,X24))
        | ~ r2_lattice3(X22,X23,X24)
        | X24 = k1_yellow_0(X22,X23)
        | ~ r1_yellow_0(X22,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ l1_orders_2(X22) )
      & ( ~ r1_orders_2(X22,X24,esk2_3(X22,X23,X24))
        | ~ r2_lattice3(X22,X23,X24)
        | X24 = k1_yellow_0(X22,X23)
        | ~ r1_yellow_0(X22,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ l1_orders_2(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).

cnf(c_0_28,plain,
    ( X1 = k1_xboole_0
    | r1_yellow_0(X3,X1)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ epred1_3(X2,X4,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_29,plain,(
    ! [X15,X16] :
      ( v2_struct_0(X15)
      | ~ v3_orders_2(X15)
      | ~ l1_orders_2(X15)
      | ~ m1_subset_1(X16,u1_struct_0(X15))
      | r1_orders_2(X15,X16,X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_orders_2])])])])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_31,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(k1_yellow_0(X2,X1),X3)
    | ~ epred1_3(X4,X3,X2)
    | ~ v1_finset_1(X1)
    | ~ r1_tarski(X1,X4) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( epred1_3(esk5_0,esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_35,plain,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_36,plain,(
    ! [X14] : v1_finset_1(k1_tarski(X14)) ),
    inference(variable_rename,[status(thm)],[fc1_finset_1])).

cnf(c_0_37,plain,
    ( r1_orders_2(X1,X2,X3)
    | ~ r2_lattice3(X1,k1_tarski(X2),X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( r2_lattice3(X1,X2,esk2_3(X1,X2,X3))
    | X3 = k1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | X3 = k1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,plain,
    ( X1 = k1_xboole_0
    | r1_yellow_0(X2,X1)
    | ~ epred1_3(X3,X4,X2)
    | ~ v1_finset_1(X1)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_28,c_0_24])).

cnf(c_0_41,plain,
    ( r2_lattice3(X1,k1_tarski(X2),X3)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_42,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_43,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_44,negated_conjecture,
    ( r2_lattice3(X1,esk5_0,X2)
    | m1_subset_1(esk1_3(X1,esk5_0,X2),u1_struct_0(esk4_0))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_45,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_46,negated_conjecture,
    ( v3_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_47,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_48,negated_conjecture,
    ( X1 = k1_xboole_0
    | r2_hidden(k1_yellow_0(esk4_0,X1),esk6_0)
    | ~ v1_finset_1(X1)
    | ~ r1_tarski(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_49,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_50,plain,
    ( v1_finset_1(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_51,plain,
    ( X2 = k1_yellow_0(X1,X3)
    | ~ r1_orders_2(X1,X2,esk2_3(X1,X3,X2))
    | ~ r2_lattice3(X1,X3,X2)
    | ~ r1_yellow_0(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_52,plain,
    ( X1 = k1_yellow_0(X2,k1_tarski(X3))
    | r1_orders_2(X2,X3,esk2_3(X2,k1_tarski(X3),X1))
    | ~ r1_yellow_0(X2,k1_tarski(X3))
    | ~ r2_lattice3(X2,k1_tarski(X3),X1)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_53,negated_conjecture,
    ( X1 = k1_xboole_0
    | r1_yellow_0(esk4_0,X1)
    | ~ v1_finset_1(X1)
    | ~ r1_tarski(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_33])).

cnf(c_0_54,plain,
    ( r2_lattice3(X1,k1_tarski(X2),esk1_3(X1,X3,X4))
    | r2_lattice3(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,esk1_3(X1,X3,X4))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_55,negated_conjecture,
    ( r2_lattice3(X1,esk5_0,X2)
    | r1_orders_2(esk4_0,esk1_3(X1,esk5_0,X2),esk1_3(X1,esk5_0,X2))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_46])]),c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( k1_tarski(X1) = k1_xboole_0
    | r2_hidden(k1_yellow_0(esk4_0,k1_tarski(X1)),esk6_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])])).

cnf(c_0_57,plain,
    ( k1_yellow_0(X1,k1_tarski(X2)) = X2
    | ~ r1_yellow_0(X1,k1_tarski(X2))
    | ~ r2_lattice3(X1,k1_tarski(X2),X2)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( k1_tarski(X1) = k1_xboole_0
    | r1_yellow_0(esk4_0,k1_tarski(X1))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_49]),c_0_50])])).

cnf(c_0_59,negated_conjecture,
    ( r2_lattice3(esk4_0,k1_tarski(esk1_3(esk4_0,esk5_0,X1)),esk1_3(esk4_0,esk5_0,X1))
    | r2_lattice3(esk4_0,esk5_0,X1)
    | ~ m1_subset_1(esk1_3(esk4_0,esk5_0,X1),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_45])])).

cnf(c_0_60,negated_conjecture,
    ( k1_tarski(X1) = k1_xboole_0
    | r2_hidden(X1,esk6_0)
    | ~ r2_lattice3(esk4_0,k1_tarski(X1),X1)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_45])]),c_0_30]),c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( r2_lattice3(esk4_0,k1_tarski(esk1_3(esk4_0,esk5_0,X1)),esk1_3(esk4_0,esk5_0,X1))
    | r2_lattice3(esk4_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_42]),c_0_45])])).

cnf(c_0_62,negated_conjecture,
    ( k1_tarski(esk1_3(esk4_0,esk5_0,X1)) = k1_xboole_0
    | r2_lattice3(esk4_0,esk5_0,X1)
    | r2_hidden(esk1_3(esk4_0,esk5_0,X1),esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(esk1_3(esk4_0,esk5_0,X1),esk5_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

fof(c_0_63,plain,(
    ! [X27,X28,X29] :
      ( ( m1_subset_1(esk3_3(X27,X28,X29),u1_struct_0(X27))
        | ~ r1_yellow_0(X27,X28)
        | k1_yellow_0(X27,X28) = k1_yellow_0(X27,X29)
        | v2_struct_0(X27)
        | ~ l1_orders_2(X27) )
      & ( ~ r2_lattice3(X27,X28,esk3_3(X27,X28,X29))
        | ~ r2_lattice3(X27,X29,esk3_3(X27,X28,X29))
        | ~ r1_yellow_0(X27,X28)
        | k1_yellow_0(X27,X28) = k1_yellow_0(X27,X29)
        | v2_struct_0(X27)
        | ~ l1_orders_2(X27) )
      & ( r2_lattice3(X27,X28,esk3_3(X27,X28,X29))
        | r2_lattice3(X27,X29,esk3_3(X27,X28,X29))
        | ~ r1_yellow_0(X27,X28)
        | k1_yellow_0(X27,X28) = k1_yellow_0(X27,X29)
        | v2_struct_0(X27)
        | ~ l1_orders_2(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_yellow_0])])])])])])).

cnf(c_0_64,negated_conjecture,
    ( k1_tarski(esk1_3(esk4_0,esk5_0,X1)) = k1_xboole_0
    | r2_lattice3(esk4_0,esk5_0,X1)
    | r2_hidden(esk1_3(esk4_0,esk5_0,X1),esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_31]),c_0_45])])).

cnf(c_0_65,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | k1_yellow_0(X1,X2) = k1_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_66,plain,
    ( r1_yellow_0(X1,X2)
    | ~ epred1_3(X2,X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_67,plain,(
    ! [X6] : ~ v1_xboole_0(k1_tarski(X6)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

cnf(c_0_68,negated_conjecture,
    ( k1_tarski(esk1_3(esk4_0,esk5_0,esk3_3(esk4_0,X1,X2))) = k1_xboole_0
    | k1_yellow_0(esk4_0,X1) = k1_yellow_0(esk4_0,X2)
    | r2_lattice3(esk4_0,esk5_0,esk3_3(esk4_0,X1,X2))
    | r2_hidden(esk1_3(esk4_0,esk5_0,esk3_3(esk4_0,X1,X2)),esk6_0)
    | ~ r1_yellow_0(esk4_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_45])]),c_0_47])).

cnf(c_0_69,negated_conjecture,
    ( r1_yellow_0(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_33])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_71,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( k1_tarski(esk1_3(esk4_0,esk5_0,esk3_3(esk4_0,esk5_0,X1))) = k1_xboole_0
    | k1_yellow_0(esk4_0,esk5_0) = k1_yellow_0(esk4_0,X1)
    | r2_lattice3(esk4_0,esk5_0,esk3_3(esk4_0,esk5_0,X1))
    | r2_hidden(esk1_3(esk4_0,esk5_0,esk3_3(esk4_0,esk5_0,X1)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_73,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_74,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_70])).

cnf(c_0_75,negated_conjecture,
    ( k1_yellow_0(esk4_0,esk5_0) = k1_yellow_0(esk4_0,X1)
    | r2_lattice3(esk4_0,esk5_0,esk3_3(esk4_0,esk5_0,X1))
    | r2_hidden(esk1_3(esk4_0,esk5_0,esk3_3(esk4_0,esk5_0,X1)),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73])])).

cnf(c_0_76,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_77,negated_conjecture,
    ( k1_yellow_0(esk4_0,esk5_0) = k1_yellow_0(esk4_0,X1)
    | r2_lattice3(esk4_0,esk5_0,esk3_3(esk4_0,esk5_0,X1))
    | m1_subset_1(esk1_3(esk4_0,esk5_0,esk3_3(esk4_0,esk5_0,X1)),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_78,negated_conjecture,
    ( k1_yellow_0(esk4_0,esk5_0) = k1_yellow_0(esk4_0,X1)
    | r2_lattice3(esk4_0,esk5_0,esk3_3(esk4_0,esk5_0,X1))
    | r1_orders_2(esk4_0,esk1_3(esk4_0,esk5_0,esk3_3(esk4_0,esk5_0,X1)),X2)
    | ~ r2_lattice3(esk4_0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | ~ r2_hidden(esk1_3(esk4_0,esk5_0,esk3_3(esk4_0,esk5_0,X1)),X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_45])])).

cnf(c_0_79,negated_conjecture,
    ( k1_yellow_0(esk4_0,esk5_0) = k1_yellow_0(esk4_0,X1)
    | r2_lattice3(esk4_0,esk5_0,esk3_3(esk4_0,esk5_0,X1))
    | r1_orders_2(esk4_0,esk1_3(esk4_0,esk5_0,esk3_3(esk4_0,esk5_0,X1)),X2)
    | ~ r2_lattice3(esk4_0,esk6_0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_75])).

cnf(c_0_80,plain,
    ( r2_lattice3(X1,X2,esk3_3(X1,X2,X3))
    | r2_lattice3(X1,X3,esk3_3(X1,X2,X3))
    | k1_yellow_0(X1,X2) = k1_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_81,negated_conjecture,
    ( k1_yellow_0(esk4_0,esk5_0) = k1_yellow_0(esk4_0,X1)
    | k1_yellow_0(esk4_0,X2) = k1_yellow_0(esk4_0,X3)
    | r2_lattice3(esk4_0,esk5_0,esk3_3(esk4_0,esk5_0,X1))
    | r1_orders_2(esk4_0,esk1_3(esk4_0,esk5_0,esk3_3(esk4_0,esk5_0,X1)),esk3_3(esk4_0,X2,X3))
    | ~ r1_yellow_0(esk4_0,X2)
    | ~ r2_lattice3(esk4_0,esk6_0,esk3_3(esk4_0,X2,X3)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_65]),c_0_45])]),c_0_47])).

cnf(c_0_82,negated_conjecture,
    ( k1_yellow_0(esk4_0,esk5_0) = k1_yellow_0(esk4_0,X1)
    | r2_lattice3(esk4_0,esk5_0,esk3_3(esk4_0,esk5_0,X1))
    | r2_lattice3(esk4_0,X1,esk3_3(esk4_0,esk5_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_69]),c_0_45])]),c_0_47])).

cnf(c_0_83,negated_conjecture,
    ( k1_yellow_0(esk4_0,esk6_0) != k1_yellow_0(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_84,plain,(
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

cnf(c_0_85,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk1_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_86,negated_conjecture,
    ( k1_yellow_0(esk4_0,esk5_0) = k1_yellow_0(esk4_0,X1)
    | r2_lattice3(esk4_0,esk5_0,esk3_3(esk4_0,esk5_0,esk6_0))
    | r2_lattice3(esk4_0,esk5_0,esk3_3(esk4_0,esk5_0,X1))
    | r1_orders_2(esk4_0,esk1_3(esk4_0,esk5_0,esk3_3(esk4_0,esk5_0,X1)),esk3_3(esk4_0,esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_69])]),c_0_83])).

cnf(c_0_87,plain,
    ( r2_lattice3(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_tarski(X4,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_88,negated_conjecture,
    ( r2_lattice3(esk4_0,esk5_0,esk3_3(esk4_0,esk5_0,esk6_0))
    | ~ m1_subset_1(esk3_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_45])]),c_0_83])).

cnf(c_0_89,plain,
    ( r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | X4 != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_90,plain,
    ( k1_yellow_0(X1,X2) = k1_yellow_0(X1,X3)
    | r2_lattice3(X1,X4,esk3_3(X1,X2,X3))
    | v2_struct_0(X1)
    | ~ r1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X5,esk3_3(X1,X2,X3))
    | ~ l1_orders_2(X1)
    | ~ r1_tarski(X4,X5) ),
    inference(spm,[status(thm)],[c_0_87,c_0_65])).

cnf(c_0_91,negated_conjecture,
    ( r2_lattice3(esk4_0,esk5_0,esk3_3(esk4_0,esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_65]),c_0_69]),c_0_45])]),c_0_83]),c_0_47])).

cnf(c_0_92,plain,
    ( m1_subset_1(esk7_4(X1,X2,X3,X4),k1_zfmisc_1(X3))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_93,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_89])).

cnf(c_0_94,plain,
    ( X1 = k1_yellow_0(X2,esk7_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ epred1_3(X4,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_95,plain,
    ( r1_yellow_0(X1,esk7_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_96,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk3_3(esk4_0,esk5_0,esk6_0))
    | ~ r1_tarski(X1,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_69]),c_0_45])]),c_0_83]),c_0_47])).

cnf(c_0_97,plain,
    ( r1_tarski(esk7_4(X1,X2,X3,X4),X3)
    | ~ epred1_3(X3,X2,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_92])).

cnf(c_0_98,plain,
    ( r1_orders_2(X1,X2,X3)
    | ~ epred1_3(X4,X5,X1)
    | ~ r2_lattice3(X1,esk7_4(X1,X5,X4,X2),X3)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X2,X5) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_95])).

cnf(c_0_99,plain,
    ( r2_lattice3(esk4_0,esk7_4(X1,X2,esk5_0,X3),esk3_3(esk4_0,esk5_0,esk6_0))
    | ~ epred1_3(esk5_0,X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_100,plain,
    ( r1_orders_2(esk4_0,X1,esk3_3(esk4_0,esk5_0,esk6_0))
    | ~ epred1_3(esk5_0,X2,esk4_0)
    | ~ m1_subset_1(esk3_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_45])])).

cnf(c_0_101,plain,
    ( r1_orders_2(esk4_0,X1,esk3_3(esk4_0,esk5_0,esk6_0))
    | ~ epred1_3(esk5_0,X2,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_65]),c_0_69]),c_0_45])]),c_0_83]),c_0_47])).

cnf(c_0_102,negated_conjecture,
    ( r1_orders_2(esk4_0,X1,esk3_3(esk4_0,esk5_0,esk6_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_33]),c_0_74])).

cnf(c_0_103,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk3_3(esk4_0,esk5_0,esk6_0))
    | ~ m1_subset_1(esk3_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk4_0))
    | ~ r2_hidden(esk1_3(esk4_0,X1,esk3_3(esk4_0,esk5_0,esk6_0)),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_102]),c_0_45])])).

cnf(c_0_104,negated_conjecture,
    ( r2_lattice3(esk4_0,esk6_0,esk3_3(esk4_0,esk5_0,esk6_0))
    | ~ m1_subset_1(esk3_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_31]),c_0_45])])).

cnf(c_0_105,plain,
    ( k1_yellow_0(X1,X2) = k1_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r2_lattice3(X1,X2,esk3_3(X1,X2,X3))
    | ~ r2_lattice3(X1,X3,esk3_3(X1,X2,X3))
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_106,negated_conjecture,
    ( r2_lattice3(esk4_0,esk6_0,esk3_3(esk4_0,esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_65]),c_0_69]),c_0_45])]),c_0_83]),c_0_47])).

cnf(c_0_107,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_69]),c_0_91]),c_0_45])]),c_0_83]),c_0_47]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:38:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.47  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 0.20/0.47  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.47  #
% 0.20/0.47  # Preprocessing time       : 0.029 s
% 0.20/0.47  # Presaturation interreduction done
% 0.20/0.47  
% 0.20/0.47  # Proof found!
% 0.20/0.47  # SZS status Theorem
% 0.20/0.47  # SZS output start CNFRefutation
% 0.20/0.47  fof(t54_waybel_0, conjecture, ![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((((![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r1_yellow_0(X1,X4)))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X3)&![X5]:((v1_finset_1(X5)&m1_subset_1(X5,k1_zfmisc_1(X2)))=>~((r1_yellow_0(X1,X5)&X4=k1_yellow_0(X1,X5))))))))&![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_hidden(k1_yellow_0(X1,X4),X3))))&r1_yellow_0(X1,X2))=>k1_yellow_0(X1,X3)=k1_yellow_0(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_waybel_0)).
% 0.20/0.47  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.20/0.47  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.47  fof(d9_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 0.20/0.47  fof(t63_subset_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 0.20/0.47  fof(t7_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((((r1_lattice3(X1,k1_tarski(X3),X2)=>r1_orders_2(X1,X2,X3))&(r1_orders_2(X1,X2,X3)=>r1_lattice3(X1,k1_tarski(X3),X2)))&(r2_lattice3(X1,k1_tarski(X3),X2)=>r1_orders_2(X1,X3,X2)))&(r1_orders_2(X1,X3,X2)=>r2_lattice3(X1,k1_tarski(X3),X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_yellow_0)).
% 0.20/0.47  fof(d9_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_yellow_0(X1,X2)=>(X3=k1_yellow_0(X1,X2)<=>(r2_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)=>r1_orders_2(X1,X3,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_yellow_0)).
% 0.20/0.47  fof(t24_orders_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,X2,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_orders_2)).
% 0.20/0.47  fof(fc1_finset_1, axiom, ![X1]:v1_finset_1(k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_finset_1)).
% 0.20/0.47  fof(t47_yellow_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2, X3]:((r1_yellow_0(X1,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)<=>r2_lattice3(X1,X3,X4))))=>k1_yellow_0(X1,X2)=k1_yellow_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_yellow_0)).
% 0.20/0.47  fof(fc2_xboole_0, axiom, ![X1]:~(v1_xboole_0(k1_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 0.20/0.47  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.47  fof(t9_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r1_lattice3(X1,X3,X4)=>r1_lattice3(X1,X2,X4))&(r2_lattice3(X1,X3,X4)=>r2_lattice3(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_yellow_0)).
% 0.20/0.47  fof(c_0_13, plain, ![X1, X3, X2]:(epred1_3(X2,X3,X1)<=>(((![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r1_yellow_0(X1,X4)))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X3)&![X5]:((v1_finset_1(X5)&m1_subset_1(X5,k1_zfmisc_1(X2)))=>~((r1_yellow_0(X1,X5)&X4=k1_yellow_0(X1,X5))))))))&![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_hidden(k1_yellow_0(X1,X4),X3))))&r1_yellow_0(X1,X2))), introduced(definition)).
% 0.20/0.47  fof(c_0_14, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(epred1_3(X2,X3,X1)=>k1_yellow_0(X1,X3)=k1_yellow_0(X1,X2)))))), inference(apply_def,[status(thm)],[inference(assume_negation,[status(cth)],[t54_waybel_0]), c_0_13])).
% 0.20/0.47  fof(c_0_15, plain, ![X1, X3, X2]:(epred1_3(X2,X3,X1)=>(((![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r1_yellow_0(X1,X4)))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X3)&![X5]:((v1_finset_1(X5)&m1_subset_1(X5,k1_zfmisc_1(X2)))=>~((r1_yellow_0(X1,X5)&X4=k1_yellow_0(X1,X5))))))))&![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_hidden(k1_yellow_0(X1,X4),X3))))&r1_yellow_0(X1,X2))), inference(split_equiv,[status(thm)],[c_0_13])).
% 0.20/0.47  fof(c_0_16, plain, ![X11, X12, X13]:(~r2_hidden(X11,X12)|~m1_subset_1(X12,k1_zfmisc_1(X13))|m1_subset_1(X11,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.20/0.47  fof(c_0_17, negated_conjecture, ((((~v2_struct_0(esk4_0)&v3_orders_2(esk4_0))&v4_orders_2(esk4_0))&l1_orders_2(esk4_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))&(epred1_3(esk5_0,esk6_0,esk4_0)&k1_yellow_0(esk4_0,esk6_0)!=k1_yellow_0(esk4_0,esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.20/0.47  fof(c_0_18, plain, ![X41, X42, X43, X44, X45, X47]:((((~v1_finset_1(X44)|~m1_subset_1(X44,k1_zfmisc_1(X43))|(X44=k1_xboole_0|r1_yellow_0(X41,X44))|~epred1_3(X43,X42,X41))&(((v1_finset_1(esk7_4(X41,X42,X43,X45))|~r2_hidden(X45,X42)|~m1_subset_1(X45,u1_struct_0(X41))|~epred1_3(X43,X42,X41))&(m1_subset_1(esk7_4(X41,X42,X43,X45),k1_zfmisc_1(X43))|~r2_hidden(X45,X42)|~m1_subset_1(X45,u1_struct_0(X41))|~epred1_3(X43,X42,X41)))&((r1_yellow_0(X41,esk7_4(X41,X42,X43,X45))|~r2_hidden(X45,X42)|~m1_subset_1(X45,u1_struct_0(X41))|~epred1_3(X43,X42,X41))&(X45=k1_yellow_0(X41,esk7_4(X41,X42,X43,X45))|~r2_hidden(X45,X42)|~m1_subset_1(X45,u1_struct_0(X41))|~epred1_3(X43,X42,X41)))))&(~v1_finset_1(X47)|~m1_subset_1(X47,k1_zfmisc_1(X43))|(X47=k1_xboole_0|r2_hidden(k1_yellow_0(X41,X47),X42))|~epred1_3(X43,X42,X41)))&(r1_yellow_0(X41,X43)|~epred1_3(X43,X42,X41))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])])])).
% 0.20/0.47  fof(c_0_19, plain, ![X9, X10]:((~m1_subset_1(X9,k1_zfmisc_1(X10))|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|m1_subset_1(X9,k1_zfmisc_1(X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.47  cnf(c_0_20, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.47  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.47  fof(c_0_22, plain, ![X17, X18, X19, X20]:((~r2_lattice3(X17,X18,X19)|(~m1_subset_1(X20,u1_struct_0(X17))|(~r2_hidden(X20,X18)|r1_orders_2(X17,X20,X19)))|~m1_subset_1(X19,u1_struct_0(X17))|~l1_orders_2(X17))&((m1_subset_1(esk1_3(X17,X18,X19),u1_struct_0(X17))|r2_lattice3(X17,X18,X19)|~m1_subset_1(X19,u1_struct_0(X17))|~l1_orders_2(X17))&((r2_hidden(esk1_3(X17,X18,X19),X18)|r2_lattice3(X17,X18,X19)|~m1_subset_1(X19,u1_struct_0(X17))|~l1_orders_2(X17))&(~r1_orders_2(X17,esk1_3(X17,X18,X19),X19)|r2_lattice3(X17,X18,X19)|~m1_subset_1(X19,u1_struct_0(X17))|~l1_orders_2(X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).
% 0.20/0.47  cnf(c_0_23, plain, (X1=k1_xboole_0|r2_hidden(k1_yellow_0(X3,X1),X4)|~v1_finset_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~epred1_3(X2,X4,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.47  cnf(c_0_24, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.47  fof(c_0_25, plain, ![X7, X8]:(~r2_hidden(X7,X8)|m1_subset_1(k1_tarski(X7),k1_zfmisc_1(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).
% 0.20/0.47  fof(c_0_26, plain, ![X31, X32, X33]:((((~r1_lattice3(X31,k1_tarski(X33),X32)|r1_orders_2(X31,X32,X33)|~m1_subset_1(X33,u1_struct_0(X31))|~m1_subset_1(X32,u1_struct_0(X31))|~l1_orders_2(X31))&(~r1_orders_2(X31,X32,X33)|r1_lattice3(X31,k1_tarski(X33),X32)|~m1_subset_1(X33,u1_struct_0(X31))|~m1_subset_1(X32,u1_struct_0(X31))|~l1_orders_2(X31)))&(~r2_lattice3(X31,k1_tarski(X33),X32)|r1_orders_2(X31,X33,X32)|~m1_subset_1(X33,u1_struct_0(X31))|~m1_subset_1(X32,u1_struct_0(X31))|~l1_orders_2(X31)))&(~r1_orders_2(X31,X33,X32)|r2_lattice3(X31,k1_tarski(X33),X32)|~m1_subset_1(X33,u1_struct_0(X31))|~m1_subset_1(X32,u1_struct_0(X31))|~l1_orders_2(X31))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_yellow_0])])])])).
% 0.20/0.47  fof(c_0_27, plain, ![X22, X23, X24, X25]:(((r2_lattice3(X22,X23,X24)|X24!=k1_yellow_0(X22,X23)|~r1_yellow_0(X22,X23)|~m1_subset_1(X24,u1_struct_0(X22))|~l1_orders_2(X22))&(~m1_subset_1(X25,u1_struct_0(X22))|(~r2_lattice3(X22,X23,X25)|r1_orders_2(X22,X24,X25))|X24!=k1_yellow_0(X22,X23)|~r1_yellow_0(X22,X23)|~m1_subset_1(X24,u1_struct_0(X22))|~l1_orders_2(X22)))&((m1_subset_1(esk2_3(X22,X23,X24),u1_struct_0(X22))|~r2_lattice3(X22,X23,X24)|X24=k1_yellow_0(X22,X23)|~r1_yellow_0(X22,X23)|~m1_subset_1(X24,u1_struct_0(X22))|~l1_orders_2(X22))&((r2_lattice3(X22,X23,esk2_3(X22,X23,X24))|~r2_lattice3(X22,X23,X24)|X24=k1_yellow_0(X22,X23)|~r1_yellow_0(X22,X23)|~m1_subset_1(X24,u1_struct_0(X22))|~l1_orders_2(X22))&(~r1_orders_2(X22,X24,esk2_3(X22,X23,X24))|~r2_lattice3(X22,X23,X24)|X24=k1_yellow_0(X22,X23)|~r1_yellow_0(X22,X23)|~m1_subset_1(X24,u1_struct_0(X22))|~l1_orders_2(X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).
% 0.20/0.47  cnf(c_0_28, plain, (X1=k1_xboole_0|r1_yellow_0(X3,X1)|~v1_finset_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~epred1_3(X2,X4,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.47  fof(c_0_29, plain, ![X15, X16]:(v2_struct_0(X15)|~v3_orders_2(X15)|~l1_orders_2(X15)|(~m1_subset_1(X16,u1_struct_0(X15))|r1_orders_2(X15,X16,X16))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_orders_2])])])])).
% 0.20/0.47  cnf(c_0_30, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk4_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.47  cnf(c_0_31, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.47  cnf(c_0_32, plain, (X1=k1_xboole_0|r2_hidden(k1_yellow_0(X2,X1),X3)|~epred1_3(X4,X3,X2)|~v1_finset_1(X1)|~r1_tarski(X1,X4)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.47  cnf(c_0_33, negated_conjecture, (epred1_3(esk5_0,esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.47  cnf(c_0_34, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.47  cnf(c_0_35, plain, (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.47  fof(c_0_36, plain, ![X14]:v1_finset_1(k1_tarski(X14)), inference(variable_rename,[status(thm)],[fc1_finset_1])).
% 0.20/0.47  cnf(c_0_37, plain, (r1_orders_2(X1,X2,X3)|~r2_lattice3(X1,k1_tarski(X2),X3)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.47  cnf(c_0_38, plain, (r2_lattice3(X1,X2,esk2_3(X1,X2,X3))|X3=k1_yellow_0(X1,X2)|~r2_lattice3(X1,X2,X3)|~r1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.47  cnf(c_0_39, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))|X3=k1_yellow_0(X1,X2)|~r2_lattice3(X1,X2,X3)|~r1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.47  cnf(c_0_40, plain, (X1=k1_xboole_0|r1_yellow_0(X2,X1)|~epred1_3(X3,X4,X2)|~v1_finset_1(X1)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_28, c_0_24])).
% 0.20/0.47  cnf(c_0_41, plain, (r2_lattice3(X1,k1_tarski(X2),X3)|~r1_orders_2(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.47  cnf(c_0_42, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.47  cnf(c_0_43, plain, (v2_struct_0(X1)|r1_orders_2(X1,X2,X2)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.47  cnf(c_0_44, negated_conjecture, (r2_lattice3(X1,esk5_0,X2)|m1_subset_1(esk1_3(X1,esk5_0,X2),u1_struct_0(esk4_0))|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.47  cnf(c_0_45, negated_conjecture, (l1_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.47  cnf(c_0_46, negated_conjecture, (v3_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.47  cnf(c_0_47, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.47  cnf(c_0_48, negated_conjecture, (X1=k1_xboole_0|r2_hidden(k1_yellow_0(esk4_0,X1),esk6_0)|~v1_finset_1(X1)|~r1_tarski(X1,esk5_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.47  cnf(c_0_49, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.47  cnf(c_0_50, plain, (v1_finset_1(k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.47  cnf(c_0_51, plain, (X2=k1_yellow_0(X1,X3)|~r1_orders_2(X1,X2,esk2_3(X1,X3,X2))|~r2_lattice3(X1,X3,X2)|~r1_yellow_0(X1,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.47  cnf(c_0_52, plain, (X1=k1_yellow_0(X2,k1_tarski(X3))|r1_orders_2(X2,X3,esk2_3(X2,k1_tarski(X3),X1))|~r1_yellow_0(X2,k1_tarski(X3))|~r2_lattice3(X2,k1_tarski(X3),X1)|~l1_orders_2(X2)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])).
% 0.20/0.47  cnf(c_0_53, negated_conjecture, (X1=k1_xboole_0|r1_yellow_0(esk4_0,X1)|~v1_finset_1(X1)|~r1_tarski(X1,esk5_0)), inference(spm,[status(thm)],[c_0_40, c_0_33])).
% 0.20/0.47  cnf(c_0_54, plain, (r2_lattice3(X1,k1_tarski(X2),esk1_3(X1,X3,X4))|r2_lattice3(X1,X3,X4)|~r1_orders_2(X1,X2,esk1_3(X1,X3,X4))|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.47  cnf(c_0_55, negated_conjecture, (r2_lattice3(X1,esk5_0,X2)|r1_orders_2(esk4_0,esk1_3(X1,esk5_0,X2),esk1_3(X1,esk5_0,X2))|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_46])]), c_0_47])).
% 0.20/0.47  cnf(c_0_56, negated_conjecture, (k1_tarski(X1)=k1_xboole_0|r2_hidden(k1_yellow_0(esk4_0,k1_tarski(X1)),esk6_0)|~r2_hidden(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])])).
% 0.20/0.47  cnf(c_0_57, plain, (k1_yellow_0(X1,k1_tarski(X2))=X2|~r1_yellow_0(X1,k1_tarski(X2))|~r2_lattice3(X1,k1_tarski(X2),X2)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.20/0.47  cnf(c_0_58, negated_conjecture, (k1_tarski(X1)=k1_xboole_0|r1_yellow_0(esk4_0,k1_tarski(X1))|~r2_hidden(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_49]), c_0_50])])).
% 0.20/0.47  cnf(c_0_59, negated_conjecture, (r2_lattice3(esk4_0,k1_tarski(esk1_3(esk4_0,esk5_0,X1)),esk1_3(esk4_0,esk5_0,X1))|r2_lattice3(esk4_0,esk5_0,X1)|~m1_subset_1(esk1_3(esk4_0,esk5_0,X1),u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_45])])).
% 0.20/0.47  cnf(c_0_60, negated_conjecture, (k1_tarski(X1)=k1_xboole_0|r2_hidden(X1,esk6_0)|~r2_lattice3(esk4_0,k1_tarski(X1),X1)|~r2_hidden(X1,esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_45])]), c_0_30]), c_0_58])).
% 0.20/0.47  cnf(c_0_61, negated_conjecture, (r2_lattice3(esk4_0,k1_tarski(esk1_3(esk4_0,esk5_0,X1)),esk1_3(esk4_0,esk5_0,X1))|r2_lattice3(esk4_0,esk5_0,X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_42]), c_0_45])])).
% 0.20/0.47  cnf(c_0_62, negated_conjecture, (k1_tarski(esk1_3(esk4_0,esk5_0,X1))=k1_xboole_0|r2_lattice3(esk4_0,esk5_0,X1)|r2_hidden(esk1_3(esk4_0,esk5_0,X1),esk6_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))|~r2_hidden(esk1_3(esk4_0,esk5_0,X1),esk5_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.20/0.47  fof(c_0_63, plain, ![X27, X28, X29]:((m1_subset_1(esk3_3(X27,X28,X29),u1_struct_0(X27))|~r1_yellow_0(X27,X28)|k1_yellow_0(X27,X28)=k1_yellow_0(X27,X29)|(v2_struct_0(X27)|~l1_orders_2(X27)))&((~r2_lattice3(X27,X28,esk3_3(X27,X28,X29))|~r2_lattice3(X27,X29,esk3_3(X27,X28,X29))|~r1_yellow_0(X27,X28)|k1_yellow_0(X27,X28)=k1_yellow_0(X27,X29)|(v2_struct_0(X27)|~l1_orders_2(X27)))&(r2_lattice3(X27,X28,esk3_3(X27,X28,X29))|r2_lattice3(X27,X29,esk3_3(X27,X28,X29))|~r1_yellow_0(X27,X28)|k1_yellow_0(X27,X28)=k1_yellow_0(X27,X29)|(v2_struct_0(X27)|~l1_orders_2(X27))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_yellow_0])])])])])])).
% 0.20/0.47  cnf(c_0_64, negated_conjecture, (k1_tarski(esk1_3(esk4_0,esk5_0,X1))=k1_xboole_0|r2_lattice3(esk4_0,esk5_0,X1)|r2_hidden(esk1_3(esk4_0,esk5_0,X1),esk6_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_31]), c_0_45])])).
% 0.20/0.47  cnf(c_0_65, plain, (m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))|k1_yellow_0(X1,X2)=k1_yellow_0(X1,X3)|v2_struct_0(X1)|~r1_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.20/0.47  cnf(c_0_66, plain, (r1_yellow_0(X1,X2)|~epred1_3(X2,X3,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.47  fof(c_0_67, plain, ![X6]:~v1_xboole_0(k1_tarski(X6)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).
% 0.20/0.47  cnf(c_0_68, negated_conjecture, (k1_tarski(esk1_3(esk4_0,esk5_0,esk3_3(esk4_0,X1,X2)))=k1_xboole_0|k1_yellow_0(esk4_0,X1)=k1_yellow_0(esk4_0,X2)|r2_lattice3(esk4_0,esk5_0,esk3_3(esk4_0,X1,X2))|r2_hidden(esk1_3(esk4_0,esk5_0,esk3_3(esk4_0,X1,X2)),esk6_0)|~r1_yellow_0(esk4_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_45])]), c_0_47])).
% 0.20/0.47  cnf(c_0_69, negated_conjecture, (r1_yellow_0(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_66, c_0_33])).
% 0.20/0.47  cnf(c_0_70, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.47  cnf(c_0_71, plain, (~v1_xboole_0(k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.47  cnf(c_0_72, negated_conjecture, (k1_tarski(esk1_3(esk4_0,esk5_0,esk3_3(esk4_0,esk5_0,X1)))=k1_xboole_0|k1_yellow_0(esk4_0,esk5_0)=k1_yellow_0(esk4_0,X1)|r2_lattice3(esk4_0,esk5_0,esk3_3(esk4_0,esk5_0,X1))|r2_hidden(esk1_3(esk4_0,esk5_0,esk3_3(esk4_0,esk5_0,X1)),esk6_0)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.20/0.47  cnf(c_0_73, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.47  cnf(c_0_74, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk4_0))|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_20, c_0_70])).
% 0.20/0.47  cnf(c_0_75, negated_conjecture, (k1_yellow_0(esk4_0,esk5_0)=k1_yellow_0(esk4_0,X1)|r2_lattice3(esk4_0,esk5_0,esk3_3(esk4_0,esk5_0,X1))|r2_hidden(esk1_3(esk4_0,esk5_0,esk3_3(esk4_0,esk5_0,X1)),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73])])).
% 0.20/0.47  cnf(c_0_76, plain, (r1_orders_2(X1,X4,X3)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.47  cnf(c_0_77, negated_conjecture, (k1_yellow_0(esk4_0,esk5_0)=k1_yellow_0(esk4_0,X1)|r2_lattice3(esk4_0,esk5_0,esk3_3(esk4_0,esk5_0,X1))|m1_subset_1(esk1_3(esk4_0,esk5_0,esk3_3(esk4_0,esk5_0,X1)),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.20/0.47  cnf(c_0_78, negated_conjecture, (k1_yellow_0(esk4_0,esk5_0)=k1_yellow_0(esk4_0,X1)|r2_lattice3(esk4_0,esk5_0,esk3_3(esk4_0,esk5_0,X1))|r1_orders_2(esk4_0,esk1_3(esk4_0,esk5_0,esk3_3(esk4_0,esk5_0,X1)),X2)|~r2_lattice3(esk4_0,X3,X2)|~m1_subset_1(X2,u1_struct_0(esk4_0))|~r2_hidden(esk1_3(esk4_0,esk5_0,esk3_3(esk4_0,esk5_0,X1)),X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_45])])).
% 0.20/0.47  cnf(c_0_79, negated_conjecture, (k1_yellow_0(esk4_0,esk5_0)=k1_yellow_0(esk4_0,X1)|r2_lattice3(esk4_0,esk5_0,esk3_3(esk4_0,esk5_0,X1))|r1_orders_2(esk4_0,esk1_3(esk4_0,esk5_0,esk3_3(esk4_0,esk5_0,X1)),X2)|~r2_lattice3(esk4_0,esk6_0,X2)|~m1_subset_1(X2,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_78, c_0_75])).
% 0.20/0.47  cnf(c_0_80, plain, (r2_lattice3(X1,X2,esk3_3(X1,X2,X3))|r2_lattice3(X1,X3,esk3_3(X1,X2,X3))|k1_yellow_0(X1,X2)=k1_yellow_0(X1,X3)|v2_struct_0(X1)|~r1_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.20/0.47  cnf(c_0_81, negated_conjecture, (k1_yellow_0(esk4_0,esk5_0)=k1_yellow_0(esk4_0,X1)|k1_yellow_0(esk4_0,X2)=k1_yellow_0(esk4_0,X3)|r2_lattice3(esk4_0,esk5_0,esk3_3(esk4_0,esk5_0,X1))|r1_orders_2(esk4_0,esk1_3(esk4_0,esk5_0,esk3_3(esk4_0,esk5_0,X1)),esk3_3(esk4_0,X2,X3))|~r1_yellow_0(esk4_0,X2)|~r2_lattice3(esk4_0,esk6_0,esk3_3(esk4_0,X2,X3))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_65]), c_0_45])]), c_0_47])).
% 0.20/0.47  cnf(c_0_82, negated_conjecture, (k1_yellow_0(esk4_0,esk5_0)=k1_yellow_0(esk4_0,X1)|r2_lattice3(esk4_0,esk5_0,esk3_3(esk4_0,esk5_0,X1))|r2_lattice3(esk4_0,X1,esk3_3(esk4_0,esk5_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_69]), c_0_45])]), c_0_47])).
% 0.20/0.47  cnf(c_0_83, negated_conjecture, (k1_yellow_0(esk4_0,esk6_0)!=k1_yellow_0(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.47  fof(c_0_84, plain, ![X34, X35, X36, X37]:((~r1_lattice3(X34,X36,X37)|r1_lattice3(X34,X35,X37)|~m1_subset_1(X37,u1_struct_0(X34))|~r1_tarski(X35,X36)|~l1_orders_2(X34))&(~r2_lattice3(X34,X36,X37)|r2_lattice3(X34,X35,X37)|~m1_subset_1(X37,u1_struct_0(X34))|~r1_tarski(X35,X36)|~l1_orders_2(X34))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_yellow_0])])])])).
% 0.20/0.47  cnf(c_0_85, plain, (r2_lattice3(X1,X2,X3)|~r1_orders_2(X1,esk1_3(X1,X2,X3),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.47  cnf(c_0_86, negated_conjecture, (k1_yellow_0(esk4_0,esk5_0)=k1_yellow_0(esk4_0,X1)|r2_lattice3(esk4_0,esk5_0,esk3_3(esk4_0,esk5_0,esk6_0))|r2_lattice3(esk4_0,esk5_0,esk3_3(esk4_0,esk5_0,X1))|r1_orders_2(esk4_0,esk1_3(esk4_0,esk5_0,esk3_3(esk4_0,esk5_0,X1)),esk3_3(esk4_0,esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_69])]), c_0_83])).
% 0.20/0.47  cnf(c_0_87, plain, (r2_lattice3(X1,X4,X3)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~r1_tarski(X4,X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.20/0.47  cnf(c_0_88, negated_conjecture, (r2_lattice3(esk4_0,esk5_0,esk3_3(esk4_0,esk5_0,esk6_0))|~m1_subset_1(esk3_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_45])]), c_0_83])).
% 0.20/0.47  cnf(c_0_89, plain, (r1_orders_2(X2,X4,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|X4!=k1_yellow_0(X2,X3)|~r1_yellow_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.47  cnf(c_0_90, plain, (k1_yellow_0(X1,X2)=k1_yellow_0(X1,X3)|r2_lattice3(X1,X4,esk3_3(X1,X2,X3))|v2_struct_0(X1)|~r1_yellow_0(X1,X2)|~r2_lattice3(X1,X5,esk3_3(X1,X2,X3))|~l1_orders_2(X1)|~r1_tarski(X4,X5)), inference(spm,[status(thm)],[c_0_87, c_0_65])).
% 0.20/0.47  cnf(c_0_91, negated_conjecture, (r2_lattice3(esk4_0,esk5_0,esk3_3(esk4_0,esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_65]), c_0_69]), c_0_45])]), c_0_83]), c_0_47])).
% 0.20/0.47  cnf(c_0_92, plain, (m1_subset_1(esk7_4(X1,X2,X3,X4),k1_zfmisc_1(X3))|~r2_hidden(X4,X2)|~m1_subset_1(X4,u1_struct_0(X1))|~epred1_3(X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.47  cnf(c_0_93, plain, (r1_orders_2(X1,k1_yellow_0(X1,X2),X3)|~r1_yellow_0(X1,X2)|~r2_lattice3(X1,X2,X3)|~l1_orders_2(X1)|~m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_89])).
% 0.20/0.47  cnf(c_0_94, plain, (X1=k1_yellow_0(X2,esk7_4(X2,X3,X4,X1))|~r2_hidden(X1,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~epred1_3(X4,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.47  cnf(c_0_95, plain, (r1_yellow_0(X1,esk7_4(X1,X2,X3,X4))|~r2_hidden(X4,X2)|~m1_subset_1(X4,u1_struct_0(X1))|~epred1_3(X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.47  cnf(c_0_96, negated_conjecture, (r2_lattice3(esk4_0,X1,esk3_3(esk4_0,esk5_0,esk6_0))|~r1_tarski(X1,esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_69]), c_0_45])]), c_0_83]), c_0_47])).
% 0.20/0.47  cnf(c_0_97, plain, (r1_tarski(esk7_4(X1,X2,X3,X4),X3)|~epred1_3(X3,X2,X1)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)), inference(spm,[status(thm)],[c_0_34, c_0_92])).
% 0.20/0.47  cnf(c_0_98, plain, (r1_orders_2(X1,X2,X3)|~epred1_3(X4,X5,X1)|~r2_lattice3(X1,esk7_4(X1,X5,X4,X2),X3)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~r2_hidden(X2,X5)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_95])).
% 0.20/0.47  cnf(c_0_99, plain, (r2_lattice3(esk4_0,esk7_4(X1,X2,esk5_0,X3),esk3_3(esk4_0,esk5_0,esk6_0))|~epred1_3(esk5_0,X2,X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 0.20/0.47  cnf(c_0_100, plain, (r1_orders_2(esk4_0,X1,esk3_3(esk4_0,esk5_0,esk6_0))|~epred1_3(esk5_0,X2,esk4_0)|~m1_subset_1(esk3_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))|~r2_hidden(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_45])])).
% 0.20/0.47  cnf(c_0_101, plain, (r1_orders_2(esk4_0,X1,esk3_3(esk4_0,esk5_0,esk6_0))|~epred1_3(esk5_0,X2,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))|~r2_hidden(X1,X2)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_65]), c_0_69]), c_0_45])]), c_0_83]), c_0_47])).
% 0.20/0.47  cnf(c_0_102, negated_conjecture, (r1_orders_2(esk4_0,X1,esk3_3(esk4_0,esk5_0,esk6_0))|~r2_hidden(X1,esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_33]), c_0_74])).
% 0.20/0.47  cnf(c_0_103, negated_conjecture, (r2_lattice3(esk4_0,X1,esk3_3(esk4_0,esk5_0,esk6_0))|~m1_subset_1(esk3_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk4_0))|~r2_hidden(esk1_3(esk4_0,X1,esk3_3(esk4_0,esk5_0,esk6_0)),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_102]), c_0_45])])).
% 0.20/0.47  cnf(c_0_104, negated_conjecture, (r2_lattice3(esk4_0,esk6_0,esk3_3(esk4_0,esk5_0,esk6_0))|~m1_subset_1(esk3_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_31]), c_0_45])])).
% 0.20/0.47  cnf(c_0_105, plain, (k1_yellow_0(X1,X2)=k1_yellow_0(X1,X3)|v2_struct_0(X1)|~r2_lattice3(X1,X2,esk3_3(X1,X2,X3))|~r2_lattice3(X1,X3,esk3_3(X1,X2,X3))|~r1_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.20/0.47  cnf(c_0_106, negated_conjecture, (r2_lattice3(esk4_0,esk6_0,esk3_3(esk4_0,esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_65]), c_0_69]), c_0_45])]), c_0_83]), c_0_47])).
% 0.20/0.47  cnf(c_0_107, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_69]), c_0_91]), c_0_45])]), c_0_83]), c_0_47]), ['proof']).
% 0.20/0.47  # SZS output end CNFRefutation
% 0.20/0.47  # Proof object total steps             : 108
% 0.20/0.47  # Proof object clause steps            : 79
% 0.20/0.47  # Proof object formula steps           : 29
% 0.20/0.47  # Proof object conjectures             : 41
% 0.20/0.47  # Proof object clause conjectures      : 38
% 0.20/0.47  # Proof object formula conjectures     : 3
% 0.20/0.47  # Proof object initial clauses used    : 35
% 0.20/0.47  # Proof object initial formulas used   : 13
% 0.20/0.47  # Proof object generating inferences   : 43
% 0.20/0.47  # Proof object simplifying inferences  : 73
% 0.20/0.47  # Training examples: 0 positive, 0 negative
% 0.20/0.47  # Parsed axioms                        : 13
% 0.20/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.47  # Initial clauses                      : 41
% 0.20/0.47  # Removed in clause preprocessing      : 0
% 0.20/0.47  # Initial clauses in saturation        : 41
% 0.20/0.47  # Processed clauses                    : 498
% 0.20/0.47  # ...of these trivial                  : 0
% 0.20/0.47  # ...subsumed                          : 97
% 0.20/0.47  # ...remaining for further processing  : 401
% 0.20/0.47  # Other redundant clauses eliminated   : 2
% 0.20/0.47  # Clauses deleted for lack of memory   : 0
% 0.20/0.47  # Backward-subsumed                    : 18
% 0.20/0.47  # Backward-rewritten                   : 9
% 0.20/0.47  # Generated clauses                    : 1267
% 0.20/0.47  # ...of the previous two non-trivial   : 1240
% 0.20/0.47  # Contextual simplify-reflections      : 40
% 0.20/0.47  # Paramodulations                      : 1263
% 0.20/0.47  # Factorizations                       : 2
% 0.20/0.47  # Equation resolutions                 : 2
% 0.20/0.47  # Propositional unsat checks           : 0
% 0.20/0.47  #    Propositional check models        : 0
% 0.20/0.47  #    Propositional check unsatisfiable : 0
% 0.20/0.47  #    Propositional clauses             : 0
% 0.20/0.47  #    Propositional clauses after purity: 0
% 0.20/0.47  #    Propositional unsat core size     : 0
% 0.20/0.47  #    Propositional preprocessing time  : 0.000
% 0.20/0.47  #    Propositional encoding time       : 0.000
% 0.20/0.47  #    Propositional solver time         : 0.000
% 0.20/0.47  #    Success case prop preproc time    : 0.000
% 0.20/0.47  #    Success case prop encoding time   : 0.000
% 0.20/0.47  #    Success case prop solver time     : 0.000
% 0.20/0.47  # Current number of processed clauses  : 331
% 0.20/0.47  #    Positive orientable unit clauses  : 13
% 0.20/0.47  #    Positive unorientable unit clauses: 0
% 0.20/0.47  #    Negative unit clauses             : 3
% 0.20/0.47  #    Non-unit-clauses                  : 315
% 0.20/0.47  # Current number of unprocessed clauses: 754
% 0.20/0.47  # ...number of literals in the above   : 6332
% 0.20/0.47  # Current number of archived formulas  : 0
% 0.20/0.47  # Current number of archived clauses   : 68
% 0.20/0.47  # Clause-clause subsumption calls (NU) : 30335
% 0.20/0.47  # Rec. Clause-clause subsumption calls : 1745
% 0.20/0.47  # Non-unit clause-clause subsumptions  : 155
% 0.20/0.47  # Unit Clause-clause subsumption calls : 188
% 0.20/0.47  # Rewrite failures with RHS unbound    : 0
% 0.20/0.47  # BW rewrite match attempts            : 23
% 0.20/0.47  # BW rewrite match successes           : 2
% 0.20/0.47  # Condensation attempts                : 0
% 0.20/0.47  # Condensation successes               : 0
% 0.20/0.47  # Termbank termtop insertions          : 56976
% 0.20/0.47  
% 0.20/0.47  # -------------------------------------------------
% 0.20/0.47  # User time                : 0.124 s
% 0.20/0.47  # System time              : 0.004 s
% 0.20/0.47  # Total time               : 0.128 s
% 0.20/0.47  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
