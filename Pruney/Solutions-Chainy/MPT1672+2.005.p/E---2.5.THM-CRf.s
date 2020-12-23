%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:26 EST 2020

% Result     : Theorem 9.25s
% Output     : CNFRefutation 9.25s
% Verified   : 
% Statistics : Number of formulae       :  187 (5987265 expanded)
%              Number of clauses        :  160 (1980138 expanded)
%              Number of leaves         :   13 (1988496 expanded)
%              Depth                    :   49
%              Number of atoms          :  787 (60872329 expanded)
%              Number of equality atoms :  209 (5328310 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   30 (   3 average)
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

fof(t24_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r1_orders_2(X1,X2,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

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

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

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
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | r1_tarski(k1_tarski(esk1_3(esk3_0,X1,esk6_0)),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

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
    ( ~ r2_lattice3(esk3_0,esk4_0,esk6_0)
    | ~ r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,X1,esk6_0)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_18]),c_0_19])])).

fof(c_0_30,plain,(
    ! [X38,X39,X40,X41,X42,X44] :
      ( ( ~ v1_finset_1(X41)
        | ~ m1_subset_1(X41,k1_zfmisc_1(X39))
        | X41 = k1_xboole_0
        | r1_yellow_0(X38,X41)
        | ~ epred1_3(X40,X39,X38) )
      & ( v1_finset_1(esk7_4(X38,X39,X40,X42))
        | ~ r2_hidden(X42,X40)
        | ~ m1_subset_1(X42,u1_struct_0(X38))
        | ~ epred1_3(X40,X39,X38) )
      & ( m1_subset_1(esk7_4(X38,X39,X40,X42),k1_zfmisc_1(X39))
        | ~ r2_hidden(X42,X40)
        | ~ m1_subset_1(X42,u1_struct_0(X38))
        | ~ epred1_3(X40,X39,X38) )
      & ( r1_yellow_0(X38,esk7_4(X38,X39,X40,X42))
        | ~ r2_hidden(X42,X40)
        | ~ m1_subset_1(X42,u1_struct_0(X38))
        | ~ epred1_3(X40,X39,X38) )
      & ( X42 = k1_yellow_0(X38,esk7_4(X38,X39,X40,X42))
        | ~ r2_hidden(X42,X40)
        | ~ m1_subset_1(X42,u1_struct_0(X38))
        | ~ epred1_3(X40,X39,X38) )
      & ( ~ v1_finset_1(X44)
        | ~ m1_subset_1(X44,k1_zfmisc_1(X39))
        | X44 = k1_xboole_0
        | r2_hidden(k1_yellow_0(X38,X44),X40)
        | ~ epred1_3(X40,X39,X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])])])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | ~ r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_32,plain,(
    ! [X14] : v1_finset_1(k1_tarski(X14)) ),
    inference(variable_rename,[status(thm)],[fc1_finset_1])).

fof(c_0_33,plain,(
    ! [X27,X28,X29] :
      ( ( ~ r1_lattice3(X27,k1_tarski(X29),X28)
        | r1_orders_2(X27,X28,X29)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | ~ l1_orders_2(X27) )
      & ( ~ r1_orders_2(X27,X28,X29)
        | r1_lattice3(X27,k1_tarski(X29),X28)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | ~ l1_orders_2(X27) )
      & ( ~ r2_lattice3(X27,k1_tarski(X29),X28)
        | r1_orders_2(X27,X29,X28)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | ~ l1_orders_2(X27) )
      & ( ~ r1_orders_2(X27,X29,X28)
        | r2_lattice3(X27,k1_tarski(X29),X28)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | ~ l1_orders_2(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_yellow_0])])])])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_29])).

fof(c_0_35,plain,(
    ! [X15,X16] :
      ( v2_struct_0(X15)
      | ~ v3_orders_2(X15)
      | ~ l1_orders_2(X15)
      | ~ m1_subset_1(X16,u1_struct_0(X15))
      | r1_orders_2(X15,X16,X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_orders_2])])])])).

fof(c_0_36,plain,(
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

cnf(c_0_37,plain,
    ( X1 = k1_xboole_0
    | r1_yellow_0(X3,X1)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ epred1_3(X4,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_29])).

cnf(c_0_39,plain,
    ( v1_finset_1(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( r2_lattice3(X1,k1_tarski(X2),X3)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_29])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( v3_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_44,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_45,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | X3 = k1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,plain,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ epred1_3(X2,esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])])).

cnf(c_0_47,negated_conjecture,
    ( epred1_3(esk5_0,esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_48,negated_conjecture,
    ( r2_lattice3(esk3_0,k1_tarski(X1),esk1_3(esk3_0,esk4_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_19])])).

cnf(c_0_49,negated_conjecture,
    ( r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_41]),c_0_19]),c_0_43])]),c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( esk1_3(esk3_0,esk4_0,esk6_0) = k1_yellow_0(esk3_0,X1)
    | m1_subset_1(esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_yellow_0(esk3_0,X1)
    | ~ r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_41]),c_0_19])])).

cnf(c_0_51,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_41]),c_0_49])).

cnf(c_0_53,plain,
    ( r2_lattice3(X1,X2,esk2_3(X1,X2,X3))
    | X3 = k1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_54,plain,
    ( X2 = k1_yellow_0(X1,X3)
    | ~ r1_orders_2(X1,X2,esk2_3(X1,X3,X2))
    | ~ r2_lattice3(X1,X3,X2)
    | ~ r1_yellow_0(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_55,plain,
    ( r1_orders_2(X1,X2,X3)
    | ~ r2_lattice3(X1,k1_tarski(X2),X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_56,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( esk1_3(esk3_0,esk4_0,esk6_0) = k1_yellow_0(esk3_0,X1)
    | r2_lattice3(esk3_0,X1,esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_yellow_0(esk3_0,X1)
    | ~ r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_41]),c_0_19])])).

cnf(c_0_58,negated_conjecture,
    ( esk1_3(esk3_0,esk4_0,esk6_0) = k1_yellow_0(esk3_0,X1)
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_yellow_0(esk3_0,X1)
    | ~ r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_41]),c_0_19])])).

cnf(c_0_59,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,X1,esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r2_lattice3(esk3_0,k1_tarski(X1),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_19])])).

cnf(c_0_60,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_51]),c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_51]),c_0_52])).

cnf(c_0_62,plain,
    ( X1 = k1_yellow_0(X2,esk7_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ epred1_3(X4,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_63,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_41]),c_0_60]),c_0_61])).

cnf(c_0_64,plain,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | ~ epred1_3(X2,X1,esk3_0)
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_65,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_28])).

cnf(c_0_67,plain,
    ( m1_subset_1(esk7_4(X1,X2,X3,X4),k1_zfmisc_1(X2))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_68,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_47])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))
    | r1_tarski(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_71,plain,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(X1))
    | ~ epred1_3(X2,X1,esk3_0)
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2) ),
    inference(spm,[status(thm)],[c_0_67,c_0_63])).

cnf(c_0_72,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_22])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))
    | r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_74,plain,
    ( r1_yellow_0(X1,esk7_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_75,plain,(
    ! [X30,X31,X32,X33] :
      ( ( ~ r1_lattice3(X30,X32,X33)
        | r1_lattice3(X30,X31,X33)
        | ~ m1_subset_1(X33,u1_struct_0(X30))
        | ~ r1_tarski(X31,X32)
        | ~ l1_orders_2(X30) )
      & ( ~ r2_lattice3(X30,X32,X33)
        | r2_lattice3(X30,X31,X33)
        | ~ m1_subset_1(X33,u1_struct_0(X30))
        | ~ r1_tarski(X31,X32)
        | ~ l1_orders_2(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_yellow_0])])])])).

cnf(c_0_76,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_47])).

cnf(c_0_77,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_72])).

cnf(c_0_78,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_73])).

cnf(c_0_79,plain,
    ( r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | X4 != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_80,plain,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)))
    | ~ epred1_3(X2,X1,esk3_0)
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2) ),
    inference(spm,[status(thm)],[c_0_74,c_0_63])).

cnf(c_0_81,plain,
    ( r2_lattice3(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_tarski(X4,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_82,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk5_0,esk6_0)
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_22])).

cnf(c_0_83,plain,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))
    | ~ epred1_3(X2,esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_77]),c_0_39])])).

cnf(c_0_84,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,k1_tarski(X1),esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_78]),c_0_19])])).

cnf(c_0_85,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_78]),c_0_19]),c_0_43])]),c_0_44])).

cnf(c_0_86,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_79])).

cnf(c_0_87,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_47])).

cnf(c_0_88,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | ~ r2_lattice3(esk3_0,X2,esk6_0)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_18]),c_0_19])])).

cnf(c_0_89,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_82])).

cnf(c_0_90,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | esk1_3(esk3_0,esk4_0,esk6_0) = k1_yellow_0(esk3_0,X1)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0))
    | ~ r1_yellow_0(esk3_0,X1)
    | ~ r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_78]),c_0_19])])).

cnf(c_0_91,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_83,c_0_47])).

cnf(c_0_92,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_78]),c_0_85])).

cnf(c_0_93,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_73])).

cnf(c_0_94,negated_conjecture,
    ( r1_orders_2(esk3_0,k1_yellow_0(esk3_0,X1),esk6_0)
    | ~ r1_yellow_0(esk3_0,X1)
    | ~ r2_lattice3(esk3_0,X1,esk6_0)
    | ~ m1_subset_1(k1_yellow_0(esk3_0,X1),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_18]),c_0_19])])).

cnf(c_0_95,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))
    | r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_22])).

cnf(c_0_96,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,X2,esk6_0)),k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_88,c_0_28])).

cnf(c_0_97,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_89])).

cnf(c_0_98,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_92])).

cnf(c_0_99,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | esk1_3(esk3_0,esk4_0,esk6_0) = k1_yellow_0(esk3_0,X1)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,X1,esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)))
    | ~ r1_yellow_0(esk3_0,X1)
    | ~ r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_78]),c_0_19])])).

cnf(c_0_100,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | esk1_3(esk3_0,esk4_0,esk6_0) = k1_yellow_0(esk3_0,X1)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | ~ r1_yellow_0(esk3_0,X1)
    | ~ r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_78]),c_0_19])])).

cnf(c_0_101,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,X2,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_88,c_0_29])).

cnf(c_0_102,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))
    | r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_93])).

cnf(c_0_103,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk5_0,esk6_0)
    | r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)
    | ~ r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)
    | ~ m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_104,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_105,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,X1,esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))
    | ~ r2_lattice3(esk3_0,k1_tarski(X1),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_98]),c_0_19])])).

cnf(c_0_106,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_91]),c_0_92])).

cnf(c_0_107,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | ~ r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_91]),c_0_92])).

cnf(c_0_108,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_109,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk1_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_110,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | ~ m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_31])).

cnf(c_0_111,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_78]),c_0_106]),c_0_107])).

cnf(c_0_112,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))
    | ~ m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_108]),c_0_34])).

cnf(c_0_113,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | ~ r1_orders_2(esk3_0,esk1_3(esk3_0,X1,esk6_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_18]),c_0_19])])).

cnf(c_0_114,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk1_3(esk3_0,esk5_0,esk6_0),esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_38])).

cnf(c_0_115,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk1_3(esk3_0,esk5_0,esk6_0),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_111]),c_0_41])).

cnf(c_0_116,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(k1_yellow_0(X3,X1),X4)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ epred1_3(X4,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_117,negated_conjecture,
    ( m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_28])).

cnf(c_0_118,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_31])).

cnf(c_0_119,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_115]),c_0_34])).

fof(c_0_120,plain,(
    ! [X11,X12,X13] :
      ( ~ r2_hidden(X11,X12)
      | ~ m1_subset_1(X12,k1_zfmisc_1(X13))
      | m1_subset_1(X11,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_121,plain,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))
    | r2_hidden(k1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)
    | ~ epred1_3(X2,esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_117]),c_0_39])])).

cnf(c_0_122,plain,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))
    | ~ epred1_3(X2,esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_118]),c_0_39])])).

cnf(c_0_123,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,k1_tarski(X1),esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_119]),c_0_19])])).

cnf(c_0_124,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_119]),c_0_19]),c_0_43])]),c_0_44])).

cnf(c_0_125,plain,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | r2_hidden(k1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)
    | ~ epred1_3(X2,esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_38]),c_0_39])])).

cnf(c_0_126,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_120])).

cnf(c_0_127,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_128,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))
    | r2_hidden(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_121,c_0_47])).

cnf(c_0_129,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | esk1_3(esk3_0,esk4_0,esk6_0) = k1_yellow_0(esk3_0,X1)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0))
    | ~ r1_yellow_0(esk3_0,X1)
    | ~ r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_119]),c_0_19])])).

cnf(c_0_130,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_122,c_0_47])).

cnf(c_0_131,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_119]),c_0_124])).

cnf(c_0_132,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | r2_hidden(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_125,c_0_47])).

cnf(c_0_133,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_126,c_0_127])).

cnf(c_0_134,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))
    | r1_tarski(k1_tarski(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_128])).

cnf(c_0_135,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_130]),c_0_131])).

cnf(c_0_136,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | esk1_3(esk3_0,esk4_0,esk6_0) = k1_yellow_0(esk3_0,X1)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,X1,esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)))
    | ~ r1_yellow_0(esk3_0,X1)
    | ~ r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_119]),c_0_19])])).

cnf(c_0_137,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | esk1_3(esk3_0,esk4_0,esk6_0) = k1_yellow_0(esk3_0,X1)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | ~ r1_yellow_0(esk3_0,X1)
    | ~ r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_119]),c_0_19])])).

cnf(c_0_138,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | r1_tarski(k1_tarski(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_132])).

cnf(c_0_139,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk6_0)
    | ~ r2_lattice3(esk3_0,k1_tarski(X1),esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_18]),c_0_19])])).

cnf(c_0_140,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),u1_struct_0(esk3_0))
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_133,c_0_128])).

cnf(c_0_141,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,k1_tarski(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))),esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_134])).

cnf(c_0_142,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,X1,esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))
    | ~ r2_lattice3(esk3_0,k1_tarski(X1),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_135]),c_0_19])])).

cnf(c_0_143,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_130]),c_0_131])).

cnf(c_0_144,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | ~ r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_130]),c_0_131])).

cnf(c_0_145,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_133,c_0_132])).

cnf(c_0_146,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,k1_tarski(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_101,c_0_138])).

cnf(c_0_147,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_140]),c_0_141])).

cnf(c_0_148,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_119]),c_0_143]),c_0_144])).

cnf(c_0_149,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_145]),c_0_146])).

cnf(c_0_150,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_147,c_0_148])).

cnf(c_0_151,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_149,c_0_148])).

cnf(c_0_152,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk4_0,esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_113,c_0_150])).

cnf(c_0_153,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk4_0,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_113,c_0_151])).

cnf(c_0_154,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_152]),c_0_28])).

cnf(c_0_155,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_153]),c_0_29])).

cnf(c_0_156,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_tarski(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_154])).

cnf(c_0_157,plain,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(X1))
    | ~ epred1_3(X2,X1,esk3_0)
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2) ),
    inference(spm,[status(thm)],[c_0_67,c_0_155])).

cnf(c_0_158,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_156])).

cnf(c_0_159,plain,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)))
    | ~ epred1_3(X2,X1,esk3_0)
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2) ),
    inference(spm,[status(thm)],[c_0_74,c_0_155])).

cnf(c_0_160,negated_conjecture,
    ( r2_lattice3(esk3_0,esk4_0,esk6_0)
    | r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_161,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_157,c_0_47]),c_0_158])).

cnf(c_0_162,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_159,c_0_47]),c_0_158])).

cnf(c_0_163,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0)
    | r2_lattice3(esk3_0,X1,esk6_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_88,c_0_160])).

cnf(c_0_164,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_161])).

cnf(c_0_165,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)
    | ~ r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)
    | ~ m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_162])).

cnf(c_0_166,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)
    | r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_163,c_0_164])).

cnf(c_0_167,plain,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | ~ epred1_3(X2,X1,esk3_0)
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2) ),
    inference(spm,[status(thm)],[c_0_62,c_0_155])).

cnf(c_0_168,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk5_0,esk6_0)
    | r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)
    | ~ m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_165,c_0_166])).

cnf(c_0_169,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_167,c_0_47]),c_0_158])).

cnf(c_0_170,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_168,c_0_169]),c_0_29]),c_0_113])).

cnf(c_0_171,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_170])).

cnf(c_0_172,plain,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_hidden(k1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)
    | ~ epred1_3(X2,esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_171]),c_0_39])])).

cnf(c_0_173,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_hidden(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_172,c_0_47])).

cnf(c_0_174,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_173,c_0_148])).

cnf(c_0_175,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_170])).

cnf(c_0_176,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,X1,esk6_0)
    | ~ r1_tarski(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_88,c_0_170])).

cnf(c_0_177,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_tarski(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_174])).

cnf(c_0_178,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0)
    | ~ r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_139,c_0_175])).

cnf(c_0_179,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_176,c_0_177])).

cnf(c_0_180,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_178,c_0_179])).

fof(c_0_181,plain,(
    ! [X6] : ~ v1_xboole_0(k1_tarski(X6)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

cnf(c_0_182,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_113,c_0_180])).

cnf(c_0_183,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_181])).

cnf(c_0_184,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_182]),c_0_170])).

cnf(c_0_185,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_186,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_183,c_0_184]),c_0_185])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:39:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 9.25/9.45  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 9.25/9.45  # and selection function SelectNewComplexAHP.
% 9.25/9.45  #
% 9.25/9.45  # Preprocessing time       : 0.034 s
% 9.25/9.45  # Presaturation interreduction done
% 9.25/9.45  
% 9.25/9.45  # Proof found!
% 9.25/9.45  # SZS status Theorem
% 9.25/9.45  # SZS output start CNFRefutation
% 9.25/9.45  fof(t52_waybel_0, conjecture, ![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(((![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r1_yellow_0(X1,X4)))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X3)&![X5]:((v1_finset_1(X5)&m1_subset_1(X5,k1_zfmisc_1(X2)))=>~((r1_yellow_0(X1,X5)&X4=k1_yellow_0(X1,X5))))))))&![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_hidden(k1_yellow_0(X1,X4),X3))))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)<=>r2_lattice3(X1,X3,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_waybel_0)).
% 9.25/9.45  fof(d9_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 9.25/9.45  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 9.25/9.45  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.25/9.45  fof(fc1_finset_1, axiom, ![X1]:v1_finset_1(k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_finset_1)).
% 9.25/9.45  fof(t7_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((((r1_lattice3(X1,k1_tarski(X3),X2)=>r1_orders_2(X1,X2,X3))&(r1_orders_2(X1,X2,X3)=>r1_lattice3(X1,k1_tarski(X3),X2)))&(r2_lattice3(X1,k1_tarski(X3),X2)=>r1_orders_2(X1,X3,X2)))&(r1_orders_2(X1,X3,X2)=>r2_lattice3(X1,k1_tarski(X3),X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_yellow_0)).
% 9.25/9.45  fof(t24_orders_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,X2,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_orders_2)).
% 9.25/9.45  fof(d9_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_yellow_0(X1,X2)=>(X3=k1_yellow_0(X1,X2)<=>(r2_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)=>r1_orders_2(X1,X3,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_yellow_0)).
% 9.25/9.45  fof(t9_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r1_lattice3(X1,X3,X4)=>r1_lattice3(X1,X2,X4))&(r2_lattice3(X1,X3,X4)=>r2_lattice3(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_yellow_0)).
% 9.25/9.45  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 9.25/9.45  fof(fc2_xboole_0, axiom, ![X1]:~(v1_xboole_0(k1_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 9.25/9.45  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.25/9.45  fof(c_0_12, plain, ![X1, X2, X3]:(epred1_3(X3,X2,X1)<=>((![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r1_yellow_0(X1,X4)))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X3)&![X5]:((v1_finset_1(X5)&m1_subset_1(X5,k1_zfmisc_1(X2)))=>~((r1_yellow_0(X1,X5)&X4=k1_yellow_0(X1,X5))))))))&![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_hidden(k1_yellow_0(X1,X4),X3))))), introduced(definition)).
% 9.25/9.45  fof(c_0_13, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(epred1_3(X3,X2,X1)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)<=>r2_lattice3(X1,X3,X4)))))))), inference(apply_def,[status(thm)],[inference(assume_negation,[status(cth)],[t52_waybel_0]), c_0_12])).
% 9.25/9.45  fof(c_0_14, plain, ![X17, X18, X19, X20]:((~r2_lattice3(X17,X18,X19)|(~m1_subset_1(X20,u1_struct_0(X17))|(~r2_hidden(X20,X18)|r1_orders_2(X17,X20,X19)))|~m1_subset_1(X19,u1_struct_0(X17))|~l1_orders_2(X17))&((m1_subset_1(esk1_3(X17,X18,X19),u1_struct_0(X17))|r2_lattice3(X17,X18,X19)|~m1_subset_1(X19,u1_struct_0(X17))|~l1_orders_2(X17))&((r2_hidden(esk1_3(X17,X18,X19),X18)|r2_lattice3(X17,X18,X19)|~m1_subset_1(X19,u1_struct_0(X17))|~l1_orders_2(X17))&(~r1_orders_2(X17,esk1_3(X17,X18,X19),X19)|r2_lattice3(X17,X18,X19)|~m1_subset_1(X19,u1_struct_0(X17))|~l1_orders_2(X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).
% 9.25/9.45  fof(c_0_15, negated_conjecture, ((((~v2_struct_0(esk3_0)&v3_orders_2(esk3_0))&v4_orders_2(esk3_0))&l1_orders_2(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(epred1_3(esk5_0,esk4_0,esk3_0)&(m1_subset_1(esk6_0,u1_struct_0(esk3_0))&((~r2_lattice3(esk3_0,esk4_0,esk6_0)|~r2_lattice3(esk3_0,esk5_0,esk6_0))&(r2_lattice3(esk3_0,esk4_0,esk6_0)|r2_lattice3(esk3_0,esk5_0,esk6_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 9.25/9.45  fof(c_0_16, plain, ![X7, X8]:((~r1_tarski(k1_tarski(X7),X8)|r2_hidden(X7,X8))&(~r2_hidden(X7,X8)|r1_tarski(k1_tarski(X7),X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 9.25/9.45  cnf(c_0_17, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 9.25/9.45  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 9.25/9.45  cnf(c_0_19, negated_conjecture, (l1_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 9.25/9.45  fof(c_0_20, plain, ![X9, X10]:((~m1_subset_1(X9,k1_zfmisc_1(X10))|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|m1_subset_1(X9,k1_zfmisc_1(X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 9.25/9.45  cnf(c_0_21, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 9.25/9.45  cnf(c_0_22, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|r2_hidden(esk1_3(esk3_0,X1,esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])])).
% 9.25/9.45  cnf(c_0_23, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 9.25/9.45  cnf(c_0_24, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|r1_tarski(k1_tarski(esk1_3(esk3_0,X1,esk6_0)),X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 9.25/9.45  cnf(c_0_25, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 9.25/9.45  fof(c_0_26, plain, ![X1, X2, X3]:(epred1_3(X3,X2,X1)=>((![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r1_yellow_0(X1,X4)))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X3)&![X5]:((v1_finset_1(X5)&m1_subset_1(X5,k1_zfmisc_1(X2)))=>~((r1_yellow_0(X1,X5)&X4=k1_yellow_0(X1,X5))))))))&![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_hidden(k1_yellow_0(X1,X4),X3))))), inference(split_equiv,[status(thm)],[c_0_12])).
% 9.25/9.45  cnf(c_0_27, negated_conjecture, (~r2_lattice3(esk3_0,esk4_0,esk6_0)|~r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 9.25/9.45  cnf(c_0_28, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,X1,esk6_0)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 9.25/9.45  cnf(c_0_29, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk1_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_18]), c_0_19])])).
% 9.25/9.45  fof(c_0_30, plain, ![X38, X39, X40, X41, X42, X44]:(((~v1_finset_1(X41)|~m1_subset_1(X41,k1_zfmisc_1(X39))|(X41=k1_xboole_0|r1_yellow_0(X38,X41))|~epred1_3(X40,X39,X38))&(((v1_finset_1(esk7_4(X38,X39,X40,X42))|~r2_hidden(X42,X40)|~m1_subset_1(X42,u1_struct_0(X38))|~epred1_3(X40,X39,X38))&(m1_subset_1(esk7_4(X38,X39,X40,X42),k1_zfmisc_1(X39))|~r2_hidden(X42,X40)|~m1_subset_1(X42,u1_struct_0(X38))|~epred1_3(X40,X39,X38)))&((r1_yellow_0(X38,esk7_4(X38,X39,X40,X42))|~r2_hidden(X42,X40)|~m1_subset_1(X42,u1_struct_0(X38))|~epred1_3(X40,X39,X38))&(X42=k1_yellow_0(X38,esk7_4(X38,X39,X40,X42))|~r2_hidden(X42,X40)|~m1_subset_1(X42,u1_struct_0(X38))|~epred1_3(X40,X39,X38)))))&(~v1_finset_1(X44)|~m1_subset_1(X44,k1_zfmisc_1(X39))|(X44=k1_xboole_0|r2_hidden(k1_yellow_0(X38,X44),X40))|~epred1_3(X40,X39,X38))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])])])).
% 9.25/9.45  cnf(c_0_31, negated_conjecture, (m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))|~r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 9.25/9.45  fof(c_0_32, plain, ![X14]:v1_finset_1(k1_tarski(X14)), inference(variable_rename,[status(thm)],[fc1_finset_1])).
% 9.25/9.45  fof(c_0_33, plain, ![X27, X28, X29]:((((~r1_lattice3(X27,k1_tarski(X29),X28)|r1_orders_2(X27,X28,X29)|~m1_subset_1(X29,u1_struct_0(X27))|~m1_subset_1(X28,u1_struct_0(X27))|~l1_orders_2(X27))&(~r1_orders_2(X27,X28,X29)|r1_lattice3(X27,k1_tarski(X29),X28)|~m1_subset_1(X29,u1_struct_0(X27))|~m1_subset_1(X28,u1_struct_0(X27))|~l1_orders_2(X27)))&(~r2_lattice3(X27,k1_tarski(X29),X28)|r1_orders_2(X27,X29,X28)|~m1_subset_1(X29,u1_struct_0(X27))|~m1_subset_1(X28,u1_struct_0(X27))|~l1_orders_2(X27)))&(~r1_orders_2(X27,X29,X28)|r2_lattice3(X27,k1_tarski(X29),X28)|~m1_subset_1(X29,u1_struct_0(X27))|~m1_subset_1(X28,u1_struct_0(X27))|~l1_orders_2(X27))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_yellow_0])])])])).
% 9.25/9.45  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))|~r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_27, c_0_29])).
% 9.25/9.45  fof(c_0_35, plain, ![X15, X16]:(v2_struct_0(X15)|~v3_orders_2(X15)|~l1_orders_2(X15)|(~m1_subset_1(X16,u1_struct_0(X15))|r1_orders_2(X15,X16,X16))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_orders_2])])])])).
% 9.25/9.45  fof(c_0_36, plain, ![X22, X23, X24, X25]:(((r2_lattice3(X22,X23,X24)|X24!=k1_yellow_0(X22,X23)|~r1_yellow_0(X22,X23)|~m1_subset_1(X24,u1_struct_0(X22))|~l1_orders_2(X22))&(~m1_subset_1(X25,u1_struct_0(X22))|(~r2_lattice3(X22,X23,X25)|r1_orders_2(X22,X24,X25))|X24!=k1_yellow_0(X22,X23)|~r1_yellow_0(X22,X23)|~m1_subset_1(X24,u1_struct_0(X22))|~l1_orders_2(X22)))&((m1_subset_1(esk2_3(X22,X23,X24),u1_struct_0(X22))|~r2_lattice3(X22,X23,X24)|X24=k1_yellow_0(X22,X23)|~r1_yellow_0(X22,X23)|~m1_subset_1(X24,u1_struct_0(X22))|~l1_orders_2(X22))&((r2_lattice3(X22,X23,esk2_3(X22,X23,X24))|~r2_lattice3(X22,X23,X24)|X24=k1_yellow_0(X22,X23)|~r1_yellow_0(X22,X23)|~m1_subset_1(X24,u1_struct_0(X22))|~l1_orders_2(X22))&(~r1_orders_2(X22,X24,esk2_3(X22,X23,X24))|~r2_lattice3(X22,X23,X24)|X24=k1_yellow_0(X22,X23)|~r1_yellow_0(X22,X23)|~m1_subset_1(X24,u1_struct_0(X22))|~l1_orders_2(X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).
% 9.25/9.45  cnf(c_0_37, plain, (X1=k1_xboole_0|r1_yellow_0(X3,X1)|~v1_finset_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~epred1_3(X4,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 9.25/9.45  cnf(c_0_38, negated_conjecture, (m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_31, c_0_29])).
% 9.25/9.45  cnf(c_0_39, plain, (v1_finset_1(k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 9.25/9.45  cnf(c_0_40, plain, (r2_lattice3(X1,k1_tarski(X2),X3)|~r1_orders_2(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 9.25/9.45  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_34, c_0_29])).
% 9.25/9.45  cnf(c_0_42, plain, (v2_struct_0(X1)|r1_orders_2(X1,X2,X2)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 9.25/9.45  cnf(c_0_43, negated_conjecture, (v3_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 9.25/9.45  cnf(c_0_44, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 9.25/9.45  cnf(c_0_45, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))|X3=k1_yellow_0(X1,X2)|~r2_lattice3(X1,X2,X3)|~r1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 9.25/9.45  cnf(c_0_46, plain, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~epred1_3(X2,esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])])).
% 9.25/9.45  cnf(c_0_47, negated_conjecture, (epred1_3(esk5_0,esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 9.25/9.45  cnf(c_0_48, negated_conjecture, (r2_lattice3(esk3_0,k1_tarski(X1),esk1_3(esk3_0,esk4_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_19])])).
% 9.25/9.45  cnf(c_0_49, negated_conjecture, (r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_41]), c_0_19]), c_0_43])]), c_0_44])).
% 9.25/9.45  cnf(c_0_50, negated_conjecture, (esk1_3(esk3_0,esk4_0,esk6_0)=k1_yellow_0(esk3_0,X1)|m1_subset_1(esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r1_yellow_0(esk3_0,X1)|~r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_41]), c_0_19])])).
% 9.25/9.45  cnf(c_0_51, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 9.25/9.45  cnf(c_0_52, negated_conjecture, (r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_41]), c_0_49])).
% 9.25/9.45  cnf(c_0_53, plain, (r2_lattice3(X1,X2,esk2_3(X1,X2,X3))|X3=k1_yellow_0(X1,X2)|~r2_lattice3(X1,X2,X3)|~r1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 9.25/9.45  cnf(c_0_54, plain, (X2=k1_yellow_0(X1,X3)|~r1_orders_2(X1,X2,esk2_3(X1,X3,X2))|~r2_lattice3(X1,X3,X2)|~r1_yellow_0(X1,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 9.25/9.45  cnf(c_0_55, plain, (r1_orders_2(X1,X2,X3)|~r2_lattice3(X1,k1_tarski(X2),X3)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 9.25/9.45  cnf(c_0_56, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])).
% 9.25/9.45  cnf(c_0_57, negated_conjecture, (esk1_3(esk3_0,esk4_0,esk6_0)=k1_yellow_0(esk3_0,X1)|r2_lattice3(esk3_0,X1,esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r1_yellow_0(esk3_0,X1)|~r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_41]), c_0_19])])).
% 9.25/9.45  cnf(c_0_58, negated_conjecture, (esk1_3(esk3_0,esk4_0,esk6_0)=k1_yellow_0(esk3_0,X1)|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r1_yellow_0(esk3_0,X1)|~r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))|~r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_41]), c_0_19])])).
% 9.25/9.45  cnf(c_0_59, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,X1,esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r2_lattice3(esk3_0,k1_tarski(X1),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_19])])).
% 9.25/9.45  cnf(c_0_60, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_51]), c_0_52])).
% 9.25/9.45  cnf(c_0_61, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_51]), c_0_52])).
% 9.25/9.45  cnf(c_0_62, plain, (X1=k1_yellow_0(X2,esk7_4(X2,X3,X4,X1))|~r2_hidden(X1,X4)|~m1_subset_1(X1,u1_struct_0(X2))|~epred1_3(X4,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 9.25/9.45  cnf(c_0_63, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_41]), c_0_60]), c_0_61])).
% 9.25/9.45  cnf(c_0_64, plain, (k1_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|~epred1_3(X2,X1,esk3_0)|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 9.25/9.45  cnf(c_0_65, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 9.25/9.45  cnf(c_0_66, negated_conjecture, (m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_34, c_0_28])).
% 9.25/9.45  cnf(c_0_67, plain, (m1_subset_1(esk7_4(X1,X2,X3,X4),k1_zfmisc_1(X2))|~r2_hidden(X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~epred1_3(X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 9.25/9.45  cnf(c_0_68, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_64, c_0_47])).
% 9.25/9.45  cnf(c_0_69, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 9.25/9.45  cnf(c_0_70, negated_conjecture, (m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))|r1_tarski(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),esk5_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 9.25/9.45  cnf(c_0_71, plain, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(X1))|~epred1_3(X2,X1,esk3_0)|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2)), inference(spm,[status(thm)],[c_0_67, c_0_63])).
% 9.25/9.45  cnf(c_0_72, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_68, c_0_22])).
% 9.25/9.45  cnf(c_0_73, negated_conjecture, (m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))|r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 9.25/9.45  cnf(c_0_74, plain, (r1_yellow_0(X1,esk7_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~epred1_3(X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 9.25/9.45  fof(c_0_75, plain, ![X30, X31, X32, X33]:((~r1_lattice3(X30,X32,X33)|r1_lattice3(X30,X31,X33)|~m1_subset_1(X33,u1_struct_0(X30))|~r1_tarski(X31,X32)|~l1_orders_2(X30))&(~r2_lattice3(X30,X32,X33)|r2_lattice3(X30,X31,X33)|~m1_subset_1(X33,u1_struct_0(X30))|~r1_tarski(X31,X32)|~l1_orders_2(X30))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_yellow_0])])])])).
% 9.25/9.45  cnf(c_0_76, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_71, c_0_47])).
% 9.25/9.45  cnf(c_0_77, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_31, c_0_72])).
% 9.25/9.45  cnf(c_0_78, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_68, c_0_73])).
% 9.25/9.45  cnf(c_0_79, plain, (r1_orders_2(X2,X4,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|X4!=k1_yellow_0(X2,X3)|~r1_yellow_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 9.25/9.45  cnf(c_0_80, plain, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)))|~epred1_3(X2,X1,esk3_0)|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2)), inference(spm,[status(thm)],[c_0_74, c_0_63])).
% 9.25/9.45  cnf(c_0_81, plain, (r2_lattice3(X1,X4,X3)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~r1_tarski(X4,X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 9.25/9.45  cnf(c_0_82, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk5_0,esk6_0)|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_76, c_0_22])).
% 9.25/9.45  cnf(c_0_83, plain, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))|~epred1_3(X2,esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_77]), c_0_39])])).
% 9.25/9.45  cnf(c_0_84, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,k1_tarski(X1),esk1_3(esk3_0,esk4_0,esk6_0))|~r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_78]), c_0_19])])).
% 9.25/9.45  cnf(c_0_85, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_78]), c_0_19]), c_0_43])]), c_0_44])).
% 9.25/9.45  cnf(c_0_86, plain, (r1_orders_2(X1,k1_yellow_0(X1,X2),X3)|~r1_yellow_0(X1,X2)|~r2_lattice3(X1,X2,X3)|~l1_orders_2(X1)|~m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_79])).
% 9.25/9.45  cnf(c_0_87, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_80, c_0_47])).
% 9.25/9.45  cnf(c_0_88, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|~r2_lattice3(esk3_0,X2,esk6_0)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_18]), c_0_19])])).
% 9.25/9.45  cnf(c_0_89, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_31, c_0_82])).
% 9.25/9.45  cnf(c_0_90, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|esk1_3(esk3_0,esk4_0,esk6_0)=k1_yellow_0(esk3_0,X1)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0))|~r1_yellow_0(esk3_0,X1)|~r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_78]), c_0_19])])).
% 9.25/9.45  cnf(c_0_91, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))), inference(spm,[status(thm)],[c_0_83, c_0_47])).
% 9.25/9.45  cnf(c_0_92, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_78]), c_0_85])).
% 9.25/9.45  cnf(c_0_93, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_76, c_0_73])).
% 9.25/9.45  cnf(c_0_94, negated_conjecture, (r1_orders_2(esk3_0,k1_yellow_0(esk3_0,X1),esk6_0)|~r1_yellow_0(esk3_0,X1)|~r2_lattice3(esk3_0,X1,esk6_0)|~m1_subset_1(k1_yellow_0(esk3_0,X1),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_18]), c_0_19])])).
% 9.25/9.45  cnf(c_0_95, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))|r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_87, c_0_22])).
% 9.25/9.45  cnf(c_0_96, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,X2,esk6_0)),k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_88, c_0_28])).
% 9.25/9.45  cnf(c_0_97, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))|r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0)), inference(spm,[status(thm)],[c_0_65, c_0_89])).
% 9.25/9.45  cnf(c_0_98, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_92])).
% 9.25/9.45  cnf(c_0_99, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|esk1_3(esk3_0,esk4_0,esk6_0)=k1_yellow_0(esk3_0,X1)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,X1,esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)))|~r1_yellow_0(esk3_0,X1)|~r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_78]), c_0_19])])).
% 9.25/9.45  cnf(c_0_100, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|esk1_3(esk3_0,esk4_0,esk6_0)=k1_yellow_0(esk3_0,X1)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|~r1_yellow_0(esk3_0,X1)|~r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))|~r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_78]), c_0_19])])).
% 9.25/9.45  cnf(c_0_101, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk1_3(esk3_0,X2,esk6_0),u1_struct_0(esk3_0))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_88, c_0_29])).
% 9.25/9.45  cnf(c_0_102, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))|r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0)), inference(spm,[status(thm)],[c_0_65, c_0_93])).
% 9.25/9.45  cnf(c_0_103, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk5_0,esk6_0)|r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)|~r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)|~m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 9.25/9.45  cnf(c_0_104, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 9.25/9.45  cnf(c_0_105, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,X1,esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))|~r2_lattice3(esk3_0,k1_tarski(X1),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_98]), c_0_19])])).
% 9.25/9.45  cnf(c_0_106, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_91]), c_0_92])).
% 9.25/9.45  cnf(c_0_107, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|~r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_91]), c_0_92])).
% 9.25/9.45  cnf(c_0_108, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_101, c_0_102])).
% 9.25/9.45  cnf(c_0_109, plain, (r2_lattice3(X1,X2,X3)|~r1_orders_2(X1,esk1_3(X1,X2,X3),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 9.25/9.45  cnf(c_0_110, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))|~m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_31])).
% 9.25/9.45  cnf(c_0_111, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_78]), c_0_106]), c_0_107])).
% 9.25/9.45  cnf(c_0_112, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))|~m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_108]), c_0_34])).
% 9.25/9.45  cnf(c_0_113, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|~r1_orders_2(esk3_0,esk1_3(esk3_0,X1,esk6_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_18]), c_0_19])])).
% 9.25/9.45  cnf(c_0_114, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk1_3(esk3_0,esk5_0,esk6_0),esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_38])).
% 9.25/9.45  cnf(c_0_115, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk1_3(esk3_0,esk5_0,esk6_0),esk6_0)|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_111]), c_0_41])).
% 9.25/9.45  cnf(c_0_116, plain, (X1=k1_xboole_0|r2_hidden(k1_yellow_0(X3,X1),X4)|~v1_finset_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~epred1_3(X4,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 9.25/9.45  cnf(c_0_117, negated_conjecture, (m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_31, c_0_28])).
% 9.25/9.45  cnf(c_0_118, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_114]), c_0_31])).
% 9.25/9.45  cnf(c_0_119, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_115]), c_0_34])).
% 9.25/9.45  fof(c_0_120, plain, ![X11, X12, X13]:(~r2_hidden(X11,X12)|~m1_subset_1(X12,k1_zfmisc_1(X13))|m1_subset_1(X11,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 9.25/9.45  cnf(c_0_121, plain, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))|r2_hidden(k1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)|~epred1_3(X2,esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_117]), c_0_39])])).
% 9.25/9.45  cnf(c_0_122, plain, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))|~epred1_3(X2,esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_118]), c_0_39])])).
% 9.25/9.45  cnf(c_0_123, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,k1_tarski(X1),esk1_3(esk3_0,esk4_0,esk6_0))|~r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_119]), c_0_19])])).
% 9.25/9.45  cnf(c_0_124, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_119]), c_0_19]), c_0_43])]), c_0_44])).
% 9.25/9.45  cnf(c_0_125, plain, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|r2_hidden(k1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)|~epred1_3(X2,esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_38]), c_0_39])])).
% 9.25/9.45  cnf(c_0_126, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_120])).
% 9.25/9.45  cnf(c_0_127, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 9.25/9.45  cnf(c_0_128, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))|r2_hidden(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0)), inference(spm,[status(thm)],[c_0_121, c_0_47])).
% 9.25/9.45  cnf(c_0_129, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|esk1_3(esk3_0,esk4_0,esk6_0)=k1_yellow_0(esk3_0,X1)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0))|~r1_yellow_0(esk3_0,X1)|~r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_119]), c_0_19])])).
% 9.25/9.45  cnf(c_0_130, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))), inference(spm,[status(thm)],[c_0_122, c_0_47])).
% 9.25/9.45  cnf(c_0_131, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_119]), c_0_124])).
% 9.25/9.45  cnf(c_0_132, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|r2_hidden(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0)), inference(spm,[status(thm)],[c_0_125, c_0_47])).
% 9.25/9.45  cnf(c_0_133, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_126, c_0_127])).
% 9.25/9.45  cnf(c_0_134, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))|r1_tarski(k1_tarski(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))),esk5_0)), inference(spm,[status(thm)],[c_0_21, c_0_128])).
% 9.25/9.45  cnf(c_0_135, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_130]), c_0_131])).
% 9.25/9.45  cnf(c_0_136, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|esk1_3(esk3_0,esk4_0,esk6_0)=k1_yellow_0(esk3_0,X1)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,X1,esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)))|~r1_yellow_0(esk3_0,X1)|~r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_119]), c_0_19])])).
% 9.25/9.45  cnf(c_0_137, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|esk1_3(esk3_0,esk4_0,esk6_0)=k1_yellow_0(esk3_0,X1)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|~r1_yellow_0(esk3_0,X1)|~r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))|~r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_119]), c_0_19])])).
% 9.25/9.45  cnf(c_0_138, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|r1_tarski(k1_tarski(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))),esk5_0)), inference(spm,[status(thm)],[c_0_21, c_0_132])).
% 9.25/9.45  cnf(c_0_139, negated_conjecture, (r1_orders_2(esk3_0,X1,esk6_0)|~r2_lattice3(esk3_0,k1_tarski(X1),esk6_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_18]), c_0_19])])).
% 9.25/9.45  cnf(c_0_140, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),u1_struct_0(esk3_0))|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_133, c_0_128])).
% 9.25/9.45  cnf(c_0_141, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,k1_tarski(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))),esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_96, c_0_134])).
% 9.25/9.45  cnf(c_0_142, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,X1,esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))|~r2_lattice3(esk3_0,k1_tarski(X1),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_135]), c_0_19])])).
% 9.25/9.45  cnf(c_0_143, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_136, c_0_130]), c_0_131])).
% 9.25/9.45  cnf(c_0_144, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|~r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_130]), c_0_131])).
% 9.25/9.45  cnf(c_0_145, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_133, c_0_132])).
% 9.25/9.45  cnf(c_0_146, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,k1_tarski(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))),esk6_0)|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_101, c_0_138])).
% 9.25/9.45  cnf(c_0_147, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_139, c_0_140]), c_0_141])).
% 9.25/9.45  cnf(c_0_148, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_142, c_0_119]), c_0_143]), c_0_144])).
% 9.25/9.45  cnf(c_0_149, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk6_0)|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_139, c_0_145]), c_0_146])).
% 9.25/9.45  cnf(c_0_150, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_147, c_0_148])).
% 9.25/9.45  cnf(c_0_151, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0)|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_149, c_0_148])).
% 9.25/9.45  cnf(c_0_152, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk4_0,esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_113, c_0_150])).
% 9.25/9.45  cnf(c_0_153, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk4_0,esk6_0)|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_113, c_0_151])).
% 9.25/9.45  cnf(c_0_154, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_152]), c_0_28])).
% 9.25/9.45  cnf(c_0_155, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_153]), c_0_29])).
% 9.25/9.45  cnf(c_0_156, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_tarski(k1_tarski(esk1_3(esk3_0,esk5_0,esk6_0)),esk5_0)), inference(spm,[status(thm)],[c_0_65, c_0_154])).
% 9.25/9.45  cnf(c_0_157, plain, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(X1))|~epred1_3(X2,X1,esk3_0)|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2)), inference(spm,[status(thm)],[c_0_67, c_0_155])).
% 9.25/9.45  cnf(c_0_158, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_69, c_0_156])).
% 9.25/9.45  cnf(c_0_159, plain, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)))|~epred1_3(X2,X1,esk3_0)|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2)), inference(spm,[status(thm)],[c_0_74, c_0_155])).
% 9.25/9.45  cnf(c_0_160, negated_conjecture, (r2_lattice3(esk3_0,esk4_0,esk6_0)|r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 9.25/9.45  cnf(c_0_161, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_157, c_0_47]), c_0_158])).
% 9.25/9.45  cnf(c_0_162, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_159, c_0_47]), c_0_158])).
% 9.25/9.45  cnf(c_0_163, negated_conjecture, (r2_lattice3(esk3_0,esk5_0,esk6_0)|r2_lattice3(esk3_0,X1,esk6_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_88, c_0_160])).
% 9.25/9.45  cnf(c_0_164, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0)), inference(spm,[status(thm)],[c_0_65, c_0_161])).
% 9.25/9.45  cnf(c_0_165, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)|~r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)|~m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_94, c_0_162])).
% 9.25/9.45  cnf(c_0_166, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)|r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_163, c_0_164])).
% 9.25/9.45  cnf(c_0_167, plain, (k1_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|~epred1_3(X2,X1,esk3_0)|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2)), inference(spm,[status(thm)],[c_0_62, c_0_155])).
% 9.25/9.45  cnf(c_0_168, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk5_0,esk6_0)|r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)|~m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_165, c_0_166])).
% 9.25/9.45  cnf(c_0_169, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_167, c_0_47]), c_0_158])).
% 9.25/9.45  cnf(c_0_170, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_168, c_0_169]), c_0_29]), c_0_113])).
% 9.25/9.45  cnf(c_0_171, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_31, c_0_170])).
% 9.25/9.45  cnf(c_0_172, plain, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_hidden(k1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)|~epred1_3(X2,esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_171]), c_0_39])])).
% 9.25/9.45  cnf(c_0_173, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_hidden(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0)), inference(spm,[status(thm)],[c_0_172, c_0_47])).
% 9.25/9.45  cnf(c_0_174, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_173, c_0_148])).
% 9.25/9.45  cnf(c_0_175, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_34, c_0_170])).
% 9.25/9.45  cnf(c_0_176, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,X1,esk6_0)|~r1_tarski(X1,esk5_0)), inference(spm,[status(thm)],[c_0_88, c_0_170])).
% 9.25/9.45  cnf(c_0_177, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_tarski(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk5_0)), inference(spm,[status(thm)],[c_0_21, c_0_174])).
% 9.25/9.45  cnf(c_0_178, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0)|~r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0)), inference(spm,[status(thm)],[c_0_139, c_0_175])).
% 9.25/9.45  cnf(c_0_179, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0)), inference(spm,[status(thm)],[c_0_176, c_0_177])).
% 9.25/9.45  cnf(c_0_180, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_178, c_0_179])).
% 9.25/9.45  fof(c_0_181, plain, ![X6]:~v1_xboole_0(k1_tarski(X6)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).
% 9.25/9.45  cnf(c_0_182, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk4_0,esk6_0)), inference(spm,[status(thm)],[c_0_113, c_0_180])).
% 9.25/9.45  cnf(c_0_183, plain, (~v1_xboole_0(k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_181])).
% 9.25/9.45  cnf(c_0_184, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_182]), c_0_170])).
% 9.25/9.45  cnf(c_0_185, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 9.25/9.45  cnf(c_0_186, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_183, c_0_184]), c_0_185])]), ['proof']).
% 9.25/9.45  # SZS output end CNFRefutation
% 9.25/9.45  # Proof object total steps             : 187
% 9.25/9.45  # Proof object clause steps            : 160
% 9.25/9.45  # Proof object formula steps           : 27
% 9.25/9.45  # Proof object conjectures             : 126
% 9.25/9.45  # Proof object clause conjectures      : 123
% 9.25/9.45  # Proof object formula conjectures     : 3
% 9.25/9.45  # Proof object initial clauses used    : 32
% 9.25/9.45  # Proof object initial formulas used   : 12
% 9.25/9.45  # Proof object generating inferences   : 127
% 9.25/9.45  # Proof object simplifying inferences  : 103
% 9.25/9.45  # Training examples: 0 positive, 0 negative
% 9.25/9.45  # Parsed axioms                        : 12
% 9.25/9.45  # Removed by relevancy pruning/SinE    : 0
% 9.25/9.45  # Initial clauses                      : 40
% 9.25/9.45  # Removed in clause preprocessing      : 0
% 9.25/9.45  # Initial clauses in saturation        : 40
% 9.25/9.45  # Processed clauses                    : 14986
% 9.25/9.45  # ...of these trivial                  : 171
% 9.25/9.45  # ...subsumed                          : 6476
% 9.25/9.45  # ...remaining for further processing  : 8339
% 9.25/9.45  # Other redundant clauses eliminated   : 2
% 9.25/9.45  # Clauses deleted for lack of memory   : 0
% 9.25/9.45  # Backward-subsumed                    : 4597
% 9.25/9.45  # Backward-rewritten                   : 2339
% 9.25/9.45  # Generated clauses                    : 120583
% 9.25/9.45  # ...of the previous two non-trivial   : 116906
% 9.25/9.45  # Contextual simplify-reflections      : 733
% 9.25/9.45  # Paramodulations                      : 120581
% 9.25/9.45  # Factorizations                       : 0
% 9.25/9.45  # Equation resolutions                 : 2
% 9.25/9.45  # Propositional unsat checks           : 0
% 9.25/9.45  #    Propositional check models        : 0
% 9.25/9.45  #    Propositional check unsatisfiable : 0
% 9.25/9.45  #    Propositional clauses             : 0
% 9.25/9.45  #    Propositional clauses after purity: 0
% 9.25/9.45  #    Propositional unsat core size     : 0
% 9.25/9.45  #    Propositional preprocessing time  : 0.000
% 9.25/9.45  #    Propositional encoding time       : 0.000
% 9.25/9.45  #    Propositional solver time         : 0.000
% 9.25/9.45  #    Success case prop preproc time    : 0.000
% 9.25/9.45  #    Success case prop encoding time   : 0.000
% 9.25/9.45  #    Success case prop solver time     : 0.000
% 9.25/9.45  # Current number of processed clauses  : 1361
% 9.25/9.45  #    Positive orientable unit clauses  : 82
% 9.25/9.45  #    Positive unorientable unit clauses: 0
% 9.25/9.45  #    Negative unit clauses             : 2
% 9.25/9.45  #    Non-unit-clauses                  : 1277
% 9.25/9.45  # Current number of unprocessed clauses: 99092
% 9.25/9.45  # ...number of literals in the above   : 642279
% 9.25/9.45  # Current number of archived formulas  : 0
% 9.25/9.45  # Current number of archived clauses   : 6976
% 9.25/9.45  # Clause-clause subsumption calls (NU) : 9366874
% 9.25/9.45  # Rec. Clause-clause subsumption calls : 537885
% 9.25/9.45  # Non-unit clause-clause subsumptions  : 11804
% 9.25/9.45  # Unit Clause-clause subsumption calls : 17956
% 9.25/9.45  # Rewrite failures with RHS unbound    : 0
% 9.25/9.45  # BW rewrite match attempts            : 3162
% 9.25/9.45  # BW rewrite match successes           : 24
% 9.25/9.45  # Condensation attempts                : 0
% 9.25/9.45  # Condensation successes               : 0
% 9.25/9.45  # Termbank termtop insertions          : 7911766
% 9.25/9.45  
% 9.25/9.45  # -------------------------------------------------
% 9.25/9.45  # User time                : 9.037 s
% 9.25/9.45  # System time              : 0.077 s
% 9.25/9.45  # Total time               : 9.114 s
% 9.25/9.45  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
