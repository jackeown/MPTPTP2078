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
% DateTime   : Thu Dec  3 11:16:28 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :  147 (27744 expanded)
%              Number of clauses        :  120 (9412 expanded)
%              Number of leaves         :   13 (9034 expanded)
%              Depth                    :   49
%              Number of atoms          :  611 (275657 expanded)
%              Number of equality atoms :  113 (25483 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_waybel_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).

fof(t63_subset_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(dt_k2_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_0)).

fof(fc1_finset_1,axiom,(
    ! [X1] : v1_finset_1(k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_finset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_yellow_0)).

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
    ! [X12,X13,X14,X15] :
      ( ( ~ r1_lattice3(X12,X13,X14)
        | ~ m1_subset_1(X15,u1_struct_0(X12))
        | ~ r2_hidden(X15,X13)
        | r1_orders_2(X12,X14,X15)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ l1_orders_2(X12) )
      & ( m1_subset_1(esk1_3(X12,X13,X14),u1_struct_0(X12))
        | r1_lattice3(X12,X13,X14)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ l1_orders_2(X12) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X13)
        | r1_lattice3(X12,X13,X14)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ l1_orders_2(X12) )
      & ( ~ r1_orders_2(X12,X14,esk1_3(X12,X13,X14))
        | r1_lattice3(X12,X13,X14)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ l1_orders_2(X12) ) ) ),
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
      ( ~ r2_hidden(X7,X8)
      | m1_subset_1(k1_tarski(X7),k1_zfmisc_1(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).

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

cnf(c_0_20,plain,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk6_0)
    | r2_hidden(esk1_3(esk3_0,X1,esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

fof(c_0_22,plain,(
    ! [X22,X23] :
      ( ~ l1_orders_2(X22)
      | m1_subset_1(k2_yellow_0(X22,X23),u1_struct_0(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_yellow_0])])).

fof(c_0_23,plain,(
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

cnf(c_0_24,negated_conjecture,
    ( ~ r1_lattice3(esk3_0,esk4_0,esk6_0)
    | ~ r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,X1,esk6_0)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_27,plain,
    ( m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_28,plain,(
    ! [X39,X40,X41,X42,X43,X45] :
      ( ( ~ v1_finset_1(X42)
        | ~ m1_subset_1(X42,k1_zfmisc_1(X40))
        | X42 = k1_xboole_0
        | r2_yellow_0(X39,X42)
        | ~ epred1_3(X41,X40,X39) )
      & ( v1_finset_1(esk7_4(X39,X40,X41,X43))
        | ~ r2_hidden(X43,X41)
        | ~ m1_subset_1(X43,u1_struct_0(X39))
        | ~ epred1_3(X41,X40,X39) )
      & ( m1_subset_1(esk7_4(X39,X40,X41,X43),k1_zfmisc_1(X40))
        | ~ r2_hidden(X43,X41)
        | ~ m1_subset_1(X43,u1_struct_0(X39))
        | ~ epred1_3(X41,X40,X39) )
      & ( r2_yellow_0(X39,esk7_4(X39,X40,X41,X43))
        | ~ r2_hidden(X43,X41)
        | ~ m1_subset_1(X43,u1_struct_0(X39))
        | ~ epred1_3(X41,X40,X39) )
      & ( X43 = k2_yellow_0(X39,esk7_4(X39,X40,X41,X43))
        | ~ r2_hidden(X43,X41)
        | ~ m1_subset_1(X43,u1_struct_0(X39))
        | ~ epred1_3(X41,X40,X39) )
      & ( ~ v1_finset_1(X45)
        | ~ m1_subset_1(X45,k1_zfmisc_1(X40))
        | X45 = k1_xboole_0
        | r2_hidden(k2_yellow_0(X39,X45),X41)
        | ~ epred1_3(X41,X40,X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])])])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | ~ r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_18]),c_0_19])])).

fof(c_0_31,plain,(
    ! [X11] : v1_finset_1(k1_tarski(X11)) ),
    inference(variable_rename,[status(thm)],[fc1_finset_1])).

cnf(c_0_32,plain,
    ( r1_orders_2(X1,X3,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(k2_yellow_0(esk3_0,X1),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_19])).

cnf(c_0_34,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(k2_yellow_0(X3,X1),X4)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ epred1_3(X4,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,plain,
    ( v1_finset_1(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_37,plain,(
    ! [X24,X25,X26,X27] :
      ( ( ~ r1_lattice3(X24,X27,X26)
        | r1_lattice3(X24,X27,X25)
        | ~ r1_orders_2(X24,X25,X26)
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | ~ v4_orders_2(X24)
        | ~ l1_orders_2(X24) )
      & ( ~ r2_lattice3(X24,X27,X25)
        | r2_lattice3(X24,X27,X26)
        | ~ r1_orders_2(X24,X25,X26)
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | ~ v4_orders_2(X24)
        | ~ l1_orders_2(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_yellow_0])])])])).

cnf(c_0_38,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,k2_yellow_0(esk3_0,X2))
    | ~ r1_lattice3(esk3_0,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(k2_yellow_0(esk3_0,X2),X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_19])])).

cnf(c_0_39,plain,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | r2_hidden(k2_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)
    | ~ epred1_3(X2,esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])])).

cnf(c_0_40,negated_conjecture,
    ( epred1_3(esk5_0,esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_41,plain,(
    ! [X17,X18,X19,X20] :
      ( ( r1_lattice3(X17,X18,X19)
        | X19 != k2_yellow_0(X17,X18)
        | ~ r2_yellow_0(X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ l1_orders_2(X17) )
      & ( ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_lattice3(X17,X18,X20)
        | r1_orders_2(X17,X20,X19)
        | X19 != k2_yellow_0(X17,X18)
        | ~ r2_yellow_0(X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ l1_orders_2(X17) )
      & ( m1_subset_1(esk2_3(X17,X18,X19),u1_struct_0(X17))
        | ~ r1_lattice3(X17,X18,X19)
        | X19 = k2_yellow_0(X17,X18)
        | ~ r2_yellow_0(X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ l1_orders_2(X17) )
      & ( r1_lattice3(X17,X18,esk2_3(X17,X18,X19))
        | ~ r1_lattice3(X17,X18,X19)
        | X19 = k2_yellow_0(X17,X18)
        | ~ r2_yellow_0(X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ l1_orders_2(X17) )
      & ( ~ r1_orders_2(X17,esk2_3(X17,X18,X19),X19)
        | ~ r1_lattice3(X17,X18,X19)
        | X19 = k2_yellow_0(X17,X18)
        | ~ r2_yellow_0(X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ l1_orders_2(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_yellow_0])])])])])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | r2_yellow_0(X3,X1)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ epred1_3(X4,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_43,plain,(
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

cnf(c_0_44,plain,
    ( r1_lattice3(X1,X2,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,X4,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( v4_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_46,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,X1))
    | m1_subset_1(esk1_3(esk3_0,X2,esk6_0),u1_struct_0(esk3_0))
    | ~ r2_hidden(k2_yellow_0(esk3_0,X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_30]),c_0_18])])).

cnf(c_0_47,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | r2_hidden(k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,plain,
    ( r1_lattice3(X1,X2,X3)
    | X3 != k2_yellow_0(X1,X2)
    | ~ r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,plain,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ epred1_3(X2,esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_35]),c_0_36])])).

cnf(c_0_50,plain,
    ( r1_orders_2(X1,X3,X2)
    | ~ r1_lattice3(X1,k1_tarski(X2),X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_30])).

cnf(c_0_52,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk6_0)
    | ~ r1_orders_2(esk3_0,esk6_0,X2)
    | ~ r1_lattice3(esk3_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_18]),c_0_45]),c_0_19])])).

cnf(c_0_53,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_54,plain,
    ( r1_lattice3(X1,X2,k2_yellow_0(X1,X2))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_48]),c_0_27])).

cnf(c_0_55,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_40])).

cnf(c_0_56,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,X1)
    | ~ r1_lattice3(esk3_0,k1_tarski(X1),esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_18]),c_0_19])])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_30])).

cnf(c_0_58,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_lattice3(esk3_0,X1,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_33])])).

cnf(c_0_59,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_19])])).

cnf(c_0_60,plain,
    ( r1_lattice3(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,esk1_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_61,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk6_0)
    | ~ r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,X1,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_18]),c_0_19])])).

cnf(c_0_64,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,esk4_0,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_66,plain,
    ( X1 = k2_yellow_0(X2,esk7_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ epred1_3(X4,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_67,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_65]),c_0_30])).

cnf(c_0_68,plain,
    ( k2_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | ~ epred1_3(X2,X1,esk3_0)
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_69,negated_conjecture,
    ( k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_40])).

cnf(c_0_70,negated_conjecture,
    ( k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_21])).

cnf(c_0_71,negated_conjecture,
    ( k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_70])).

cnf(c_0_72,plain,
    ( m1_subset_1(esk7_4(X1,X2,X3,X4),k1_zfmisc_1(X2))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_73,plain,
    ( k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_hidden(k2_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)
    | ~ epred1_3(X2,esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_71]),c_0_36])])).

cnf(c_0_74,plain,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(X1))
    | ~ epred1_3(X2,X1,esk3_0)
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2) ),
    inference(spm,[status(thm)],[c_0_72,c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,X1))
    | ~ r2_hidden(k2_yellow_0(esk3_0,X1),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_70]),c_0_18])])).

cnf(c_0_76,negated_conjecture,
    ( k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_hidden(k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_40])).

cnf(c_0_77,plain,
    ( k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))
    | ~ epred1_3(X2,esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_71]),c_0_36])])).

cnf(c_0_78,plain,
    ( r2_yellow_0(X1,esk7_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_79,plain,(
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

cnf(c_0_80,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_40])).

cnf(c_0_81,negated_conjecture,
    ( k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_82,negated_conjecture,
    ( k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_77,c_0_40])).

cnf(c_0_83,plain,
    ( r1_orders_2(X2,X1,X4)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | X4 != k2_yellow_0(X2,X3)
    | ~ r2_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_84,plain,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)))
    | ~ epred1_3(X2,X1,esk3_0)
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2) ),
    inference(spm,[status(thm)],[c_0_78,c_0_67])).

cnf(c_0_85,plain,
    ( r1_lattice3(X1,X4,X3)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_tarski(X4,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

fof(c_0_86,plain,(
    ! [X9,X10] :
      ( ( ~ m1_subset_1(X9,k1_zfmisc_1(X10))
        | r1_tarski(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | m1_subset_1(X9,k1_zfmisc_1(X10)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_87,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,esk5_0,esk6_0)
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_21])).

cnf(c_0_88,negated_conjecture,
    ( k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_70])).

cnf(c_0_89,negated_conjecture,
    ( k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,X1,esk6_0)
    | ~ r1_lattice3(esk3_0,X1,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_81]),c_0_33])])).

cnf(c_0_90,negated_conjecture,
    ( k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_82]),c_0_19])])).

cnf(c_0_91,plain,
    ( r1_orders_2(X1,X2,k2_yellow_0(X1,X3))
    | ~ r2_yellow_0(X1,X3)
    | ~ r1_lattice3(X1,X3,X2)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_83]),c_0_27])).

cnf(c_0_92,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_40])).

cnf(c_0_93,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk6_0)
    | ~ r1_lattice3(esk3_0,X2,esk6_0)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_18]),c_0_19])])).

cnf(c_0_94,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_95,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_87])).

cnf(c_0_96,negated_conjecture,
    ( k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_88])).

cnf(c_0_97,negated_conjecture,
    ( k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_98,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,X1))
    | ~ r2_yellow_0(esk3_0,X1)
    | ~ r1_lattice3(esk3_0,X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_18]),c_0_19])])).

cnf(c_0_99,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))
    | r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_92,c_0_21])).

cnf(c_0_100,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,X2,esk6_0)),k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_93,c_0_25])).

cnf(c_0_101,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_102,negated_conjecture,
    ( k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_103,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))))
    | r1_lattice3(esk3_0,esk5_0,esk6_0)
    | ~ r1_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_104,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_105,negated_conjecture,
    ( k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_102])).

cnf(c_0_106,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))))
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_29])).

cnf(c_0_107,negated_conjecture,
    ( k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_105]),c_0_70])).

cnf(c_0_108,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_87])).

cnf(c_0_109,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_110,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,X2,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_93,c_0_30])).

cnf(c_0_111,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_108])).

cnf(c_0_112,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_109]),c_0_29])).

cnf(c_0_113,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_110,c_0_111])).

cnf(c_0_114,plain,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_hidden(k2_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)
    | ~ epred1_3(X2,esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_112]),c_0_36])])).

cnf(c_0_115,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_113]),c_0_51])).

cnf(c_0_116,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,X1))
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | ~ r2_hidden(k2_yellow_0(esk3_0,X1),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_87]),c_0_18])])).

cnf(c_0_117,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_hidden(k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_114,c_0_40])).

cnf(c_0_118,plain,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))
    | ~ epred1_3(X2,esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_112]),c_0_36])])).

cnf(c_0_119,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_115,c_0_107])).

cnf(c_0_120,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_116,c_0_117])).

cnf(c_0_121,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_118,c_0_40])).

cnf(c_0_122,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_119]),c_0_51])).

cnf(c_0_123,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | ~ r1_lattice3(esk3_0,X1,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_120]),c_0_33])])).

cnf(c_0_124,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_121]),c_0_19])])).

cnf(c_0_125,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_122])).

cnf(c_0_126,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0)
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_123,c_0_124])).

cnf(c_0_127,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_125,c_0_126])).

cnf(c_0_128,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,esk4_0,esk6_0)
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_127])).

cnf(c_0_129,negated_conjecture,
    ( r1_lattice3(esk3_0,esk4_0,esk6_0)
    | r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_130,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_128]),c_0_87])).

cnf(c_0_131,negated_conjecture,
    ( r1_lattice3(esk3_0,esk5_0,esk6_0)
    | r1_lattice3(esk3_0,X1,esk6_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_93,c_0_129])).

cnf(c_0_132,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_130])).

cnf(c_0_133,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)
    | r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_131,c_0_132])).

cnf(c_0_134,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))))
    | r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_133])).

cnf(c_0_135,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_107]),c_0_63])).

cnf(c_0_136,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,X1))
    | ~ r2_hidden(k2_yellow_0(esk3_0,X1),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_135]),c_0_18])])).

cnf(c_0_137,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_136,c_0_117])).

cnf(c_0_138,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,X1,esk6_0)
    | ~ r1_lattice3(esk3_0,X1,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_137]),c_0_33])])).

cnf(c_0_139,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_138,c_0_124])).

cnf(c_0_140,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_125,c_0_139])).

fof(c_0_141,plain,(
    ! [X6] : ~ v1_xboole_0(k1_tarski(X6)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

cnf(c_0_142,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_140])).

cnf(c_0_143,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_141])).

cnf(c_0_144,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_142]),c_0_135])).

cnf(c_0_145,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_146,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_144]),c_0_145])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:47:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 3.09/3.26  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 3.09/3.26  # and selection function SelectNewComplexAHP.
% 3.09/3.26  #
% 3.09/3.26  # Preprocessing time       : 0.029 s
% 3.09/3.26  # Presaturation interreduction done
% 3.09/3.26  
% 3.09/3.26  # Proof found!
% 3.09/3.26  # SZS status Theorem
% 3.09/3.26  # SZS output start CNFRefutation
% 3.09/3.26  fof(t57_waybel_0, conjecture, ![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(((![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_yellow_0(X1,X4)))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X3)&![X5]:((v1_finset_1(X5)&m1_subset_1(X5,k1_zfmisc_1(X2)))=>~((r2_yellow_0(X1,X5)&X4=k2_yellow_0(X1,X5))))))))&![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_hidden(k2_yellow_0(X1,X4),X3))))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X4)<=>r1_lattice3(X1,X3,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_waybel_0)).
% 3.09/3.26  fof(d8_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_lattice3)).
% 3.09/3.26  fof(t63_subset_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 3.09/3.26  fof(dt_k2_yellow_0, axiom, ![X1, X2]:(l1_orders_2(X1)=>m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_0)).
% 3.09/3.26  fof(fc1_finset_1, axiom, ![X1]:v1_finset_1(k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_finset_1)).
% 3.09/3.26  fof(t4_yellow_0, axiom, ![X1]:((v4_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_orders_2(X1,X2,X3)=>![X4]:((r1_lattice3(X1,X4,X3)=>r1_lattice3(X1,X4,X2))&(r2_lattice3(X1,X4,X2)=>r2_lattice3(X1,X4,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_0)).
% 3.09/3.26  fof(d10_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_yellow_0(X1,X2)=>(X3=k2_yellow_0(X1,X2)<=>(r1_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X4)=>r1_orders_2(X1,X4,X3)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_yellow_0)).
% 3.09/3.26  fof(t7_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((((r1_lattice3(X1,k1_tarski(X3),X2)=>r1_orders_2(X1,X2,X3))&(r1_orders_2(X1,X2,X3)=>r1_lattice3(X1,k1_tarski(X3),X2)))&(r2_lattice3(X1,k1_tarski(X3),X2)=>r1_orders_2(X1,X3,X2)))&(r1_orders_2(X1,X3,X2)=>r2_lattice3(X1,k1_tarski(X3),X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_yellow_0)).
% 3.09/3.26  fof(t9_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r1_lattice3(X1,X3,X4)=>r1_lattice3(X1,X2,X4))&(r2_lattice3(X1,X3,X4)=>r2_lattice3(X1,X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_yellow_0)).
% 3.09/3.26  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.09/3.26  fof(fc2_xboole_0, axiom, ![X1]:~(v1_xboole_0(k1_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 3.09/3.26  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.09/3.26  fof(c_0_12, plain, ![X1, X2, X3]:(epred1_3(X3,X2,X1)<=>((![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_yellow_0(X1,X4)))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X3)&![X5]:((v1_finset_1(X5)&m1_subset_1(X5,k1_zfmisc_1(X2)))=>~((r2_yellow_0(X1,X5)&X4=k2_yellow_0(X1,X5))))))))&![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_hidden(k2_yellow_0(X1,X4),X3))))), introduced(definition)).
% 3.09/3.26  fof(c_0_13, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(epred1_3(X3,X2,X1)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X4)<=>r1_lattice3(X1,X3,X4)))))))), inference(apply_def,[status(thm)],[inference(assume_negation,[status(cth)],[t57_waybel_0]), c_0_12])).
% 3.09/3.26  fof(c_0_14, plain, ![X12, X13, X14, X15]:((~r1_lattice3(X12,X13,X14)|(~m1_subset_1(X15,u1_struct_0(X12))|(~r2_hidden(X15,X13)|r1_orders_2(X12,X14,X15)))|~m1_subset_1(X14,u1_struct_0(X12))|~l1_orders_2(X12))&((m1_subset_1(esk1_3(X12,X13,X14),u1_struct_0(X12))|r1_lattice3(X12,X13,X14)|~m1_subset_1(X14,u1_struct_0(X12))|~l1_orders_2(X12))&((r2_hidden(esk1_3(X12,X13,X14),X13)|r1_lattice3(X12,X13,X14)|~m1_subset_1(X14,u1_struct_0(X12))|~l1_orders_2(X12))&(~r1_orders_2(X12,X14,esk1_3(X12,X13,X14))|r1_lattice3(X12,X13,X14)|~m1_subset_1(X14,u1_struct_0(X12))|~l1_orders_2(X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).
% 3.09/3.26  fof(c_0_15, negated_conjecture, ((((~v2_struct_0(esk3_0)&v3_orders_2(esk3_0))&v4_orders_2(esk3_0))&l1_orders_2(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(epred1_3(esk5_0,esk4_0,esk3_0)&(m1_subset_1(esk6_0,u1_struct_0(esk3_0))&((~r1_lattice3(esk3_0,esk4_0,esk6_0)|~r1_lattice3(esk3_0,esk5_0,esk6_0))&(r1_lattice3(esk3_0,esk4_0,esk6_0)|r1_lattice3(esk3_0,esk5_0,esk6_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 3.09/3.26  fof(c_0_16, plain, ![X7, X8]:(~r2_hidden(X7,X8)|m1_subset_1(k1_tarski(X7),k1_zfmisc_1(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).
% 3.09/3.26  cnf(c_0_17, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.09/3.26  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 3.09/3.26  cnf(c_0_19, negated_conjecture, (l1_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 3.09/3.26  cnf(c_0_20, plain, (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 3.09/3.26  cnf(c_0_21, negated_conjecture, (r1_lattice3(esk3_0,X1,esk6_0)|r2_hidden(esk1_3(esk3_0,X1,esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])])).
% 3.09/3.26  fof(c_0_22, plain, ![X22, X23]:(~l1_orders_2(X22)|m1_subset_1(k2_yellow_0(X22,X23),u1_struct_0(X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_yellow_0])])).
% 3.09/3.26  fof(c_0_23, plain, ![X1, X2, X3]:(epred1_3(X3,X2,X1)=>((![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_yellow_0(X1,X4)))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X3)&![X5]:((v1_finset_1(X5)&m1_subset_1(X5,k1_zfmisc_1(X2)))=>~((r2_yellow_0(X1,X5)&X4=k2_yellow_0(X1,X5))))))))&![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_hidden(k2_yellow_0(X1,X4),X3))))), inference(split_equiv,[status(thm)],[c_0_12])).
% 3.09/3.26  cnf(c_0_24, negated_conjecture, (~r1_lattice3(esk3_0,esk4_0,esk6_0)|~r1_lattice3(esk3_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 3.09/3.26  cnf(c_0_25, negated_conjecture, (r1_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,X1,esk6_0)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 3.09/3.26  cnf(c_0_26, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.09/3.26  cnf(c_0_27, plain, (m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 3.09/3.26  fof(c_0_28, plain, ![X39, X40, X41, X42, X43, X45]:(((~v1_finset_1(X42)|~m1_subset_1(X42,k1_zfmisc_1(X40))|(X42=k1_xboole_0|r2_yellow_0(X39,X42))|~epred1_3(X41,X40,X39))&(((v1_finset_1(esk7_4(X39,X40,X41,X43))|~r2_hidden(X43,X41)|~m1_subset_1(X43,u1_struct_0(X39))|~epred1_3(X41,X40,X39))&(m1_subset_1(esk7_4(X39,X40,X41,X43),k1_zfmisc_1(X40))|~r2_hidden(X43,X41)|~m1_subset_1(X43,u1_struct_0(X39))|~epred1_3(X41,X40,X39)))&((r2_yellow_0(X39,esk7_4(X39,X40,X41,X43))|~r2_hidden(X43,X41)|~m1_subset_1(X43,u1_struct_0(X39))|~epred1_3(X41,X40,X39))&(X43=k2_yellow_0(X39,esk7_4(X39,X40,X41,X43))|~r2_hidden(X43,X41)|~m1_subset_1(X43,u1_struct_0(X39))|~epred1_3(X41,X40,X39)))))&(~v1_finset_1(X45)|~m1_subset_1(X45,k1_zfmisc_1(X40))|(X45=k1_xboole_0|r2_hidden(k2_yellow_0(X39,X45),X41))|~epred1_3(X41,X40,X39))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])])])).
% 3.09/3.26  cnf(c_0_29, negated_conjecture, (m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))|~r1_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 3.09/3.26  cnf(c_0_30, negated_conjecture, (r1_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk1_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_18]), c_0_19])])).
% 3.09/3.26  fof(c_0_31, plain, ![X11]:v1_finset_1(k1_tarski(X11)), inference(variable_rename,[status(thm)],[fc1_finset_1])).
% 3.09/3.26  cnf(c_0_32, plain, (r1_orders_2(X1,X3,X4)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.09/3.26  cnf(c_0_33, negated_conjecture, (m1_subset_1(k2_yellow_0(esk3_0,X1),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_27, c_0_19])).
% 3.09/3.26  cnf(c_0_34, plain, (X1=k1_xboole_0|r2_hidden(k2_yellow_0(X3,X1),X4)|~v1_finset_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~epred1_3(X4,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 3.09/3.26  cnf(c_0_35, negated_conjecture, (m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 3.09/3.26  cnf(c_0_36, plain, (v1_finset_1(k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 3.09/3.26  fof(c_0_37, plain, ![X24, X25, X26, X27]:((~r1_lattice3(X24,X27,X26)|r1_lattice3(X24,X27,X25)|~r1_orders_2(X24,X25,X26)|~m1_subset_1(X26,u1_struct_0(X24))|~m1_subset_1(X25,u1_struct_0(X24))|(~v4_orders_2(X24)|~l1_orders_2(X24)))&(~r2_lattice3(X24,X27,X25)|r2_lattice3(X24,X27,X26)|~r1_orders_2(X24,X25,X26)|~m1_subset_1(X26,u1_struct_0(X24))|~m1_subset_1(X25,u1_struct_0(X24))|(~v4_orders_2(X24)|~l1_orders_2(X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_yellow_0])])])])).
% 3.09/3.26  cnf(c_0_38, negated_conjecture, (r1_orders_2(esk3_0,X1,k2_yellow_0(esk3_0,X2))|~r1_lattice3(esk3_0,X3,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(k2_yellow_0(esk3_0,X2),X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_19])])).
% 3.09/3.26  cnf(c_0_39, plain, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|r2_hidden(k2_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)|~epred1_3(X2,esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])])).
% 3.09/3.26  cnf(c_0_40, negated_conjecture, (epred1_3(esk5_0,esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 3.09/3.26  fof(c_0_41, plain, ![X17, X18, X19, X20]:(((r1_lattice3(X17,X18,X19)|X19!=k2_yellow_0(X17,X18)|~r2_yellow_0(X17,X18)|~m1_subset_1(X19,u1_struct_0(X17))|~l1_orders_2(X17))&(~m1_subset_1(X20,u1_struct_0(X17))|(~r1_lattice3(X17,X18,X20)|r1_orders_2(X17,X20,X19))|X19!=k2_yellow_0(X17,X18)|~r2_yellow_0(X17,X18)|~m1_subset_1(X19,u1_struct_0(X17))|~l1_orders_2(X17)))&((m1_subset_1(esk2_3(X17,X18,X19),u1_struct_0(X17))|~r1_lattice3(X17,X18,X19)|X19=k2_yellow_0(X17,X18)|~r2_yellow_0(X17,X18)|~m1_subset_1(X19,u1_struct_0(X17))|~l1_orders_2(X17))&((r1_lattice3(X17,X18,esk2_3(X17,X18,X19))|~r1_lattice3(X17,X18,X19)|X19=k2_yellow_0(X17,X18)|~r2_yellow_0(X17,X18)|~m1_subset_1(X19,u1_struct_0(X17))|~l1_orders_2(X17))&(~r1_orders_2(X17,esk2_3(X17,X18,X19),X19)|~r1_lattice3(X17,X18,X19)|X19=k2_yellow_0(X17,X18)|~r2_yellow_0(X17,X18)|~m1_subset_1(X19,u1_struct_0(X17))|~l1_orders_2(X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_yellow_0])])])])])).
% 3.09/3.26  cnf(c_0_42, plain, (X1=k1_xboole_0|r2_yellow_0(X3,X1)|~v1_finset_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~epred1_3(X4,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 3.09/3.26  fof(c_0_43, plain, ![X28, X29, X30]:((((~r1_lattice3(X28,k1_tarski(X30),X29)|r1_orders_2(X28,X29,X30)|~m1_subset_1(X30,u1_struct_0(X28))|~m1_subset_1(X29,u1_struct_0(X28))|~l1_orders_2(X28))&(~r1_orders_2(X28,X29,X30)|r1_lattice3(X28,k1_tarski(X30),X29)|~m1_subset_1(X30,u1_struct_0(X28))|~m1_subset_1(X29,u1_struct_0(X28))|~l1_orders_2(X28)))&(~r2_lattice3(X28,k1_tarski(X30),X29)|r1_orders_2(X28,X30,X29)|~m1_subset_1(X30,u1_struct_0(X28))|~m1_subset_1(X29,u1_struct_0(X28))|~l1_orders_2(X28)))&(~r1_orders_2(X28,X30,X29)|r2_lattice3(X28,k1_tarski(X30),X29)|~m1_subset_1(X30,u1_struct_0(X28))|~m1_subset_1(X29,u1_struct_0(X28))|~l1_orders_2(X28))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_yellow_0])])])])).
% 3.09/3.26  cnf(c_0_44, plain, (r1_lattice3(X1,X2,X4)|~r1_lattice3(X1,X2,X3)|~r1_orders_2(X1,X4,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~v4_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 3.09/3.26  cnf(c_0_45, negated_conjecture, (v4_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 3.09/3.26  cnf(c_0_46, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,X1))|m1_subset_1(esk1_3(esk3_0,X2,esk6_0),u1_struct_0(esk3_0))|~r2_hidden(k2_yellow_0(esk3_0,X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_30]), c_0_18])])).
% 3.09/3.26  cnf(c_0_47, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|r2_hidden(k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 3.09/3.26  cnf(c_0_48, plain, (r1_lattice3(X1,X2,X3)|X3!=k2_yellow_0(X1,X2)|~r2_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 3.09/3.26  cnf(c_0_49, plain, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~epred1_3(X2,esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_35]), c_0_36])])).
% 3.09/3.26  cnf(c_0_50, plain, (r1_orders_2(X1,X3,X2)|~r1_lattice3(X1,k1_tarski(X2),X3)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 3.09/3.26  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))|~r1_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_24, c_0_30])).
% 3.09/3.26  cnf(c_0_52, negated_conjecture, (r1_lattice3(esk3_0,X1,esk6_0)|~r1_orders_2(esk3_0,esk6_0,X2)|~r1_lattice3(esk3_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_18]), c_0_45]), c_0_19])])).
% 3.09/3.26  cnf(c_0_53, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 3.09/3.26  cnf(c_0_54, plain, (r1_lattice3(X1,X2,k2_yellow_0(X1,X2))|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_48]), c_0_27])).
% 3.09/3.26  cnf(c_0_55, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_49, c_0_40])).
% 3.09/3.26  cnf(c_0_56, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,X1)|~r1_lattice3(esk3_0,k1_tarski(X1),esk6_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_18]), c_0_19])])).
% 3.09/3.26  cnf(c_0_57, negated_conjecture, (m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_51, c_0_30])).
% 3.09/3.26  cnf(c_0_58, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r1_lattice3(esk3_0,X1,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_33])])).
% 3.09/3.26  cnf(c_0_59, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_19])])).
% 3.09/3.26  cnf(c_0_60, plain, (r1_lattice3(X1,X3,X2)|~r1_orders_2(X1,X2,esk1_3(X1,X3,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.09/3.26  cnf(c_0_61, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 3.09/3.26  cnf(c_0_62, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0)|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 3.09/3.26  cnf(c_0_63, negated_conjecture, (r1_lattice3(esk3_0,X1,esk6_0)|~r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,X1,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_18]), c_0_19])])).
% 3.09/3.26  cnf(c_0_64, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 3.09/3.26  cnf(c_0_65, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,esk4_0,esk6_0)|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 3.09/3.26  cnf(c_0_66, plain, (X1=k2_yellow_0(X2,esk7_4(X2,X3,X4,X1))|~r2_hidden(X1,X4)|~m1_subset_1(X1,u1_struct_0(X2))|~epred1_3(X4,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 3.09/3.26  cnf(c_0_67, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_65]), c_0_30])).
% 3.09/3.26  cnf(c_0_68, plain, (k2_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|~epred1_3(X2,X1,esk3_0)|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 3.09/3.26  cnf(c_0_69, negated_conjecture, (k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_68, c_0_40])).
% 3.09/3.26  cnf(c_0_70, negated_conjecture, (k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_69, c_0_21])).
% 3.09/3.26  cnf(c_0_71, negated_conjecture, (k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_29, c_0_70])).
% 3.09/3.26  cnf(c_0_72, plain, (m1_subset_1(esk7_4(X1,X2,X3,X4),k1_zfmisc_1(X2))|~r2_hidden(X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~epred1_3(X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 3.09/3.26  cnf(c_0_73, plain, (k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_hidden(k2_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)|~epred1_3(X2,esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_71]), c_0_36])])).
% 3.09/3.26  cnf(c_0_74, plain, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(X1))|~epred1_3(X2,X1,esk3_0)|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2)), inference(spm,[status(thm)],[c_0_72, c_0_67])).
% 3.09/3.26  cnf(c_0_75, negated_conjecture, (k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,X1))|~r2_hidden(k2_yellow_0(esk3_0,X1),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_70]), c_0_18])])).
% 3.09/3.26  cnf(c_0_76, negated_conjecture, (k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_hidden(k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0)), inference(spm,[status(thm)],[c_0_73, c_0_40])).
% 3.09/3.26  cnf(c_0_77, plain, (k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))|~epred1_3(X2,esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_71]), c_0_36])])).
% 3.09/3.26  cnf(c_0_78, plain, (r2_yellow_0(X1,esk7_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~epred1_3(X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 3.09/3.26  fof(c_0_79, plain, ![X31, X32, X33, X34]:((~r1_lattice3(X31,X33,X34)|r1_lattice3(X31,X32,X34)|~m1_subset_1(X34,u1_struct_0(X31))|~r1_tarski(X32,X33)|~l1_orders_2(X31))&(~r2_lattice3(X31,X33,X34)|r2_lattice3(X31,X32,X34)|~m1_subset_1(X34,u1_struct_0(X31))|~r1_tarski(X32,X33)|~l1_orders_2(X31))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_yellow_0])])])])).
% 3.09/3.26  cnf(c_0_80, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_74, c_0_40])).
% 3.09/3.26  cnf(c_0_81, negated_conjecture, (k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 3.09/3.26  cnf(c_0_82, negated_conjecture, (k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))), inference(spm,[status(thm)],[c_0_77, c_0_40])).
% 3.09/3.26  cnf(c_0_83, plain, (r1_orders_2(X2,X1,X4)|~m1_subset_1(X1,u1_struct_0(X2))|~r1_lattice3(X2,X3,X1)|X4!=k2_yellow_0(X2,X3)|~r2_yellow_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 3.09/3.26  cnf(c_0_84, plain, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)))|~epred1_3(X2,X1,esk3_0)|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2)), inference(spm,[status(thm)],[c_0_78, c_0_67])).
% 3.09/3.26  cnf(c_0_85, plain, (r1_lattice3(X1,X4,X3)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~r1_tarski(X4,X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 3.09/3.26  fof(c_0_86, plain, ![X9, X10]:((~m1_subset_1(X9,k1_zfmisc_1(X10))|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|m1_subset_1(X9,k1_zfmisc_1(X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 3.09/3.26  cnf(c_0_87, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,esk5_0,esk6_0)|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_80, c_0_21])).
% 3.09/3.26  cnf(c_0_88, negated_conjecture, (k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_51, c_0_70])).
% 3.09/3.26  cnf(c_0_89, negated_conjecture, (k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,X1,esk6_0)|~r1_lattice3(esk3_0,X1,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_81]), c_0_33])])).
% 3.09/3.26  cnf(c_0_90, negated_conjecture, (k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_82]), c_0_19])])).
% 3.09/3.26  cnf(c_0_91, plain, (r1_orders_2(X1,X2,k2_yellow_0(X1,X3))|~r2_yellow_0(X1,X3)|~r1_lattice3(X1,X3,X2)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_83]), c_0_27])).
% 3.09/3.26  cnf(c_0_92, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_84, c_0_40])).
% 3.09/3.26  cnf(c_0_93, negated_conjecture, (r1_lattice3(esk3_0,X1,esk6_0)|~r1_lattice3(esk3_0,X2,esk6_0)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_18]), c_0_19])])).
% 3.09/3.26  cnf(c_0_94, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_86])).
% 3.09/3.26  cnf(c_0_95, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_29, c_0_87])).
% 3.09/3.26  cnf(c_0_96, negated_conjecture, (k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))|~r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0)), inference(spm,[status(thm)],[c_0_56, c_0_88])).
% 3.09/3.26  cnf(c_0_97, negated_conjecture, (k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0)), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 3.09/3.26  cnf(c_0_98, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,X1))|~r2_yellow_0(esk3_0,X1)|~r1_lattice3(esk3_0,X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_18]), c_0_19])])).
% 3.09/3.26  cnf(c_0_99, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))|r1_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_92, c_0_21])).
% 3.09/3.26  cnf(c_0_100, negated_conjecture, (r1_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,X2,esk6_0)),k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_93, c_0_25])).
% 3.09/3.26  cnf(c_0_101, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 3.09/3.26  cnf(c_0_102, negated_conjecture, (k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 3.09/3.26  cnf(c_0_103, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))))|r1_lattice3(esk3_0,esk5_0,esk6_0)|~r1_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)), inference(spm,[status(thm)],[c_0_98, c_0_99])).
% 3.09/3.26  cnf(c_0_104, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_100, c_0_101])).
% 3.09/3.26  cnf(c_0_105, negated_conjecture, (k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,esk4_0,esk6_0)), inference(spm,[status(thm)],[c_0_63, c_0_102])).
% 3.09/3.26  cnf(c_0_106, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))))|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_29])).
% 3.09/3.26  cnf(c_0_107, negated_conjecture, (k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_105]), c_0_70])).
% 3.09/3.26  cnf(c_0_108, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_51, c_0_87])).
% 3.09/3.26  cnf(c_0_109, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_106, c_0_107])).
% 3.09/3.26  cnf(c_0_110, negated_conjecture, (r1_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk1_3(esk3_0,X2,esk6_0),u1_struct_0(esk3_0))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_93, c_0_30])).
% 3.09/3.26  cnf(c_0_111, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0)|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_94, c_0_108])).
% 3.09/3.26  cnf(c_0_112, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_109]), c_0_29])).
% 3.09/3.26  cnf(c_0_113, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_110, c_0_111])).
% 3.09/3.26  cnf(c_0_114, plain, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_hidden(k2_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)|~epred1_3(X2,esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_112]), c_0_36])])).
% 3.09/3.26  cnf(c_0_115, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_113]), c_0_51])).
% 3.09/3.26  cnf(c_0_116, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,X1))|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))|~r2_hidden(k2_yellow_0(esk3_0,X1),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_87]), c_0_18])])).
% 3.09/3.26  cnf(c_0_117, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_hidden(k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0)), inference(spm,[status(thm)],[c_0_114, c_0_40])).
% 3.09/3.26  cnf(c_0_118, plain, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))|~epred1_3(X2,esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_112]), c_0_36])])).
% 3.09/3.26  cnf(c_0_119, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_115, c_0_107])).
% 3.09/3.26  cnf(c_0_120, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_116, c_0_117])).
% 3.09/3.26  cnf(c_0_121, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))), inference(spm,[status(thm)],[c_0_118, c_0_40])).
% 3.09/3.26  cnf(c_0_122, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_119]), c_0_51])).
% 3.09/3.26  cnf(c_0_123, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))|~r1_lattice3(esk3_0,X1,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_120]), c_0_33])])).
% 3.09/3.26  cnf(c_0_124, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_121]), c_0_19])])).
% 3.09/3.26  cnf(c_0_125, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))|~r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0)), inference(spm,[status(thm)],[c_0_56, c_0_122])).
% 3.09/3.26  cnf(c_0_126, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0)|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_123, c_0_124])).
% 3.09/3.26  cnf(c_0_127, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_125, c_0_126])).
% 3.09/3.26  cnf(c_0_128, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,esk4_0,esk6_0)|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_63, c_0_127])).
% 3.09/3.26  cnf(c_0_129, negated_conjecture, (r1_lattice3(esk3_0,esk4_0,esk6_0)|r1_lattice3(esk3_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 3.09/3.26  cnf(c_0_130, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_128]), c_0_87])).
% 3.09/3.26  cnf(c_0_131, negated_conjecture, (r1_lattice3(esk3_0,esk5_0,esk6_0)|r1_lattice3(esk3_0,X1,esk6_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_93, c_0_129])).
% 3.09/3.26  cnf(c_0_132, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0)), inference(spm,[status(thm)],[c_0_94, c_0_130])).
% 3.09/3.26  cnf(c_0_133, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)|r1_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_131, c_0_132])).
% 3.09/3.26  cnf(c_0_134, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))))|r1_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_103, c_0_133])).
% 3.09/3.26  cnf(c_0_135, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,esk5_0,esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_107]), c_0_63])).
% 3.09/3.26  cnf(c_0_136, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,X1))|~r2_hidden(k2_yellow_0(esk3_0,X1),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_135]), c_0_18])])).
% 3.09/3.26  cnf(c_0_137, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))), inference(spm,[status(thm)],[c_0_136, c_0_117])).
% 3.09/3.26  cnf(c_0_138, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,X1,esk6_0)|~r1_lattice3(esk3_0,X1,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_137]), c_0_33])])).
% 3.09/3.26  cnf(c_0_139, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0)), inference(spm,[status(thm)],[c_0_138, c_0_124])).
% 3.09/3.26  cnf(c_0_140, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_125, c_0_139])).
% 3.09/3.26  fof(c_0_141, plain, ![X6]:~v1_xboole_0(k1_tarski(X6)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).
% 3.09/3.26  cnf(c_0_142, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,esk4_0,esk6_0)), inference(spm,[status(thm)],[c_0_63, c_0_140])).
% 3.09/3.26  cnf(c_0_143, plain, (~v1_xboole_0(k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_141])).
% 3.09/3.26  cnf(c_0_144, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_142]), c_0_135])).
% 3.09/3.26  cnf(c_0_145, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 3.09/3.26  cnf(c_0_146, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_144]), c_0_145])]), ['proof']).
% 3.09/3.26  # SZS output end CNFRefutation
% 3.09/3.26  # Proof object total steps             : 147
% 3.09/3.26  # Proof object clause steps            : 120
% 3.09/3.26  # Proof object formula steps           : 27
% 3.09/3.26  # Proof object conjectures             : 92
% 3.09/3.26  # Proof object clause conjectures      : 89
% 3.09/3.26  # Proof object formula conjectures     : 3
% 3.09/3.26  # Proof object initial clauses used    : 26
% 3.09/3.26  # Proof object initial formulas used   : 12
% 3.09/3.26  # Proof object generating inferences   : 92
% 3.09/3.26  # Proof object simplifying inferences  : 66
% 3.09/3.26  # Training examples: 0 positive, 0 negative
% 3.09/3.26  # Parsed axioms                        : 12
% 3.09/3.26  # Removed by relevancy pruning/SinE    : 0
% 3.09/3.26  # Initial clauses                      : 40
% 3.09/3.26  # Removed in clause preprocessing      : 0
% 3.09/3.26  # Initial clauses in saturation        : 40
% 3.09/3.26  # Processed clauses                    : 4831
% 3.09/3.26  # ...of these trivial                  : 2
% 3.09/3.26  # ...subsumed                          : 1499
% 3.09/3.26  # ...remaining for further processing  : 3330
% 3.09/3.26  # Other redundant clauses eliminated   : 2
% 3.09/3.26  # Clauses deleted for lack of memory   : 0
% 3.09/3.26  # Backward-subsumed                    : 915
% 3.09/3.26  # Backward-rewritten                   : 921
% 3.09/3.26  # Generated clauses                    : 41965
% 3.09/3.26  # ...of the previous two non-trivial   : 41441
% 3.09/3.26  # Contextual simplify-reflections      : 173
% 3.09/3.26  # Paramodulations                      : 41955
% 3.09/3.26  # Factorizations                       : 8
% 3.09/3.26  # Equation resolutions                 : 2
% 3.09/3.26  # Propositional unsat checks           : 0
% 3.09/3.26  #    Propositional check models        : 0
% 3.09/3.26  #    Propositional check unsatisfiable : 0
% 3.09/3.26  #    Propositional clauses             : 0
% 3.09/3.26  #    Propositional clauses after purity: 0
% 3.09/3.26  #    Propositional unsat core size     : 0
% 3.09/3.26  #    Propositional preprocessing time  : 0.000
% 3.09/3.26  #    Propositional encoding time       : 0.000
% 3.09/3.26  #    Propositional solver time         : 0.000
% 3.09/3.26  #    Success case prop preproc time    : 0.000
% 3.09/3.26  #    Success case prop encoding time   : 0.000
% 3.09/3.26  #    Success case prop solver time     : 0.000
% 3.09/3.26  # Current number of processed clauses  : 1452
% 3.09/3.26  #    Positive orientable unit clauses  : 21
% 3.09/3.26  #    Positive unorientable unit clauses: 0
% 3.09/3.26  #    Negative unit clauses             : 2
% 3.09/3.26  #    Non-unit-clauses                  : 1429
% 3.09/3.26  # Current number of unprocessed clauses: 35640
% 3.09/3.26  # ...number of literals in the above   : 183208
% 3.09/3.26  # Current number of archived formulas  : 0
% 3.09/3.26  # Current number of archived clauses   : 1876
% 3.09/3.26  # Clause-clause subsumption calls (NU) : 1236611
% 3.09/3.26  # Rec. Clause-clause subsumption calls : 270255
% 3.09/3.26  # Non-unit clause-clause subsumptions  : 2587
% 3.09/3.26  # Unit Clause-clause subsumption calls : 1320
% 3.09/3.26  # Rewrite failures with RHS unbound    : 0
% 3.09/3.26  # BW rewrite match attempts            : 63
% 3.09/3.26  # BW rewrite match successes           : 7
% 3.09/3.26  # Condensation attempts                : 0
% 3.09/3.26  # Condensation successes               : 0
% 3.09/3.26  # Termbank termtop insertions          : 1786331
% 3.09/3.27  
% 3.09/3.27  # -------------------------------------------------
% 3.09/3.27  # User time                : 2.877 s
% 3.09/3.27  # System time              : 0.045 s
% 3.09/3.27  # Total time               : 2.922 s
% 3.09/3.27  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
