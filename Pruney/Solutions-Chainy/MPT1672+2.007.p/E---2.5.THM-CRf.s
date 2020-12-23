%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:27 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :  190 (14859974 expanded)
%              Number of clauses        :  165 (4835679 expanded)
%              Number of leaves         :   12 (4973595 expanded)
%              Depth                    :   61
%              Number of atoms          :  823 (154563820 expanded)
%              Number of equality atoms :  234 (13680619 expanded)
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

fof(t24_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r1_orders_2(X1,X2,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_orders_2)).

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

fof(c_0_11,plain,(
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

fof(c_0_12,negated_conjecture,(
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
    inference(apply_def,[status(thm)],[inference(assume_negation,[status(cth)],[t52_waybel_0]),c_0_11])).

fof(c_0_13,plain,(
    ! [X14,X15,X16,X17] :
      ( ( ~ r2_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X17,u1_struct_0(X14))
        | ~ r2_hidden(X17,X15)
        | r1_orders_2(X14,X17,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) )
      & ( m1_subset_1(esk1_3(X14,X15,X16),u1_struct_0(X14))
        | r2_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) )
      & ( r2_hidden(esk1_3(X14,X15,X16),X15)
        | r2_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) )
      & ( ~ r1_orders_2(X14,esk1_3(X14,X15,X16),X16)
        | r2_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

fof(c_0_14,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

fof(c_0_15,plain,(
    ! [X7,X8] :
      ( ~ r2_hidden(X7,X8)
      | m1_subset_1(k1_tarski(X7),k1_zfmisc_1(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).

cnf(c_0_16,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | r2_hidden(esk1_3(esk3_0,X1,esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])])).

cnf(c_0_21,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_22,plain,(
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
    inference(split_equiv,[status(thm)],[c_0_11])).

cnf(c_0_23,negated_conjecture,
    ( ~ r2_lattice3(esk3_0,esk4_0,esk6_0)
    | ~ r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,X1,esk6_0)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_17]),c_0_18])])).

fof(c_0_26,plain,(
    ! [X35,X36,X37,X38,X39,X41] :
      ( ( ~ v1_finset_1(X38)
        | ~ m1_subset_1(X38,k1_zfmisc_1(X36))
        | X38 = k1_xboole_0
        | r1_yellow_0(X35,X38)
        | ~ epred1_3(X37,X36,X35) )
      & ( v1_finset_1(esk7_4(X35,X36,X37,X39))
        | ~ r2_hidden(X39,X37)
        | ~ m1_subset_1(X39,u1_struct_0(X35))
        | ~ epred1_3(X37,X36,X35) )
      & ( m1_subset_1(esk7_4(X35,X36,X37,X39),k1_zfmisc_1(X36))
        | ~ r2_hidden(X39,X37)
        | ~ m1_subset_1(X39,u1_struct_0(X35))
        | ~ epred1_3(X37,X36,X35) )
      & ( r1_yellow_0(X35,esk7_4(X35,X36,X37,X39))
        | ~ r2_hidden(X39,X37)
        | ~ m1_subset_1(X39,u1_struct_0(X35))
        | ~ epred1_3(X37,X36,X35) )
      & ( X39 = k1_yellow_0(X35,esk7_4(X35,X36,X37,X39))
        | ~ r2_hidden(X39,X37)
        | ~ m1_subset_1(X39,u1_struct_0(X35))
        | ~ epred1_3(X37,X36,X35) )
      & ( ~ v1_finset_1(X41)
        | ~ m1_subset_1(X41,k1_zfmisc_1(X36))
        | X41 = k1_xboole_0
        | r2_hidden(k1_yellow_0(X35,X41),X37)
        | ~ epred1_3(X37,X36,X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])])])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | ~ r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_28,plain,(
    ! [X11] : v1_finset_1(k1_tarski(X11)) ),
    inference(variable_rename,[status(thm)],[fc1_finset_1])).

fof(c_0_29,plain,(
    ! [X24,X25,X26] :
      ( ( ~ r1_lattice3(X24,k1_tarski(X26),X25)
        | r1_orders_2(X24,X25,X26)
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | ~ l1_orders_2(X24) )
      & ( ~ r1_orders_2(X24,X25,X26)
        | r1_lattice3(X24,k1_tarski(X26),X25)
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | ~ l1_orders_2(X24) )
      & ( ~ r2_lattice3(X24,k1_tarski(X26),X25)
        | r1_orders_2(X24,X26,X25)
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | ~ l1_orders_2(X24) )
      & ( ~ r1_orders_2(X24,X26,X25)
        | r2_lattice3(X24,k1_tarski(X26),X25)
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | ~ l1_orders_2(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_yellow_0])])])])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_25])).

fof(c_0_31,plain,(
    ! [X12,X13] :
      ( v2_struct_0(X12)
      | ~ v3_orders_2(X12)
      | ~ l1_orders_2(X12)
      | ~ m1_subset_1(X13,u1_struct_0(X12))
      | r1_orders_2(X12,X13,X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_orders_2])])])])).

fof(c_0_32,plain,(
    ! [X19,X20,X21,X22] :
      ( ( r2_lattice3(X19,X20,X21)
        | X21 != k1_yellow_0(X19,X20)
        | ~ r1_yellow_0(X19,X20)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ l1_orders_2(X19) )
      & ( ~ m1_subset_1(X22,u1_struct_0(X19))
        | ~ r2_lattice3(X19,X20,X22)
        | r1_orders_2(X19,X21,X22)
        | X21 != k1_yellow_0(X19,X20)
        | ~ r1_yellow_0(X19,X20)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ l1_orders_2(X19) )
      & ( m1_subset_1(esk2_3(X19,X20,X21),u1_struct_0(X19))
        | ~ r2_lattice3(X19,X20,X21)
        | X21 = k1_yellow_0(X19,X20)
        | ~ r1_yellow_0(X19,X20)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ l1_orders_2(X19) )
      & ( r2_lattice3(X19,X20,esk2_3(X19,X20,X21))
        | ~ r2_lattice3(X19,X20,X21)
        | X21 = k1_yellow_0(X19,X20)
        | ~ r1_yellow_0(X19,X20)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ l1_orders_2(X19) )
      & ( ~ r1_orders_2(X19,X21,esk2_3(X19,X20,X21))
        | ~ r2_lattice3(X19,X20,X21)
        | X21 = k1_yellow_0(X19,X20)
        | ~ r1_yellow_0(X19,X20)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ l1_orders_2(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).

cnf(c_0_33,plain,
    ( X1 = k1_xboole_0
    | r1_yellow_0(X3,X1)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ epred1_3(X4,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_25])).

cnf(c_0_35,plain,
    ( v1_finset_1(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( r2_lattice3(X1,k1_tarski(X2),X3)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_25])).

cnf(c_0_38,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( v3_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_40,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_41,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | X3 = k1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ epred1_3(X2,esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

cnf(c_0_43,negated_conjecture,
    ( epred1_3(esk5_0,esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_44,negated_conjecture,
    ( r2_lattice3(esk3_0,k1_tarski(X1),esk1_3(esk3_0,esk4_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_18])])).

cnf(c_0_45,negated_conjecture,
    ( r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_37]),c_0_18]),c_0_39])]),c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( esk1_3(esk3_0,esk4_0,esk6_0) = k1_yellow_0(esk3_0,X1)
    | m1_subset_1(esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_yellow_0(esk3_0,X1)
    | ~ r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_37]),c_0_18])])).

cnf(c_0_47,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_37]),c_0_45])).

cnf(c_0_49,plain,
    ( r2_lattice3(X1,X2,esk2_3(X1,X2,X3))
    | X3 = k1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_50,plain,
    ( X2 = k1_yellow_0(X1,X3)
    | ~ r1_orders_2(X1,X2,esk2_3(X1,X3,X2))
    | ~ r2_lattice3(X1,X3,X2)
    | ~ r1_yellow_0(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_51,plain,
    ( r1_orders_2(X1,X2,X3)
    | ~ r2_lattice3(X1,k1_tarski(X2),X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_52,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( esk1_3(esk3_0,esk4_0,esk6_0) = k1_yellow_0(esk3_0,X1)
    | r2_lattice3(esk3_0,X1,esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_yellow_0(esk3_0,X1)
    | ~ r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_37]),c_0_18])])).

cnf(c_0_54,negated_conjecture,
    ( esk1_3(esk3_0,esk4_0,esk6_0) = k1_yellow_0(esk3_0,X1)
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_yellow_0(esk3_0,X1)
    | ~ r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_37]),c_0_18])])).

cnf(c_0_55,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,X1,esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r2_lattice3(esk3_0,k1_tarski(X1),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_18])])).

cnf(c_0_56,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_47]),c_0_48])).

cnf(c_0_57,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_47]),c_0_48])).

cnf(c_0_58,plain,
    ( X1 = k1_yellow_0(X2,esk7_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ epred1_3(X4,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_59,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_37]),c_0_56]),c_0_57])).

cnf(c_0_60,plain,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | ~ epred1_3(X2,X1,esk3_0)
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_61,plain,
    ( m1_subset_1(esk7_4(X1,X2,X3,X4),k1_zfmisc_1(X2))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_62,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_43])).

cnf(c_0_63,plain,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(X1))
    | ~ epred1_3(X2,X1,esk3_0)
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2) ),
    inference(spm,[status(thm)],[c_0_61,c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_20])).

cnf(c_0_65,plain,
    ( r1_yellow_0(X1,esk7_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_66,plain,(
    ! [X27,X28,X29,X30] :
      ( ( ~ r1_lattice3(X27,X29,X30)
        | r1_lattice3(X27,X28,X30)
        | ~ m1_subset_1(X30,u1_struct_0(X27))
        | ~ r1_tarski(X28,X29)
        | ~ l1_orders_2(X27) )
      & ( ~ r2_lattice3(X27,X29,X30)
        | r2_lattice3(X27,X28,X30)
        | ~ m1_subset_1(X30,u1_struct_0(X27))
        | ~ r1_tarski(X28,X29)
        | ~ l1_orders_2(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_yellow_0])])])])).

cnf(c_0_67,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_43])).

cnf(c_0_68,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_64])).

cnf(c_0_70,plain,
    ( r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | X4 != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_71,plain,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)))
    | ~ epred1_3(X2,X1,esk3_0)
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2) ),
    inference(spm,[status(thm)],[c_0_65,c_0_59])).

cnf(c_0_72,plain,
    ( r2_lattice3(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_tarski(X4,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

fof(c_0_73,plain,(
    ! [X9,X10] :
      ( ( ~ m1_subset_1(X9,k1_zfmisc_1(X10))
        | r1_tarski(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | m1_subset_1(X9,k1_zfmisc_1(X10)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_74,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk5_0,esk6_0)
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_20])).

cnf(c_0_75,plain,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))
    | ~ epred1_3(X2,esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_68]),c_0_35])])).

cnf(c_0_76,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,k1_tarski(X1),esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_69]),c_0_18])])).

cnf(c_0_77,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_69]),c_0_18]),c_0_39])]),c_0_40])).

cnf(c_0_78,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_70])).

cnf(c_0_79,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_43])).

cnf(c_0_80,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | ~ r2_lattice3(esk3_0,X2,esk6_0)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_17]),c_0_18])])).

cnf(c_0_81,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_82,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_74])).

cnf(c_0_83,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | esk1_3(esk3_0,esk4_0,esk6_0) = k1_yellow_0(esk3_0,X1)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0))
    | ~ r1_yellow_0(esk3_0,X1)
    | ~ r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_69]),c_0_18])])).

cnf(c_0_84,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_75,c_0_43])).

cnf(c_0_85,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_69]),c_0_77])).

cnf(c_0_86,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_74])).

cnf(c_0_87,negated_conjecture,
    ( r1_orders_2(esk3_0,k1_yellow_0(esk3_0,X1),esk6_0)
    | ~ r1_yellow_0(esk3_0,X1)
    | ~ r2_lattice3(esk3_0,X1,esk6_0)
    | ~ m1_subset_1(k1_yellow_0(esk3_0,X1),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_17]),c_0_18])])).

cnf(c_0_88,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))
    | r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_20])).

cnf(c_0_89,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,X2,esk6_0)),k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_80,c_0_24])).

cnf(c_0_90,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_91,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85])).

cnf(c_0_92,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | esk1_3(esk3_0,esk4_0,esk6_0) = k1_yellow_0(esk3_0,X1)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,X1,esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)))
    | ~ r1_yellow_0(esk3_0,X1)
    | ~ r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_69]),c_0_18])])).

cnf(c_0_93,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | esk1_3(esk3_0,esk4_0,esk6_0) = k1_yellow_0(esk3_0,X1)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | ~ r1_yellow_0(esk3_0,X1)
    | ~ r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_69]),c_0_18])])).

cnf(c_0_94,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,X2,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_80,c_0_25])).

cnf(c_0_95,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_86])).

cnf(c_0_96,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk5_0,esk6_0)
    | r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)
    | ~ r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)
    | ~ m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_97,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_98,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,X1,esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))
    | ~ r2_lattice3(esk3_0,k1_tarski(X1),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_91]),c_0_18])])).

cnf(c_0_99,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_84]),c_0_85])).

cnf(c_0_100,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | ~ r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_84]),c_0_85])).

cnf(c_0_101,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_102,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk1_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_103,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | ~ m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_27])).

cnf(c_0_104,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_69]),c_0_99]),c_0_100])).

cnf(c_0_105,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))
    | ~ m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_101]),c_0_30])).

cnf(c_0_106,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | ~ r1_orders_2(esk3_0,esk1_3(esk3_0,X1,esk6_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_17]),c_0_18])])).

cnf(c_0_107,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk1_3(esk3_0,esk5_0,esk6_0),esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_34])).

cnf(c_0_108,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk1_3(esk3_0,esk5_0,esk6_0),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_104]),c_0_37])).

cnf(c_0_109,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_27])).

cnf(c_0_110,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_108]),c_0_30])).

cnf(c_0_111,plain,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))
    | ~ epred1_3(X2,esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_109]),c_0_35])])).

cnf(c_0_112,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,k1_tarski(X1),esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_110]),c_0_18])])).

cnf(c_0_113,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_110]),c_0_18]),c_0_39])]),c_0_40])).

cnf(c_0_114,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | esk1_3(esk3_0,esk4_0,esk6_0) = k1_yellow_0(esk3_0,X1)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0))
    | ~ r1_yellow_0(esk3_0,X1)
    | ~ r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_110]),c_0_18])])).

cnf(c_0_115,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_111,c_0_43])).

cnf(c_0_116,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_110]),c_0_113])).

cnf(c_0_117,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(k1_yellow_0(X3,X1),X4)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ epred1_3(X4,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_118,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_115]),c_0_116])).

cnf(c_0_119,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | esk1_3(esk3_0,esk4_0,esk6_0) = k1_yellow_0(esk3_0,X1)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,X1,esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)))
    | ~ r1_yellow_0(esk3_0,X1)
    | ~ r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_110]),c_0_18])])).

cnf(c_0_120,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | esk1_3(esk3_0,esk4_0,esk6_0) = k1_yellow_0(esk3_0,X1)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | ~ r1_yellow_0(esk3_0,X1)
    | ~ r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_110]),c_0_18])])).

cnf(c_0_121,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_122,plain,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | r2_hidden(k1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)
    | ~ epred1_3(X2,esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_34]),c_0_35])])).

cnf(c_0_123,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,X1,esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))
    | ~ r2_lattice3(esk3_0,k1_tarski(X1),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_118]),c_0_18])])).

cnf(c_0_124,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_115]),c_0_116])).

cnf(c_0_125,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | ~ r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_115]),c_0_116])).

cnf(c_0_126,negated_conjecture,
    ( r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),X1)
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r2_lattice3(esk3_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_37]),c_0_18])])).

cnf(c_0_127,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | r2_hidden(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_122,c_0_43])).

cnf(c_0_128,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) = esk1_3(esk3_0,esk4_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_110]),c_0_124]),c_0_125])).

cnf(c_0_129,negated_conjecture,
    ( r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0))
    | ~ r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_25]),c_0_17])])).

cnf(c_0_130,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_127,c_0_128])).

cnf(c_0_131,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_129,c_0_130])).

cnf(c_0_132,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk4_0,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_106,c_0_131])).

cnf(c_0_133,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_132]),c_0_25])).

cnf(c_0_134,plain,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | ~ epred1_3(X2,X1,esk3_0)
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2) ),
    inference(spm,[status(thm)],[c_0_58,c_0_133])).

cnf(c_0_135,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_134,c_0_43])).

cnf(c_0_136,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_135,c_0_20])).

cnf(c_0_137,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_136])).

cnf(c_0_138,plain,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_hidden(k1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)
    | ~ epred1_3(X2,esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_137]),c_0_35])])).

cnf(c_0_139,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_hidden(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_138,c_0_43])).

cnf(c_0_140,plain,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(X1))
    | ~ epred1_3(X2,X1,esk3_0)
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2) ),
    inference(spm,[status(thm)],[c_0_61,c_0_133])).

cnf(c_0_141,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_139,c_0_128])).

cnf(c_0_142,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_140,c_0_43])).

cnf(c_0_143,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_141])).

cnf(c_0_144,plain,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)))
    | ~ epred1_3(X2,X1,esk3_0)
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2) ),
    inference(spm,[status(thm)],[c_0_65,c_0_133])).

cnf(c_0_145,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk5_0,esk6_0)
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_142,c_0_20])).

cnf(c_0_146,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,X1,esk6_0)
    | ~ r1_tarski(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_136])).

cnf(c_0_147,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_tarski(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_143])).

cnf(c_0_148,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_144,c_0_43])).

cnf(c_0_149,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_145])).

cnf(c_0_150,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk6_0)
    | ~ r2_lattice3(esk3_0,k1_tarski(X1),esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_17]),c_0_18])])).

cnf(c_0_151,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_136])).

cnf(c_0_152,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_146,c_0_147])).

cnf(c_0_153,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_145])).

cnf(c_0_154,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))
    | r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_148,c_0_20])).

cnf(c_0_155,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_149])).

cnf(c_0_156,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_150,c_0_151]),c_0_152])).

cnf(c_0_157,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_153])).

cnf(c_0_158,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk5_0,esk6_0)
    | r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)
    | ~ r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)
    | ~ m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_154])).

cnf(c_0_159,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_155])).

cnf(c_0_160,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_106,c_0_156])).

cnf(c_0_161,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_157])).

cnf(c_0_162,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | ~ m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_158,c_0_159]),c_0_27])).

cnf(c_0_163,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_160]),c_0_136])).

cnf(c_0_164,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))
    | ~ m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_158,c_0_161]),c_0_30])).

cnf(c_0_165,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk1_3(esk3_0,esk5_0,esk6_0),esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_162,c_0_163]),c_0_133])).

cnf(c_0_166,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk1_3(esk3_0,esk5_0,esk6_0),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_164,c_0_163]),c_0_37])).

cnf(c_0_167,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_165]),c_0_27])).

cnf(c_0_168,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_166]),c_0_30])).

cnf(c_0_169,plain,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_hidden(k1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)
    | ~ epred1_3(X2,esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_167]),c_0_35])])).

cnf(c_0_170,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),X1)
    | ~ r2_lattice3(esk3_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_168]),c_0_18])])).

cnf(c_0_171,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_hidden(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_169,c_0_43])).

cnf(c_0_172,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0)
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | ~ r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_170,c_0_145]),c_0_17])])).

cnf(c_0_173,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_171,c_0_128])).

cnf(c_0_174,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0)
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_172,c_0_173])).

cnf(c_0_175,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk4_0,esk6_0)
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_106,c_0_174])).

cnf(c_0_176,negated_conjecture,
    ( r2_lattice3(esk3_0,esk4_0,esk6_0)
    | r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_177,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_175]),c_0_145])).

cnf(c_0_178,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0)
    | r2_lattice3(esk3_0,X1,esk6_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_176])).

cnf(c_0_179,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_177])).

cnf(c_0_180,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)
    | r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_178,c_0_179])).

cnf(c_0_181,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk5_0,esk6_0)
    | r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)
    | ~ m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_158,c_0_180])).

cnf(c_0_182,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_181,c_0_163]),c_0_25]),c_0_106])).

cnf(c_0_183,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_170,c_0_182]),c_0_17])]),c_0_173])).

fof(c_0_184,plain,(
    ! [X6] : ~ v1_xboole_0(k1_tarski(X6)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

cnf(c_0_185,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_106,c_0_183])).

cnf(c_0_186,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_184])).

cnf(c_0_187,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_185]),c_0_182])).

cnf(c_0_188,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_189,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_186,c_0_187]),c_0_188])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:54:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 2.83/3.04  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 2.83/3.04  # and selection function SelectNewComplexAHP.
% 2.83/3.04  #
% 2.83/3.04  # Preprocessing time       : 0.029 s
% 2.83/3.04  # Presaturation interreduction done
% 2.83/3.04  
% 2.83/3.04  # Proof found!
% 2.83/3.04  # SZS status Theorem
% 2.83/3.04  # SZS output start CNFRefutation
% 2.83/3.04  fof(t52_waybel_0, conjecture, ![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(((![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r1_yellow_0(X1,X4)))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X3)&![X5]:((v1_finset_1(X5)&m1_subset_1(X5,k1_zfmisc_1(X2)))=>~((r1_yellow_0(X1,X5)&X4=k1_yellow_0(X1,X5))))))))&![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_hidden(k1_yellow_0(X1,X4),X3))))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)<=>r2_lattice3(X1,X3,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_waybel_0)).
% 2.83/3.04  fof(d9_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattice3)).
% 2.83/3.04  fof(t63_subset_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 2.83/3.04  fof(fc1_finset_1, axiom, ![X1]:v1_finset_1(k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_finset_1)).
% 2.83/3.04  fof(t7_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((((r1_lattice3(X1,k1_tarski(X3),X2)=>r1_orders_2(X1,X2,X3))&(r1_orders_2(X1,X2,X3)=>r1_lattice3(X1,k1_tarski(X3),X2)))&(r2_lattice3(X1,k1_tarski(X3),X2)=>r1_orders_2(X1,X3,X2)))&(r1_orders_2(X1,X3,X2)=>r2_lattice3(X1,k1_tarski(X3),X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_yellow_0)).
% 2.83/3.04  fof(t24_orders_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,X2,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_orders_2)).
% 2.83/3.04  fof(d9_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_yellow_0(X1,X2)=>(X3=k1_yellow_0(X1,X2)<=>(r2_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)=>r1_orders_2(X1,X3,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_yellow_0)).
% 2.83/3.04  fof(t9_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r1_lattice3(X1,X3,X4)=>r1_lattice3(X1,X2,X4))&(r2_lattice3(X1,X3,X4)=>r2_lattice3(X1,X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_yellow_0)).
% 2.83/3.04  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.83/3.04  fof(fc2_xboole_0, axiom, ![X1]:~(v1_xboole_0(k1_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 2.83/3.04  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.83/3.04  fof(c_0_11, plain, ![X1, X2, X3]:(epred1_3(X3,X2,X1)<=>((![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r1_yellow_0(X1,X4)))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X3)&![X5]:((v1_finset_1(X5)&m1_subset_1(X5,k1_zfmisc_1(X2)))=>~((r1_yellow_0(X1,X5)&X4=k1_yellow_0(X1,X5))))))))&![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_hidden(k1_yellow_0(X1,X4),X3))))), introduced(definition)).
% 2.83/3.04  fof(c_0_12, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(epred1_3(X3,X2,X1)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)<=>r2_lattice3(X1,X3,X4)))))))), inference(apply_def,[status(thm)],[inference(assume_negation,[status(cth)],[t52_waybel_0]), c_0_11])).
% 2.83/3.04  fof(c_0_13, plain, ![X14, X15, X16, X17]:((~r2_lattice3(X14,X15,X16)|(~m1_subset_1(X17,u1_struct_0(X14))|(~r2_hidden(X17,X15)|r1_orders_2(X14,X17,X16)))|~m1_subset_1(X16,u1_struct_0(X14))|~l1_orders_2(X14))&((m1_subset_1(esk1_3(X14,X15,X16),u1_struct_0(X14))|r2_lattice3(X14,X15,X16)|~m1_subset_1(X16,u1_struct_0(X14))|~l1_orders_2(X14))&((r2_hidden(esk1_3(X14,X15,X16),X15)|r2_lattice3(X14,X15,X16)|~m1_subset_1(X16,u1_struct_0(X14))|~l1_orders_2(X14))&(~r1_orders_2(X14,esk1_3(X14,X15,X16),X16)|r2_lattice3(X14,X15,X16)|~m1_subset_1(X16,u1_struct_0(X14))|~l1_orders_2(X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).
% 2.83/3.04  fof(c_0_14, negated_conjecture, ((((~v2_struct_0(esk3_0)&v3_orders_2(esk3_0))&v4_orders_2(esk3_0))&l1_orders_2(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(epred1_3(esk5_0,esk4_0,esk3_0)&(m1_subset_1(esk6_0,u1_struct_0(esk3_0))&((~r2_lattice3(esk3_0,esk4_0,esk6_0)|~r2_lattice3(esk3_0,esk5_0,esk6_0))&(r2_lattice3(esk3_0,esk4_0,esk6_0)|r2_lattice3(esk3_0,esk5_0,esk6_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).
% 2.83/3.04  fof(c_0_15, plain, ![X7, X8]:(~r2_hidden(X7,X8)|m1_subset_1(k1_tarski(X7),k1_zfmisc_1(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).
% 2.83/3.04  cnf(c_0_16, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.83/3.04  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.83/3.04  cnf(c_0_18, negated_conjecture, (l1_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.83/3.04  cnf(c_0_19, plain, (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.83/3.04  cnf(c_0_20, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|r2_hidden(esk1_3(esk3_0,X1,esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])])).
% 2.83/3.04  cnf(c_0_21, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.83/3.04  fof(c_0_22, plain, ![X1, X2, X3]:(epred1_3(X3,X2,X1)=>((![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r1_yellow_0(X1,X4)))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X3)&![X5]:((v1_finset_1(X5)&m1_subset_1(X5,k1_zfmisc_1(X2)))=>~((r1_yellow_0(X1,X5)&X4=k1_yellow_0(X1,X5))))))))&![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_hidden(k1_yellow_0(X1,X4),X3))))), inference(split_equiv,[status(thm)],[c_0_11])).
% 2.83/3.04  cnf(c_0_23, negated_conjecture, (~r2_lattice3(esk3_0,esk4_0,esk6_0)|~r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.83/3.04  cnf(c_0_24, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,X1,esk6_0)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 2.83/3.04  cnf(c_0_25, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk1_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_17]), c_0_18])])).
% 2.83/3.04  fof(c_0_26, plain, ![X35, X36, X37, X38, X39, X41]:(((~v1_finset_1(X38)|~m1_subset_1(X38,k1_zfmisc_1(X36))|(X38=k1_xboole_0|r1_yellow_0(X35,X38))|~epred1_3(X37,X36,X35))&(((v1_finset_1(esk7_4(X35,X36,X37,X39))|~r2_hidden(X39,X37)|~m1_subset_1(X39,u1_struct_0(X35))|~epred1_3(X37,X36,X35))&(m1_subset_1(esk7_4(X35,X36,X37,X39),k1_zfmisc_1(X36))|~r2_hidden(X39,X37)|~m1_subset_1(X39,u1_struct_0(X35))|~epred1_3(X37,X36,X35)))&((r1_yellow_0(X35,esk7_4(X35,X36,X37,X39))|~r2_hidden(X39,X37)|~m1_subset_1(X39,u1_struct_0(X35))|~epred1_3(X37,X36,X35))&(X39=k1_yellow_0(X35,esk7_4(X35,X36,X37,X39))|~r2_hidden(X39,X37)|~m1_subset_1(X39,u1_struct_0(X35))|~epred1_3(X37,X36,X35)))))&(~v1_finset_1(X41)|~m1_subset_1(X41,k1_zfmisc_1(X36))|(X41=k1_xboole_0|r2_hidden(k1_yellow_0(X35,X41),X37))|~epred1_3(X37,X36,X35))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])])])).
% 2.83/3.04  cnf(c_0_27, negated_conjecture, (m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))|~r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 2.83/3.04  fof(c_0_28, plain, ![X11]:v1_finset_1(k1_tarski(X11)), inference(variable_rename,[status(thm)],[fc1_finset_1])).
% 2.83/3.04  fof(c_0_29, plain, ![X24, X25, X26]:((((~r1_lattice3(X24,k1_tarski(X26),X25)|r1_orders_2(X24,X25,X26)|~m1_subset_1(X26,u1_struct_0(X24))|~m1_subset_1(X25,u1_struct_0(X24))|~l1_orders_2(X24))&(~r1_orders_2(X24,X25,X26)|r1_lattice3(X24,k1_tarski(X26),X25)|~m1_subset_1(X26,u1_struct_0(X24))|~m1_subset_1(X25,u1_struct_0(X24))|~l1_orders_2(X24)))&(~r2_lattice3(X24,k1_tarski(X26),X25)|r1_orders_2(X24,X26,X25)|~m1_subset_1(X26,u1_struct_0(X24))|~m1_subset_1(X25,u1_struct_0(X24))|~l1_orders_2(X24)))&(~r1_orders_2(X24,X26,X25)|r2_lattice3(X24,k1_tarski(X26),X25)|~m1_subset_1(X26,u1_struct_0(X24))|~m1_subset_1(X25,u1_struct_0(X24))|~l1_orders_2(X24))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_yellow_0])])])])).
% 2.83/3.04  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))|~r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_23, c_0_25])).
% 2.83/3.04  fof(c_0_31, plain, ![X12, X13]:(v2_struct_0(X12)|~v3_orders_2(X12)|~l1_orders_2(X12)|(~m1_subset_1(X13,u1_struct_0(X12))|r1_orders_2(X12,X13,X13))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_orders_2])])])])).
% 2.83/3.04  fof(c_0_32, plain, ![X19, X20, X21, X22]:(((r2_lattice3(X19,X20,X21)|X21!=k1_yellow_0(X19,X20)|~r1_yellow_0(X19,X20)|~m1_subset_1(X21,u1_struct_0(X19))|~l1_orders_2(X19))&(~m1_subset_1(X22,u1_struct_0(X19))|(~r2_lattice3(X19,X20,X22)|r1_orders_2(X19,X21,X22))|X21!=k1_yellow_0(X19,X20)|~r1_yellow_0(X19,X20)|~m1_subset_1(X21,u1_struct_0(X19))|~l1_orders_2(X19)))&((m1_subset_1(esk2_3(X19,X20,X21),u1_struct_0(X19))|~r2_lattice3(X19,X20,X21)|X21=k1_yellow_0(X19,X20)|~r1_yellow_0(X19,X20)|~m1_subset_1(X21,u1_struct_0(X19))|~l1_orders_2(X19))&((r2_lattice3(X19,X20,esk2_3(X19,X20,X21))|~r2_lattice3(X19,X20,X21)|X21=k1_yellow_0(X19,X20)|~r1_yellow_0(X19,X20)|~m1_subset_1(X21,u1_struct_0(X19))|~l1_orders_2(X19))&(~r1_orders_2(X19,X21,esk2_3(X19,X20,X21))|~r2_lattice3(X19,X20,X21)|X21=k1_yellow_0(X19,X20)|~r1_yellow_0(X19,X20)|~m1_subset_1(X21,u1_struct_0(X19))|~l1_orders_2(X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).
% 2.83/3.04  cnf(c_0_33, plain, (X1=k1_xboole_0|r1_yellow_0(X3,X1)|~v1_finset_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~epred1_3(X4,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 2.83/3.04  cnf(c_0_34, negated_conjecture, (m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_27, c_0_25])).
% 2.83/3.04  cnf(c_0_35, plain, (v1_finset_1(k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 2.83/3.04  cnf(c_0_36, plain, (r2_lattice3(X1,k1_tarski(X2),X3)|~r1_orders_2(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 2.83/3.04  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_30, c_0_25])).
% 2.83/3.04  cnf(c_0_38, plain, (v2_struct_0(X1)|r1_orders_2(X1,X2,X2)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 2.83/3.04  cnf(c_0_39, negated_conjecture, (v3_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.83/3.04  cnf(c_0_40, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.83/3.04  cnf(c_0_41, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))|X3=k1_yellow_0(X1,X2)|~r2_lattice3(X1,X2,X3)|~r1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 2.83/3.04  cnf(c_0_42, plain, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~epred1_3(X2,esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])])).
% 2.83/3.04  cnf(c_0_43, negated_conjecture, (epred1_3(esk5_0,esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.83/3.04  cnf(c_0_44, negated_conjecture, (r2_lattice3(esk3_0,k1_tarski(X1),esk1_3(esk3_0,esk4_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_18])])).
% 2.83/3.04  cnf(c_0_45, negated_conjecture, (r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_37]), c_0_18]), c_0_39])]), c_0_40])).
% 2.83/3.04  cnf(c_0_46, negated_conjecture, (esk1_3(esk3_0,esk4_0,esk6_0)=k1_yellow_0(esk3_0,X1)|m1_subset_1(esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r1_yellow_0(esk3_0,X1)|~r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_37]), c_0_18])])).
% 2.83/3.04  cnf(c_0_47, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 2.83/3.04  cnf(c_0_48, negated_conjecture, (r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_37]), c_0_45])).
% 2.83/3.04  cnf(c_0_49, plain, (r2_lattice3(X1,X2,esk2_3(X1,X2,X3))|X3=k1_yellow_0(X1,X2)|~r2_lattice3(X1,X2,X3)|~r1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 2.83/3.04  cnf(c_0_50, plain, (X2=k1_yellow_0(X1,X3)|~r1_orders_2(X1,X2,esk2_3(X1,X3,X2))|~r2_lattice3(X1,X3,X2)|~r1_yellow_0(X1,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 2.83/3.04  cnf(c_0_51, plain, (r1_orders_2(X1,X2,X3)|~r2_lattice3(X1,k1_tarski(X2),X3)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 2.83/3.04  cnf(c_0_52, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])).
% 2.83/3.04  cnf(c_0_53, negated_conjecture, (esk1_3(esk3_0,esk4_0,esk6_0)=k1_yellow_0(esk3_0,X1)|r2_lattice3(esk3_0,X1,esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r1_yellow_0(esk3_0,X1)|~r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_37]), c_0_18])])).
% 2.83/3.04  cnf(c_0_54, negated_conjecture, (esk1_3(esk3_0,esk4_0,esk6_0)=k1_yellow_0(esk3_0,X1)|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r1_yellow_0(esk3_0,X1)|~r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))|~r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_37]), c_0_18])])).
% 2.83/3.04  cnf(c_0_55, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,X1,esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r2_lattice3(esk3_0,k1_tarski(X1),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_18])])).
% 2.83/3.04  cnf(c_0_56, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_47]), c_0_48])).
% 2.83/3.04  cnf(c_0_57, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_47]), c_0_48])).
% 2.83/3.04  cnf(c_0_58, plain, (X1=k1_yellow_0(X2,esk7_4(X2,X3,X4,X1))|~r2_hidden(X1,X4)|~m1_subset_1(X1,u1_struct_0(X2))|~epred1_3(X4,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 2.83/3.04  cnf(c_0_59, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_37]), c_0_56]), c_0_57])).
% 2.83/3.04  cnf(c_0_60, plain, (k1_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|~epred1_3(X2,X1,esk3_0)|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 2.83/3.04  cnf(c_0_61, plain, (m1_subset_1(esk7_4(X1,X2,X3,X4),k1_zfmisc_1(X2))|~r2_hidden(X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~epred1_3(X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 2.83/3.04  cnf(c_0_62, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_60, c_0_43])).
% 2.83/3.04  cnf(c_0_63, plain, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(X1))|~epred1_3(X2,X1,esk3_0)|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2)), inference(spm,[status(thm)],[c_0_61, c_0_59])).
% 2.83/3.04  cnf(c_0_64, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_62, c_0_20])).
% 2.83/3.04  cnf(c_0_65, plain, (r1_yellow_0(X1,esk7_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~epred1_3(X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 2.83/3.04  fof(c_0_66, plain, ![X27, X28, X29, X30]:((~r1_lattice3(X27,X29,X30)|r1_lattice3(X27,X28,X30)|~m1_subset_1(X30,u1_struct_0(X27))|~r1_tarski(X28,X29)|~l1_orders_2(X27))&(~r2_lattice3(X27,X29,X30)|r2_lattice3(X27,X28,X30)|~m1_subset_1(X30,u1_struct_0(X27))|~r1_tarski(X28,X29)|~l1_orders_2(X27))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_yellow_0])])])])).
% 2.83/3.04  cnf(c_0_67, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_63, c_0_43])).
% 2.83/3.04  cnf(c_0_68, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_27, c_0_64])).
% 2.83/3.04  cnf(c_0_69, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_30, c_0_64])).
% 2.83/3.04  cnf(c_0_70, plain, (r1_orders_2(X2,X4,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|X4!=k1_yellow_0(X2,X3)|~r1_yellow_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 2.83/3.04  cnf(c_0_71, plain, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)))|~epred1_3(X2,X1,esk3_0)|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2)), inference(spm,[status(thm)],[c_0_65, c_0_59])).
% 2.83/3.04  cnf(c_0_72, plain, (r2_lattice3(X1,X4,X3)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~r1_tarski(X4,X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 2.83/3.04  fof(c_0_73, plain, ![X9, X10]:((~m1_subset_1(X9,k1_zfmisc_1(X10))|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|m1_subset_1(X9,k1_zfmisc_1(X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 2.83/3.04  cnf(c_0_74, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk5_0,esk6_0)|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_67, c_0_20])).
% 2.83/3.04  cnf(c_0_75, plain, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))|~epred1_3(X2,esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_68]), c_0_35])])).
% 2.83/3.04  cnf(c_0_76, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,k1_tarski(X1),esk1_3(esk3_0,esk4_0,esk6_0))|~r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_69]), c_0_18])])).
% 2.83/3.04  cnf(c_0_77, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_69]), c_0_18]), c_0_39])]), c_0_40])).
% 2.83/3.04  cnf(c_0_78, plain, (r1_orders_2(X1,k1_yellow_0(X1,X2),X3)|~r1_yellow_0(X1,X2)|~r2_lattice3(X1,X2,X3)|~l1_orders_2(X1)|~m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_70])).
% 2.83/3.04  cnf(c_0_79, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_71, c_0_43])).
% 2.83/3.04  cnf(c_0_80, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|~r2_lattice3(esk3_0,X2,esk6_0)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_17]), c_0_18])])).
% 2.83/3.04  cnf(c_0_81, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 2.83/3.04  cnf(c_0_82, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_27, c_0_74])).
% 2.83/3.04  cnf(c_0_83, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|esk1_3(esk3_0,esk4_0,esk6_0)=k1_yellow_0(esk3_0,X1)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0))|~r1_yellow_0(esk3_0,X1)|~r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_69]), c_0_18])])).
% 2.83/3.04  cnf(c_0_84, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))), inference(spm,[status(thm)],[c_0_75, c_0_43])).
% 2.83/3.04  cnf(c_0_85, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_69]), c_0_77])).
% 2.83/3.04  cnf(c_0_86, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_30, c_0_74])).
% 2.83/3.04  cnf(c_0_87, negated_conjecture, (r1_orders_2(esk3_0,k1_yellow_0(esk3_0,X1),esk6_0)|~r1_yellow_0(esk3_0,X1)|~r2_lattice3(esk3_0,X1,esk6_0)|~m1_subset_1(k1_yellow_0(esk3_0,X1),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_17]), c_0_18])])).
% 2.83/3.04  cnf(c_0_88, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))|r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_79, c_0_20])).
% 2.83/3.04  cnf(c_0_89, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,X2,esk6_0)),k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_80, c_0_24])).
% 2.83/3.04  cnf(c_0_90, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 2.83/3.04  cnf(c_0_91, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_85])).
% 2.83/3.04  cnf(c_0_92, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|esk1_3(esk3_0,esk4_0,esk6_0)=k1_yellow_0(esk3_0,X1)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,X1,esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)))|~r1_yellow_0(esk3_0,X1)|~r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_69]), c_0_18])])).
% 2.83/3.04  cnf(c_0_93, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|esk1_3(esk3_0,esk4_0,esk6_0)=k1_yellow_0(esk3_0,X1)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|~r1_yellow_0(esk3_0,X1)|~r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))|~r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_69]), c_0_18])])).
% 2.83/3.04  cnf(c_0_94, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk1_3(esk3_0,X2,esk6_0),u1_struct_0(esk3_0))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_80, c_0_25])).
% 2.83/3.04  cnf(c_0_95, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0)|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_81, c_0_86])).
% 2.83/3.04  cnf(c_0_96, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk5_0,esk6_0)|r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)|~r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)|~m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 2.83/3.04  cnf(c_0_97, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 2.83/3.04  cnf(c_0_98, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,X1,esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))|~r2_lattice3(esk3_0,k1_tarski(X1),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_91]), c_0_18])])).
% 2.83/3.04  cnf(c_0_99, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_84]), c_0_85])).
% 2.83/3.04  cnf(c_0_100, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|~r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_84]), c_0_85])).
% 2.83/3.04  cnf(c_0_101, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 2.83/3.04  cnf(c_0_102, plain, (r2_lattice3(X1,X2,X3)|~r1_orders_2(X1,esk1_3(X1,X2,X3),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.83/3.04  cnf(c_0_103, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))|~m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_27])).
% 2.83/3.04  cnf(c_0_104, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_69]), c_0_99]), c_0_100])).
% 2.83/3.04  cnf(c_0_105, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))|~m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_101]), c_0_30])).
% 2.83/3.04  cnf(c_0_106, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|~r1_orders_2(esk3_0,esk1_3(esk3_0,X1,esk6_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_17]), c_0_18])])).
% 2.83/3.04  cnf(c_0_107, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk1_3(esk3_0,esk5_0,esk6_0),esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_34])).
% 2.83/3.04  cnf(c_0_108, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk1_3(esk3_0,esk5_0,esk6_0),esk6_0)|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_104]), c_0_37])).
% 2.83/3.04  cnf(c_0_109, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_27])).
% 2.83/3.04  cnf(c_0_110, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_108]), c_0_30])).
% 2.83/3.04  cnf(c_0_111, plain, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))|~epred1_3(X2,esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_109]), c_0_35])])).
% 2.83/3.04  cnf(c_0_112, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,k1_tarski(X1),esk1_3(esk3_0,esk4_0,esk6_0))|~r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_110]), c_0_18])])).
% 2.83/3.04  cnf(c_0_113, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_110]), c_0_18]), c_0_39])]), c_0_40])).
% 2.83/3.04  cnf(c_0_114, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|esk1_3(esk3_0,esk4_0,esk6_0)=k1_yellow_0(esk3_0,X1)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0))|~r1_yellow_0(esk3_0,X1)|~r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_110]), c_0_18])])).
% 2.83/3.04  cnf(c_0_115, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))), inference(spm,[status(thm)],[c_0_111, c_0_43])).
% 2.83/3.04  cnf(c_0_116, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_110]), c_0_113])).
% 2.83/3.04  cnf(c_0_117, plain, (X1=k1_xboole_0|r2_hidden(k1_yellow_0(X3,X1),X4)|~v1_finset_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~epred1_3(X4,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 2.83/3.04  cnf(c_0_118, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_115]), c_0_116])).
% 2.83/3.04  cnf(c_0_119, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|esk1_3(esk3_0,esk4_0,esk6_0)=k1_yellow_0(esk3_0,X1)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,X1,esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)))|~r1_yellow_0(esk3_0,X1)|~r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_110]), c_0_18])])).
% 2.83/3.04  cnf(c_0_120, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|esk1_3(esk3_0,esk4_0,esk6_0)=k1_yellow_0(esk3_0,X1)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|~r1_yellow_0(esk3_0,X1)|~r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))|~r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_110]), c_0_18])])).
% 2.83/3.04  cnf(c_0_121, plain, (r1_orders_2(X1,X4,X3)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.83/3.04  cnf(c_0_122, plain, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|r2_hidden(k1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)|~epred1_3(X2,esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_34]), c_0_35])])).
% 2.83/3.04  cnf(c_0_123, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,X1,esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))|~r2_lattice3(esk3_0,k1_tarski(X1),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_118]), c_0_18])])).
% 2.83/3.04  cnf(c_0_124, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_115]), c_0_116])).
% 2.83/3.04  cnf(c_0_125, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|~r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk2_3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk1_3(esk3_0,esk4_0,esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_115]), c_0_116])).
% 2.83/3.04  cnf(c_0_126, negated_conjecture, (r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),X1)|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r2_lattice3(esk3_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_37]), c_0_18])])).
% 2.83/3.04  cnf(c_0_127, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|r2_hidden(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0)), inference(spm,[status(thm)],[c_0_122, c_0_43])).
% 2.83/3.04  cnf(c_0_128, negated_conjecture, (k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))=esk1_3(esk3_0,esk4_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_110]), c_0_124]), c_0_125])).
% 2.83/3.04  cnf(c_0_129, negated_conjecture, (r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0)|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0))|~r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_25]), c_0_17])])).
% 2.83/3.04  cnf(c_0_130, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_127, c_0_128])).
% 2.83/3.04  cnf(c_0_131, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0)|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_129, c_0_130])).
% 2.83/3.04  cnf(c_0_132, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk4_0,esk6_0)|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_106, c_0_131])).
% 2.83/3.04  cnf(c_0_133, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_132]), c_0_25])).
% 2.83/3.04  cnf(c_0_134, plain, (k1_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|~epred1_3(X2,X1,esk3_0)|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2)), inference(spm,[status(thm)],[c_0_58, c_0_133])).
% 2.83/3.04  cnf(c_0_135, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_134, c_0_43])).
% 2.83/3.04  cnf(c_0_136, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_135, c_0_20])).
% 2.83/3.04  cnf(c_0_137, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_27, c_0_136])).
% 2.83/3.04  cnf(c_0_138, plain, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_hidden(k1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)|~epred1_3(X2,esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_137]), c_0_35])])).
% 2.83/3.04  cnf(c_0_139, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_hidden(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0)), inference(spm,[status(thm)],[c_0_138, c_0_43])).
% 2.83/3.04  cnf(c_0_140, plain, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(X1))|~epred1_3(X2,X1,esk3_0)|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2)), inference(spm,[status(thm)],[c_0_61, c_0_133])).
% 2.83/3.04  cnf(c_0_141, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_139, c_0_128])).
% 2.83/3.04  cnf(c_0_142, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_140, c_0_43])).
% 2.83/3.04  cnf(c_0_143, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_19, c_0_141])).
% 2.83/3.04  cnf(c_0_144, plain, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,esk5_0,esk6_0)))|~epred1_3(X2,X1,esk3_0)|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2)), inference(spm,[status(thm)],[c_0_65, c_0_133])).
% 2.83/3.04  cnf(c_0_145, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk5_0,esk6_0)|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_142, c_0_20])).
% 2.83/3.04  cnf(c_0_146, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,X1,esk6_0)|~r1_tarski(X1,esk5_0)), inference(spm,[status(thm)],[c_0_80, c_0_136])).
% 2.83/3.04  cnf(c_0_147, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_tarski(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk5_0)), inference(spm,[status(thm)],[c_0_81, c_0_143])).
% 2.83/3.04  cnf(c_0_148, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_144, c_0_43])).
% 2.83/3.04  cnf(c_0_149, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_27, c_0_145])).
% 2.83/3.04  cnf(c_0_150, negated_conjecture, (r1_orders_2(esk3_0,X1,esk6_0)|~r2_lattice3(esk3_0,k1_tarski(X1),esk6_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_17]), c_0_18])])).
% 2.83/3.04  cnf(c_0_151, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_30, c_0_136])).
% 2.83/3.04  cnf(c_0_152, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0)), inference(spm,[status(thm)],[c_0_146, c_0_147])).
% 2.83/3.04  cnf(c_0_153, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_30, c_0_145])).
% 2.83/3.04  cnf(c_0_154, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))|r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_148, c_0_20])).
% 2.83/3.04  cnf(c_0_155, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_81, c_0_149])).
% 2.83/3.04  cnf(c_0_156, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_150, c_0_151]), c_0_152])).
% 2.83/3.04  cnf(c_0_157, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0)|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_81, c_0_153])).
% 2.83/3.04  cnf(c_0_158, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk5_0,esk6_0)|r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)|~r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)|~m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_87, c_0_154])).
% 2.83/3.04  cnf(c_0_159, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_89, c_0_155])).
% 2.83/3.04  cnf(c_0_160, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk4_0,esk6_0)), inference(spm,[status(thm)],[c_0_106, c_0_156])).
% 2.83/3.04  cnf(c_0_161, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_94, c_0_157])).
% 2.83/3.04  cnf(c_0_162, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))|~m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_158, c_0_159]), c_0_27])).
% 2.83/3.04  cnf(c_0_163, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_160]), c_0_136])).
% 2.83/3.04  cnf(c_0_164, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))|~m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_158, c_0_161]), c_0_30])).
% 2.83/3.04  cnf(c_0_165, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk1_3(esk3_0,esk5_0,esk6_0),esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_162, c_0_163]), c_0_133])).
% 2.83/3.04  cnf(c_0_166, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk1_3(esk3_0,esk5_0,esk6_0),esk6_0)|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_164, c_0_163]), c_0_37])).
% 2.83/3.04  cnf(c_0_167, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_165]), c_0_27])).
% 2.83/3.04  cnf(c_0_168, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_166]), c_0_30])).
% 2.83/3.04  cnf(c_0_169, plain, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_hidden(k1_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)|~epred1_3(X2,esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_167]), c_0_35])])).
% 2.83/3.04  cnf(c_0_170, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),X1)|~r2_lattice3(esk3_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_168]), c_0_18])])).
% 2.83/3.04  cnf(c_0_171, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_hidden(k1_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0)), inference(spm,[status(thm)],[c_0_169, c_0_43])).
% 2.83/3.04  cnf(c_0_172, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0)|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))|~r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_170, c_0_145]), c_0_17])])).
% 2.83/3.04  cnf(c_0_173, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_171, c_0_128])).
% 2.83/3.04  cnf(c_0_174, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0)|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_172, c_0_173])).
% 2.83/3.04  cnf(c_0_175, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk4_0,esk6_0)|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_106, c_0_174])).
% 2.83/3.04  cnf(c_0_176, negated_conjecture, (r2_lattice3(esk3_0,esk4_0,esk6_0)|r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.83/3.04  cnf(c_0_177, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_175]), c_0_145])).
% 2.83/3.04  cnf(c_0_178, negated_conjecture, (r2_lattice3(esk3_0,esk5_0,esk6_0)|r2_lattice3(esk3_0,X1,esk6_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_80, c_0_176])).
% 2.83/3.04  cnf(c_0_179, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0)), inference(spm,[status(thm)],[c_0_81, c_0_177])).
% 2.83/3.04  cnf(c_0_180, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)|r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_178, c_0_179])).
% 2.83/3.04  cnf(c_0_181, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk5_0,esk6_0)|r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),esk6_0)|~m1_subset_1(k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_158, c_0_180])).
% 2.83/3.04  cnf(c_0_182, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_181, c_0_163]), c_0_25]), c_0_106])).
% 2.83/3.04  cnf(c_0_183, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_170, c_0_182]), c_0_17])]), c_0_173])).
% 2.83/3.04  fof(c_0_184, plain, ![X6]:~v1_xboole_0(k1_tarski(X6)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).
% 2.83/3.04  cnf(c_0_185, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,esk4_0,esk6_0)), inference(spm,[status(thm)],[c_0_106, c_0_183])).
% 2.83/3.04  cnf(c_0_186, plain, (~v1_xboole_0(k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_184])).
% 2.83/3.04  cnf(c_0_187, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_185]), c_0_182])).
% 2.83/3.04  cnf(c_0_188, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 2.83/3.04  cnf(c_0_189, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_186, c_0_187]), c_0_188])]), ['proof']).
% 2.83/3.04  # SZS output end CNFRefutation
% 2.83/3.04  # Proof object total steps             : 190
% 2.83/3.04  # Proof object clause steps            : 165
% 2.83/3.04  # Proof object formula steps           : 25
% 2.83/3.04  # Proof object conjectures             : 133
% 2.83/3.04  # Proof object clause conjectures      : 130
% 2.83/3.04  # Proof object formula conjectures     : 3
% 2.83/3.04  # Proof object initial clauses used    : 29
% 2.83/3.04  # Proof object initial formulas used   : 11
% 2.83/3.04  # Proof object generating inferences   : 135
% 2.83/3.04  # Proof object simplifying inferences  : 117
% 2.83/3.04  # Training examples: 0 positive, 0 negative
% 2.83/3.04  # Parsed axioms                        : 11
% 2.83/3.04  # Removed by relevancy pruning/SinE    : 0
% 2.83/3.04  # Initial clauses                      : 38
% 2.83/3.04  # Removed in clause preprocessing      : 0
% 2.83/3.04  # Initial clauses in saturation        : 38
% 2.83/3.04  # Processed clauses                    : 8195
% 2.83/3.04  # ...of these trivial                  : 202
% 2.83/3.04  # ...subsumed                          : 2929
% 2.83/3.04  # ...remaining for further processing  : 5064
% 2.83/3.04  # Other redundant clauses eliminated   : 2
% 2.83/3.04  # Clauses deleted for lack of memory   : 0
% 2.83/3.04  # Backward-subsumed                    : 2381
% 2.83/3.04  # Backward-rewritten                   : 1876
% 2.83/3.04  # Generated clauses                    : 33400
% 2.83/3.04  # ...of the previous two non-trivial   : 33227
% 2.83/3.04  # Contextual simplify-reflections      : 419
% 2.83/3.04  # Paramodulations                      : 33398
% 2.83/3.04  # Factorizations                       : 0
% 2.83/3.04  # Equation resolutions                 : 2
% 2.83/3.04  # Propositional unsat checks           : 0
% 2.83/3.04  #    Propositional check models        : 0
% 2.83/3.04  #    Propositional check unsatisfiable : 0
% 2.83/3.04  #    Propositional clauses             : 0
% 2.83/3.04  #    Propositional clauses after purity: 0
% 2.83/3.04  #    Propositional unsat core size     : 0
% 2.83/3.04  #    Propositional preprocessing time  : 0.000
% 2.83/3.04  #    Propositional encoding time       : 0.000
% 2.83/3.04  #    Propositional solver time         : 0.000
% 2.83/3.04  #    Success case prop preproc time    : 0.000
% 2.83/3.04  #    Success case prop encoding time   : 0.000
% 2.83/3.04  #    Success case prop solver time     : 0.000
% 2.83/3.04  # Current number of processed clauses  : 767
% 2.83/3.04  #    Positive orientable unit clauses  : 76
% 2.83/3.04  #    Positive unorientable unit clauses: 0
% 2.83/3.04  #    Negative unit clauses             : 2
% 2.83/3.04  #    Non-unit-clauses                  : 689
% 2.83/3.04  # Current number of unprocessed clauses: 22954
% 2.83/3.04  # ...number of literals in the above   : 141226
% 2.83/3.04  # Current number of archived formulas  : 0
% 2.83/3.04  # Current number of archived clauses   : 4295
% 2.83/3.04  # Clause-clause subsumption calls (NU) : 3445025
% 2.83/3.04  # Rec. Clause-clause subsumption calls : 446735
% 2.83/3.04  # Non-unit clause-clause subsumptions  : 5726
% 2.83/3.04  # Unit Clause-clause subsumption calls : 9897
% 2.83/3.04  # Rewrite failures with RHS unbound    : 0
% 2.83/3.04  # BW rewrite match attempts            : 1874
% 2.83/3.04  # BW rewrite match successes           : 24
% 2.83/3.04  # Condensation attempts                : 0
% 2.83/3.04  # Condensation successes               : 0
% 2.83/3.04  # Termbank termtop insertions          : 2078577
% 2.83/3.05  
% 2.83/3.05  # -------------------------------------------------
% 2.83/3.05  # User time                : 2.675 s
% 2.83/3.05  # System time              : 0.019 s
% 2.83/3.05  # Total time               : 2.695 s
% 2.83/3.05  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
