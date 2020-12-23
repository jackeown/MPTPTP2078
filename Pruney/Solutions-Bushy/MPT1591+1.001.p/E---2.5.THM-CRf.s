%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1591+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:27 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 549 expanded)
%              Number of clauses        :   61 ( 188 expanded)
%              Number of leaves         :   16 ( 132 expanded)
%              Depth                    :   13
%              Number of atoms          :  490 (5467 expanded)
%              Number of equality atoms :   29 ( 934 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   40 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t70_yellow_0,conjecture,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_yellow_0(X2,X1)
            & v5_yellow_0(X2,X1)
            & m1_yellow_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X2))
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X1))
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X1))
                         => ( ( X5 = X3
                              & X6 = X4 )
                           => k12_lattice3(X2,X3,X4) = k12_lattice3(X1,X5,X6) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_yellow_0)).

fof(redefinition_k7_domain_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1)
        & m1_subset_1(X3,X1) )
     => k7_domain_1(X1,X2,X3) = k2_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_domain_1)).

fof(t21_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ( v2_lattice3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => r2_yellow_0(X1,k2_tarski(X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_yellow_0)).

fof(d16_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_yellow_0(X2,X1)
         => ( v5_yellow_0(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( ( r2_hidden(X3,u1_struct_0(X2))
                        & r2_hidden(X4,u1_struct_0(X2))
                        & r2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X3,X4)) )
                     => r2_hidden(k2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X3,X4)),u1_struct_0(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_yellow_0)).

fof(t40_yellow_0,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => k2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) = k12_lattice3(X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_yellow_0)).

fof(cc2_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(dt_m1_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_yellow_0(X2,X1)
         => l1_orders_2(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_yellow_0)).

fof(cc6_yellow_0,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_yellow_0(X2,X1)
         => ( v4_yellow_0(X2,X1)
           => ( v3_orders_2(X2)
              & v4_yellow_0(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_yellow_0)).

fof(cc11_yellow_0,axiom,(
    ! [X1] :
      ( ( v4_orders_2(X1)
        & v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_yellow_0(X2,X1)
         => ( ( ~ v2_struct_0(X2)
              & v4_yellow_0(X2,X1)
              & v5_yellow_0(X2,X1) )
           => ( ~ v2_struct_0(X2)
              & v2_lattice3(X2)
              & v4_yellow_0(X2,X1)
              & v5_yellow_0(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc11_yellow_0)).

fof(cc8_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_yellow_0(X2,X1)
         => ( v4_yellow_0(X2,X1)
           => ( v5_orders_2(X2)
              & v4_yellow_0(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc8_yellow_0)).

fof(cc7_yellow_0,axiom,(
    ! [X1] :
      ( ( v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_yellow_0(X2,X1)
         => ( v4_yellow_0(X2,X1)
           => ( v4_orders_2(X2)
              & v4_yellow_0(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc7_yellow_0)).

fof(t64_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_yellow_0(X2,X1)
            & m1_yellow_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => ( ( r2_yellow_0(X1,X3)
                  & r2_hidden(k2_yellow_0(X1,X3),u1_struct_0(X2)) )
               => ( r2_yellow_0(X2,X3)
                  & k2_yellow_0(X2,X3) = k2_yellow_0(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_yellow_0)).

fof(dt_k7_domain_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1)
        & m1_subset_1(X3,X1) )
     => m1_subset_1(k7_domain_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_domain_1)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( ( v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & v2_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_yellow_0(X2,X1)
              & v5_yellow_0(X2,X1)
              & m1_yellow_0(X2,X1) )
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X2))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X2))
                   => ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X1))
                       => ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X1))
                           => ( ( X5 = X3
                                & X6 = X4 )
                             => k12_lattice3(X2,X3,X4) = k12_lattice3(X1,X5,X6) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t70_yellow_0])).

fof(c_0_17,plain,(
    ! [X29,X30,X31] :
      ( v1_xboole_0(X29)
      | ~ m1_subset_1(X30,X29)
      | ~ m1_subset_1(X31,X29)
      | k7_domain_1(X29,X30,X31) = k2_tarski(X30,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k7_domain_1])])])).

fof(c_0_18,negated_conjecture,
    ( v3_orders_2(esk5_0)
    & v4_orders_2(esk5_0)
    & v5_orders_2(esk5_0)
    & v2_lattice3(esk5_0)
    & l1_orders_2(esk5_0)
    & ~ v2_struct_0(esk6_0)
    & v4_yellow_0(esk6_0,esk5_0)
    & v5_yellow_0(esk6_0,esk5_0)
    & m1_yellow_0(esk6_0,esk5_0)
    & m1_subset_1(esk7_0,u1_struct_0(esk6_0))
    & m1_subset_1(esk8_0,u1_struct_0(esk6_0))
    & m1_subset_1(esk9_0,u1_struct_0(esk5_0))
    & m1_subset_1(esk10_0,u1_struct_0(esk5_0))
    & esk9_0 = esk7_0
    & esk10_0 = esk8_0
    & k12_lattice3(esk6_0,esk7_0,esk8_0) != k12_lattice3(esk5_0,esk9_0,esk10_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).

cnf(c_0_19,plain,
    ( v1_xboole_0(X1)
    | k7_domain_1(X1,X2,X3) = k2_tarski(X2,X3)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk10_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk9_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( esk9_0 = esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( esk10_0 = esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X32,X33,X34] :
      ( ( ~ v2_lattice3(X32)
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | ~ m1_subset_1(X34,u1_struct_0(X32))
        | r2_yellow_0(X32,k2_tarski(X33,X34))
        | ~ v5_orders_2(X32)
        | ~ l1_orders_2(X32) )
      & ( m1_subset_1(esk3_1(X32),u1_struct_0(X32))
        | v2_lattice3(X32)
        | ~ v5_orders_2(X32)
        | ~ l1_orders_2(X32) )
      & ( m1_subset_1(esk4_1(X32),u1_struct_0(X32))
        | v2_lattice3(X32)
        | ~ v5_orders_2(X32)
        | ~ l1_orders_2(X32) )
      & ( ~ r2_yellow_0(X32,k2_tarski(esk3_1(X32),esk4_1(X32)))
        | v2_lattice3(X32)
        | ~ v5_orders_2(X32)
        | ~ l1_orders_2(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_yellow_0])])])])])).

cnf(c_0_26,negated_conjecture,
    ( k2_tarski(X1,esk10_0) = k7_domain_1(u1_struct_0(esk5_0),X1,esk10_0)
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk10_0,u1_struct_0(esk6_0)) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_29,plain,(
    ! [X16,X17,X18,X19] :
      ( ( ~ v5_yellow_0(X17,X16)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ r2_hidden(X18,u1_struct_0(X17))
        | ~ r2_hidden(X19,u1_struct_0(X17))
        | ~ r2_yellow_0(X16,k7_domain_1(u1_struct_0(X16),X18,X19))
        | r2_hidden(k2_yellow_0(X16,k7_domain_1(u1_struct_0(X16),X18,X19)),u1_struct_0(X17))
        | ~ m1_yellow_0(X17,X16)
        | v2_struct_0(X16)
        | ~ l1_orders_2(X16) )
      & ( m1_subset_1(esk1_2(X16,X17),u1_struct_0(X16))
        | v5_yellow_0(X17,X16)
        | ~ m1_yellow_0(X17,X16)
        | v2_struct_0(X16)
        | ~ l1_orders_2(X16) )
      & ( m1_subset_1(esk2_2(X16,X17),u1_struct_0(X16))
        | v5_yellow_0(X17,X16)
        | ~ m1_yellow_0(X17,X16)
        | v2_struct_0(X16)
        | ~ l1_orders_2(X16) )
      & ( r2_hidden(esk1_2(X16,X17),u1_struct_0(X17))
        | v5_yellow_0(X17,X16)
        | ~ m1_yellow_0(X17,X16)
        | v2_struct_0(X16)
        | ~ l1_orders_2(X16) )
      & ( r2_hidden(esk2_2(X16,X17),u1_struct_0(X17))
        | v5_yellow_0(X17,X16)
        | ~ m1_yellow_0(X17,X16)
        | v2_struct_0(X16)
        | ~ l1_orders_2(X16) )
      & ( r2_yellow_0(X16,k7_domain_1(u1_struct_0(X16),esk1_2(X16,X17),esk2_2(X16,X17)))
        | v5_yellow_0(X17,X16)
        | ~ m1_yellow_0(X17,X16)
        | v2_struct_0(X16)
        | ~ l1_orders_2(X16) )
      & ( ~ r2_hidden(k2_yellow_0(X16,k7_domain_1(u1_struct_0(X16),esk1_2(X16,X17),esk2_2(X16,X17))),u1_struct_0(X17))
        | v5_yellow_0(X17,X16)
        | ~ m1_yellow_0(X17,X16)
        | v2_struct_0(X16)
        | ~ l1_orders_2(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_yellow_0])])])])])])).

fof(c_0_30,plain,(
    ! [X39,X40,X41] :
      ( ~ v3_orders_2(X39)
      | ~ v4_orders_2(X39)
      | ~ v5_orders_2(X39)
      | ~ v2_lattice3(X39)
      | ~ l1_orders_2(X39)
      | ~ m1_subset_1(X40,u1_struct_0(X39))
      | ~ m1_subset_1(X41,u1_struct_0(X39))
      | k2_yellow_0(X39,k7_domain_1(u1_struct_0(X39),X40,X41)) = k12_lattice3(X39,X40,X41) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t40_yellow_0])])])).

fof(c_0_31,plain,(
    ! [X9] :
      ( ~ l1_orders_2(X9)
      | ~ v2_lattice3(X9)
      | ~ v2_struct_0(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

cnf(c_0_32,plain,
    ( r2_yellow_0(X1,k2_tarski(X2,X3))
    | ~ v2_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( k2_tarski(esk7_0,esk10_0) = k7_domain_1(u1_struct_0(esk5_0),esk7_0,esk10_0)
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_34,plain,(
    ! [X28] :
      ( v2_struct_0(X28)
      | ~ l1_struct_0(X28)
      | ~ v1_xboole_0(u1_struct_0(X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_35,plain,(
    ! [X25] :
      ( ~ l1_orders_2(X25)
      | l1_struct_0(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_36,plain,(
    ! [X37,X38] :
      ( ~ m1_subset_1(X37,X38)
      | v1_xboole_0(X38)
      | r2_hidden(X37,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_37,plain,(
    ! [X26,X27] :
      ( ~ l1_orders_2(X26)
      | ~ m1_yellow_0(X27,X26)
      | l1_orders_2(X27) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_yellow_0])])])).

cnf(c_0_38,negated_conjecture,
    ( k2_tarski(X1,esk10_0) = k7_domain_1(u1_struct_0(esk6_0),X1,esk10_0)
    | v1_xboole_0(u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_28])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_40,plain,(
    ! [X10,X11] :
      ( ( v3_orders_2(X11)
        | ~ v4_yellow_0(X11,X10)
        | ~ m1_yellow_0(X11,X10)
        | ~ v3_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( v4_yellow_0(X11,X10)
        | ~ v4_yellow_0(X11,X10)
        | ~ m1_yellow_0(X11,X10)
        | ~ v3_orders_2(X10)
        | ~ l1_orders_2(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc6_yellow_0])])])])).

fof(c_0_41,plain,(
    ! [X7,X8] :
      ( ( ~ v2_struct_0(X8)
        | v2_struct_0(X8)
        | ~ v4_yellow_0(X8,X7)
        | ~ v5_yellow_0(X8,X7)
        | ~ m1_yellow_0(X8,X7)
        | ~ v4_orders_2(X7)
        | ~ v5_orders_2(X7)
        | ~ v2_lattice3(X7)
        | ~ l1_orders_2(X7) )
      & ( v2_lattice3(X8)
        | v2_struct_0(X8)
        | ~ v4_yellow_0(X8,X7)
        | ~ v5_yellow_0(X8,X7)
        | ~ m1_yellow_0(X8,X7)
        | ~ v4_orders_2(X7)
        | ~ v5_orders_2(X7)
        | ~ v2_lattice3(X7)
        | ~ l1_orders_2(X7) )
      & ( v4_yellow_0(X8,X7)
        | v2_struct_0(X8)
        | ~ v4_yellow_0(X8,X7)
        | ~ v5_yellow_0(X8,X7)
        | ~ m1_yellow_0(X8,X7)
        | ~ v4_orders_2(X7)
        | ~ v5_orders_2(X7)
        | ~ v2_lattice3(X7)
        | ~ l1_orders_2(X7) )
      & ( v5_yellow_0(X8,X7)
        | v2_struct_0(X8)
        | ~ v4_yellow_0(X8,X7)
        | ~ v5_yellow_0(X8,X7)
        | ~ m1_yellow_0(X8,X7)
        | ~ v4_orders_2(X7)
        | ~ v5_orders_2(X7)
        | ~ v2_lattice3(X7)
        | ~ l1_orders_2(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc11_yellow_0])])])])])).

fof(c_0_42,plain,(
    ! [X14,X15] :
      ( ( v5_orders_2(X15)
        | ~ v4_yellow_0(X15,X14)
        | ~ m1_yellow_0(X15,X14)
        | ~ v5_orders_2(X14)
        | ~ l1_orders_2(X14) )
      & ( v4_yellow_0(X15,X14)
        | ~ v4_yellow_0(X15,X14)
        | ~ m1_yellow_0(X15,X14)
        | ~ v5_orders_2(X14)
        | ~ l1_orders_2(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc8_yellow_0])])])])).

fof(c_0_43,plain,(
    ! [X12,X13] :
      ( ( v4_orders_2(X13)
        | ~ v4_yellow_0(X13,X12)
        | ~ m1_yellow_0(X13,X12)
        | ~ v4_orders_2(X12)
        | ~ l1_orders_2(X12) )
      & ( v4_yellow_0(X13,X12)
        | ~ v4_yellow_0(X13,X12)
        | ~ m1_yellow_0(X13,X12)
        | ~ v4_orders_2(X12)
        | ~ l1_orders_2(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc7_yellow_0])])])])).

cnf(c_0_44,plain,
    ( r2_hidden(k2_yellow_0(X2,k7_domain_1(u1_struct_0(X2),X3,X4)),u1_struct_0(X1))
    | v2_struct_0(X2)
    | ~ v5_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X3,u1_struct_0(X1))
    | ~ r2_hidden(X4,u1_struct_0(X1))
    | ~ r2_yellow_0(X2,k7_domain_1(u1_struct_0(X2),X3,X4))
    | ~ m1_yellow_0(X1,X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_45,plain,
    ( k2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) = k12_lattice3(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_46,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_47,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | r2_yellow_0(X1,k7_domain_1(u1_struct_0(esk5_0),esk7_0,esk10_0))
    | ~ m1_subset_1(esk10_0,u1_struct_0(X1))
    | ~ m1_subset_1(esk7_0,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_48,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_49,negated_conjecture,
    ( v2_lattice3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_50,negated_conjecture,
    ( v5_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_51,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_52,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_53,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_54,plain,
    ( l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ m1_yellow_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_55,negated_conjecture,
    ( m1_yellow_0(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_56,plain,(
    ! [X42,X43,X44] :
      ( ( r2_yellow_0(X43,X44)
        | ~ r2_yellow_0(X42,X44)
        | ~ r2_hidden(k2_yellow_0(X42,X44),u1_struct_0(X43))
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
        | v2_struct_0(X43)
        | ~ v4_yellow_0(X43,X42)
        | ~ m1_yellow_0(X43,X42)
        | v2_struct_0(X42)
        | ~ v4_orders_2(X42)
        | ~ l1_orders_2(X42) )
      & ( k2_yellow_0(X43,X44) = k2_yellow_0(X42,X44)
        | ~ r2_yellow_0(X42,X44)
        | ~ r2_hidden(k2_yellow_0(X42,X44),u1_struct_0(X43))
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
        | v2_struct_0(X43)
        | ~ v4_yellow_0(X43,X42)
        | ~ m1_yellow_0(X43,X42)
        | v2_struct_0(X42)
        | ~ v4_orders_2(X42)
        | ~ l1_orders_2(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t64_yellow_0])])])])])).

cnf(c_0_57,negated_conjecture,
    ( k2_tarski(esk7_0,esk10_0) = k7_domain_1(u1_struct_0(esk6_0),esk7_0,esk10_0)
    | v1_xboole_0(u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_58,plain,
    ( v3_orders_2(X1)
    | ~ v4_yellow_0(X1,X2)
    | ~ m1_yellow_0(X1,X2)
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_59,negated_conjecture,
    ( v4_yellow_0(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_60,negated_conjecture,
    ( v3_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_61,plain,
    ( v2_lattice3(X1)
    | v2_struct_0(X1)
    | ~ v4_yellow_0(X1,X2)
    | ~ v5_yellow_0(X1,X2)
    | ~ m1_yellow_0(X1,X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_62,negated_conjecture,
    ( v5_yellow_0(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_63,negated_conjecture,
    ( v4_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_64,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_65,plain,
    ( v5_orders_2(X1)
    | ~ v4_yellow_0(X1,X2)
    | ~ m1_yellow_0(X1,X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_66,plain,
    ( v4_orders_2(X1)
    | ~ v4_yellow_0(X1,X2)
    | ~ m1_yellow_0(X1,X2)
    | ~ v4_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_67,plain,
    ( r2_hidden(k12_lattice3(X1,X2,X3),u1_struct_0(X4))
    | ~ r2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3))
    | ~ r2_hidden(X3,u1_struct_0(X4))
    | ~ r2_hidden(X2,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v5_yellow_0(X4,X1)
    | ~ m1_yellow_0(X4,X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])).

cnf(c_0_68,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | r2_yellow_0(esk5_0,k7_domain_1(u1_struct_0(esk5_0),esk7_0,esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_20]),c_0_27]),c_0_48]),c_0_49]),c_0_50])])).

cnf(c_0_69,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_70,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk6_0))
    | r2_hidden(esk10_0,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_28])).

cnf(c_0_71,negated_conjecture,
    ( l1_orders_2(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_48])])).

cnf(c_0_72,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk6_0))
    | r2_hidden(esk7_0,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_39])).

cnf(c_0_73,plain,
    ( k2_yellow_0(X1,X2) = k2_yellow_0(X3,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ r2_yellow_0(X3,X2)
    | ~ r2_hidden(k2_yellow_0(X3,X2),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_yellow_0(X1,X3)
    | ~ m1_yellow_0(X1,X3)
    | ~ v4_orders_2(X3)
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_74,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk6_0),esk7_0,esk10_0) = k7_domain_1(u1_struct_0(esk5_0),esk7_0,esk10_0)
    | v1_xboole_0(u1_struct_0(esk6_0))
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_57]),c_0_27])])).

cnf(c_0_75,negated_conjecture,
    ( v3_orders_2(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60]),c_0_55]),c_0_48])])).

cnf(c_0_76,negated_conjecture,
    ( v2_lattice3(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_59]),c_0_55]),c_0_48]),c_0_49]),c_0_50]),c_0_63])]),c_0_64])).

cnf(c_0_77,negated_conjecture,
    ( v5_orders_2(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_59]),c_0_55]),c_0_48]),c_0_50])])).

cnf(c_0_78,negated_conjecture,
    ( v4_orders_2(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_59]),c_0_55]),c_0_48]),c_0_63])])).

cnf(c_0_79,negated_conjecture,
    ( k12_lattice3(esk6_0,esk7_0,esk8_0) != k12_lattice3(esk5_0,esk9_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_80,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | r2_hidden(k12_lattice3(esk5_0,esk7_0,esk10_0),u1_struct_0(X1))
    | ~ r2_hidden(esk10_0,u1_struct_0(X1))
    | ~ r2_hidden(esk7_0,u1_struct_0(X1))
    | ~ v5_yellow_0(X1,esk5_0)
    | ~ m1_yellow_0(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_20]),c_0_27]),c_0_60]),c_0_48]),c_0_49]),c_0_50]),c_0_63])])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk10_0,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])]),c_0_64])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk7_0,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_72]),c_0_71])]),c_0_64])).

fof(c_0_83,plain,(
    ! [X22,X23,X24] :
      ( v1_xboole_0(X22)
      | ~ m1_subset_1(X23,X22)
      | ~ m1_subset_1(X24,X22)
      | m1_subset_1(k7_domain_1(X22,X23,X24),k1_zfmisc_1(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_domain_1])])])).

cnf(c_0_84,plain,
    ( k2_yellow_0(X1,k7_domain_1(u1_struct_0(X2),X3,X4)) = k12_lattice3(X2,X3,X4)
    | v2_struct_0(X1)
    | ~ r2_yellow_0(X2,k7_domain_1(u1_struct_0(X2),X3,X4))
    | ~ r2_hidden(k12_lattice3(X2,X3,X4),u1_struct_0(X1))
    | ~ m1_subset_1(k7_domain_1(u1_struct_0(X2),X3,X4),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v3_orders_2(X2)
    | ~ v4_yellow_0(X1,X2)
    | ~ m1_yellow_0(X1,X2)
    | ~ l1_orders_2(X2)
    | ~ v2_lattice3(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_45]),c_0_46])).

cnf(c_0_85,negated_conjecture,
    ( k2_yellow_0(esk6_0,k7_domain_1(u1_struct_0(esk5_0),esk7_0,esk10_0)) = k12_lattice3(esk6_0,esk7_0,esk10_0)
    | v1_xboole_0(u1_struct_0(esk5_0))
    | v1_xboole_0(u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_74]),c_0_28]),c_0_39]),c_0_75]),c_0_71]),c_0_76]),c_0_77]),c_0_78])])).

cnf(c_0_86,negated_conjecture,
    ( k12_lattice3(esk6_0,esk7_0,esk10_0) != k12_lattice3(esk5_0,esk7_0,esk10_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_24]),c_0_22])).

cnf(c_0_87,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | r2_hidden(k12_lattice3(esk5_0,esk7_0,esk10_0),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82]),c_0_62]),c_0_55])])).

cnf(c_0_88,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k7_domain_1(X1,X2,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_89,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk6_0))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ m1_subset_1(k7_domain_1(u1_struct_0(esk5_0),esk7_0,esk10_0),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_20]),c_0_27]),c_0_60]),c_0_59]),c_0_55]),c_0_48]),c_0_49]),c_0_50]),c_0_63])]),c_0_86]),c_0_64]),c_0_87]),c_0_68])).

cnf(c_0_90,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | v1_xboole_0(u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_74]),c_0_28]),c_0_39])]),c_0_89])).

cnf(c_0_91,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_90]),c_0_71])]),c_0_64])).

cnf(c_0_92,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_49]),c_0_48])])).

cnf(c_0_93,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_91]),c_0_48])]),c_0_92]),
    [proof]).

%------------------------------------------------------------------------------
