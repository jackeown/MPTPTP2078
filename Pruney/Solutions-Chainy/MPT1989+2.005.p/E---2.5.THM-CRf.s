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
% DateTime   : Thu Dec  3 11:21:31 EST 2020

% Result     : Theorem 0.40s
% Output     : CNFRefutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 576 expanded)
%              Number of clauses        :   60 ( 196 expanded)
%              Number of leaves         :   15 ( 141 expanded)
%              Depth                    :   11
%              Number of atoms          :  625 (3899 expanded)
%              Number of equality atoms :   30 (  44 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal clause size      :   74 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t38_waybel_7,conjecture,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( v5_waybel_6(X2,X1)
           => v4_waybel_7(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_waybel_7)).

fof(cc2_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

fof(l28_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( X4 = k11_lattice3(X1,X2,X3)
                  <=> ( r1_orders_2(X1,X4,X2)
                      & r1_orders_2(X1,X4,X3)
                      & ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r1_orders_2(X1,X5,X2)
                              & r1_orders_2(X1,X5,X3) )
                           => r1_orders_2(X1,X5,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l28_lattice3)).

fof(dt_k11_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_lattice3)).

fof(d6_waybel_6,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( v5_waybel_6(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ~ ( r1_orders_2(X1,k11_lattice3(X1,X3,X4),X2)
                        & ~ r1_orders_2(X1,X3,X2)
                        & ~ r1_orders_2(X1,X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_waybel_6)).

fof(dt_k5_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k5_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_waybel_0)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t17_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_hidden(X3,k5_waybel_0(X1,X2))
              <=> r1_orders_2(X1,X3,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_waybel_0)).

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

fof(d6_waybel_7,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( v4_waybel_7(X2,X1)
          <=> ? [X3] :
                ( ~ v1_xboole_0(X3)
                & v1_waybel_0(X3,X1)
                & v12_waybel_0(X3,X1)
                & v1_waybel_7(X3,X1)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                & X2 = k1_yellow_0(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_waybel_7)).

fof(dt_k1_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(t37_waybel_7,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( v5_waybel_6(X2,X1)
           => v1_waybel_7(k5_waybel_0(X1,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_waybel_7)).

fof(fc8_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v1_xboole_0(k5_waybel_0(X1,X2))
        & v1_waybel_0(k5_waybel_0(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_waybel_0)).

fof(fc12_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => v12_waybel_0(k5_waybel_0(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_waybel_0)).

fof(t30_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( ( X2 = k1_yellow_0(X1,X3)
                  & r1_yellow_0(X1,X3) )
               => ( r2_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r2_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X2,X4) ) ) ) )
              & ( ( r2_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r2_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X2,X4) ) ) )
               => ( X2 = k1_yellow_0(X1,X3)
                  & r1_yellow_0(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_yellow_0)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( ( v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & v1_lattice3(X1)
          & v2_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( v5_waybel_6(X2,X1)
             => v4_waybel_7(X2,X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t38_waybel_7])).

fof(c_0_16,plain,(
    ! [X9] :
      ( ~ l1_orders_2(X9)
      | ~ v2_lattice3(X9)
      | ~ v2_struct_0(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

fof(c_0_17,negated_conjecture,
    ( v3_orders_2(esk7_0)
    & v4_orders_2(esk7_0)
    & v5_orders_2(esk7_0)
    & v1_lattice3(esk7_0)
    & v2_lattice3(esk7_0)
    & l1_orders_2(esk7_0)
    & m1_subset_1(esk8_0,u1_struct_0(esk7_0))
    & v5_waybel_6(esk8_0,esk7_0)
    & ~ v4_waybel_7(esk8_0,esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_18,plain,(
    ! [X18,X19,X20,X21,X22] :
      ( ( r1_orders_2(X18,X21,X19)
        | X21 != k11_lattice3(X18,X19,X20)
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | v2_struct_0(X18)
        | ~ v5_orders_2(X18)
        | ~ v2_lattice3(X18)
        | ~ l1_orders_2(X18) )
      & ( r1_orders_2(X18,X21,X20)
        | X21 != k11_lattice3(X18,X19,X20)
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | v2_struct_0(X18)
        | ~ v5_orders_2(X18)
        | ~ v2_lattice3(X18)
        | ~ l1_orders_2(X18) )
      & ( ~ m1_subset_1(X22,u1_struct_0(X18))
        | ~ r1_orders_2(X18,X22,X19)
        | ~ r1_orders_2(X18,X22,X20)
        | r1_orders_2(X18,X22,X21)
        | X21 != k11_lattice3(X18,X19,X20)
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | v2_struct_0(X18)
        | ~ v5_orders_2(X18)
        | ~ v2_lattice3(X18)
        | ~ l1_orders_2(X18) )
      & ( m1_subset_1(esk2_4(X18,X19,X20,X21),u1_struct_0(X18))
        | ~ r1_orders_2(X18,X21,X19)
        | ~ r1_orders_2(X18,X21,X20)
        | X21 = k11_lattice3(X18,X19,X20)
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | v2_struct_0(X18)
        | ~ v5_orders_2(X18)
        | ~ v2_lattice3(X18)
        | ~ l1_orders_2(X18) )
      & ( r1_orders_2(X18,esk2_4(X18,X19,X20,X21),X19)
        | ~ r1_orders_2(X18,X21,X19)
        | ~ r1_orders_2(X18,X21,X20)
        | X21 = k11_lattice3(X18,X19,X20)
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | v2_struct_0(X18)
        | ~ v5_orders_2(X18)
        | ~ v2_lattice3(X18)
        | ~ l1_orders_2(X18) )
      & ( r1_orders_2(X18,esk2_4(X18,X19,X20,X21),X20)
        | ~ r1_orders_2(X18,X21,X19)
        | ~ r1_orders_2(X18,X21,X20)
        | X21 = k11_lattice3(X18,X19,X20)
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | v2_struct_0(X18)
        | ~ v5_orders_2(X18)
        | ~ v2_lattice3(X18)
        | ~ l1_orders_2(X18) )
      & ( ~ r1_orders_2(X18,esk2_4(X18,X19,X20,X21),X21)
        | ~ r1_orders_2(X18,X21,X19)
        | ~ r1_orders_2(X18,X21,X20)
        | X21 = k11_lattice3(X18,X19,X20)
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | v2_struct_0(X18)
        | ~ v5_orders_2(X18)
        | ~ v2_lattice3(X18)
        | ~ l1_orders_2(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l28_lattice3])])])])])])).

fof(c_0_19,plain,(
    ! [X15,X16,X17] :
      ( ~ l1_orders_2(X15)
      | ~ m1_subset_1(X16,u1_struct_0(X15))
      | ~ m1_subset_1(X17,u1_struct_0(X15))
      | m1_subset_1(k11_lattice3(X15,X16,X17),u1_struct_0(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_lattice3])])).

fof(c_0_20,plain,(
    ! [X41,X42,X43,X44] :
      ( ( ~ v5_waybel_6(X42,X41)
        | ~ m1_subset_1(X43,u1_struct_0(X41))
        | ~ m1_subset_1(X44,u1_struct_0(X41))
        | ~ r1_orders_2(X41,k11_lattice3(X41,X43,X44),X42)
        | r1_orders_2(X41,X43,X42)
        | r1_orders_2(X41,X44,X42)
        | ~ m1_subset_1(X42,u1_struct_0(X41))
        | v2_struct_0(X41)
        | ~ l1_orders_2(X41) )
      & ( m1_subset_1(esk4_2(X41,X42),u1_struct_0(X41))
        | v5_waybel_6(X42,X41)
        | ~ m1_subset_1(X42,u1_struct_0(X41))
        | v2_struct_0(X41)
        | ~ l1_orders_2(X41) )
      & ( m1_subset_1(esk5_2(X41,X42),u1_struct_0(X41))
        | v5_waybel_6(X42,X41)
        | ~ m1_subset_1(X42,u1_struct_0(X41))
        | v2_struct_0(X41)
        | ~ l1_orders_2(X41) )
      & ( r1_orders_2(X41,k11_lattice3(X41,esk4_2(X41,X42),esk5_2(X41,X42)),X42)
        | v5_waybel_6(X42,X41)
        | ~ m1_subset_1(X42,u1_struct_0(X41))
        | v2_struct_0(X41)
        | ~ l1_orders_2(X41) )
      & ( ~ r1_orders_2(X41,esk4_2(X41,X42),X42)
        | v5_waybel_6(X42,X41)
        | ~ m1_subset_1(X42,u1_struct_0(X41))
        | v2_struct_0(X41)
        | ~ l1_orders_2(X41) )
      & ( ~ r1_orders_2(X41,esk5_2(X41,X42),X42)
        | v5_waybel_6(X42,X41)
        | ~ m1_subset_1(X42,u1_struct_0(X41))
        | v2_struct_0(X41)
        | ~ l1_orders_2(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_waybel_6])])])])])])).

cnf(c_0_21,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( v2_lattice3(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( l1_orders_2(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | X2 != k11_lattice3(X1,X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,plain,(
    ! [X32,X33] :
      ( v2_struct_0(X32)
      | ~ l1_orders_2(X32)
      | ~ m1_subset_1(X33,u1_struct_0(X32))
      | m1_subset_1(k5_waybel_0(X32,X33),k1_zfmisc_1(u1_struct_0(X32))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_waybel_0])])])).

cnf(c_0_27,plain,
    ( r1_orders_2(X2,X3,X1)
    | r1_orders_2(X2,X4,X1)
    | v2_struct_0(X2)
    | ~ v5_waybel_6(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r1_orders_2(X2,k11_lattice3(X2,X3,X4),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_30,plain,
    ( r1_orders_2(X1,k11_lattice3(X1,X2,X3),X3)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_24,c_0_21])]),c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( v5_orders_2(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_32,plain,(
    ! [X6,X7,X8] :
      ( ~ r2_hidden(X6,X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X8))
      | m1_subset_1(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_33,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_34,plain,(
    ! [X38,X39,X40] :
      ( ( ~ r2_hidden(X40,k5_waybel_0(X38,X39))
        | r1_orders_2(X38,X40,X39)
        | ~ m1_subset_1(X40,u1_struct_0(X38))
        | ~ m1_subset_1(X39,u1_struct_0(X38))
        | v2_struct_0(X38)
        | ~ l1_orders_2(X38) )
      & ( ~ r1_orders_2(X38,X40,X39)
        | r2_hidden(X40,k5_waybel_0(X38,X39))
        | ~ m1_subset_1(X40,u1_struct_0(X38))
        | ~ m1_subset_1(X39,u1_struct_0(X38))
        | v2_struct_0(X38)
        | ~ l1_orders_2(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t17_waybel_0])])])])])).

cnf(c_0_35,negated_conjecture,
    ( r1_orders_2(esk7_0,esk8_0,X1)
    | r1_orders_2(esk7_0,X2,X1)
    | ~ v5_waybel_6(X1,esk7_0)
    | ~ r1_orders_2(esk7_0,k11_lattice3(esk7_0,X2,esk8_0),X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_23])]),c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( v5_waybel_6(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_37,negated_conjecture,
    ( r1_orders_2(esk7_0,k11_lattice3(esk7_0,esk8_0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_28]),c_0_31]),c_0_22]),c_0_23])])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(k5_waybel_0(esk7_0,esk8_0),k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_28]),c_0_23])]),c_0_29])).

fof(c_0_40,plain,(
    ! [X10,X11,X12,X13] :
      ( ( ~ r2_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r2_hidden(X13,X11)
        | r1_orders_2(X10,X13,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ l1_orders_2(X10) )
      & ( m1_subset_1(esk1_3(X10,X11,X12),u1_struct_0(X10))
        | r2_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ l1_orders_2(X10) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ l1_orders_2(X10) )
      & ( ~ r1_orders_2(X10,esk1_3(X10,X11,X12),X12)
        | r2_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ l1_orders_2(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

fof(c_0_41,plain,(
    ! [X47,X48,X50] :
      ( ( ~ v1_xboole_0(esk6_2(X47,X48))
        | ~ v4_waybel_7(X48,X47)
        | ~ m1_subset_1(X48,u1_struct_0(X47))
        | ~ v3_orders_2(X47)
        | ~ v4_orders_2(X47)
        | ~ v5_orders_2(X47)
        | ~ v1_lattice3(X47)
        | ~ v2_lattice3(X47)
        | ~ l1_orders_2(X47) )
      & ( v1_waybel_0(esk6_2(X47,X48),X47)
        | ~ v4_waybel_7(X48,X47)
        | ~ m1_subset_1(X48,u1_struct_0(X47))
        | ~ v3_orders_2(X47)
        | ~ v4_orders_2(X47)
        | ~ v5_orders_2(X47)
        | ~ v1_lattice3(X47)
        | ~ v2_lattice3(X47)
        | ~ l1_orders_2(X47) )
      & ( v12_waybel_0(esk6_2(X47,X48),X47)
        | ~ v4_waybel_7(X48,X47)
        | ~ m1_subset_1(X48,u1_struct_0(X47))
        | ~ v3_orders_2(X47)
        | ~ v4_orders_2(X47)
        | ~ v5_orders_2(X47)
        | ~ v1_lattice3(X47)
        | ~ v2_lattice3(X47)
        | ~ l1_orders_2(X47) )
      & ( v1_waybel_7(esk6_2(X47,X48),X47)
        | ~ v4_waybel_7(X48,X47)
        | ~ m1_subset_1(X48,u1_struct_0(X47))
        | ~ v3_orders_2(X47)
        | ~ v4_orders_2(X47)
        | ~ v5_orders_2(X47)
        | ~ v1_lattice3(X47)
        | ~ v2_lattice3(X47)
        | ~ l1_orders_2(X47) )
      & ( m1_subset_1(esk6_2(X47,X48),k1_zfmisc_1(u1_struct_0(X47)))
        | ~ v4_waybel_7(X48,X47)
        | ~ m1_subset_1(X48,u1_struct_0(X47))
        | ~ v3_orders_2(X47)
        | ~ v4_orders_2(X47)
        | ~ v5_orders_2(X47)
        | ~ v1_lattice3(X47)
        | ~ v2_lattice3(X47)
        | ~ l1_orders_2(X47) )
      & ( X48 = k1_yellow_0(X47,esk6_2(X47,X48))
        | ~ v4_waybel_7(X48,X47)
        | ~ m1_subset_1(X48,u1_struct_0(X47))
        | ~ v3_orders_2(X47)
        | ~ v4_orders_2(X47)
        | ~ v5_orders_2(X47)
        | ~ v1_lattice3(X47)
        | ~ v2_lattice3(X47)
        | ~ l1_orders_2(X47) )
      & ( v1_xboole_0(X50)
        | ~ v1_waybel_0(X50,X47)
        | ~ v12_waybel_0(X50,X47)
        | ~ v1_waybel_7(X50,X47)
        | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X47)))
        | X48 != k1_yellow_0(X47,X50)
        | v4_waybel_7(X48,X47)
        | ~ m1_subset_1(X48,u1_struct_0(X47))
        | ~ v3_orders_2(X47)
        | ~ v4_orders_2(X47)
        | ~ v5_orders_2(X47)
        | ~ v1_lattice3(X47)
        | ~ v2_lattice3(X47)
        | ~ l1_orders_2(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_waybel_7])])])])])])).

fof(c_0_42,plain,(
    ! [X24,X25] :
      ( ~ l1_orders_2(X24)
      | m1_subset_1(k1_yellow_0(X24,X25),u1_struct_0(X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

fof(c_0_43,plain,(
    ! [X51,X52] :
      ( ~ v3_orders_2(X51)
      | ~ v4_orders_2(X51)
      | ~ v5_orders_2(X51)
      | ~ v1_lattice3(X51)
      | ~ v2_lattice3(X51)
      | ~ l1_orders_2(X51)
      | ~ m1_subset_1(X52,u1_struct_0(X51))
      | ~ v5_waybel_6(X52,X51)
      | v1_waybel_7(k5_waybel_0(X51,X52),X51) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_waybel_7])])])).

fof(c_0_44,plain,(
    ! [X36,X37] :
      ( ( ~ v1_xboole_0(k5_waybel_0(X36,X37))
        | v2_struct_0(X36)
        | ~ v3_orders_2(X36)
        | ~ l1_orders_2(X36)
        | ~ m1_subset_1(X37,u1_struct_0(X36)) )
      & ( v1_waybel_0(k5_waybel_0(X36,X37),X36)
        | v2_struct_0(X36)
        | ~ v3_orders_2(X36)
        | ~ l1_orders_2(X36)
        | ~ m1_subset_1(X37,u1_struct_0(X36)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc8_waybel_0])])])])).

fof(c_0_45,plain,(
    ! [X34,X35] :
      ( v2_struct_0(X34)
      | ~ v4_orders_2(X34)
      | ~ l1_orders_2(X34)
      | ~ m1_subset_1(X35,u1_struct_0(X34))
      | v12_waybel_0(k5_waybel_0(X34,X35),X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc12_waybel_0])])])).

cnf(c_0_46,plain,
    ( r2_hidden(X2,k5_waybel_0(X1,X3))
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,negated_conjecture,
    ( r1_orders_2(esk7_0,esk8_0,esk8_0)
    | r1_orders_2(esk7_0,X1,esk8_0)
    | ~ r1_orders_2(esk7_0,k11_lattice3(esk7_0,X1,esk8_0),esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_28])])).

cnf(c_0_48,negated_conjecture,
    ( r1_orders_2(esk7_0,k11_lattice3(esk7_0,esk8_0,esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_28])).

fof(c_0_49,plain,(
    ! [X26,X27,X28,X29,X30] :
      ( ( r2_lattice3(X26,X28,X27)
        | X27 != k1_yellow_0(X26,X28)
        | ~ r1_yellow_0(X26,X28)
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | ~ v5_orders_2(X26)
        | ~ l1_orders_2(X26) )
      & ( ~ m1_subset_1(X29,u1_struct_0(X26))
        | ~ r2_lattice3(X26,X28,X29)
        | r1_orders_2(X26,X27,X29)
        | X27 != k1_yellow_0(X26,X28)
        | ~ r1_yellow_0(X26,X28)
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | ~ v5_orders_2(X26)
        | ~ l1_orders_2(X26) )
      & ( X27 = k1_yellow_0(X26,X30)
        | m1_subset_1(esk3_3(X26,X27,X30),u1_struct_0(X26))
        | ~ r2_lattice3(X26,X30,X27)
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | ~ v5_orders_2(X26)
        | ~ l1_orders_2(X26) )
      & ( r1_yellow_0(X26,X30)
        | m1_subset_1(esk3_3(X26,X27,X30),u1_struct_0(X26))
        | ~ r2_lattice3(X26,X30,X27)
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | ~ v5_orders_2(X26)
        | ~ l1_orders_2(X26) )
      & ( X27 = k1_yellow_0(X26,X30)
        | r2_lattice3(X26,X30,esk3_3(X26,X27,X30))
        | ~ r2_lattice3(X26,X30,X27)
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | ~ v5_orders_2(X26)
        | ~ l1_orders_2(X26) )
      & ( r1_yellow_0(X26,X30)
        | r2_lattice3(X26,X30,esk3_3(X26,X27,X30))
        | ~ r2_lattice3(X26,X30,X27)
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | ~ v5_orders_2(X26)
        | ~ l1_orders_2(X26) )
      & ( X27 = k1_yellow_0(X26,X30)
        | ~ r1_orders_2(X26,X27,esk3_3(X26,X27,X30))
        | ~ r2_lattice3(X26,X30,X27)
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | ~ v5_orders_2(X26)
        | ~ l1_orders_2(X26) )
      & ( r1_yellow_0(X26,X30)
        | ~ r1_orders_2(X26,X27,esk3_3(X26,X27,X30))
        | ~ r2_lattice3(X26,X30,X27)
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | ~ v5_orders_2(X26)
        | ~ l1_orders_2(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_yellow_0])])])])])])).

cnf(c_0_50,plain,
    ( r1_orders_2(X2,X1,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k5_waybel_0(X2,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ r2_hidden(X1,k5_waybel_0(esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_52,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_53,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk1_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_54,plain,
    ( v1_xboole_0(X1)
    | v4_waybel_7(X3,X2)
    | ~ v1_waybel_0(X1,X2)
    | ~ v12_waybel_0(X1,X2)
    | ~ v1_waybel_7(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != k1_yellow_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v1_lattice3(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_55,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_56,plain,
    ( v1_waybel_7(k5_waybel_0(X1,X2),X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_waybel_6(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_57,negated_conjecture,
    ( v1_lattice3(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_58,negated_conjecture,
    ( v3_orders_2(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_59,negated_conjecture,
    ( v4_orders_2(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_60,plain,
    ( v1_waybel_0(k5_waybel_0(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_61,plain,
    ( v2_struct_0(X1)
    | v12_waybel_0(k5_waybel_0(X1,X2),X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_62,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(X1,k5_waybel_0(esk7_0,esk8_0))
    | ~ r1_orders_2(esk7_0,X1,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_28]),c_0_23])]),c_0_29])).

cnf(c_0_64,negated_conjecture,
    ( r1_orders_2(esk7_0,esk8_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_28]),c_0_48])])).

cnf(c_0_65,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | m1_subset_1(esk3_3(X2,X1,X3),u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_66,negated_conjecture,
    ( r1_orders_2(esk7_0,X1,esk8_0)
    | ~ r2_hidden(X1,k5_waybel_0(esk7_0,esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_28]),c_0_23])]),c_0_29]),c_0_51])).

cnf(c_0_67,negated_conjecture,
    ( r2_lattice3(esk7_0,X1,esk8_0)
    | r2_hidden(esk1_3(esk7_0,X1,esk8_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_28]),c_0_23])])).

cnf(c_0_68,negated_conjecture,
    ( r2_lattice3(esk7_0,X1,esk8_0)
    | ~ r1_orders_2(esk7_0,esk1_3(esk7_0,X1,esk8_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_28]),c_0_23])])).

cnf(c_0_69,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | r2_lattice3(X2,X3,esk3_3(X2,X1,X3))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_70,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | ~ r1_orders_2(X2,X1,esk3_3(X2,X1,X3))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_71,plain,
    ( v4_waybel_7(k1_yellow_0(X1,X2),X1)
    | v1_xboole_0(X2)
    | ~ v1_waybel_7(X2,X1)
    | ~ v1_lattice3(X1)
    | ~ v1_waybel_0(X2,X1)
    | ~ v3_orders_2(X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_54]),c_0_55])).

cnf(c_0_72,negated_conjecture,
    ( v1_waybel_7(k5_waybel_0(esk7_0,esk8_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_28]),c_0_57]),c_0_36]),c_0_58]),c_0_59]),c_0_31]),c_0_22]),c_0_23])])).

cnf(c_0_73,negated_conjecture,
    ( v1_waybel_0(k5_waybel_0(esk7_0,esk8_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_28]),c_0_58]),c_0_23])]),c_0_29])).

cnf(c_0_74,negated_conjecture,
    ( v12_waybel_0(k5_waybel_0(esk7_0,esk8_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_28]),c_0_59]),c_0_23])]),c_0_29])).

cnf(c_0_75,negated_conjecture,
    ( r1_orders_2(esk7_0,esk8_0,X1)
    | ~ r2_lattice3(esk7_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ r2_hidden(esk8_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_28]),c_0_23])])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk8_0,k5_waybel_0(esk7_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_28])])).

cnf(c_0_77,negated_conjecture,
    ( k1_yellow_0(esk7_0,X1) = esk8_0
    | m1_subset_1(esk3_3(esk7_0,esk8_0,X1),u1_struct_0(esk7_0))
    | ~ r2_lattice3(esk7_0,X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_28]),c_0_31]),c_0_23])])).

cnf(c_0_78,negated_conjecture,
    ( r2_lattice3(esk7_0,k5_waybel_0(esk7_0,esk8_0),esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68])).

cnf(c_0_79,negated_conjecture,
    ( k1_yellow_0(esk7_0,X1) = esk8_0
    | r2_lattice3(esk7_0,X1,esk3_3(esk7_0,esk8_0,X1))
    | ~ r2_lattice3(esk7_0,X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_28]),c_0_31]),c_0_23])])).

cnf(c_0_80,negated_conjecture,
    ( k1_yellow_0(esk7_0,X1) = esk8_0
    | ~ r1_orders_2(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,X1))
    | ~ r2_lattice3(esk7_0,X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_28]),c_0_31]),c_0_23])])).

cnf(c_0_81,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(k5_waybel_0(X1,X2))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_82,negated_conjecture,
    ( v4_waybel_7(k1_yellow_0(esk7_0,k5_waybel_0(esk7_0,esk8_0)),esk7_0)
    | v1_xboole_0(k5_waybel_0(esk7_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_39]),c_0_72]),c_0_57]),c_0_58]),c_0_59]),c_0_31]),c_0_22]),c_0_23])]),c_0_73]),c_0_74])])).

cnf(c_0_83,negated_conjecture,
    ( r1_orders_2(esk7_0,esk8_0,X1)
    | ~ r2_lattice3(esk7_0,k5_waybel_0(esk7_0,esk8_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_84,negated_conjecture,
    ( k1_yellow_0(esk7_0,k5_waybel_0(esk7_0,esk8_0)) = esk8_0
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k5_waybel_0(esk7_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_85,negated_conjecture,
    ( k1_yellow_0(esk7_0,k5_waybel_0(esk7_0,esk8_0)) = esk8_0
    | r2_lattice3(esk7_0,k5_waybel_0(esk7_0,esk8_0),esk3_3(esk7_0,esk8_0,k5_waybel_0(esk7_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_79,c_0_78])).

cnf(c_0_86,negated_conjecture,
    ( k1_yellow_0(esk7_0,k5_waybel_0(esk7_0,esk8_0)) = esk8_0
    | ~ r1_orders_2(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,k5_waybel_0(esk7_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_80,c_0_78])).

cnf(c_0_87,negated_conjecture,
    ( v4_waybel_7(k1_yellow_0(esk7_0,k5_waybel_0(esk7_0,esk8_0)),esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_58]),c_0_23]),c_0_28])]),c_0_29])).

cnf(c_0_88,negated_conjecture,
    ( k1_yellow_0(esk7_0,k5_waybel_0(esk7_0,esk8_0)) = esk8_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85]),c_0_86])).

cnf(c_0_89,negated_conjecture,
    ( ~ v4_waybel_7(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_90,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_88]),c_0_89]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:50:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.40/0.56  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.40/0.56  # and selection function SelectNewComplexAHP.
% 0.40/0.56  #
% 0.40/0.56  # Preprocessing time       : 0.031 s
% 0.40/0.56  # Presaturation interreduction done
% 0.40/0.56  
% 0.40/0.56  # Proof found!
% 0.40/0.56  # SZS status Theorem
% 0.40/0.56  # SZS output start CNFRefutation
% 0.40/0.56  fof(t38_waybel_7, conjecture, ![X1]:((((((v3_orders_2(X1)&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v5_waybel_6(X2,X1)=>v4_waybel_7(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_waybel_7)).
% 0.40/0.56  fof(cc2_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v2_lattice3(X1)=>~(v2_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_lattice3)).
% 0.40/0.56  fof(l28_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(X4=k11_lattice3(X1,X2,X3)<=>((r1_orders_2(X1,X4,X2)&r1_orders_2(X1,X4,X3))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X5,X2)&r1_orders_2(X1,X5,X3))=>r1_orders_2(X1,X5,X4))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l28_lattice3)).
% 0.40/0.56  fof(dt_k11_lattice3, axiom, ![X1, X2, X3]:(((l1_orders_2(X1)&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k11_lattice3)).
% 0.40/0.56  fof(d6_waybel_6, axiom, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v5_waybel_6(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~(((r1_orders_2(X1,k11_lattice3(X1,X3,X4),X2)&~(r1_orders_2(X1,X3,X2)))&~(r1_orders_2(X1,X4,X2))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_waybel_6)).
% 0.40/0.56  fof(dt_k5_waybel_0, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>m1_subset_1(k5_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_waybel_0)).
% 0.40/0.56  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.40/0.56  fof(t17_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k5_waybel_0(X1,X2))<=>r1_orders_2(X1,X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_waybel_0)).
% 0.40/0.56  fof(d9_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 0.40/0.56  fof(d6_waybel_7, axiom, ![X1]:((((((v3_orders_2(X1)&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v4_waybel_7(X2,X1)<=>?[X3]:(((((~(v1_xboole_0(X3))&v1_waybel_0(X3,X1))&v12_waybel_0(X3,X1))&v1_waybel_7(X3,X1))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))&X2=k1_yellow_0(X1,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_waybel_7)).
% 0.40/0.56  fof(dt_k1_yellow_0, axiom, ![X1, X2]:(l1_orders_2(X1)=>m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 0.40/0.56  fof(t37_waybel_7, axiom, ![X1]:((((((v3_orders_2(X1)&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v5_waybel_6(X2,X1)=>v1_waybel_7(k5_waybel_0(X1,X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_waybel_7)).
% 0.40/0.56  fof(fc8_waybel_0, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>(~(v1_xboole_0(k5_waybel_0(X1,X2)))&v1_waybel_0(k5_waybel_0(X1,X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_waybel_0)).
% 0.40/0.56  fof(fc12_waybel_0, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v4_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>v12_waybel_0(k5_waybel_0(X1,X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc12_waybel_0)).
% 0.40/0.56  fof(t30_yellow_0, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(((X2=k1_yellow_0(X1,X3)&r1_yellow_0(X1,X3))=>(r2_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X3,X4)=>r1_orders_2(X1,X2,X4)))))&((r2_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X3,X4)=>r1_orders_2(X1,X2,X4))))=>(X2=k1_yellow_0(X1,X3)&r1_yellow_0(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_yellow_0)).
% 0.40/0.56  fof(c_0_15, negated_conjecture, ~(![X1]:((((((v3_orders_2(X1)&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v5_waybel_6(X2,X1)=>v4_waybel_7(X2,X1))))), inference(assume_negation,[status(cth)],[t38_waybel_7])).
% 0.40/0.56  fof(c_0_16, plain, ![X9]:(~l1_orders_2(X9)|(~v2_lattice3(X9)|~v2_struct_0(X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).
% 0.40/0.56  fof(c_0_17, negated_conjecture, ((((((v3_orders_2(esk7_0)&v4_orders_2(esk7_0))&v5_orders_2(esk7_0))&v1_lattice3(esk7_0))&v2_lattice3(esk7_0))&l1_orders_2(esk7_0))&(m1_subset_1(esk8_0,u1_struct_0(esk7_0))&(v5_waybel_6(esk8_0,esk7_0)&~v4_waybel_7(esk8_0,esk7_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.40/0.56  fof(c_0_18, plain, ![X18, X19, X20, X21, X22]:((((r1_orders_2(X18,X21,X19)|X21!=k11_lattice3(X18,X19,X20)|~m1_subset_1(X21,u1_struct_0(X18))|~m1_subset_1(X20,u1_struct_0(X18))|~m1_subset_1(X19,u1_struct_0(X18))|(v2_struct_0(X18)|~v5_orders_2(X18)|~v2_lattice3(X18)|~l1_orders_2(X18)))&(r1_orders_2(X18,X21,X20)|X21!=k11_lattice3(X18,X19,X20)|~m1_subset_1(X21,u1_struct_0(X18))|~m1_subset_1(X20,u1_struct_0(X18))|~m1_subset_1(X19,u1_struct_0(X18))|(v2_struct_0(X18)|~v5_orders_2(X18)|~v2_lattice3(X18)|~l1_orders_2(X18))))&(~m1_subset_1(X22,u1_struct_0(X18))|(~r1_orders_2(X18,X22,X19)|~r1_orders_2(X18,X22,X20)|r1_orders_2(X18,X22,X21))|X21!=k11_lattice3(X18,X19,X20)|~m1_subset_1(X21,u1_struct_0(X18))|~m1_subset_1(X20,u1_struct_0(X18))|~m1_subset_1(X19,u1_struct_0(X18))|(v2_struct_0(X18)|~v5_orders_2(X18)|~v2_lattice3(X18)|~l1_orders_2(X18))))&((m1_subset_1(esk2_4(X18,X19,X20,X21),u1_struct_0(X18))|(~r1_orders_2(X18,X21,X19)|~r1_orders_2(X18,X21,X20))|X21=k11_lattice3(X18,X19,X20)|~m1_subset_1(X21,u1_struct_0(X18))|~m1_subset_1(X20,u1_struct_0(X18))|~m1_subset_1(X19,u1_struct_0(X18))|(v2_struct_0(X18)|~v5_orders_2(X18)|~v2_lattice3(X18)|~l1_orders_2(X18)))&(((r1_orders_2(X18,esk2_4(X18,X19,X20,X21),X19)|(~r1_orders_2(X18,X21,X19)|~r1_orders_2(X18,X21,X20))|X21=k11_lattice3(X18,X19,X20)|~m1_subset_1(X21,u1_struct_0(X18))|~m1_subset_1(X20,u1_struct_0(X18))|~m1_subset_1(X19,u1_struct_0(X18))|(v2_struct_0(X18)|~v5_orders_2(X18)|~v2_lattice3(X18)|~l1_orders_2(X18)))&(r1_orders_2(X18,esk2_4(X18,X19,X20,X21),X20)|(~r1_orders_2(X18,X21,X19)|~r1_orders_2(X18,X21,X20))|X21=k11_lattice3(X18,X19,X20)|~m1_subset_1(X21,u1_struct_0(X18))|~m1_subset_1(X20,u1_struct_0(X18))|~m1_subset_1(X19,u1_struct_0(X18))|(v2_struct_0(X18)|~v5_orders_2(X18)|~v2_lattice3(X18)|~l1_orders_2(X18))))&(~r1_orders_2(X18,esk2_4(X18,X19,X20,X21),X21)|(~r1_orders_2(X18,X21,X19)|~r1_orders_2(X18,X21,X20))|X21=k11_lattice3(X18,X19,X20)|~m1_subset_1(X21,u1_struct_0(X18))|~m1_subset_1(X20,u1_struct_0(X18))|~m1_subset_1(X19,u1_struct_0(X18))|(v2_struct_0(X18)|~v5_orders_2(X18)|~v2_lattice3(X18)|~l1_orders_2(X18)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l28_lattice3])])])])])])).
% 0.40/0.56  fof(c_0_19, plain, ![X15, X16, X17]:(~l1_orders_2(X15)|~m1_subset_1(X16,u1_struct_0(X15))|~m1_subset_1(X17,u1_struct_0(X15))|m1_subset_1(k11_lattice3(X15,X16,X17),u1_struct_0(X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_lattice3])])).
% 0.40/0.56  fof(c_0_20, plain, ![X41, X42, X43, X44]:((~v5_waybel_6(X42,X41)|(~m1_subset_1(X43,u1_struct_0(X41))|(~m1_subset_1(X44,u1_struct_0(X41))|(~r1_orders_2(X41,k11_lattice3(X41,X43,X44),X42)|r1_orders_2(X41,X43,X42)|r1_orders_2(X41,X44,X42))))|~m1_subset_1(X42,u1_struct_0(X41))|(v2_struct_0(X41)|~l1_orders_2(X41)))&((m1_subset_1(esk4_2(X41,X42),u1_struct_0(X41))|v5_waybel_6(X42,X41)|~m1_subset_1(X42,u1_struct_0(X41))|(v2_struct_0(X41)|~l1_orders_2(X41)))&((m1_subset_1(esk5_2(X41,X42),u1_struct_0(X41))|v5_waybel_6(X42,X41)|~m1_subset_1(X42,u1_struct_0(X41))|(v2_struct_0(X41)|~l1_orders_2(X41)))&(((r1_orders_2(X41,k11_lattice3(X41,esk4_2(X41,X42),esk5_2(X41,X42)),X42)|v5_waybel_6(X42,X41)|~m1_subset_1(X42,u1_struct_0(X41))|(v2_struct_0(X41)|~l1_orders_2(X41)))&(~r1_orders_2(X41,esk4_2(X41,X42),X42)|v5_waybel_6(X42,X41)|~m1_subset_1(X42,u1_struct_0(X41))|(v2_struct_0(X41)|~l1_orders_2(X41))))&(~r1_orders_2(X41,esk5_2(X41,X42),X42)|v5_waybel_6(X42,X41)|~m1_subset_1(X42,u1_struct_0(X41))|(v2_struct_0(X41)|~l1_orders_2(X41))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_waybel_6])])])])])])).
% 0.40/0.56  cnf(c_0_21, plain, (~l1_orders_2(X1)|~v2_lattice3(X1)|~v2_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.40/0.56  cnf(c_0_22, negated_conjecture, (v2_lattice3(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.40/0.56  cnf(c_0_23, negated_conjecture, (l1_orders_2(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.40/0.56  cnf(c_0_24, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|X2!=k11_lattice3(X1,X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.40/0.56  cnf(c_0_25, plain, (m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.40/0.56  fof(c_0_26, plain, ![X32, X33]:(v2_struct_0(X32)|~l1_orders_2(X32)|~m1_subset_1(X33,u1_struct_0(X32))|m1_subset_1(k5_waybel_0(X32,X33),k1_zfmisc_1(u1_struct_0(X32)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_waybel_0])])])).
% 0.40/0.56  cnf(c_0_27, plain, (r1_orders_2(X2,X3,X1)|r1_orders_2(X2,X4,X1)|v2_struct_0(X2)|~v5_waybel_6(X1,X2)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~r1_orders_2(X2,k11_lattice3(X2,X3,X4),X1)|~m1_subset_1(X1,u1_struct_0(X2))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.40/0.56  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.40/0.56  cnf(c_0_29, negated_conjecture, (~v2_struct_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])])).
% 0.40/0.56  cnf(c_0_30, plain, (r1_orders_2(X1,k11_lattice3(X1,X2,X3),X3)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_24, c_0_21])]), c_0_25])).
% 0.40/0.56  cnf(c_0_31, negated_conjecture, (v5_orders_2(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.40/0.56  fof(c_0_32, plain, ![X6, X7, X8]:(~r2_hidden(X6,X7)|~m1_subset_1(X7,k1_zfmisc_1(X8))|m1_subset_1(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.40/0.56  cnf(c_0_33, plain, (v2_struct_0(X1)|m1_subset_1(k5_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.40/0.56  fof(c_0_34, plain, ![X38, X39, X40]:((~r2_hidden(X40,k5_waybel_0(X38,X39))|r1_orders_2(X38,X40,X39)|~m1_subset_1(X40,u1_struct_0(X38))|~m1_subset_1(X39,u1_struct_0(X38))|(v2_struct_0(X38)|~l1_orders_2(X38)))&(~r1_orders_2(X38,X40,X39)|r2_hidden(X40,k5_waybel_0(X38,X39))|~m1_subset_1(X40,u1_struct_0(X38))|~m1_subset_1(X39,u1_struct_0(X38))|(v2_struct_0(X38)|~l1_orders_2(X38)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t17_waybel_0])])])])])).
% 0.40/0.56  cnf(c_0_35, negated_conjecture, (r1_orders_2(esk7_0,esk8_0,X1)|r1_orders_2(esk7_0,X2,X1)|~v5_waybel_6(X1,esk7_0)|~r1_orders_2(esk7_0,k11_lattice3(esk7_0,X2,esk8_0),X1)|~m1_subset_1(X2,u1_struct_0(esk7_0))|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_23])]), c_0_29])).
% 0.40/0.56  cnf(c_0_36, negated_conjecture, (v5_waybel_6(esk8_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.40/0.56  cnf(c_0_37, negated_conjecture, (r1_orders_2(esk7_0,k11_lattice3(esk7_0,esk8_0,X1),X1)|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_28]), c_0_31]), c_0_22]), c_0_23])])).
% 0.40/0.56  cnf(c_0_38, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.40/0.56  cnf(c_0_39, negated_conjecture, (m1_subset_1(k5_waybel_0(esk7_0,esk8_0),k1_zfmisc_1(u1_struct_0(esk7_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_28]), c_0_23])]), c_0_29])).
% 0.40/0.56  fof(c_0_40, plain, ![X10, X11, X12, X13]:((~r2_lattice3(X10,X11,X12)|(~m1_subset_1(X13,u1_struct_0(X10))|(~r2_hidden(X13,X11)|r1_orders_2(X10,X13,X12)))|~m1_subset_1(X12,u1_struct_0(X10))|~l1_orders_2(X10))&((m1_subset_1(esk1_3(X10,X11,X12),u1_struct_0(X10))|r2_lattice3(X10,X11,X12)|~m1_subset_1(X12,u1_struct_0(X10))|~l1_orders_2(X10))&((r2_hidden(esk1_3(X10,X11,X12),X11)|r2_lattice3(X10,X11,X12)|~m1_subset_1(X12,u1_struct_0(X10))|~l1_orders_2(X10))&(~r1_orders_2(X10,esk1_3(X10,X11,X12),X12)|r2_lattice3(X10,X11,X12)|~m1_subset_1(X12,u1_struct_0(X10))|~l1_orders_2(X10))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).
% 0.40/0.56  fof(c_0_41, plain, ![X47, X48, X50]:(((((((~v1_xboole_0(esk6_2(X47,X48))|~v4_waybel_7(X48,X47)|~m1_subset_1(X48,u1_struct_0(X47))|(~v3_orders_2(X47)|~v4_orders_2(X47)|~v5_orders_2(X47)|~v1_lattice3(X47)|~v2_lattice3(X47)|~l1_orders_2(X47)))&(v1_waybel_0(esk6_2(X47,X48),X47)|~v4_waybel_7(X48,X47)|~m1_subset_1(X48,u1_struct_0(X47))|(~v3_orders_2(X47)|~v4_orders_2(X47)|~v5_orders_2(X47)|~v1_lattice3(X47)|~v2_lattice3(X47)|~l1_orders_2(X47))))&(v12_waybel_0(esk6_2(X47,X48),X47)|~v4_waybel_7(X48,X47)|~m1_subset_1(X48,u1_struct_0(X47))|(~v3_orders_2(X47)|~v4_orders_2(X47)|~v5_orders_2(X47)|~v1_lattice3(X47)|~v2_lattice3(X47)|~l1_orders_2(X47))))&(v1_waybel_7(esk6_2(X47,X48),X47)|~v4_waybel_7(X48,X47)|~m1_subset_1(X48,u1_struct_0(X47))|(~v3_orders_2(X47)|~v4_orders_2(X47)|~v5_orders_2(X47)|~v1_lattice3(X47)|~v2_lattice3(X47)|~l1_orders_2(X47))))&(m1_subset_1(esk6_2(X47,X48),k1_zfmisc_1(u1_struct_0(X47)))|~v4_waybel_7(X48,X47)|~m1_subset_1(X48,u1_struct_0(X47))|(~v3_orders_2(X47)|~v4_orders_2(X47)|~v5_orders_2(X47)|~v1_lattice3(X47)|~v2_lattice3(X47)|~l1_orders_2(X47))))&(X48=k1_yellow_0(X47,esk6_2(X47,X48))|~v4_waybel_7(X48,X47)|~m1_subset_1(X48,u1_struct_0(X47))|(~v3_orders_2(X47)|~v4_orders_2(X47)|~v5_orders_2(X47)|~v1_lattice3(X47)|~v2_lattice3(X47)|~l1_orders_2(X47))))&(v1_xboole_0(X50)|~v1_waybel_0(X50,X47)|~v12_waybel_0(X50,X47)|~v1_waybel_7(X50,X47)|~m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X47)))|X48!=k1_yellow_0(X47,X50)|v4_waybel_7(X48,X47)|~m1_subset_1(X48,u1_struct_0(X47))|(~v3_orders_2(X47)|~v4_orders_2(X47)|~v5_orders_2(X47)|~v1_lattice3(X47)|~v2_lattice3(X47)|~l1_orders_2(X47)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_waybel_7])])])])])])).
% 0.40/0.56  fof(c_0_42, plain, ![X24, X25]:(~l1_orders_2(X24)|m1_subset_1(k1_yellow_0(X24,X25),u1_struct_0(X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).
% 0.40/0.56  fof(c_0_43, plain, ![X51, X52]:(~v3_orders_2(X51)|~v4_orders_2(X51)|~v5_orders_2(X51)|~v1_lattice3(X51)|~v2_lattice3(X51)|~l1_orders_2(X51)|(~m1_subset_1(X52,u1_struct_0(X51))|(~v5_waybel_6(X52,X51)|v1_waybel_7(k5_waybel_0(X51,X52),X51)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_waybel_7])])])).
% 0.40/0.56  fof(c_0_44, plain, ![X36, X37]:((~v1_xboole_0(k5_waybel_0(X36,X37))|(v2_struct_0(X36)|~v3_orders_2(X36)|~l1_orders_2(X36)|~m1_subset_1(X37,u1_struct_0(X36))))&(v1_waybel_0(k5_waybel_0(X36,X37),X36)|(v2_struct_0(X36)|~v3_orders_2(X36)|~l1_orders_2(X36)|~m1_subset_1(X37,u1_struct_0(X36))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc8_waybel_0])])])])).
% 0.40/0.56  fof(c_0_45, plain, ![X34, X35]:(v2_struct_0(X34)|~v4_orders_2(X34)|~l1_orders_2(X34)|~m1_subset_1(X35,u1_struct_0(X34))|v12_waybel_0(k5_waybel_0(X34,X35),X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc12_waybel_0])])])).
% 0.40/0.56  cnf(c_0_46, plain, (r2_hidden(X2,k5_waybel_0(X1,X3))|v2_struct_0(X1)|~r1_orders_2(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.40/0.56  cnf(c_0_47, negated_conjecture, (r1_orders_2(esk7_0,esk8_0,esk8_0)|r1_orders_2(esk7_0,X1,esk8_0)|~r1_orders_2(esk7_0,k11_lattice3(esk7_0,X1,esk8_0),esk8_0)|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_28])])).
% 0.40/0.56  cnf(c_0_48, negated_conjecture, (r1_orders_2(esk7_0,k11_lattice3(esk7_0,esk8_0,esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_37, c_0_28])).
% 0.40/0.56  fof(c_0_49, plain, ![X26, X27, X28, X29, X30]:(((r2_lattice3(X26,X28,X27)|(X27!=k1_yellow_0(X26,X28)|~r1_yellow_0(X26,X28))|~m1_subset_1(X27,u1_struct_0(X26))|(~v5_orders_2(X26)|~l1_orders_2(X26)))&(~m1_subset_1(X29,u1_struct_0(X26))|(~r2_lattice3(X26,X28,X29)|r1_orders_2(X26,X27,X29))|(X27!=k1_yellow_0(X26,X28)|~r1_yellow_0(X26,X28))|~m1_subset_1(X27,u1_struct_0(X26))|(~v5_orders_2(X26)|~l1_orders_2(X26))))&(((X27=k1_yellow_0(X26,X30)|(m1_subset_1(esk3_3(X26,X27,X30),u1_struct_0(X26))|~r2_lattice3(X26,X30,X27))|~m1_subset_1(X27,u1_struct_0(X26))|(~v5_orders_2(X26)|~l1_orders_2(X26)))&(r1_yellow_0(X26,X30)|(m1_subset_1(esk3_3(X26,X27,X30),u1_struct_0(X26))|~r2_lattice3(X26,X30,X27))|~m1_subset_1(X27,u1_struct_0(X26))|(~v5_orders_2(X26)|~l1_orders_2(X26))))&(((X27=k1_yellow_0(X26,X30)|(r2_lattice3(X26,X30,esk3_3(X26,X27,X30))|~r2_lattice3(X26,X30,X27))|~m1_subset_1(X27,u1_struct_0(X26))|(~v5_orders_2(X26)|~l1_orders_2(X26)))&(r1_yellow_0(X26,X30)|(r2_lattice3(X26,X30,esk3_3(X26,X27,X30))|~r2_lattice3(X26,X30,X27))|~m1_subset_1(X27,u1_struct_0(X26))|(~v5_orders_2(X26)|~l1_orders_2(X26))))&((X27=k1_yellow_0(X26,X30)|(~r1_orders_2(X26,X27,esk3_3(X26,X27,X30))|~r2_lattice3(X26,X30,X27))|~m1_subset_1(X27,u1_struct_0(X26))|(~v5_orders_2(X26)|~l1_orders_2(X26)))&(r1_yellow_0(X26,X30)|(~r1_orders_2(X26,X27,esk3_3(X26,X27,X30))|~r2_lattice3(X26,X30,X27))|~m1_subset_1(X27,u1_struct_0(X26))|(~v5_orders_2(X26)|~l1_orders_2(X26))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_yellow_0])])])])])])).
% 0.40/0.56  cnf(c_0_50, plain, (r1_orders_2(X2,X1,X3)|v2_struct_0(X2)|~r2_hidden(X1,k5_waybel_0(X2,X3))|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.40/0.56  cnf(c_0_51, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk7_0))|~r2_hidden(X1,k5_waybel_0(esk7_0,esk8_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.40/0.56  cnf(c_0_52, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.40/0.56  cnf(c_0_53, plain, (r2_lattice3(X1,X2,X3)|~r1_orders_2(X1,esk1_3(X1,X2,X3),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.40/0.56  cnf(c_0_54, plain, (v1_xboole_0(X1)|v4_waybel_7(X3,X2)|~v1_waybel_0(X1,X2)|~v12_waybel_0(X1,X2)|~v1_waybel_7(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|X3!=k1_yellow_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~v1_lattice3(X2)|~v2_lattice3(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.40/0.56  cnf(c_0_55, plain, (m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.40/0.56  cnf(c_0_56, plain, (v1_waybel_7(k5_waybel_0(X1,X2),X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v5_waybel_6(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.40/0.56  cnf(c_0_57, negated_conjecture, (v1_lattice3(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.40/0.56  cnf(c_0_58, negated_conjecture, (v3_orders_2(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.40/0.56  cnf(c_0_59, negated_conjecture, (v4_orders_2(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.40/0.56  cnf(c_0_60, plain, (v1_waybel_0(k5_waybel_0(X1,X2),X1)|v2_struct_0(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.40/0.56  cnf(c_0_61, plain, (v2_struct_0(X1)|v12_waybel_0(k5_waybel_0(X1,X2),X1)|~v4_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.40/0.56  cnf(c_0_62, plain, (r1_orders_2(X1,X4,X3)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.40/0.56  cnf(c_0_63, negated_conjecture, (r2_hidden(X1,k5_waybel_0(esk7_0,esk8_0))|~r1_orders_2(esk7_0,X1,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_28]), c_0_23])]), c_0_29])).
% 0.40/0.56  cnf(c_0_64, negated_conjecture, (r1_orders_2(esk7_0,esk8_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_28]), c_0_48])])).
% 0.40/0.56  cnf(c_0_65, plain, (X1=k1_yellow_0(X2,X3)|m1_subset_1(esk3_3(X2,X1,X3),u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.40/0.56  cnf(c_0_66, negated_conjecture, (r1_orders_2(esk7_0,X1,esk8_0)|~r2_hidden(X1,k5_waybel_0(esk7_0,esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_28]), c_0_23])]), c_0_29]), c_0_51])).
% 0.40/0.56  cnf(c_0_67, negated_conjecture, (r2_lattice3(esk7_0,X1,esk8_0)|r2_hidden(esk1_3(esk7_0,X1,esk8_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_28]), c_0_23])])).
% 0.40/0.56  cnf(c_0_68, negated_conjecture, (r2_lattice3(esk7_0,X1,esk8_0)|~r1_orders_2(esk7_0,esk1_3(esk7_0,X1,esk8_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_28]), c_0_23])])).
% 0.40/0.56  cnf(c_0_69, plain, (X1=k1_yellow_0(X2,X3)|r2_lattice3(X2,X3,esk3_3(X2,X1,X3))|~r2_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.40/0.56  cnf(c_0_70, plain, (X1=k1_yellow_0(X2,X3)|~r1_orders_2(X2,X1,esk3_3(X2,X1,X3))|~r2_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.40/0.56  cnf(c_0_71, plain, (v4_waybel_7(k1_yellow_0(X1,X2),X1)|v1_xboole_0(X2)|~v1_waybel_7(X2,X1)|~v1_lattice3(X1)|~v1_waybel_0(X2,X1)|~v3_orders_2(X1)|~v12_waybel_0(X2,X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_54]), c_0_55])).
% 0.40/0.56  cnf(c_0_72, negated_conjecture, (v1_waybel_7(k5_waybel_0(esk7_0,esk8_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_28]), c_0_57]), c_0_36]), c_0_58]), c_0_59]), c_0_31]), c_0_22]), c_0_23])])).
% 0.40/0.56  cnf(c_0_73, negated_conjecture, (v1_waybel_0(k5_waybel_0(esk7_0,esk8_0),esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_28]), c_0_58]), c_0_23])]), c_0_29])).
% 0.40/0.56  cnf(c_0_74, negated_conjecture, (v12_waybel_0(k5_waybel_0(esk7_0,esk8_0),esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_28]), c_0_59]), c_0_23])]), c_0_29])).
% 0.40/0.56  cnf(c_0_75, negated_conjecture, (r1_orders_2(esk7_0,esk8_0,X1)|~r2_lattice3(esk7_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk7_0))|~r2_hidden(esk8_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_28]), c_0_23])])).
% 0.40/0.56  cnf(c_0_76, negated_conjecture, (r2_hidden(esk8_0,k5_waybel_0(esk7_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_28])])).
% 0.40/0.56  cnf(c_0_77, negated_conjecture, (k1_yellow_0(esk7_0,X1)=esk8_0|m1_subset_1(esk3_3(esk7_0,esk8_0,X1),u1_struct_0(esk7_0))|~r2_lattice3(esk7_0,X1,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_28]), c_0_31]), c_0_23])])).
% 0.40/0.56  cnf(c_0_78, negated_conjecture, (r2_lattice3(esk7_0,k5_waybel_0(esk7_0,esk8_0),esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68])).
% 0.40/0.56  cnf(c_0_79, negated_conjecture, (k1_yellow_0(esk7_0,X1)=esk8_0|r2_lattice3(esk7_0,X1,esk3_3(esk7_0,esk8_0,X1))|~r2_lattice3(esk7_0,X1,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_28]), c_0_31]), c_0_23])])).
% 0.40/0.56  cnf(c_0_80, negated_conjecture, (k1_yellow_0(esk7_0,X1)=esk8_0|~r1_orders_2(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,X1))|~r2_lattice3(esk7_0,X1,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_28]), c_0_31]), c_0_23])])).
% 0.40/0.56  cnf(c_0_81, plain, (v2_struct_0(X1)|~v1_xboole_0(k5_waybel_0(X1,X2))|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.40/0.56  cnf(c_0_82, negated_conjecture, (v4_waybel_7(k1_yellow_0(esk7_0,k5_waybel_0(esk7_0,esk8_0)),esk7_0)|v1_xboole_0(k5_waybel_0(esk7_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_39]), c_0_72]), c_0_57]), c_0_58]), c_0_59]), c_0_31]), c_0_22]), c_0_23])]), c_0_73]), c_0_74])])).
% 0.40/0.56  cnf(c_0_83, negated_conjecture, (r1_orders_2(esk7_0,esk8_0,X1)|~r2_lattice3(esk7_0,k5_waybel_0(esk7_0,esk8_0),X1)|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.40/0.56  cnf(c_0_84, negated_conjecture, (k1_yellow_0(esk7_0,k5_waybel_0(esk7_0,esk8_0))=esk8_0|m1_subset_1(esk3_3(esk7_0,esk8_0,k5_waybel_0(esk7_0,esk8_0)),u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.40/0.56  cnf(c_0_85, negated_conjecture, (k1_yellow_0(esk7_0,k5_waybel_0(esk7_0,esk8_0))=esk8_0|r2_lattice3(esk7_0,k5_waybel_0(esk7_0,esk8_0),esk3_3(esk7_0,esk8_0,k5_waybel_0(esk7_0,esk8_0)))), inference(spm,[status(thm)],[c_0_79, c_0_78])).
% 0.40/0.56  cnf(c_0_86, negated_conjecture, (k1_yellow_0(esk7_0,k5_waybel_0(esk7_0,esk8_0))=esk8_0|~r1_orders_2(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,k5_waybel_0(esk7_0,esk8_0)))), inference(spm,[status(thm)],[c_0_80, c_0_78])).
% 0.40/0.56  cnf(c_0_87, negated_conjecture, (v4_waybel_7(k1_yellow_0(esk7_0,k5_waybel_0(esk7_0,esk8_0)),esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_58]), c_0_23]), c_0_28])]), c_0_29])).
% 0.40/0.56  cnf(c_0_88, negated_conjecture, (k1_yellow_0(esk7_0,k5_waybel_0(esk7_0,esk8_0))=esk8_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_85]), c_0_86])).
% 0.40/0.56  cnf(c_0_89, negated_conjecture, (~v4_waybel_7(esk8_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.40/0.56  cnf(c_0_90, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_88]), c_0_89]), ['proof']).
% 0.40/0.56  # SZS output end CNFRefutation
% 0.40/0.56  # Proof object total steps             : 91
% 0.40/0.56  # Proof object clause steps            : 60
% 0.40/0.56  # Proof object formula steps           : 31
% 0.40/0.56  # Proof object conjectures             : 41
% 0.40/0.56  # Proof object clause conjectures      : 38
% 0.40/0.56  # Proof object formula conjectures     : 3
% 0.40/0.56  # Proof object initial clauses used    : 29
% 0.40/0.56  # Proof object initial formulas used   : 15
% 0.40/0.56  # Proof object generating inferences   : 28
% 0.40/0.56  # Proof object simplifying inferences  : 82
% 0.40/0.56  # Training examples: 0 positive, 0 negative
% 0.40/0.56  # Parsed axioms                        : 15
% 0.40/0.56  # Removed by relevancy pruning/SinE    : 0
% 0.40/0.56  # Initial clauses                      : 52
% 0.40/0.56  # Removed in clause preprocessing      : 0
% 0.40/0.56  # Initial clauses in saturation        : 52
% 0.40/0.56  # Processed clauses                    : 729
% 0.40/0.56  # ...of these trivial                  : 5
% 0.40/0.56  # ...subsumed                          : 113
% 0.40/0.56  # ...remaining for further processing  : 611
% 0.40/0.56  # Other redundant clauses eliminated   : 6
% 0.40/0.56  # Clauses deleted for lack of memory   : 0
% 0.40/0.56  # Backward-subsumed                    : 2
% 0.40/0.56  # Backward-rewritten                   : 180
% 0.40/0.56  # Generated clauses                    : 9299
% 0.40/0.56  # ...of the previous two non-trivial   : 8988
% 0.40/0.56  # Contextual simplify-reflections      : 26
% 0.40/0.56  # Paramodulations                      : 9293
% 0.40/0.56  # Factorizations                       : 0
% 0.40/0.56  # Equation resolutions                 : 6
% 0.40/0.56  # Propositional unsat checks           : 0
% 0.40/0.56  #    Propositional check models        : 0
% 0.40/0.56  #    Propositional check unsatisfiable : 0
% 0.40/0.56  #    Propositional clauses             : 0
% 0.40/0.56  #    Propositional clauses after purity: 0
% 0.40/0.56  #    Propositional unsat core size     : 0
% 0.40/0.56  #    Propositional preprocessing time  : 0.000
% 0.40/0.56  #    Propositional encoding time       : 0.000
% 0.40/0.56  #    Propositional solver time         : 0.000
% 0.40/0.56  #    Success case prop preproc time    : 0.000
% 0.40/0.56  #    Success case prop encoding time   : 0.000
% 0.40/0.56  #    Success case prop solver time     : 0.000
% 0.40/0.56  # Current number of processed clauses  : 371
% 0.40/0.56  #    Positive orientable unit clauses  : 91
% 0.40/0.56  #    Positive unorientable unit clauses: 0
% 0.40/0.56  #    Negative unit clauses             : 2
% 0.40/0.56  #    Non-unit-clauses                  : 278
% 0.40/0.56  # Current number of unprocessed clauses: 8020
% 0.40/0.56  # ...number of literals in the above   : 19464
% 0.40/0.56  # Current number of archived formulas  : 0
% 0.40/0.56  # Current number of archived clauses   : 234
% 0.40/0.56  # Clause-clause subsumption calls (NU) : 16143
% 0.40/0.56  # Rec. Clause-clause subsumption calls : 8500
% 0.40/0.56  # Non-unit clause-clause subsumptions  : 123
% 0.40/0.56  # Unit Clause-clause subsumption calls : 1364
% 0.40/0.56  # Rewrite failures with RHS unbound    : 0
% 0.40/0.56  # BW rewrite match attempts            : 690
% 0.40/0.56  # BW rewrite match successes           : 5
% 0.40/0.56  # Condensation attempts                : 0
% 0.40/0.56  # Condensation successes               : 0
% 0.40/0.56  # Termbank termtop insertions          : 346062
% 0.40/0.56  
% 0.40/0.56  # -------------------------------------------------
% 0.40/0.56  # User time                : 0.210 s
% 0.40/0.56  # System time              : 0.013 s
% 0.40/0.56  # Total time               : 0.223 s
% 0.40/0.56  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
