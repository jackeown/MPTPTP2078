%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1987+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:06 EST 2020

% Result     : Theorem 0.40s
% Output     : CNFRefutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  138 (78349 expanded)
%              Number of clauses        :  117 (25806 expanded)
%              Number of leaves         :   10 (18922 expanded)
%              Depth                    :   30
%              Number of atoms          :  901 (1178346 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   27 (   6 average)
%              Maximal clause size      :   98 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t36_waybel_7,conjecture,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v2_waybel_1(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & v3_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_waybel_3(X1,X2,X3)
              <=> ! [X4] :
                    ( ( ~ v1_xboole_0(X4)
                      & v1_waybel_0(X4,X1)
                      & v12_waybel_0(X4,X1)
                      & v1_waybel_7(X4,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                   => ( r3_orders_2(X1,X3,k1_yellow_0(X1,X4))
                     => r2_hidden(X2,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_waybel_7)).

fof(cc2_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

fof(cc11_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v3_lattice3(X1) )
       => ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v24_waybel_0(X1)
          & v25_waybel_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc11_waybel_0)).

fof(t21_waybel_3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v24_waybel_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ! [X4] :
                    ( ( ~ v1_xboole_0(X4)
                      & v1_waybel_0(X4,X1)
                      & v12_waybel_0(X4,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                   => ( r3_orders_2(X1,X3,k1_yellow_0(X1,X4))
                     => r2_hidden(X2,X4) ) )
               => r1_waybel_3(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_waybel_3)).

fof(t20_waybel_3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_waybel_3(X1,X2,X3)
               => ! [X4] :
                    ( ( ~ v1_xboole_0(X4)
                      & v1_waybel_0(X4,X1)
                      & v12_waybel_0(X4,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                   => ( r3_orders_2(X1,X3,k1_yellow_0(X1,X4))
                     => r2_hidden(X2,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_waybel_3)).

fof(t28_waybel_7,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v2_waybel_1(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_waybel_0(X2,X1)
            & v12_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ~ ( ~ r2_hidden(X3,X2)
                  & ! [X4] :
                      ( ( ~ v1_xboole_0(X4)
                        & v1_waybel_0(X4,X1)
                        & v12_waybel_0(X4,X1)
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                     => ~ ( v1_waybel_7(X4,X1)
                          & r1_tarski(X2,X4)
                          & ~ r2_hidden(X3,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_waybel_7)).

fof(dt_k1_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(t3_waybel_7,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & v3_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2,X3] :
          ( r1_tarski(X2,X3)
         => ( r3_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3))
            & r1_orders_2(X1,k2_yellow_0(X1,X3),k2_yellow_0(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_waybel_7)).

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

fof(t26_orders_2,axiom,(
    ! [X1] :
      ( ( v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( ( r1_orders_2(X1,X2,X3)
                      & r1_orders_2(X1,X3,X4) )
                   => r1_orders_2(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_orders_2)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & v2_waybel_1(X1)
          & v1_lattice3(X1)
          & v2_lattice3(X1)
          & v3_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r1_waybel_3(X1,X2,X3)
                <=> ! [X4] :
                      ( ( ~ v1_xboole_0(X4)
                        & v1_waybel_0(X4,X1)
                        & v12_waybel_0(X4,X1)
                        & v1_waybel_7(X4,X1)
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                     => ( r3_orders_2(X1,X3,k1_yellow_0(X1,X4))
                       => r2_hidden(X2,X4) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t36_waybel_7])).

fof(c_0_11,plain,(
    ! [X6] :
      ( ~ l1_orders_2(X6)
      | ~ v2_lattice3(X6)
      | ~ v2_struct_0(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

fof(c_0_12,negated_conjecture,(
    ! [X35] :
      ( v3_orders_2(esk3_0)
      & v4_orders_2(esk3_0)
      & v5_orders_2(esk3_0)
      & v2_waybel_1(esk3_0)
      & v1_lattice3(esk3_0)
      & v2_lattice3(esk3_0)
      & v3_lattice3(esk3_0)
      & l1_orders_2(esk3_0)
      & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
      & m1_subset_1(esk5_0,u1_struct_0(esk3_0))
      & ( ~ v1_xboole_0(esk6_0)
        | ~ r1_waybel_3(esk3_0,esk4_0,esk5_0) )
      & ( v1_waybel_0(esk6_0,esk3_0)
        | ~ r1_waybel_3(esk3_0,esk4_0,esk5_0) )
      & ( v12_waybel_0(esk6_0,esk3_0)
        | ~ r1_waybel_3(esk3_0,esk4_0,esk5_0) )
      & ( v1_waybel_7(esk6_0,esk3_0)
        | ~ r1_waybel_3(esk3_0,esk4_0,esk5_0) )
      & ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
        | ~ r1_waybel_3(esk3_0,esk4_0,esk5_0) )
      & ( r3_orders_2(esk3_0,esk5_0,k1_yellow_0(esk3_0,esk6_0))
        | ~ r1_waybel_3(esk3_0,esk4_0,esk5_0) )
      & ( ~ r2_hidden(esk4_0,esk6_0)
        | ~ r1_waybel_3(esk3_0,esk4_0,esk5_0) )
      & ( r1_waybel_3(esk3_0,esk4_0,esk5_0)
        | v1_xboole_0(X35)
        | ~ v1_waybel_0(X35,esk3_0)
        | ~ v12_waybel_0(X35,esk3_0)
        | ~ v1_waybel_7(X35,esk3_0)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(esk3_0)))
        | ~ r3_orders_2(esk3_0,esk5_0,k1_yellow_0(esk3_0,X35))
        | r2_hidden(esk4_0,X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])])).

fof(c_0_13,plain,(
    ! [X5] :
      ( ( ~ v2_struct_0(X5)
        | v2_struct_0(X5)
        | ~ v3_orders_2(X5)
        | ~ v3_lattice3(X5)
        | ~ l1_orders_2(X5) )
      & ( v3_orders_2(X5)
        | v2_struct_0(X5)
        | ~ v3_orders_2(X5)
        | ~ v3_lattice3(X5)
        | ~ l1_orders_2(X5) )
      & ( v24_waybel_0(X5)
        | v2_struct_0(X5)
        | ~ v3_orders_2(X5)
        | ~ v3_lattice3(X5)
        | ~ l1_orders_2(X5) )
      & ( v25_waybel_0(X5)
        | v2_struct_0(X5)
        | ~ v3_orders_2(X5)
        | ~ v3_lattice3(X5)
        | ~ l1_orders_2(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc11_waybel_0])])])])).

cnf(c_0_14,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( v2_lattice3(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X16,X17,X18] :
      ( ( ~ v1_xboole_0(esk1_3(X16,X17,X18))
        | r1_waybel_3(X16,X17,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v3_orders_2(X16)
        | ~ v4_orders_2(X16)
        | ~ v5_orders_2(X16)
        | ~ v24_waybel_0(X16)
        | ~ l1_orders_2(X16) )
      & ( v1_waybel_0(esk1_3(X16,X17,X18),X16)
        | r1_waybel_3(X16,X17,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v3_orders_2(X16)
        | ~ v4_orders_2(X16)
        | ~ v5_orders_2(X16)
        | ~ v24_waybel_0(X16)
        | ~ l1_orders_2(X16) )
      & ( v12_waybel_0(esk1_3(X16,X17,X18),X16)
        | r1_waybel_3(X16,X17,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v3_orders_2(X16)
        | ~ v4_orders_2(X16)
        | ~ v5_orders_2(X16)
        | ~ v24_waybel_0(X16)
        | ~ l1_orders_2(X16) )
      & ( m1_subset_1(esk1_3(X16,X17,X18),k1_zfmisc_1(u1_struct_0(X16)))
        | r1_waybel_3(X16,X17,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v3_orders_2(X16)
        | ~ v4_orders_2(X16)
        | ~ v5_orders_2(X16)
        | ~ v24_waybel_0(X16)
        | ~ l1_orders_2(X16) )
      & ( r3_orders_2(X16,X18,k1_yellow_0(X16,esk1_3(X16,X17,X18)))
        | r1_waybel_3(X16,X17,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v3_orders_2(X16)
        | ~ v4_orders_2(X16)
        | ~ v5_orders_2(X16)
        | ~ v24_waybel_0(X16)
        | ~ l1_orders_2(X16) )
      & ( ~ r2_hidden(X17,esk1_3(X16,X17,X18))
        | r1_waybel_3(X16,X17,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v3_orders_2(X16)
        | ~ v4_orders_2(X16)
        | ~ v5_orders_2(X16)
        | ~ v24_waybel_0(X16)
        | ~ l1_orders_2(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_waybel_3])])])])])])).

cnf(c_0_18,plain,
    ( v24_waybel_0(X1)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v3_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( v3_lattice3(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( v3_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])])).

cnf(c_0_22,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | r1_waybel_3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v24_waybel_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( v5_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,negated_conjecture,
    ( v4_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,negated_conjecture,
    ( v24_waybel_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_16])]),c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( r1_waybel_3(esk3_0,X1,X2)
    | m1_subset_1(esk1_3(esk3_0,X1,X2),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25]),c_0_20]),c_0_16])]),c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_28,negated_conjecture,
    ( r1_waybel_3(esk3_0,X1,esk5_0)
    | m1_subset_1(esk1_3(esk3_0,X1,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_30,plain,(
    ! [X12,X13,X14,X15] :
      ( v2_struct_0(X12)
      | ~ v3_orders_2(X12)
      | ~ v4_orders_2(X12)
      | ~ l1_orders_2(X12)
      | ~ m1_subset_1(X13,u1_struct_0(X12))
      | ~ m1_subset_1(X14,u1_struct_0(X12))
      | ~ r1_waybel_3(X12,X13,X14)
      | v1_xboole_0(X15)
      | ~ v1_waybel_0(X15,X12)
      | ~ v12_waybel_0(X15,X12)
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X12)))
      | ~ r3_orders_2(X12,X14,k1_yellow_0(X12,X15))
      | r2_hidden(X13,X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t20_waybel_3])])])])).

cnf(c_0_31,negated_conjecture,
    ( v12_waybel_0(esk6_0,esk3_0)
    | ~ r1_waybel_3(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_32,negated_conjecture,
    ( r1_waybel_3(esk3_0,esk4_0,esk5_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_waybel_3(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_34,negated_conjecture,
    ( v1_waybel_0(esk6_0,esk3_0)
    | ~ r1_waybel_3(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_35,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0)
    | ~ r1_waybel_3(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_36,plain,
    ( v12_waybel_0(esk1_3(X1,X2,X3),X1)
    | r1_waybel_3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v24_waybel_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_37,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X4)
    | r2_hidden(X2,X4)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_waybel_3(X1,X2,X3)
    | ~ v1_waybel_0(X4,X1)
    | ~ v12_waybel_0(X4,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r3_orders_2(X1,X3,k1_yellow_0(X1,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( v12_waybel_0(esk6_0,esk3_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( v1_waybel_0(esk6_0,esk3_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( r3_orders_2(esk3_0,esk5_0,k1_yellow_0(esk3_0,esk6_0))
    | ~ r1_waybel_3(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_43,plain,
    ( v1_waybel_0(esk1_3(X1,X2,X3),X1)
    | r1_waybel_3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v24_waybel_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_44,plain,(
    ! [X24,X25,X26] :
      ( ( ~ v1_xboole_0(esk2_3(X24,X25,X26))
        | r2_hidden(X26,X25)
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | v1_xboole_0(X25)
        | ~ v1_waybel_0(X25,X24)
        | ~ v12_waybel_0(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ v3_orders_2(X24)
        | ~ v4_orders_2(X24)
        | ~ v5_orders_2(X24)
        | ~ v2_waybel_1(X24)
        | ~ v1_lattice3(X24)
        | ~ v2_lattice3(X24)
        | ~ l1_orders_2(X24) )
      & ( v1_waybel_0(esk2_3(X24,X25,X26),X24)
        | r2_hidden(X26,X25)
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | v1_xboole_0(X25)
        | ~ v1_waybel_0(X25,X24)
        | ~ v12_waybel_0(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ v3_orders_2(X24)
        | ~ v4_orders_2(X24)
        | ~ v5_orders_2(X24)
        | ~ v2_waybel_1(X24)
        | ~ v1_lattice3(X24)
        | ~ v2_lattice3(X24)
        | ~ l1_orders_2(X24) )
      & ( v12_waybel_0(esk2_3(X24,X25,X26),X24)
        | r2_hidden(X26,X25)
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | v1_xboole_0(X25)
        | ~ v1_waybel_0(X25,X24)
        | ~ v12_waybel_0(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ v3_orders_2(X24)
        | ~ v4_orders_2(X24)
        | ~ v5_orders_2(X24)
        | ~ v2_waybel_1(X24)
        | ~ v1_lattice3(X24)
        | ~ v2_lattice3(X24)
        | ~ l1_orders_2(X24) )
      & ( m1_subset_1(esk2_3(X24,X25,X26),k1_zfmisc_1(u1_struct_0(X24)))
        | r2_hidden(X26,X25)
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | v1_xboole_0(X25)
        | ~ v1_waybel_0(X25,X24)
        | ~ v12_waybel_0(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ v3_orders_2(X24)
        | ~ v4_orders_2(X24)
        | ~ v5_orders_2(X24)
        | ~ v2_waybel_1(X24)
        | ~ v1_lattice3(X24)
        | ~ v2_lattice3(X24)
        | ~ l1_orders_2(X24) )
      & ( v1_waybel_7(esk2_3(X24,X25,X26),X24)
        | r2_hidden(X26,X25)
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | v1_xboole_0(X25)
        | ~ v1_waybel_0(X25,X24)
        | ~ v12_waybel_0(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ v3_orders_2(X24)
        | ~ v4_orders_2(X24)
        | ~ v5_orders_2(X24)
        | ~ v2_waybel_1(X24)
        | ~ v1_lattice3(X24)
        | ~ v2_lattice3(X24)
        | ~ l1_orders_2(X24) )
      & ( r1_tarski(X25,esk2_3(X24,X25,X26))
        | r2_hidden(X26,X25)
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | v1_xboole_0(X25)
        | ~ v1_waybel_0(X25,X24)
        | ~ v12_waybel_0(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ v3_orders_2(X24)
        | ~ v4_orders_2(X24)
        | ~ v5_orders_2(X24)
        | ~ v2_waybel_1(X24)
        | ~ v1_lattice3(X24)
        | ~ v2_lattice3(X24)
        | ~ l1_orders_2(X24) )
      & ( ~ r2_hidden(X26,esk2_3(X24,X25,X26))
        | r2_hidden(X26,X25)
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | v1_xboole_0(X25)
        | ~ v1_waybel_0(X25,X24)
        | ~ v12_waybel_0(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ v3_orders_2(X24)
        | ~ v4_orders_2(X24)
        | ~ v5_orders_2(X24)
        | ~ v2_waybel_1(X24)
        | ~ v1_lattice3(X24)
        | ~ v2_lattice3(X24)
        | ~ l1_orders_2(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t28_waybel_7])])])])])])).

cnf(c_0_45,negated_conjecture,
    ( v12_waybel_0(esk1_3(esk3_0,X1,X2),esk3_0)
    | r1_waybel_3(esk3_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_23]),c_0_24]),c_0_25]),c_0_20]),c_0_16])]),c_0_21])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_waybel_3(esk3_0,X1,X2)
    | ~ r3_orders_2(esk3_0,X2,k1_yellow_0(esk3_0,esk6_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_24]),c_0_20]),c_0_16])]),c_0_21]),c_0_39]),c_0_40]),c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( r3_orders_2(esk3_0,esk5_0,k1_yellow_0(esk3_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_32])).

cnf(c_0_48,negated_conjecture,
    ( ~ r2_hidden(esk4_0,esk6_0)
    | ~ r1_waybel_3(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_49,negated_conjecture,
    ( v1_waybel_0(esk1_3(esk3_0,X1,X2),esk3_0)
    | r1_waybel_3(esk3_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_23]),c_0_24]),c_0_25]),c_0_20]),c_0_16])]),c_0_21])).

cnf(c_0_50,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X3,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_waybel_1(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( v1_lattice3(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_52,negated_conjecture,
    ( v2_waybel_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_53,negated_conjecture,
    ( v12_waybel_0(esk1_3(esk3_0,X1,esk5_0),esk3_0)
    | r1_waybel_3(esk3_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_27])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_waybel_3(esk3_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_27])])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_32])).

cnf(c_0_56,negated_conjecture,
    ( v1_waybel_0(esk1_3(esk3_0,X1,esk5_0),esk3_0)
    | r1_waybel_3(esk3_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_27])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,esk2_3(X2,X1,X3))
    | r2_hidden(X3,X1)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v1_waybel_0(X1,X2)
    | ~ v12_waybel_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v2_waybel_1(X2)
    | ~ v1_lattice3(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | m1_subset_1(esk2_3(esk3_0,X2,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v12_waybel_0(X2,esk3_0)
    | ~ v1_waybel_0(X2,esk3_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_23]),c_0_24]),c_0_15]),c_0_20]),c_0_16])])).

cnf(c_0_59,negated_conjecture,
    ( v12_waybel_0(esk1_3(esk3_0,esk4_0,esk5_0),esk3_0)
    | r1_waybel_3(esk3_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_29])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_32]),c_0_29])]),c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( v1_waybel_0(esk1_3(esk3_0,esk4_0,esk5_0),esk3_0)
    | r1_waybel_3(esk3_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_29])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(X1,esk2_3(esk3_0,X1,X2))
    | r2_hidden(X2,X1)
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,esk3_0)
    | ~ v1_waybel_0(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_51]),c_0_52]),c_0_23]),c_0_24]),c_0_15]),c_0_20]),c_0_16])])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(X1,esk1_3(esk3_0,esk4_0,esk5_0))
    | v1_xboole_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | r1_waybel_3(esk3_0,esk4_0,esk5_0)
    | m1_subset_1(esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])]),c_0_61])).

fof(c_0_64,plain,(
    ! [X7,X8] :
      ( ~ l1_orders_2(X7)
      | m1_subset_1(k1_yellow_0(X7,X8),u1_struct_0(X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

fof(c_0_65,plain,(
    ! [X28,X29,X30] :
      ( ( r3_orders_2(X28,k1_yellow_0(X28,X29),k1_yellow_0(X28,X30))
        | ~ r1_tarski(X29,X30)
        | ~ v3_orders_2(X28)
        | ~ v4_orders_2(X28)
        | ~ v5_orders_2(X28)
        | ~ v1_lattice3(X28)
        | ~ v2_lattice3(X28)
        | ~ v3_lattice3(X28)
        | ~ l1_orders_2(X28) )
      & ( r1_orders_2(X28,k2_yellow_0(X28,X30),k2_yellow_0(X28,X29))
        | ~ r1_tarski(X29,X30)
        | ~ v3_orders_2(X28)
        | ~ v4_orders_2(X28)
        | ~ v5_orders_2(X28)
        | ~ v1_lattice3(X28)
        | ~ v2_lattice3(X28)
        | ~ v3_lattice3(X28)
        | ~ l1_orders_2(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_waybel_7])])])])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),X1))
    | r2_hidden(X1,esk1_3(esk3_0,esk4_0,esk5_0))
    | v1_xboole_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | r1_waybel_3(esk3_0,esk4_0,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_59]),c_0_60])]),c_0_61])).

cnf(c_0_67,plain,
    ( r1_waybel_3(X2,X1,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,esk1_3(X2,X1,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v24_waybel_0(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk4_0,esk1_3(esk3_0,esk4_0,esk5_0))
    | v1_xboole_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | r1_waybel_3(esk3_0,esk4_0,esk5_0)
    | m1_subset_1(esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_63,c_0_29])).

fof(c_0_69,plain,(
    ! [X9,X10,X11] :
      ( ( ~ r3_orders_2(X9,X10,X11)
        | r1_orders_2(X9,X10,X11)
        | v2_struct_0(X9)
        | ~ v3_orders_2(X9)
        | ~ l1_orders_2(X9)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | ~ m1_subset_1(X11,u1_struct_0(X9)) )
      & ( ~ r1_orders_2(X9,X10,X11)
        | r3_orders_2(X9,X10,X11)
        | v2_struct_0(X9)
        | ~ v3_orders_2(X9)
        | ~ l1_orders_2(X9)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | ~ m1_subset_1(X11,u1_struct_0(X9)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_70,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_71,plain,
    ( r3_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3))
    | ~ r1_tarski(X2,X3)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ v3_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk4_0))
    | r2_hidden(esk4_0,esk1_3(esk3_0,esk4_0,esk5_0))
    | v1_xboole_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | r1_waybel_3(esk3_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_29])).

cnf(c_0_73,plain,
    ( r3_orders_2(X1,X2,k1_yellow_0(X1,esk1_3(X1,X3,X2)))
    | r1_waybel_3(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v24_waybel_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_74,plain,
    ( r1_waybel_3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ v1_xboole_0(esk1_3(X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v24_waybel_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_75,negated_conjecture,
    ( v1_xboole_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | r1_waybel_3(esk3_0,esk4_0,esk5_0)
    | m1_subset_1(esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_23]),c_0_24]),c_0_27]),c_0_29]),c_0_25]),c_0_20]),c_0_16])]),c_0_21])).

cnf(c_0_76,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(k1_yellow_0(esk3_0,X1),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_16])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk4_0,esk1_3(esk3_0,esk4_0,esk5_0))
    | v1_xboole_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | r1_waybel_3(esk3_0,esk4_0,esk5_0)
    | r3_orders_2(X1,k1_yellow_0(X1,esk1_3(esk3_0,esk4_0,esk5_0)),k1_yellow_0(X1,esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk4_0)))
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v3_lattice3(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_79,negated_conjecture,
    ( r1_waybel_3(esk3_0,X1,X2)
    | r3_orders_2(esk3_0,X2,k1_yellow_0(esk3_0,esk1_3(esk3_0,X1,X2)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_23]),c_0_24]),c_0_25]),c_0_20]),c_0_16])]),c_0_21])).

cnf(c_0_80,negated_conjecture,
    ( r1_waybel_3(esk3_0,esk4_0,esk5_0)
    | m1_subset_1(esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_23]),c_0_24]),c_0_27]),c_0_29]),c_0_25]),c_0_20]),c_0_16])]),c_0_21])).

fof(c_0_81,plain,(
    ! [X20,X21,X22,X23] :
      ( ~ v4_orders_2(X20)
      | ~ l1_orders_2(X20)
      | ~ m1_subset_1(X21,u1_struct_0(X20))
      | ~ m1_subset_1(X22,u1_struct_0(X20))
      | ~ m1_subset_1(X23,u1_struct_0(X20))
      | ~ r1_orders_2(X20,X21,X22)
      | ~ r1_orders_2(X20,X22,X23)
      | r1_orders_2(X20,X21,X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_orders_2])])])).

cnf(c_0_82,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,k1_yellow_0(esk3_0,X2))
    | ~ r3_orders_2(esk3_0,X1,k1_yellow_0(esk3_0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_20]),c_0_16])]),c_0_21])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(esk4_0,esk1_3(esk3_0,esk4_0,esk5_0))
    | v1_xboole_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | r1_waybel_3(esk3_0,esk4_0,esk5_0)
    | r3_orders_2(esk3_0,k1_yellow_0(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0)),k1_yellow_0(esk3_0,esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_51]),c_0_23]),c_0_24]),c_0_15]),c_0_19]),c_0_20]),c_0_16])])).

cnf(c_0_84,negated_conjecture,
    ( r1_waybel_3(esk3_0,esk4_0,X1)
    | r3_orders_2(esk3_0,X1,k1_yellow_0(esk3_0,esk1_3(esk3_0,esk4_0,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_29])).

cnf(c_0_85,plain,
    ( v1_waybel_0(esk2_3(X1,X2,X3),X1)
    | r2_hidden(X3,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_waybel_1(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_86,plain,
    ( v12_waybel_0(esk2_3(X1,X2,X3),X1)
    | r2_hidden(X3,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_waybel_1(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_87,plain,
    ( v1_waybel_7(esk2_3(X1,X2,X3),X1)
    | r2_hidden(X3,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_waybel_1(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_88,negated_conjecture,
    ( v12_waybel_0(esk6_0,esk3_0)
    | m1_subset_1(esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_80])).

cnf(c_0_89,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_80])).

cnf(c_0_90,negated_conjecture,
    ( v1_waybel_0(esk6_0,esk3_0)
    | m1_subset_1(esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_80])).

cnf(c_0_91,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_80])).

cnf(c_0_92,plain,
    ( r1_orders_2(X1,X2,X4)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(esk4_0,esk1_3(esk3_0,esk4_0,esk5_0))
    | v1_xboole_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | r1_waybel_3(esk3_0,esk4_0,esk5_0)
    | r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0)),k1_yellow_0(esk3_0,esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_77])])).

cnf(c_0_94,negated_conjecture,
    ( r1_waybel_3(esk3_0,esk4_0,esk5_0)
    | r3_orders_2(esk3_0,esk5_0,k1_yellow_0(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_84,c_0_27])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(X1,X2)
    | v1_waybel_0(esk2_3(esk3_0,X2,X1),esk3_0)
    | v1_xboole_0(X2)
    | ~ v12_waybel_0(X2,esk3_0)
    | ~ v1_waybel_0(X2,esk3_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_51]),c_0_52]),c_0_23]),c_0_24]),c_0_15]),c_0_20]),c_0_16])])).

cnf(c_0_96,negated_conjecture,
    ( r2_hidden(X1,X2)
    | v12_waybel_0(esk2_3(esk3_0,X2,X1),esk3_0)
    | v1_xboole_0(X2)
    | ~ v12_waybel_0(X2,esk3_0)
    | ~ v1_waybel_0(X2,esk3_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_51]),c_0_52]),c_0_23]),c_0_24]),c_0_15]),c_0_20]),c_0_16])])).

cnf(c_0_97,negated_conjecture,
    ( v1_waybel_7(esk2_3(esk3_0,X1,X2),esk3_0)
    | r2_hidden(X2,X1)
    | v1_xboole_0(X1)
    | ~ v12_waybel_0(X1,esk3_0)
    | ~ v1_waybel_0(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_51]),c_0_52]),c_0_23]),c_0_24]),c_0_15]),c_0_20]),c_0_16])])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | m1_subset_1(esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_waybel_3(esk3_0,X1,X2)
    | ~ r3_orders_2(esk3_0,X2,k1_yellow_0(esk3_0,esk6_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_88]),c_0_24]),c_0_20]),c_0_16])]),c_0_21]),c_0_89]),c_0_90]),c_0_91])).

cnf(c_0_99,negated_conjecture,
    ( r3_orders_2(esk3_0,esk5_0,k1_yellow_0(esk3_0,esk6_0))
    | m1_subset_1(esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_80])).

cnf(c_0_100,plain,
    ( r3_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_101,negated_conjecture,
    ( r2_hidden(esk4_0,esk1_3(esk3_0,esk4_0,esk5_0))
    | v1_xboole_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | r1_waybel_3(esk3_0,esk4_0,esk5_0)
    | r1_orders_2(esk3_0,X1,k1_yellow_0(esk3_0,esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk4_0)))
    | ~ r1_orders_2(esk3_0,X1,k1_yellow_0(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_24]),c_0_77]),c_0_77]),c_0_16])])).

cnf(c_0_102,negated_conjecture,
    ( r1_waybel_3(esk3_0,esk4_0,esk5_0)
    | r1_orders_2(esk3_0,esk5_0,k1_yellow_0(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_94]),c_0_27])])).

cnf(c_0_103,negated_conjecture,
    ( r2_hidden(X1,esk1_3(esk3_0,esk4_0,esk5_0))
    | v1_waybel_0(esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),X1),esk3_0)
    | v1_xboole_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | r1_waybel_3(esk3_0,esk4_0,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_59]),c_0_60])]),c_0_61])).

cnf(c_0_104,negated_conjecture,
    ( r2_hidden(X1,esk1_3(esk3_0,esk4_0,esk5_0))
    | v12_waybel_0(esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),X1),esk3_0)
    | v1_xboole_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | r1_waybel_3(esk3_0,esk4_0,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_59]),c_0_60])]),c_0_61])).

cnf(c_0_105,negated_conjecture,
    ( v1_waybel_7(esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),X1),esk3_0)
    | r2_hidden(X1,esk1_3(esk3_0,esk4_0,esk5_0))
    | v1_xboole_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | r1_waybel_3(esk3_0,esk4_0,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_59]),c_0_60])]),c_0_61])).

cnf(c_0_106,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | m1_subset_1(esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_waybel_3(esk3_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_27])])).

cnf(c_0_107,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_80])).

cnf(c_0_108,negated_conjecture,
    ( r3_orders_2(esk3_0,X1,k1_yellow_0(esk3_0,X2))
    | ~ r1_orders_2(esk3_0,X1,k1_yellow_0(esk3_0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_77]),c_0_20]),c_0_16])]),c_0_21])).

cnf(c_0_109,negated_conjecture,
    ( r2_hidden(esk4_0,esk1_3(esk3_0,esk4_0,esk5_0))
    | v1_xboole_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | r1_waybel_3(esk3_0,esk4_0,esk5_0)
    | r1_orders_2(esk3_0,esk5_0,k1_yellow_0(esk3_0,esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_27])])).

cnf(c_0_110,negated_conjecture,
    ( r2_hidden(esk4_0,esk1_3(esk3_0,esk4_0,esk5_0))
    | v1_waybel_0(esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk4_0),esk3_0)
    | v1_xboole_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | r1_waybel_3(esk3_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_29])).

cnf(c_0_111,negated_conjecture,
    ( r2_hidden(esk4_0,esk1_3(esk3_0,esk4_0,esk5_0))
    | v12_waybel_0(esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk4_0),esk3_0)
    | v1_xboole_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | r1_waybel_3(esk3_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_104,c_0_29])).

cnf(c_0_112,plain,
    ( r2_hidden(X1,X3)
    | v1_xboole_0(X3)
    | ~ r2_hidden(X1,esk2_3(X2,X3,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v1_waybel_0(X3,X2)
    | ~ v12_waybel_0(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v2_waybel_1(X2)
    | ~ v1_lattice3(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_113,negated_conjecture,
    ( r1_waybel_3(esk3_0,esk4_0,esk5_0)
    | v1_xboole_0(X1)
    | r2_hidden(esk4_0,X1)
    | ~ v1_waybel_0(X1,esk3_0)
    | ~ v12_waybel_0(X1,esk3_0)
    | ~ v1_waybel_7(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r3_orders_2(esk3_0,esk5_0,k1_yellow_0(esk3_0,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_114,negated_conjecture,
    ( v1_waybel_7(esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk4_0),esk3_0)
    | r2_hidden(esk4_0,esk1_3(esk3_0,esk4_0,esk5_0))
    | v1_xboole_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | r1_waybel_3(esk3_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_105,c_0_29])).

cnf(c_0_115,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_80]),c_0_29])]),c_0_107])).

cnf(c_0_116,negated_conjecture,
    ( r2_hidden(esk4_0,esk1_3(esk3_0,esk4_0,esk5_0))
    | v1_xboole_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | r1_waybel_3(esk3_0,esk4_0,esk5_0)
    | r3_orders_2(esk3_0,esk5_0,k1_yellow_0(esk3_0,esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_27])])).

cnf(c_0_117,negated_conjecture,
    ( v1_waybel_0(esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk4_0),esk3_0)
    | v1_xboole_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | r1_waybel_3(esk3_0,esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_110]),c_0_23]),c_0_24]),c_0_27]),c_0_29]),c_0_25]),c_0_20]),c_0_16])]),c_0_21])).

cnf(c_0_118,negated_conjecture,
    ( v12_waybel_0(esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk4_0),esk3_0)
    | v1_xboole_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | r1_waybel_3(esk3_0,esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_111]),c_0_23]),c_0_24]),c_0_27]),c_0_29]),c_0_25]),c_0_20]),c_0_16])]),c_0_21])).

cnf(c_0_119,plain,
    ( r2_hidden(X3,X2)
    | v1_xboole_0(X2)
    | ~ v1_xboole_0(esk2_3(X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_waybel_1(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_120,negated_conjecture,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,esk2_3(esk3_0,X2,X1))
    | ~ v12_waybel_0(X2,esk3_0)
    | ~ v1_waybel_0(X2,esk3_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_51]),c_0_52]),c_0_23]),c_0_24]),c_0_15]),c_0_20]),c_0_16])])).

cnf(c_0_121,negated_conjecture,
    ( r2_hidden(esk4_0,esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk4_0))
    | r2_hidden(esk4_0,esk1_3(esk3_0,esk4_0,esk5_0))
    | v1_xboole_0(esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk4_0))
    | v1_xboole_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | r1_waybel_3(esk3_0,esk4_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_115])]),c_0_116]),c_0_117]),c_0_118])).

cnf(c_0_122,negated_conjecture,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ v12_waybel_0(X2,esk3_0)
    | ~ v1_waybel_0(X2,esk3_0)
    | ~ v1_xboole_0(esk2_3(esk3_0,X2,X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_51]),c_0_52]),c_0_23]),c_0_24]),c_0_15]),c_0_20]),c_0_16])])).

cnf(c_0_123,negated_conjecture,
    ( r2_hidden(esk4_0,esk1_3(esk3_0,esk4_0,esk5_0))
    | v1_xboole_0(esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk4_0))
    | v1_xboole_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | r1_waybel_3(esk3_0,esk4_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_121]),c_0_60]),c_0_29])]),c_0_61]),c_0_59])).

cnf(c_0_124,negated_conjecture,
    ( r2_hidden(X1,esk1_3(esk3_0,esk4_0,esk5_0))
    | v1_xboole_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | r1_waybel_3(esk3_0,esk4_0,esk5_0)
    | ~ v1_xboole_0(esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_59]),c_0_60])]),c_0_61])).

cnf(c_0_125,negated_conjecture,
    ( v1_xboole_0(esk2_3(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk4_0))
    | v1_xboole_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | r1_waybel_3(esk3_0,esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_123]),c_0_23]),c_0_24]),c_0_27]),c_0_29]),c_0_25]),c_0_20]),c_0_16])]),c_0_21])).

cnf(c_0_126,negated_conjecture,
    ( r2_hidden(esk4_0,esk1_3(esk3_0,esk4_0,esk5_0))
    | v1_xboole_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | r1_waybel_3(esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_125]),c_0_29])])).

cnf(c_0_127,negated_conjecture,
    ( v1_xboole_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | r1_waybel_3(esk3_0,esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_126]),c_0_23]),c_0_24]),c_0_27]),c_0_29]),c_0_25]),c_0_20]),c_0_16])]),c_0_21])).

cnf(c_0_128,negated_conjecture,
    ( r1_waybel_3(esk3_0,esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_127]),c_0_23]),c_0_24]),c_0_27]),c_0_29]),c_0_25]),c_0_20]),c_0_16])]),c_0_21])).

cnf(c_0_129,negated_conjecture,
    ( v12_waybel_0(esk6_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_128])])).

cnf(c_0_130,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_128])])).

cnf(c_0_131,negated_conjecture,
    ( v1_waybel_0(esk6_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_128])])).

cnf(c_0_132,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_128])])).

cnf(c_0_133,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r1_waybel_3(esk3_0,X1,X2)
    | ~ r3_orders_2(esk3_0,X2,k1_yellow_0(esk3_0,esk6_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_129]),c_0_24]),c_0_20]),c_0_16])]),c_0_130]),c_0_21]),c_0_131]),c_0_132])])).

cnf(c_0_134,negated_conjecture,
    ( r3_orders_2(esk3_0,esk5_0,k1_yellow_0(esk3_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_128])])).

cnf(c_0_135,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r1_waybel_3(esk3_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_134]),c_0_27])])).

cnf(c_0_136,negated_conjecture,
    ( ~ r2_hidden(esk4_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_128])])).

cnf(c_0_137,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_128]),c_0_29])]),c_0_136]),
    [proof]).

%------------------------------------------------------------------------------
