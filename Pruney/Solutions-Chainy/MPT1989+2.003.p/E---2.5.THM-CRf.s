%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:31 EST 2020

% Result     : Theorem 0.17s
% Output     : CNFRefutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 841 expanded)
%              Number of clauses        :   56 ( 290 expanded)
%              Number of leaves         :   12 ( 205 expanded)
%              Depth                    :   15
%              Number of atoms          :  476 (5646 expanded)
%              Number of equality atoms :   22 (  68 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal clause size      :   68 (   3 average)
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

fof(dt_k5_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k5_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_waybel_0)).

fof(cc1_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

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

fof(t24_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r1_orders_2(X1,X2,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

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

fof(c_0_12,negated_conjecture,(
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

fof(c_0_13,plain,(
    ! [X22,X23] :
      ( v2_struct_0(X22)
      | ~ l1_orders_2(X22)
      | ~ m1_subset_1(X23,u1_struct_0(X22))
      | m1_subset_1(k5_waybel_0(X22,X23),k1_zfmisc_1(u1_struct_0(X22))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_waybel_0])])])).

fof(c_0_14,negated_conjecture,
    ( v3_orders_2(esk4_0)
    & v4_orders_2(esk4_0)
    & v5_orders_2(esk4_0)
    & v1_lattice3(esk4_0)
    & v2_lattice3(esk4_0)
    & l1_orders_2(esk4_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & v5_waybel_6(esk5_0,esk4_0)
    & ~ v4_waybel_7(esk5_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_15,plain,(
    ! [X10] :
      ( ~ l1_orders_2(X10)
      | ~ v1_lattice3(X10)
      | ~ v2_struct_0(X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).

cnf(c_0_16,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X5,X6,X7] :
      ( ~ r2_hidden(X5,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X7))
      | m1_subset_1(X5,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_20,plain,
    ( ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( v2_struct_0(esk4_0)
    | m1_subset_1(k5_waybel_0(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])])).

cnf(c_0_22,negated_conjecture,
    ( v1_lattice3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_23,plain,(
    ! [X28,X29,X30] :
      ( ( ~ r2_hidden(X30,k5_waybel_0(X28,X29))
        | r1_orders_2(X28,X30,X29)
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | v2_struct_0(X28)
        | ~ l1_orders_2(X28) )
      & ( ~ r1_orders_2(X28,X30,X29)
        | r2_hidden(X30,k5_waybel_0(X28,X29))
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | v2_struct_0(X28)
        | ~ l1_orders_2(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t17_waybel_0])])])])])).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(k5_waybel_0(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_18])])).

fof(c_0_26,plain,(
    ! [X11,X12,X13,X14] :
      ( ( ~ r2_lattice3(X11,X12,X13)
        | ~ m1_subset_1(X14,u1_struct_0(X11))
        | ~ r2_hidden(X14,X12)
        | r1_orders_2(X11,X14,X13)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ l1_orders_2(X11) )
      & ( m1_subset_1(esk1_3(X11,X12,X13),u1_struct_0(X11))
        | r2_lattice3(X11,X12,X13)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ l1_orders_2(X11) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X12)
        | r2_lattice3(X11,X12,X13)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ l1_orders_2(X11) )
      & ( ~ r1_orders_2(X11,esk1_3(X11,X12,X13),X13)
        | r2_lattice3(X11,X12,X13)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ l1_orders_2(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

fof(c_0_27,plain,(
    ! [X8,X9] :
      ( v2_struct_0(X8)
      | ~ v3_orders_2(X8)
      | ~ l1_orders_2(X8)
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | r1_orders_2(X8,X9,X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_orders_2])])])])).

cnf(c_0_28,plain,
    ( r1_orders_2(X2,X1,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k5_waybel_0(X2,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,k5_waybel_0(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk1_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( r2_hidden(X2,k5_waybel_0(X1,X3))
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( v3_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_35,plain,(
    ! [X16,X17,X18,X19,X20] :
      ( ( r2_lattice3(X16,X18,X17)
        | X17 != k1_yellow_0(X16,X18)
        | ~ r1_yellow_0(X16,X18)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ v5_orders_2(X16)
        | ~ l1_orders_2(X16) )
      & ( ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ r2_lattice3(X16,X18,X19)
        | r1_orders_2(X16,X17,X19)
        | X17 != k1_yellow_0(X16,X18)
        | ~ r1_yellow_0(X16,X18)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ v5_orders_2(X16)
        | ~ l1_orders_2(X16) )
      & ( X17 = k1_yellow_0(X16,X20)
        | m1_subset_1(esk2_3(X16,X17,X20),u1_struct_0(X16))
        | ~ r2_lattice3(X16,X20,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ v5_orders_2(X16)
        | ~ l1_orders_2(X16) )
      & ( r1_yellow_0(X16,X20)
        | m1_subset_1(esk2_3(X16,X17,X20),u1_struct_0(X16))
        | ~ r2_lattice3(X16,X20,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ v5_orders_2(X16)
        | ~ l1_orders_2(X16) )
      & ( X17 = k1_yellow_0(X16,X20)
        | r2_lattice3(X16,X20,esk2_3(X16,X17,X20))
        | ~ r2_lattice3(X16,X20,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ v5_orders_2(X16)
        | ~ l1_orders_2(X16) )
      & ( r1_yellow_0(X16,X20)
        | r2_lattice3(X16,X20,esk2_3(X16,X17,X20))
        | ~ r2_lattice3(X16,X20,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ v5_orders_2(X16)
        | ~ l1_orders_2(X16) )
      & ( X17 = k1_yellow_0(X16,X20)
        | ~ r1_orders_2(X16,X17,esk2_3(X16,X17,X20))
        | ~ r2_lattice3(X16,X20,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ v5_orders_2(X16)
        | ~ l1_orders_2(X16) )
      & ( r1_yellow_0(X16,X20)
        | ~ r1_orders_2(X16,X17,esk2_3(X16,X17,X20))
        | ~ r2_lattice3(X16,X20,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ v5_orders_2(X16)
        | ~ l1_orders_2(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_yellow_0])])])])])])).

cnf(c_0_36,negated_conjecture,
    ( r1_orders_2(esk4_0,X1,esk5_0)
    | v2_struct_0(esk4_0)
    | ~ r2_hidden(X1,k5_waybel_0(esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_17]),c_0_18])]),c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk5_0)
    | r2_hidden(esk1_3(esk4_0,X1,esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_17]),c_0_18])])).

cnf(c_0_38,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk5_0)
    | ~ r1_orders_2(esk4_0,esk1_3(esk4_0,X1,esk5_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_17]),c_0_18])])).

fof(c_0_39,plain,(
    ! [X31,X32,X34] :
      ( ( ~ v1_xboole_0(esk3_2(X31,X32))
        | ~ v4_waybel_7(X32,X31)
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | ~ v3_orders_2(X31)
        | ~ v4_orders_2(X31)
        | ~ v5_orders_2(X31)
        | ~ v1_lattice3(X31)
        | ~ v2_lattice3(X31)
        | ~ l1_orders_2(X31) )
      & ( v1_waybel_0(esk3_2(X31,X32),X31)
        | ~ v4_waybel_7(X32,X31)
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | ~ v3_orders_2(X31)
        | ~ v4_orders_2(X31)
        | ~ v5_orders_2(X31)
        | ~ v1_lattice3(X31)
        | ~ v2_lattice3(X31)
        | ~ l1_orders_2(X31) )
      & ( v12_waybel_0(esk3_2(X31,X32),X31)
        | ~ v4_waybel_7(X32,X31)
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | ~ v3_orders_2(X31)
        | ~ v4_orders_2(X31)
        | ~ v5_orders_2(X31)
        | ~ v1_lattice3(X31)
        | ~ v2_lattice3(X31)
        | ~ l1_orders_2(X31) )
      & ( v1_waybel_7(esk3_2(X31,X32),X31)
        | ~ v4_waybel_7(X32,X31)
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | ~ v3_orders_2(X31)
        | ~ v4_orders_2(X31)
        | ~ v5_orders_2(X31)
        | ~ v1_lattice3(X31)
        | ~ v2_lattice3(X31)
        | ~ l1_orders_2(X31) )
      & ( m1_subset_1(esk3_2(X31,X32),k1_zfmisc_1(u1_struct_0(X31)))
        | ~ v4_waybel_7(X32,X31)
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | ~ v3_orders_2(X31)
        | ~ v4_orders_2(X31)
        | ~ v5_orders_2(X31)
        | ~ v1_lattice3(X31)
        | ~ v2_lattice3(X31)
        | ~ l1_orders_2(X31) )
      & ( X32 = k1_yellow_0(X31,esk3_2(X31,X32))
        | ~ v4_waybel_7(X32,X31)
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | ~ v3_orders_2(X31)
        | ~ v4_orders_2(X31)
        | ~ v5_orders_2(X31)
        | ~ v1_lattice3(X31)
        | ~ v2_lattice3(X31)
        | ~ l1_orders_2(X31) )
      & ( v1_xboole_0(X34)
        | ~ v1_waybel_0(X34,X31)
        | ~ v12_waybel_0(X34,X31)
        | ~ v1_waybel_7(X34,X31)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X31)))
        | X32 != k1_yellow_0(X31,X34)
        | v4_waybel_7(X32,X31)
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | ~ v3_orders_2(X31)
        | ~ v4_orders_2(X31)
        | ~ v5_orders_2(X31)
        | ~ v1_lattice3(X31)
        | ~ v2_lattice3(X31)
        | ~ l1_orders_2(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_waybel_7])])])])])])).

fof(c_0_40,plain,(
    ! [X35,X36] :
      ( ~ v3_orders_2(X35)
      | ~ v4_orders_2(X35)
      | ~ v5_orders_2(X35)
      | ~ v1_lattice3(X35)
      | ~ v2_lattice3(X35)
      | ~ l1_orders_2(X35)
      | ~ m1_subset_1(X36,u1_struct_0(X35))
      | ~ v5_waybel_6(X36,X35)
      | v1_waybel_7(k5_waybel_0(X35,X36),X35) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_waybel_7])])])).

cnf(c_0_41,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_42,negated_conjecture,
    ( v2_struct_0(esk4_0)
    | r2_hidden(X1,k5_waybel_0(esk4_0,esk5_0))
    | ~ r1_orders_2(esk4_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_17]),c_0_18])])).

cnf(c_0_43,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk5_0)
    | v2_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_17]),c_0_18]),c_0_34])])).

cnf(c_0_44,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | m1_subset_1(esk2_3(X2,X1,X3),u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( v5_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_46,negated_conjecture,
    ( r2_lattice3(esk4_0,k5_waybel_0(esk4_0,esk5_0),esk5_0)
    | v2_struct_0(esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])).

cnf(c_0_47,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | r2_lattice3(X2,X3,esk2_3(X2,X1,X3))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | ~ r1_orders_2(X2,X1,esk2_3(X2,X1,X3))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_49,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_50,plain,
    ( v1_waybel_7(k5_waybel_0(X1,X2),X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_waybel_6(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_51,negated_conjecture,
    ( v5_waybel_6(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_52,negated_conjecture,
    ( v2_lattice3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_53,negated_conjecture,
    ( v4_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_54,plain,(
    ! [X26,X27] :
      ( ( ~ v1_xboole_0(k5_waybel_0(X26,X27))
        | v2_struct_0(X26)
        | ~ v3_orders_2(X26)
        | ~ l1_orders_2(X26)
        | ~ m1_subset_1(X27,u1_struct_0(X26)) )
      & ( v1_waybel_0(k5_waybel_0(X26,X27),X26)
        | v2_struct_0(X26)
        | ~ v3_orders_2(X26)
        | ~ l1_orders_2(X26)
        | ~ m1_subset_1(X27,u1_struct_0(X26)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc8_waybel_0])])])])).

fof(c_0_55,plain,(
    ! [X24,X25] :
      ( v2_struct_0(X24)
      | ~ v4_orders_2(X24)
      | ~ l1_orders_2(X24)
      | ~ m1_subset_1(X25,u1_struct_0(X24))
      | v12_waybel_0(k5_waybel_0(X24,X25),X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc12_waybel_0])])])).

cnf(c_0_56,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,X1)
    | ~ r2_lattice3(esk4_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(esk5_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_17]),c_0_18])])).

cnf(c_0_57,negated_conjecture,
    ( v2_struct_0(esk4_0)
    | r2_hidden(esk5_0,k5_waybel_0(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_17])])).

cnf(c_0_58,negated_conjecture,
    ( k1_yellow_0(esk4_0,X1) = esk5_0
    | m1_subset_1(esk2_3(esk4_0,esk5_0,X1),u1_struct_0(esk4_0))
    | ~ r2_lattice3(esk4_0,X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_17]),c_0_45]),c_0_18])])).

cnf(c_0_59,negated_conjecture,
    ( r2_lattice3(esk4_0,k5_waybel_0(esk4_0,esk5_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_46]),c_0_22]),c_0_18])])).

cnf(c_0_60,negated_conjecture,
    ( k1_yellow_0(esk4_0,X1) = esk5_0
    | r2_lattice3(esk4_0,X1,esk2_3(esk4_0,esk5_0,X1))
    | ~ r2_lattice3(esk4_0,X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_17]),c_0_45]),c_0_18])])).

cnf(c_0_61,negated_conjecture,
    ( k1_yellow_0(esk4_0,X1) = esk5_0
    | ~ r2_lattice3(esk4_0,X1,esk5_0)
    | ~ r1_orders_2(esk4_0,esk5_0,esk2_3(esk4_0,esk5_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_17]),c_0_45]),c_0_18])])).

cnf(c_0_62,plain,
    ( v4_waybel_7(k1_yellow_0(X1,X2),X1)
    | v1_xboole_0(X2)
    | ~ v1_waybel_7(X2,X1)
    | ~ v2_lattice3(X1)
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_63,negated_conjecture,
    ( v1_waybel_7(k5_waybel_0(esk4_0,esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_17]),c_0_51]),c_0_52]),c_0_53]),c_0_45]),c_0_22]),c_0_18]),c_0_34])])).

cnf(c_0_64,plain,
    ( v1_waybel_0(k5_waybel_0(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_65,plain,
    ( v2_struct_0(X1)
    | v12_waybel_0(k5_waybel_0(X1,X2),X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_66,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,X1)
    | v2_struct_0(esk4_0)
    | ~ r2_lattice3(esk4_0,k5_waybel_0(esk4_0,esk5_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_67,negated_conjecture,
    ( k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0)) = esk5_0
    | m1_subset_1(esk2_3(esk4_0,esk5_0,k5_waybel_0(esk4_0,esk5_0)),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_68,negated_conjecture,
    ( k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0)) = esk5_0
    | r2_lattice3(esk4_0,k5_waybel_0(esk4_0,esk5_0),esk2_3(esk4_0,esk5_0,k5_waybel_0(esk4_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_59])).

cnf(c_0_69,negated_conjecture,
    ( k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0)) = esk5_0
    | ~ r1_orders_2(esk4_0,esk5_0,esk2_3(esk4_0,esk5_0,k5_waybel_0(esk4_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_59])).

cnf(c_0_70,negated_conjecture,
    ( v4_waybel_7(k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0)),esk4_0)
    | v1_xboole_0(k5_waybel_0(esk4_0,esk5_0))
    | ~ v1_waybel_0(k5_waybel_0(esk4_0,esk5_0),esk4_0)
    | ~ v12_waybel_0(k5_waybel_0(esk4_0,esk5_0),esk4_0)
    | ~ m1_subset_1(k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0)),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_25]),c_0_63]),c_0_52]),c_0_53]),c_0_45]),c_0_22]),c_0_18]),c_0_34])])).

cnf(c_0_71,negated_conjecture,
    ( v1_waybel_0(k5_waybel_0(esk4_0,esk5_0),esk4_0)
    | v2_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_17]),c_0_18]),c_0_34])])).

cnf(c_0_72,negated_conjecture,
    ( v12_waybel_0(k5_waybel_0(esk4_0,esk5_0),esk4_0)
    | v2_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_17]),c_0_53]),c_0_18])])).

cnf(c_0_73,negated_conjecture,
    ( k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0)) = esk5_0
    | v2_struct_0(esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68]),c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( v4_waybel_7(k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0)),esk4_0)
    | v1_xboole_0(k5_waybel_0(esk4_0,esk5_0))
    | v2_struct_0(esk4_0)
    | ~ m1_subset_1(k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0)),u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72])).

cnf(c_0_75,negated_conjecture,
    ( k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0)) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_73]),c_0_22]),c_0_18])])).

cnf(c_0_76,negated_conjecture,
    ( ~ v4_waybel_7(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_77,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(k5_waybel_0(X1,X2))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_78,negated_conjecture,
    ( v1_xboole_0(k5_waybel_0(esk4_0,esk5_0))
    | v2_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_75]),c_0_75]),c_0_17])]),c_0_76])).

cnf(c_0_79,negated_conjecture,
    ( v2_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_18]),c_0_34]),c_0_17])])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_79]),c_0_22]),c_0_18])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n019.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 13:51:07 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 0.17/0.40  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.17/0.40  # and selection function SelectNewComplexAHP.
% 0.17/0.40  #
% 0.17/0.40  # Preprocessing time       : 0.054 s
% 0.17/0.40  # Presaturation interreduction done
% 0.17/0.40  
% 0.17/0.40  # Proof found!
% 0.17/0.40  # SZS status Theorem
% 0.17/0.40  # SZS output start CNFRefutation
% 0.17/0.40  fof(t38_waybel_7, conjecture, ![X1]:((((((v3_orders_2(X1)&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v5_waybel_6(X2,X1)=>v4_waybel_7(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_waybel_7)).
% 0.17/0.40  fof(dt_k5_waybel_0, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>m1_subset_1(k5_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_waybel_0)).
% 0.17/0.40  fof(cc1_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v1_lattice3(X1)=>~(v2_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattice3)).
% 0.17/0.40  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.17/0.40  fof(t17_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k5_waybel_0(X1,X2))<=>r1_orders_2(X1,X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_waybel_0)).
% 0.17/0.40  fof(d9_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 0.17/0.40  fof(t24_orders_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,X2,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_orders_2)).
% 0.17/0.40  fof(t30_yellow_0, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(((X2=k1_yellow_0(X1,X3)&r1_yellow_0(X1,X3))=>(r2_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X3,X4)=>r1_orders_2(X1,X2,X4)))))&((r2_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X3,X4)=>r1_orders_2(X1,X2,X4))))=>(X2=k1_yellow_0(X1,X3)&r1_yellow_0(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_yellow_0)).
% 0.17/0.40  fof(d6_waybel_7, axiom, ![X1]:((((((v3_orders_2(X1)&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v4_waybel_7(X2,X1)<=>?[X3]:(((((~(v1_xboole_0(X3))&v1_waybel_0(X3,X1))&v12_waybel_0(X3,X1))&v1_waybel_7(X3,X1))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))&X2=k1_yellow_0(X1,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_waybel_7)).
% 0.17/0.40  fof(t37_waybel_7, axiom, ![X1]:((((((v3_orders_2(X1)&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v5_waybel_6(X2,X1)=>v1_waybel_7(k5_waybel_0(X1,X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_waybel_7)).
% 0.17/0.40  fof(fc8_waybel_0, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>(~(v1_xboole_0(k5_waybel_0(X1,X2)))&v1_waybel_0(k5_waybel_0(X1,X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_waybel_0)).
% 0.17/0.40  fof(fc12_waybel_0, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v4_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>v12_waybel_0(k5_waybel_0(X1,X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc12_waybel_0)).
% 0.17/0.40  fof(c_0_12, negated_conjecture, ~(![X1]:((((((v3_orders_2(X1)&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v5_waybel_6(X2,X1)=>v4_waybel_7(X2,X1))))), inference(assume_negation,[status(cth)],[t38_waybel_7])).
% 0.17/0.40  fof(c_0_13, plain, ![X22, X23]:(v2_struct_0(X22)|~l1_orders_2(X22)|~m1_subset_1(X23,u1_struct_0(X22))|m1_subset_1(k5_waybel_0(X22,X23),k1_zfmisc_1(u1_struct_0(X22)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_waybel_0])])])).
% 0.17/0.40  fof(c_0_14, negated_conjecture, ((((((v3_orders_2(esk4_0)&v4_orders_2(esk4_0))&v5_orders_2(esk4_0))&v1_lattice3(esk4_0))&v2_lattice3(esk4_0))&l1_orders_2(esk4_0))&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&(v5_waybel_6(esk5_0,esk4_0)&~v4_waybel_7(esk5_0,esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.17/0.40  fof(c_0_15, plain, ![X10]:(~l1_orders_2(X10)|(~v1_lattice3(X10)|~v2_struct_0(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).
% 0.17/0.40  cnf(c_0_16, plain, (v2_struct_0(X1)|m1_subset_1(k5_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.17/0.40  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.17/0.40  cnf(c_0_18, negated_conjecture, (l1_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.17/0.40  fof(c_0_19, plain, ![X5, X6, X7]:(~r2_hidden(X5,X6)|~m1_subset_1(X6,k1_zfmisc_1(X7))|m1_subset_1(X5,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.17/0.40  cnf(c_0_20, plain, (~l1_orders_2(X1)|~v1_lattice3(X1)|~v2_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.17/0.40  cnf(c_0_21, negated_conjecture, (v2_struct_0(esk4_0)|m1_subset_1(k5_waybel_0(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])])).
% 0.17/0.40  cnf(c_0_22, negated_conjecture, (v1_lattice3(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.17/0.40  fof(c_0_23, plain, ![X28, X29, X30]:((~r2_hidden(X30,k5_waybel_0(X28,X29))|r1_orders_2(X28,X30,X29)|~m1_subset_1(X30,u1_struct_0(X28))|~m1_subset_1(X29,u1_struct_0(X28))|(v2_struct_0(X28)|~l1_orders_2(X28)))&(~r1_orders_2(X28,X30,X29)|r2_hidden(X30,k5_waybel_0(X28,X29))|~m1_subset_1(X30,u1_struct_0(X28))|~m1_subset_1(X29,u1_struct_0(X28))|(v2_struct_0(X28)|~l1_orders_2(X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t17_waybel_0])])])])])).
% 0.17/0.40  cnf(c_0_24, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.17/0.40  cnf(c_0_25, negated_conjecture, (m1_subset_1(k5_waybel_0(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_18])])).
% 0.17/0.40  fof(c_0_26, plain, ![X11, X12, X13, X14]:((~r2_lattice3(X11,X12,X13)|(~m1_subset_1(X14,u1_struct_0(X11))|(~r2_hidden(X14,X12)|r1_orders_2(X11,X14,X13)))|~m1_subset_1(X13,u1_struct_0(X11))|~l1_orders_2(X11))&((m1_subset_1(esk1_3(X11,X12,X13),u1_struct_0(X11))|r2_lattice3(X11,X12,X13)|~m1_subset_1(X13,u1_struct_0(X11))|~l1_orders_2(X11))&((r2_hidden(esk1_3(X11,X12,X13),X12)|r2_lattice3(X11,X12,X13)|~m1_subset_1(X13,u1_struct_0(X11))|~l1_orders_2(X11))&(~r1_orders_2(X11,esk1_3(X11,X12,X13),X13)|r2_lattice3(X11,X12,X13)|~m1_subset_1(X13,u1_struct_0(X11))|~l1_orders_2(X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).
% 0.17/0.40  fof(c_0_27, plain, ![X8, X9]:(v2_struct_0(X8)|~v3_orders_2(X8)|~l1_orders_2(X8)|(~m1_subset_1(X9,u1_struct_0(X8))|r1_orders_2(X8,X9,X9))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_orders_2])])])])).
% 0.17/0.40  cnf(c_0_28, plain, (r1_orders_2(X2,X1,X3)|v2_struct_0(X2)|~r2_hidden(X1,k5_waybel_0(X2,X3))|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.17/0.40  cnf(c_0_29, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk4_0))|~r2_hidden(X1,k5_waybel_0(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.17/0.40  cnf(c_0_30, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.17/0.40  cnf(c_0_31, plain, (r2_lattice3(X1,X2,X3)|~r1_orders_2(X1,esk1_3(X1,X2,X3),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.17/0.40  cnf(c_0_32, plain, (r2_hidden(X2,k5_waybel_0(X1,X3))|v2_struct_0(X1)|~r1_orders_2(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.17/0.40  cnf(c_0_33, plain, (v2_struct_0(X1)|r1_orders_2(X1,X2,X2)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.17/0.40  cnf(c_0_34, negated_conjecture, (v3_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.17/0.40  fof(c_0_35, plain, ![X16, X17, X18, X19, X20]:(((r2_lattice3(X16,X18,X17)|(X17!=k1_yellow_0(X16,X18)|~r1_yellow_0(X16,X18))|~m1_subset_1(X17,u1_struct_0(X16))|(~v5_orders_2(X16)|~l1_orders_2(X16)))&(~m1_subset_1(X19,u1_struct_0(X16))|(~r2_lattice3(X16,X18,X19)|r1_orders_2(X16,X17,X19))|(X17!=k1_yellow_0(X16,X18)|~r1_yellow_0(X16,X18))|~m1_subset_1(X17,u1_struct_0(X16))|(~v5_orders_2(X16)|~l1_orders_2(X16))))&(((X17=k1_yellow_0(X16,X20)|(m1_subset_1(esk2_3(X16,X17,X20),u1_struct_0(X16))|~r2_lattice3(X16,X20,X17))|~m1_subset_1(X17,u1_struct_0(X16))|(~v5_orders_2(X16)|~l1_orders_2(X16)))&(r1_yellow_0(X16,X20)|(m1_subset_1(esk2_3(X16,X17,X20),u1_struct_0(X16))|~r2_lattice3(X16,X20,X17))|~m1_subset_1(X17,u1_struct_0(X16))|(~v5_orders_2(X16)|~l1_orders_2(X16))))&(((X17=k1_yellow_0(X16,X20)|(r2_lattice3(X16,X20,esk2_3(X16,X17,X20))|~r2_lattice3(X16,X20,X17))|~m1_subset_1(X17,u1_struct_0(X16))|(~v5_orders_2(X16)|~l1_orders_2(X16)))&(r1_yellow_0(X16,X20)|(r2_lattice3(X16,X20,esk2_3(X16,X17,X20))|~r2_lattice3(X16,X20,X17))|~m1_subset_1(X17,u1_struct_0(X16))|(~v5_orders_2(X16)|~l1_orders_2(X16))))&((X17=k1_yellow_0(X16,X20)|(~r1_orders_2(X16,X17,esk2_3(X16,X17,X20))|~r2_lattice3(X16,X20,X17))|~m1_subset_1(X17,u1_struct_0(X16))|(~v5_orders_2(X16)|~l1_orders_2(X16)))&(r1_yellow_0(X16,X20)|(~r1_orders_2(X16,X17,esk2_3(X16,X17,X20))|~r2_lattice3(X16,X20,X17))|~m1_subset_1(X17,u1_struct_0(X16))|(~v5_orders_2(X16)|~l1_orders_2(X16))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_yellow_0])])])])])])).
% 0.17/0.40  cnf(c_0_36, negated_conjecture, (r1_orders_2(esk4_0,X1,esk5_0)|v2_struct_0(esk4_0)|~r2_hidden(X1,k5_waybel_0(esk4_0,esk5_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_17]), c_0_18])]), c_0_29])).
% 0.17/0.40  cnf(c_0_37, negated_conjecture, (r2_lattice3(esk4_0,X1,esk5_0)|r2_hidden(esk1_3(esk4_0,X1,esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_17]), c_0_18])])).
% 0.17/0.40  cnf(c_0_38, negated_conjecture, (r2_lattice3(esk4_0,X1,esk5_0)|~r1_orders_2(esk4_0,esk1_3(esk4_0,X1,esk5_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_17]), c_0_18])])).
% 0.17/0.40  fof(c_0_39, plain, ![X31, X32, X34]:(((((((~v1_xboole_0(esk3_2(X31,X32))|~v4_waybel_7(X32,X31)|~m1_subset_1(X32,u1_struct_0(X31))|(~v3_orders_2(X31)|~v4_orders_2(X31)|~v5_orders_2(X31)|~v1_lattice3(X31)|~v2_lattice3(X31)|~l1_orders_2(X31)))&(v1_waybel_0(esk3_2(X31,X32),X31)|~v4_waybel_7(X32,X31)|~m1_subset_1(X32,u1_struct_0(X31))|(~v3_orders_2(X31)|~v4_orders_2(X31)|~v5_orders_2(X31)|~v1_lattice3(X31)|~v2_lattice3(X31)|~l1_orders_2(X31))))&(v12_waybel_0(esk3_2(X31,X32),X31)|~v4_waybel_7(X32,X31)|~m1_subset_1(X32,u1_struct_0(X31))|(~v3_orders_2(X31)|~v4_orders_2(X31)|~v5_orders_2(X31)|~v1_lattice3(X31)|~v2_lattice3(X31)|~l1_orders_2(X31))))&(v1_waybel_7(esk3_2(X31,X32),X31)|~v4_waybel_7(X32,X31)|~m1_subset_1(X32,u1_struct_0(X31))|(~v3_orders_2(X31)|~v4_orders_2(X31)|~v5_orders_2(X31)|~v1_lattice3(X31)|~v2_lattice3(X31)|~l1_orders_2(X31))))&(m1_subset_1(esk3_2(X31,X32),k1_zfmisc_1(u1_struct_0(X31)))|~v4_waybel_7(X32,X31)|~m1_subset_1(X32,u1_struct_0(X31))|(~v3_orders_2(X31)|~v4_orders_2(X31)|~v5_orders_2(X31)|~v1_lattice3(X31)|~v2_lattice3(X31)|~l1_orders_2(X31))))&(X32=k1_yellow_0(X31,esk3_2(X31,X32))|~v4_waybel_7(X32,X31)|~m1_subset_1(X32,u1_struct_0(X31))|(~v3_orders_2(X31)|~v4_orders_2(X31)|~v5_orders_2(X31)|~v1_lattice3(X31)|~v2_lattice3(X31)|~l1_orders_2(X31))))&(v1_xboole_0(X34)|~v1_waybel_0(X34,X31)|~v12_waybel_0(X34,X31)|~v1_waybel_7(X34,X31)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X31)))|X32!=k1_yellow_0(X31,X34)|v4_waybel_7(X32,X31)|~m1_subset_1(X32,u1_struct_0(X31))|(~v3_orders_2(X31)|~v4_orders_2(X31)|~v5_orders_2(X31)|~v1_lattice3(X31)|~v2_lattice3(X31)|~l1_orders_2(X31)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_waybel_7])])])])])])).
% 0.17/0.40  fof(c_0_40, plain, ![X35, X36]:(~v3_orders_2(X35)|~v4_orders_2(X35)|~v5_orders_2(X35)|~v1_lattice3(X35)|~v2_lattice3(X35)|~l1_orders_2(X35)|(~m1_subset_1(X36,u1_struct_0(X35))|(~v5_waybel_6(X36,X35)|v1_waybel_7(k5_waybel_0(X35,X36),X35)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_waybel_7])])])).
% 0.17/0.40  cnf(c_0_41, plain, (r1_orders_2(X1,X4,X3)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.17/0.40  cnf(c_0_42, negated_conjecture, (v2_struct_0(esk4_0)|r2_hidden(X1,k5_waybel_0(esk4_0,esk5_0))|~r1_orders_2(esk4_0,X1,esk5_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_17]), c_0_18])])).
% 0.17/0.40  cnf(c_0_43, negated_conjecture, (r1_orders_2(esk4_0,esk5_0,esk5_0)|v2_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_17]), c_0_18]), c_0_34])])).
% 0.17/0.40  cnf(c_0_44, plain, (X1=k1_yellow_0(X2,X3)|m1_subset_1(esk2_3(X2,X1,X3),u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.17/0.40  cnf(c_0_45, negated_conjecture, (v5_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.17/0.40  cnf(c_0_46, negated_conjecture, (r2_lattice3(esk4_0,k5_waybel_0(esk4_0,esk5_0),esk5_0)|v2_struct_0(esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])).
% 0.17/0.40  cnf(c_0_47, plain, (X1=k1_yellow_0(X2,X3)|r2_lattice3(X2,X3,esk2_3(X2,X1,X3))|~r2_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.17/0.40  cnf(c_0_48, plain, (X1=k1_yellow_0(X2,X3)|~r1_orders_2(X2,X1,esk2_3(X2,X1,X3))|~r2_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.17/0.40  cnf(c_0_49, plain, (v1_xboole_0(X1)|v4_waybel_7(X3,X2)|~v1_waybel_0(X1,X2)|~v12_waybel_0(X1,X2)|~v1_waybel_7(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|X3!=k1_yellow_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~v1_lattice3(X2)|~v2_lattice3(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.17/0.40  cnf(c_0_50, plain, (v1_waybel_7(k5_waybel_0(X1,X2),X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v5_waybel_6(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.17/0.40  cnf(c_0_51, negated_conjecture, (v5_waybel_6(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.17/0.40  cnf(c_0_52, negated_conjecture, (v2_lattice3(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.17/0.40  cnf(c_0_53, negated_conjecture, (v4_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.17/0.40  fof(c_0_54, plain, ![X26, X27]:((~v1_xboole_0(k5_waybel_0(X26,X27))|(v2_struct_0(X26)|~v3_orders_2(X26)|~l1_orders_2(X26)|~m1_subset_1(X27,u1_struct_0(X26))))&(v1_waybel_0(k5_waybel_0(X26,X27),X26)|(v2_struct_0(X26)|~v3_orders_2(X26)|~l1_orders_2(X26)|~m1_subset_1(X27,u1_struct_0(X26))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc8_waybel_0])])])])).
% 0.17/0.40  fof(c_0_55, plain, ![X24, X25]:(v2_struct_0(X24)|~v4_orders_2(X24)|~l1_orders_2(X24)|~m1_subset_1(X25,u1_struct_0(X24))|v12_waybel_0(k5_waybel_0(X24,X25),X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc12_waybel_0])])])).
% 0.17/0.40  cnf(c_0_56, negated_conjecture, (r1_orders_2(esk4_0,esk5_0,X1)|~r2_lattice3(esk4_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))|~r2_hidden(esk5_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_17]), c_0_18])])).
% 0.17/0.40  cnf(c_0_57, negated_conjecture, (v2_struct_0(esk4_0)|r2_hidden(esk5_0,k5_waybel_0(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_17])])).
% 0.17/0.40  cnf(c_0_58, negated_conjecture, (k1_yellow_0(esk4_0,X1)=esk5_0|m1_subset_1(esk2_3(esk4_0,esk5_0,X1),u1_struct_0(esk4_0))|~r2_lattice3(esk4_0,X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_17]), c_0_45]), c_0_18])])).
% 0.17/0.40  cnf(c_0_59, negated_conjecture, (r2_lattice3(esk4_0,k5_waybel_0(esk4_0,esk5_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_46]), c_0_22]), c_0_18])])).
% 0.17/0.40  cnf(c_0_60, negated_conjecture, (k1_yellow_0(esk4_0,X1)=esk5_0|r2_lattice3(esk4_0,X1,esk2_3(esk4_0,esk5_0,X1))|~r2_lattice3(esk4_0,X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_17]), c_0_45]), c_0_18])])).
% 0.17/0.40  cnf(c_0_61, negated_conjecture, (k1_yellow_0(esk4_0,X1)=esk5_0|~r2_lattice3(esk4_0,X1,esk5_0)|~r1_orders_2(esk4_0,esk5_0,esk2_3(esk4_0,esk5_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_17]), c_0_45]), c_0_18])])).
% 0.17/0.40  cnf(c_0_62, plain, (v4_waybel_7(k1_yellow_0(X1,X2),X1)|v1_xboole_0(X2)|~v1_waybel_7(X2,X1)|~v2_lattice3(X1)|~v1_waybel_0(X2,X1)|~v12_waybel_0(X2,X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(er,[status(thm)],[c_0_49])).
% 0.17/0.40  cnf(c_0_63, negated_conjecture, (v1_waybel_7(k5_waybel_0(esk4_0,esk5_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_17]), c_0_51]), c_0_52]), c_0_53]), c_0_45]), c_0_22]), c_0_18]), c_0_34])])).
% 0.17/0.40  cnf(c_0_64, plain, (v1_waybel_0(k5_waybel_0(X1,X2),X1)|v2_struct_0(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.17/0.40  cnf(c_0_65, plain, (v2_struct_0(X1)|v12_waybel_0(k5_waybel_0(X1,X2),X1)|~v4_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.17/0.40  cnf(c_0_66, negated_conjecture, (r1_orders_2(esk4_0,esk5_0,X1)|v2_struct_0(esk4_0)|~r2_lattice3(esk4_0,k5_waybel_0(esk4_0,esk5_0),X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.17/0.40  cnf(c_0_67, negated_conjecture, (k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0))=esk5_0|m1_subset_1(esk2_3(esk4_0,esk5_0,k5_waybel_0(esk4_0,esk5_0)),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.17/0.40  cnf(c_0_68, negated_conjecture, (k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0))=esk5_0|r2_lattice3(esk4_0,k5_waybel_0(esk4_0,esk5_0),esk2_3(esk4_0,esk5_0,k5_waybel_0(esk4_0,esk5_0)))), inference(spm,[status(thm)],[c_0_60, c_0_59])).
% 0.17/0.40  cnf(c_0_69, negated_conjecture, (k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0))=esk5_0|~r1_orders_2(esk4_0,esk5_0,esk2_3(esk4_0,esk5_0,k5_waybel_0(esk4_0,esk5_0)))), inference(spm,[status(thm)],[c_0_61, c_0_59])).
% 0.17/0.40  cnf(c_0_70, negated_conjecture, (v4_waybel_7(k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0)),esk4_0)|v1_xboole_0(k5_waybel_0(esk4_0,esk5_0))|~v1_waybel_0(k5_waybel_0(esk4_0,esk5_0),esk4_0)|~v12_waybel_0(k5_waybel_0(esk4_0,esk5_0),esk4_0)|~m1_subset_1(k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0)),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_25]), c_0_63]), c_0_52]), c_0_53]), c_0_45]), c_0_22]), c_0_18]), c_0_34])])).
% 0.17/0.40  cnf(c_0_71, negated_conjecture, (v1_waybel_0(k5_waybel_0(esk4_0,esk5_0),esk4_0)|v2_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_17]), c_0_18]), c_0_34])])).
% 0.17/0.40  cnf(c_0_72, negated_conjecture, (v12_waybel_0(k5_waybel_0(esk4_0,esk5_0),esk4_0)|v2_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_17]), c_0_53]), c_0_18])])).
% 0.17/0.40  cnf(c_0_73, negated_conjecture, (k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0))=esk5_0|v2_struct_0(esk4_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68]), c_0_69])).
% 0.17/0.40  cnf(c_0_74, negated_conjecture, (v4_waybel_7(k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0)),esk4_0)|v1_xboole_0(k5_waybel_0(esk4_0,esk5_0))|v2_struct_0(esk4_0)|~m1_subset_1(k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0)),u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72])).
% 0.17/0.40  cnf(c_0_75, negated_conjecture, (k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0))=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_73]), c_0_22]), c_0_18])])).
% 0.17/0.40  cnf(c_0_76, negated_conjecture, (~v4_waybel_7(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.17/0.40  cnf(c_0_77, plain, (v2_struct_0(X1)|~v1_xboole_0(k5_waybel_0(X1,X2))|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.17/0.40  cnf(c_0_78, negated_conjecture, (v1_xboole_0(k5_waybel_0(esk4_0,esk5_0))|v2_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_75]), c_0_75]), c_0_17])]), c_0_76])).
% 0.17/0.40  cnf(c_0_79, negated_conjecture, (v2_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_18]), c_0_34]), c_0_17])])).
% 0.17/0.40  cnf(c_0_80, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_79]), c_0_22]), c_0_18])]), ['proof']).
% 0.17/0.40  # SZS output end CNFRefutation
% 0.17/0.40  # Proof object total steps             : 81
% 0.17/0.40  # Proof object clause steps            : 56
% 0.17/0.40  # Proof object formula steps           : 25
% 0.17/0.40  # Proof object conjectures             : 41
% 0.17/0.40  # Proof object clause conjectures      : 38
% 0.17/0.40  # Proof object formula conjectures     : 3
% 0.17/0.40  # Proof object initial clauses used    : 26
% 0.17/0.40  # Proof object initial formulas used   : 12
% 0.17/0.40  # Proof object generating inferences   : 28
% 0.17/0.40  # Proof object simplifying inferences  : 75
% 0.17/0.40  # Training examples: 0 positive, 0 negative
% 0.17/0.40  # Parsed axioms                        : 12
% 0.17/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.17/0.40  # Initial clauses                      : 38
% 0.17/0.40  # Removed in clause preprocessing      : 0
% 0.17/0.40  # Initial clauses in saturation        : 38
% 0.17/0.40  # Processed clauses                    : 154
% 0.17/0.40  # ...of these trivial                  : 0
% 0.17/0.40  # ...subsumed                          : 8
% 0.17/0.40  # ...remaining for further processing  : 146
% 0.17/0.40  # Other redundant clauses eliminated   : 3
% 0.17/0.40  # Clauses deleted for lack of memory   : 0
% 0.17/0.40  # Backward-subsumed                    : 6
% 0.17/0.40  # Backward-rewritten                   : 31
% 0.17/0.40  # Generated clauses                    : 121
% 0.17/0.40  # ...of the previous two non-trivial   : 122
% 0.17/0.40  # Contextual simplify-reflections      : 6
% 0.17/0.40  # Paramodulations                      : 118
% 0.17/0.40  # Factorizations                       : 0
% 0.17/0.40  # Equation resolutions                 : 3
% 0.17/0.40  # Propositional unsat checks           : 0
% 0.17/0.40  #    Propositional check models        : 0
% 0.17/0.40  #    Propositional check unsatisfiable : 0
% 0.17/0.40  #    Propositional clauses             : 0
% 0.17/0.40  #    Propositional clauses after purity: 0
% 0.17/0.40  #    Propositional unsat core size     : 0
% 0.17/0.40  #    Propositional preprocessing time  : 0.000
% 0.17/0.40  #    Propositional encoding time       : 0.000
% 0.17/0.40  #    Propositional solver time         : 0.000
% 0.17/0.40  #    Success case prop preproc time    : 0.000
% 0.17/0.40  #    Success case prop encoding time   : 0.000
% 0.17/0.40  #    Success case prop solver time     : 0.000
% 0.17/0.40  # Current number of processed clauses  : 68
% 0.17/0.40  #    Positive orientable unit clauses  : 13
% 0.17/0.40  #    Positive unorientable unit clauses: 0
% 0.17/0.40  #    Negative unit clauses             : 1
% 0.17/0.40  #    Non-unit-clauses                  : 54
% 0.17/0.40  # Current number of unprocessed clauses: 44
% 0.17/0.40  # ...number of literals in the above   : 195
% 0.17/0.40  # Current number of archived formulas  : 0
% 0.17/0.40  # Current number of archived clauses   : 75
% 0.17/0.40  # Clause-clause subsumption calls (NU) : 1612
% 0.17/0.40  # Rec. Clause-clause subsumption calls : 333
% 0.17/0.40  # Non-unit clause-clause subsumptions  : 15
% 0.17/0.40  # Unit Clause-clause subsumption calls : 43
% 0.17/0.40  # Rewrite failures with RHS unbound    : 0
% 0.17/0.40  # BW rewrite match attempts            : 4
% 0.17/0.40  # BW rewrite match successes           : 4
% 0.17/0.40  # Condensation attempts                : 0
% 0.17/0.40  # Condensation successes               : 0
% 0.17/0.40  # Termbank termtop insertions          : 8566
% 0.17/0.40  
% 0.17/0.40  # -------------------------------------------------
% 0.17/0.40  # User time                : 0.071 s
% 0.17/0.40  # System time              : 0.008 s
% 0.17/0.40  # Total time               : 0.079 s
% 0.17/0.40  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
