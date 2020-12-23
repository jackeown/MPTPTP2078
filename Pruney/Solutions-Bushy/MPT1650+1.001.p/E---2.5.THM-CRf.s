%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1650+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:31 EST 2020

% Result     : Theorem 5.84s
% Output     : CNFRefutation 5.84s
% Verified   : 
% Statistics : Number of formulae       :  188 (26301 expanded)
%              Number of clauses        :  169 (10246 expanded)
%              Number of leaves         :    9 (6587 expanded)
%              Depth                    :   48
%              Number of atoms          : 1241 (198891 expanded)
%              Number of equality atoms :  157 (8674 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal clause size      :   61 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t30_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_waybel_0(X2,X1)
          <=> v1_waybel_0(k3_waybel_0(X1,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_waybel_0)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(d1_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_waybel_0(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ~ ( r2_hidden(X3,X2)
                        & r2_hidden(X4,X2)
                        & ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ~ ( r2_hidden(X5,X2)
                                & r1_orders_2(X1,X3,X5)
                                & r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_waybel_0)).

fof(reflexivity_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => r3_orders_2(X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(d15_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = k3_waybel_0(X1,X2)
              <=> ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r2_hidden(X4,X3)
                    <=> ? [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                          & r1_orders_2(X1,X4,X5)
                          & r2_hidden(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_waybel_0)).

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

fof(dt_k3_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k3_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_waybel_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_orders_2)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v1_waybel_0(X2,X1)
            <=> v1_waybel_0(k3_waybel_0(X1,X2),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t30_waybel_0])).

fof(c_0_10,plain,(
    ! [X37,X38,X39] :
      ( ~ r2_hidden(X37,X38)
      | ~ m1_subset_1(X38,k1_zfmisc_1(X39))
      | m1_subset_1(X37,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk8_0)
    & v3_orders_2(esk8_0)
    & v4_orders_2(esk8_0)
    & l1_orders_2(esk8_0)
    & m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(esk8_0)))
    & ( ~ v1_waybel_0(esk9_0,esk8_0)
      | ~ v1_waybel_0(k3_waybel_0(esk8_0,esk9_0),esk8_0) )
    & ( v1_waybel_0(esk9_0,esk8_0)
      | v1_waybel_0(k3_waybel_0(esk8_0,esk9_0),esk8_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

cnf(c_0_12,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X15,X16,X17,X18,X22] :
      ( ( m1_subset_1(esk4_4(X15,X16,X17,X18),u1_struct_0(X15))
        | ~ r2_hidden(X17,X16)
        | ~ r2_hidden(X18,X16)
        | ~ m1_subset_1(X18,u1_struct_0(X15))
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ v1_waybel_0(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_orders_2(X15) )
      & ( r2_hidden(esk4_4(X15,X16,X17,X18),X16)
        | ~ r2_hidden(X17,X16)
        | ~ r2_hidden(X18,X16)
        | ~ m1_subset_1(X18,u1_struct_0(X15))
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ v1_waybel_0(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_orders_2(X15) )
      & ( r1_orders_2(X15,X17,esk4_4(X15,X16,X17,X18))
        | ~ r2_hidden(X17,X16)
        | ~ r2_hidden(X18,X16)
        | ~ m1_subset_1(X18,u1_struct_0(X15))
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ v1_waybel_0(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_orders_2(X15) )
      & ( r1_orders_2(X15,X18,esk4_4(X15,X16,X17,X18))
        | ~ r2_hidden(X17,X16)
        | ~ r2_hidden(X18,X16)
        | ~ m1_subset_1(X18,u1_struct_0(X15))
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ v1_waybel_0(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_orders_2(X15) )
      & ( m1_subset_1(esk5_2(X15,X16),u1_struct_0(X15))
        | v1_waybel_0(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_orders_2(X15) )
      & ( m1_subset_1(esk6_2(X15,X16),u1_struct_0(X15))
        | v1_waybel_0(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_orders_2(X15) )
      & ( r2_hidden(esk5_2(X15,X16),X16)
        | v1_waybel_0(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_orders_2(X15) )
      & ( r2_hidden(esk6_2(X15,X16),X16)
        | v1_waybel_0(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_orders_2(X15) )
      & ( ~ m1_subset_1(X22,u1_struct_0(X15))
        | ~ r2_hidden(X22,X16)
        | ~ r1_orders_2(X15,esk5_2(X15,X16),X22)
        | ~ r1_orders_2(X15,esk6_2(X15,X16),X22)
        | v1_waybel_0(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_orders_2(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_waybel_0])])])])])).

fof(c_0_15,plain,(
    ! [X30,X31,X32] :
      ( v2_struct_0(X30)
      | ~ v3_orders_2(X30)
      | ~ l1_orders_2(X30)
      | ~ m1_subset_1(X31,u1_struct_0(X30))
      | ~ m1_subset_1(X32,u1_struct_0(X30))
      | r3_orders_2(X30,X31,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk8_0))
    | ~ r2_hidden(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( r2_hidden(esk6_2(X1,X2),X2)
    | v1_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X25] : m1_subset_1(esk7_1(X25),X25) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_19,plain,
    ( v2_struct_0(X1)
    | r3_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( v1_waybel_0(esk9_0,X1)
    | m1_subset_1(esk6_2(X1,esk9_0),u1_struct_0(esk8_0))
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( v3_orders_2(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,negated_conjecture,
    ( l1_orders_2(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_24,plain,(
    ! [X6,X7,X8,X9,X11,X13] :
      ( ( m1_subset_1(esk1_4(X6,X7,X8,X9),u1_struct_0(X6))
        | ~ r2_hidden(X9,X8)
        | ~ m1_subset_1(X9,u1_struct_0(X6))
        | X8 != k3_waybel_0(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) )
      & ( r1_orders_2(X6,X9,esk1_4(X6,X7,X8,X9))
        | ~ r2_hidden(X9,X8)
        | ~ m1_subset_1(X9,u1_struct_0(X6))
        | X8 != k3_waybel_0(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) )
      & ( r2_hidden(esk1_4(X6,X7,X8,X9),X7)
        | ~ r2_hidden(X9,X8)
        | ~ m1_subset_1(X9,u1_struct_0(X6))
        | X8 != k3_waybel_0(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) )
      & ( ~ m1_subset_1(X11,u1_struct_0(X6))
        | ~ r1_orders_2(X6,X9,X11)
        | ~ r2_hidden(X11,X7)
        | r2_hidden(X9,X8)
        | ~ m1_subset_1(X9,u1_struct_0(X6))
        | X8 != k3_waybel_0(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) )
      & ( m1_subset_1(esk2_3(X6,X7,X8),u1_struct_0(X6))
        | X8 = k3_waybel_0(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) )
      & ( ~ r2_hidden(esk2_3(X6,X7,X8),X8)
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r1_orders_2(X6,esk2_3(X6,X7,X8),X13)
        | ~ r2_hidden(X13,X7)
        | X8 = k3_waybel_0(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) )
      & ( m1_subset_1(esk3_3(X6,X7,X8),u1_struct_0(X6))
        | r2_hidden(esk2_3(X6,X7,X8),X8)
        | X8 = k3_waybel_0(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) )
      & ( r1_orders_2(X6,esk2_3(X6,X7,X8),esk3_3(X6,X7,X8))
        | r2_hidden(esk2_3(X6,X7,X8),X8)
        | X8 = k3_waybel_0(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) )
      & ( r2_hidden(esk3_3(X6,X7,X8),X7)
        | r2_hidden(esk2_3(X6,X7,X8),X8)
        | X8 = k3_waybel_0(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d15_waybel_0])])])])])).

fof(c_0_25,plain,(
    ! [X27,X28,X29] :
      ( ( ~ r3_orders_2(X27,X28,X29)
        | r1_orders_2(X27,X28,X29)
        | v2_struct_0(X27)
        | ~ v3_orders_2(X27)
        | ~ l1_orders_2(X27)
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | ~ m1_subset_1(X29,u1_struct_0(X27)) )
      & ( ~ r1_orders_2(X27,X28,X29)
        | r3_orders_2(X27,X28,X29)
        | v2_struct_0(X27)
        | ~ v3_orders_2(X27)
        | ~ l1_orders_2(X27)
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | ~ m1_subset_1(X29,u1_struct_0(X27)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_26,plain,
    ( m1_subset_1(esk7_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( r3_orders_2(esk8_0,X1,X1)
    | v1_waybel_0(esk9_0,X2)
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0))
    | ~ l1_orders_2(X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_28,plain,
    ( r2_hidden(X3,X5)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ r2_hidden(X1,X4)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | X5 != k3_waybel_0(X2,X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_29,plain,(
    ! [X23,X24] :
      ( ~ l1_orders_2(X23)
      | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
      | m1_subset_1(k3_waybel_0(X23,X24),k1_zfmisc_1(u1_struct_0(X23))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_waybel_0])])).

cnf(c_0_30,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( r3_orders_2(X1,X2,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_26])).

cnf(c_0_32,plain,
    ( r2_hidden(esk5_2(X1,X2),X2)
    | v1_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_33,negated_conjecture,
    ( r3_orders_2(esk8_0,X1,X1)
    | v1_waybel_0(esk9_0,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_13]),c_0_22])])).

cnf(c_0_34,plain,
    ( m1_subset_1(esk5_2(X1,X2),u1_struct_0(X1))
    | v1_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X2)
    | X2 != k3_waybel_0(X3,X4)
    | ~ r1_orders_2(X3,X1,X5)
    | ~ r2_hidden(X5,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(csr,[status(thm)],[c_0_28,c_0_12])).

cnf(c_0_36,plain,
    ( m1_subset_1(k3_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( v1_waybel_0(esk9_0,X1)
    | m1_subset_1(esk5_2(X1,esk9_0),u1_struct_0(esk8_0))
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( r3_orders_2(esk8_0,esk5_2(esk8_0,X1),esk5_2(esk8_0,X1))
    | v1_waybel_0(esk9_0,esk8_0)
    | v1_waybel_0(X1,esk8_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_22])])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k3_waybel_0(X2,X3))
    | k3_waybel_0(X2,X3) != k3_waybel_0(X2,X4)
    | ~ r1_orders_2(X2,X1,X5)
    | ~ r2_hidden(X5,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( v1_waybel_0(esk9_0,X1)
    | r1_orders_2(esk8_0,esk5_2(X1,esk9_0),esk5_2(X1,esk9_0))
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_42,negated_conjecture,
    ( v1_waybel_0(esk9_0,esk8_0)
    | v1_waybel_0(X1,esk8_0)
    | r1_orders_2(esk8_0,esk5_2(esk8_0,X1),esk5_2(esk8_0,X1))
    | ~ m1_subset_1(esk5_2(esk8_0,X1),u1_struct_0(esk8_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_39]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_43,negated_conjecture,
    ( v1_waybel_0(esk9_0,X1)
    | r2_hidden(esk5_2(X1,esk9_0),k3_waybel_0(esk8_0,X2))
    | k3_waybel_0(esk8_0,X2) != k3_waybel_0(esk8_0,X3)
    | ~ r2_hidden(esk5_2(X1,esk9_0),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_22])]),c_0_12])).

cnf(c_0_44,plain,
    ( m1_subset_1(esk6_2(X1,X2),u1_struct_0(X1))
    | v1_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_45,plain,
    ( r1_orders_2(X1,esk2_3(X1,X2,X3),esk3_3(X1,X2,X3))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k3_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_46,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | X3 = k3_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_47,negated_conjecture,
    ( v1_waybel_0(esk9_0,esk8_0)
    | v1_waybel_0(X1,esk8_0)
    | r2_hidden(esk5_2(esk8_0,X1),k3_waybel_0(esk8_0,X2))
    | k3_waybel_0(esk8_0,X2) != k3_waybel_0(esk8_0,X3)
    | ~ r2_hidden(esk5_2(esk8_0,X1),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_42]),c_0_22])]),c_0_12])).

cnf(c_0_48,negated_conjecture,
    ( v1_waybel_0(esk9_0,X1)
    | r2_hidden(esk5_2(X1,esk9_0),k3_waybel_0(esk8_0,X2))
    | k3_waybel_0(esk8_0,X2) != k3_waybel_0(esk8_0,esk9_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_32]),c_0_13])])).

cnf(c_0_49,negated_conjecture,
    ( r3_orders_2(esk8_0,esk6_2(esk8_0,X1),esk6_2(esk8_0,X1))
    | v1_waybel_0(esk9_0,esk8_0)
    | v1_waybel_0(X1,esk8_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_44]),c_0_22])])).

cnf(c_0_50,negated_conjecture,
    ( v1_waybel_0(esk9_0,X1)
    | r1_orders_2(esk8_0,esk6_2(X1,esk9_0),esk6_2(X1,esk9_0))
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_51,plain,
    ( X1 = k3_waybel_0(X2,X3)
    | r2_hidden(esk2_3(X2,X3,X1),k3_waybel_0(X2,X4))
    | r2_hidden(esk2_3(X2,X3,X1),X1)
    | k3_waybel_0(X2,X4) != k3_waybel_0(X2,X5)
    | ~ r2_hidden(esk3_3(X2,X3,X1),X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_45]),c_0_46])).

cnf(c_0_52,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k3_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_53,negated_conjecture,
    ( v1_waybel_0(esk9_0,esk8_0)
    | r2_hidden(esk5_2(esk8_0,esk9_0),k3_waybel_0(esk8_0,X1))
    | k3_waybel_0(esk8_0,X1) != k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,X2))
    | k3_waybel_0(esk8_0,X2) != k3_waybel_0(esk8_0,esk9_0)
    | ~ m1_subset_1(k3_waybel_0(esk8_0,X2),k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_13]),c_0_22])])).

cnf(c_0_54,negated_conjecture,
    ( v1_waybel_0(esk9_0,esk8_0)
    | v1_waybel_0(X1,esk8_0)
    | r1_orders_2(esk8_0,esk6_2(esk8_0,X1),esk6_2(esk8_0,X1))
    | ~ m1_subset_1(esk6_2(esk8_0,X1),u1_struct_0(esk8_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_49]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_55,negated_conjecture,
    ( v1_waybel_0(esk9_0,X1)
    | r2_hidden(esk6_2(X1,esk9_0),k3_waybel_0(esk8_0,X2))
    | k3_waybel_0(esk8_0,X2) != k3_waybel_0(esk8_0,X3)
    | ~ r2_hidden(esk6_2(X1,esk9_0),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_50]),c_0_22])]),c_0_12])).

cnf(c_0_56,plain,
    ( X1 = k3_waybel_0(X2,X3)
    | r2_hidden(esk2_3(X2,X3,X1),k3_waybel_0(X2,X4))
    | r2_hidden(esk2_3(X2,X3,X1),X1)
    | k3_waybel_0(X2,X4) != k3_waybel_0(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,plain,
    ( m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(X1,k3_waybel_0(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_36])).

cnf(c_0_58,negated_conjecture,
    ( v1_waybel_0(esk9_0,esk8_0)
    | r2_hidden(esk5_2(esk8_0,esk9_0),k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,X1)))
    | k3_waybel_0(esk8_0,X1) != k3_waybel_0(esk8_0,esk9_0)
    | ~ m1_subset_1(k3_waybel_0(esk8_0,X1),k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(er,[status(thm)],[c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( v1_waybel_0(esk9_0,esk8_0)
    | v1_waybel_0(X1,esk8_0)
    | r2_hidden(esk6_2(esk8_0,X1),k3_waybel_0(esk8_0,X2))
    | k3_waybel_0(esk8_0,X2) != k3_waybel_0(esk8_0,X3)
    | ~ r2_hidden(esk6_2(esk8_0,X1),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_54]),c_0_22])]),c_0_12])).

cnf(c_0_60,negated_conjecture,
    ( v1_waybel_0(esk9_0,X1)
    | r2_hidden(esk6_2(X1,esk9_0),k3_waybel_0(esk8_0,X2))
    | k3_waybel_0(esk8_0,X2) != k3_waybel_0(esk8_0,esk9_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_17]),c_0_13])])).

cnf(c_0_61,negated_conjecture,
    ( X1 = k3_waybel_0(esk8_0,esk9_0)
    | r2_hidden(esk2_3(esk8_0,esk9_0,X1),k3_waybel_0(esk8_0,X2))
    | r2_hidden(esk2_3(esk8_0,esk9_0,X1),X1)
    | k3_waybel_0(esk8_0,X2) != k3_waybel_0(esk8_0,esk9_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_13]),c_0_22])])).

fof(c_0_62,plain,(
    ! [X33,X34,X35,X36] :
      ( ~ v4_orders_2(X33)
      | ~ l1_orders_2(X33)
      | ~ m1_subset_1(X34,u1_struct_0(X33))
      | ~ m1_subset_1(X35,u1_struct_0(X33))
      | ~ m1_subset_1(X36,u1_struct_0(X33))
      | ~ r1_orders_2(X33,X34,X35)
      | ~ r1_orders_2(X33,X35,X36)
      | r1_orders_2(X33,X34,X36) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_orders_2])])])).

cnf(c_0_63,plain,
    ( r1_orders_2(X1,X2,esk1_4(X1,X3,X4,X2))
    | ~ r2_hidden(X2,X4)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | X4 != k3_waybel_0(X1,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_64,plain,
    ( m1_subset_1(esk1_4(X1,X2,X3,X4),u1_struct_0(X1))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | X3 != k3_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_65,negated_conjecture,
    ( v1_waybel_0(esk9_0,esk8_0)
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | k3_waybel_0(esk8_0,X1) != k3_waybel_0(esk8_0,esk9_0)
    | ~ m1_subset_1(k3_waybel_0(esk8_0,X1),k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_22])])).

cnf(c_0_66,negated_conjecture,
    ( v1_waybel_0(esk9_0,esk8_0)
    | r2_hidden(esk6_2(esk8_0,esk9_0),k3_waybel_0(esk8_0,X1))
    | k3_waybel_0(esk8_0,X1) != k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,X2))
    | k3_waybel_0(esk8_0,X2) != k3_waybel_0(esk8_0,esk9_0)
    | ~ m1_subset_1(k3_waybel_0(esk8_0,X2),k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_13]),c_0_22])])).

cnf(c_0_67,negated_conjecture,
    ( X1 = k3_waybel_0(esk8_0,esk9_0)
    | r2_hidden(esk2_3(esk8_0,esk9_0,X1),k3_waybel_0(esk8_0,esk9_0))
    | r2_hidden(esk2_3(esk8_0,esk9_0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_13])).

cnf(c_0_68,plain,
    ( r1_orders_2(X1,X2,X4)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_69,plain,
    ( r1_orders_2(X1,X2,esk1_4(X1,X3,X4,X2))
    | X4 != k3_waybel_0(X1,X3)
    | ~ r2_hidden(X2,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[c_0_63,c_0_12])).

cnf(c_0_70,plain,
    ( m1_subset_1(esk1_4(X1,X2,X3,X4),u1_struct_0(X1))
    | X3 != k3_waybel_0(X1,X2)
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[c_0_64,c_0_12])).

cnf(c_0_71,negated_conjecture,
    ( v1_waybel_0(esk9_0,esk8_0)
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | k3_waybel_0(esk8_0,X1) != k3_waybel_0(esk8_0,esk9_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_36]),c_0_22])])).

cnf(c_0_72,negated_conjecture,
    ( v1_waybel_0(esk9_0,esk8_0)
    | r2_hidden(esk6_2(esk8_0,esk9_0),k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,X1)))
    | k3_waybel_0(esk8_0,X1) != k3_waybel_0(esk8_0,esk9_0)
    | ~ m1_subset_1(k3_waybel_0(esk8_0,X1),k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(er,[status(thm)],[c_0_66])).

cnf(c_0_73,negated_conjecture,
    ( k3_waybel_0(esk8_0,X1) = k3_waybel_0(esk8_0,esk9_0)
    | r2_hidden(esk2_3(esk8_0,esk9_0,k3_waybel_0(esk8_0,X1)),k3_waybel_0(esk8_0,esk9_0))
    | r2_hidden(esk2_3(esk8_0,esk9_0,k3_waybel_0(esk8_0,X1)),k3_waybel_0(esk8_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_36]),c_0_22])])).

cnf(c_0_74,negated_conjecture,
    ( X1 = k3_waybel_0(X2,esk9_0)
    | r2_hidden(esk2_3(X2,esk9_0,X1),X1)
    | m1_subset_1(esk3_3(X2,esk9_0,X1),u1_struct_0(esk8_0))
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_52])).

cnf(c_0_75,plain,
    ( v1_waybel_0(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(X1,X3)
    | ~ r1_orders_2(X2,esk5_2(X2,X3),X1)
    | ~ r1_orders_2(X2,esk6_2(X2,X3),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_76,plain,
    ( r1_orders_2(X1,X2,esk1_4(X1,X3,X4,X5))
    | X4 != k3_waybel_0(X1,X3)
    | ~ v4_orders_2(X1)
    | ~ r1_orders_2(X1,X2,X5)
    | ~ r2_hidden(X5,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_12]),c_0_70])).

cnf(c_0_77,negated_conjecture,
    ( v1_waybel_0(esk9_0,esk8_0)
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_71]),c_0_13])])).

cnf(c_0_78,plain,
    ( r1_orders_2(X1,X2,esk4_4(X1,X3,X4,X2))
    | ~ r2_hidden(X4,X3)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v1_waybel_0(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_79,plain,
    ( m1_subset_1(esk4_4(X1,X2,X3,X4),u1_struct_0(X1))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_80,negated_conjecture,
    ( v1_waybel_0(esk9_0,esk8_0)
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | k3_waybel_0(esk8_0,X1) != k3_waybel_0(esk8_0,esk9_0)
    | ~ m1_subset_1(k3_waybel_0(esk8_0,X1),k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_72]),c_0_22])])).

cnf(c_0_81,plain,
    ( X1 = k3_waybel_0(X2,X3)
    | v2_struct_0(X2)
    | r1_orders_2(X2,esk2_3(X2,X3,X1),esk2_3(X2,X3,X1))
    | ~ v3_orders_2(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_46])).

cnf(c_0_82,negated_conjecture,
    ( k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,X1)) = k3_waybel_0(esk8_0,esk9_0)
    | r2_hidden(esk2_3(esk8_0,esk9_0,k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,X1))),k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,X1)))
    | r2_hidden(esk2_3(esk8_0,esk9_0,k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,X1))),k3_waybel_0(esk8_0,esk9_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_36]),c_0_22])])).

cnf(c_0_83,negated_conjecture,
    ( X1 = k3_waybel_0(X2,esk9_0)
    | r1_orders_2(esk8_0,esk3_3(X2,esk9_0,X1),esk3_3(X2,esk9_0,X1))
    | r2_hidden(esk2_3(X2,esk9_0,X1),X1)
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_74]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_84,plain,
    ( v1_waybel_0(X1,X2)
    | ~ r1_orders_2(X2,esk5_2(X2,X1),X3)
    | ~ r1_orders_2(X2,esk6_2(X2,X1),X3)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_75,c_0_12])).

cnf(c_0_85,plain,
    ( r1_orders_2(X1,X2,esk1_4(X1,X3,X4,X5))
    | X4 != k3_waybel_0(X1,X3)
    | ~ v4_orders_2(X1)
    | ~ r1_orders_2(X1,X2,X6)
    | ~ r1_orders_2(X1,X6,X5)
    | ~ r2_hidden(X5,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X6,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_76]),c_0_70])).

cnf(c_0_86,negated_conjecture,
    ( v1_waybel_0(esk9_0,esk8_0)
    | r1_orders_2(esk8_0,esk5_2(esk8_0,esk9_0),esk5_2(esk8_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_77]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_87,negated_conjecture,
    ( v4_orders_2(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_88,plain,
    ( r1_orders_2(X1,X2,esk4_4(X1,X3,X4,X2))
    | ~ v1_waybel_0(X3,X1)
    | ~ r2_hidden(X4,X3)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_78,c_0_12]),c_0_12])).

cnf(c_0_89,plain,
    ( m1_subset_1(esk4_4(X1,X2,X3,X4),u1_struct_0(X1))
    | ~ v1_waybel_0(X2,X1)
    | ~ r2_hidden(X4,X2)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_79,c_0_12]),c_0_12])).

cnf(c_0_90,negated_conjecture,
    ( v1_waybel_0(esk9_0,esk8_0)
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | k3_waybel_0(esk8_0,X1) != k3_waybel_0(esk8_0,esk9_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_36]),c_0_22])])).

cnf(c_0_91,plain,
    ( X1 = k3_waybel_0(X2,X3)
    | v2_struct_0(X2)
    | r2_hidden(esk2_3(X2,X3,X1),k3_waybel_0(X2,X4))
    | k3_waybel_0(X2,X4) != k3_waybel_0(X2,X5)
    | ~ v3_orders_2(X2)
    | ~ r2_hidden(esk2_3(X2,X3,X1),X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_81]),c_0_12])).

cnf(c_0_92,negated_conjecture,
    ( k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)) = k3_waybel_0(esk8_0,esk9_0)
    | r2_hidden(esk2_3(esk8_0,esk9_0,k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0))),k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)))
    | r2_hidden(esk2_3(esk8_0,esk9_0,k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0))),k3_waybel_0(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_13])).

cnf(c_0_93,negated_conjecture,
    ( X1 = k3_waybel_0(X2,esk9_0)
    | r2_hidden(esk3_3(X2,esk9_0,X1),k3_waybel_0(esk8_0,X3))
    | r2_hidden(esk2_3(X2,esk9_0,X1),X1)
    | k3_waybel_0(esk8_0,X3) != k3_waybel_0(esk8_0,X4)
    | ~ r2_hidden(esk3_3(X2,esk9_0,X1),X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_83]),c_0_22])]),c_0_12])).

cnf(c_0_94,plain,
    ( v1_waybel_0(X1,X2)
    | X3 != k3_waybel_0(X2,X4)
    | ~ v4_orders_2(X2)
    | ~ r1_orders_2(X2,esk5_2(X2,X1),esk1_4(X2,X4,X3,X5))
    | ~ r1_orders_2(X2,esk6_2(X2,X1),X5)
    | ~ r2_hidden(esk1_4(X2,X4,X3,X5),X1)
    | ~ r2_hidden(X5,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_76]),c_0_44])).

cnf(c_0_95,negated_conjecture,
    ( v1_waybel_0(esk9_0,esk8_0)
    | r1_orders_2(esk8_0,esk5_2(esk8_0,esk9_0),esk1_4(esk8_0,X1,X2,X3))
    | X2 != k3_waybel_0(esk8_0,X1)
    | ~ r1_orders_2(esk8_0,esk5_2(esk8_0,esk9_0),X3)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_87]),c_0_22])]),c_0_77])).

cnf(c_0_96,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | X3 != k3_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_97,plain,
    ( r1_orders_2(X1,X2,esk4_4(X1,X3,X4,X5))
    | ~ v4_orders_2(X1)
    | ~ v1_waybel_0(X3,X1)
    | ~ r1_orders_2(X1,X2,X5)
    | ~ r2_hidden(X4,X3)
    | ~ r2_hidden(X5,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_88]),c_0_12]),c_0_89])).

cnf(c_0_98,negated_conjecture,
    ( v1_waybel_0(esk9_0,esk8_0)
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_90]),c_0_13])])).

cnf(c_0_99,negated_conjecture,
    ( k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)) = k3_waybel_0(esk8_0,esk9_0)
    | r2_hidden(esk2_3(esk8_0,esk9_0,k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0))),k3_waybel_0(esk8_0,esk9_0))
    | r2_hidden(esk2_3(esk8_0,esk9_0,k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0))),k3_waybel_0(esk8_0,X1))
    | k3_waybel_0(esk8_0,X1) != k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)))
    | ~ m1_subset_1(k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)),k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_21]),c_0_13]),c_0_22])]),c_0_23])).

cnf(c_0_100,negated_conjecture,
    ( X1 = k3_waybel_0(X2,esk9_0)
    | r2_hidden(esk3_3(X2,esk9_0,X1),k3_waybel_0(esk8_0,X3))
    | r2_hidden(esk2_3(X2,esk9_0,X1),X1)
    | k3_waybel_0(esk8_0,X3) != k3_waybel_0(esk8_0,esk9_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_52]),c_0_13])])).

cnf(c_0_101,negated_conjecture,
    ( v1_waybel_0(esk9_0,esk8_0)
    | X1 != k3_waybel_0(esk8_0,X2)
    | ~ r1_orders_2(esk8_0,esk6_2(esk8_0,esk9_0),X3)
    | ~ r1_orders_2(esk8_0,esk5_2(esk8_0,esk9_0),X3)
    | ~ r2_hidden(esk1_4(esk8_0,X2,X1,X3),esk9_0)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_87]),c_0_13]),c_0_22])])).

cnf(c_0_102,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X2)
    | X3 != k3_waybel_0(X1,X2)
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[c_0_96,c_0_12])).

cnf(c_0_103,plain,
    ( r1_orders_2(X1,X2,esk4_4(X1,X3,X4,X5))
    | ~ v4_orders_2(X1)
    | ~ v1_waybel_0(X3,X1)
    | ~ r1_orders_2(X1,X2,X6)
    | ~ r1_orders_2(X1,X6,X5)
    | ~ r2_hidden(X4,X3)
    | ~ r2_hidden(X5,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X6,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_97]),c_0_89])).

cnf(c_0_104,negated_conjecture,
    ( v1_waybel_0(esk9_0,esk8_0)
    | r1_orders_2(esk8_0,esk6_2(esk8_0,esk9_0),esk6_2(esk8_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_98]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_105,negated_conjecture,
    ( k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)) = k3_waybel_0(esk8_0,esk9_0)
    | r2_hidden(esk2_3(esk8_0,esk9_0,k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0))),k3_waybel_0(esk8_0,esk9_0))
    | r2_hidden(esk2_3(esk8_0,esk9_0,k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0))),k3_waybel_0(esk8_0,X1))
    | k3_waybel_0(esk8_0,X1) != k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)))
    | ~ m1_subset_1(k3_waybel_0(esk8_0,esk9_0),k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_36]),c_0_22])])).

cnf(c_0_106,negated_conjecture,
    ( X1 = k3_waybel_0(X2,esk9_0)
    | r2_hidden(esk2_3(X2,esk9_0,X1),k3_waybel_0(X2,X3))
    | r2_hidden(esk2_3(X2,esk9_0,X1),X1)
    | k3_waybel_0(X2,X3) != k3_waybel_0(X2,k3_waybel_0(esk8_0,X4))
    | k3_waybel_0(esk8_0,X4) != k3_waybel_0(esk8_0,esk9_0)
    | ~ m1_subset_1(k3_waybel_0(esk8_0,X4),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_100])).

cnf(c_0_107,negated_conjecture,
    ( v1_waybel_0(esk9_0,esk8_0)
    | X1 != k3_waybel_0(esk8_0,esk9_0)
    | ~ r1_orders_2(esk8_0,esk6_2(esk8_0,esk9_0),X2)
    | ~ r1_orders_2(esk8_0,esk5_2(esk8_0,esk9_0),X2)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_13]),c_0_22])])).

cnf(c_0_108,negated_conjecture,
    ( v1_waybel_0(esk9_0,esk8_0)
    | r1_orders_2(esk8_0,esk6_2(esk8_0,esk9_0),esk4_4(esk8_0,X1,X2,X3))
    | ~ v1_waybel_0(X1,esk8_0)
    | ~ r1_orders_2(esk8_0,esk6_2(esk8_0,esk9_0),X3)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_87]),c_0_22])]),c_0_98])).

cnf(c_0_109,plain,
    ( r1_orders_2(X1,X2,esk4_4(X1,X3,X2,X4))
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_waybel_0(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_110,negated_conjecture,
    ( k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)) = k3_waybel_0(esk8_0,esk9_0)
    | r2_hidden(esk2_3(esk8_0,esk9_0,k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0))),k3_waybel_0(esk8_0,esk9_0))
    | r2_hidden(esk2_3(esk8_0,esk9_0,k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0))),k3_waybel_0(esk8_0,X1))
    | k3_waybel_0(esk8_0,X1) != k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_36]),c_0_13]),c_0_22])])).

cnf(c_0_111,negated_conjecture,
    ( X1 = k3_waybel_0(X2,esk9_0)
    | r2_hidden(esk2_3(X2,esk9_0,X1),k3_waybel_0(X2,k3_waybel_0(esk8_0,X3)))
    | r2_hidden(esk2_3(X2,esk9_0,X1),X1)
    | k3_waybel_0(esk8_0,X3) != k3_waybel_0(esk8_0,esk9_0)
    | ~ m1_subset_1(k3_waybel_0(esk8_0,X3),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(er,[status(thm)],[c_0_106])).

cnf(c_0_112,negated_conjecture,
    ( v1_waybel_0(esk9_0,esk8_0)
    | X1 != k3_waybel_0(esk8_0,esk9_0)
    | ~ v1_waybel_0(X2,esk8_0)
    | ~ r1_orders_2(esk8_0,esk5_2(esk8_0,esk9_0),esk4_4(esk8_0,X2,X3,X4))
    | ~ r1_orders_2(esk8_0,esk6_2(esk8_0,esk9_0),X4)
    | ~ r2_hidden(esk4_4(esk8_0,X2,X3,X4),X1)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_107,c_0_108])).

cnf(c_0_113,plain,
    ( r1_orders_2(X1,X2,esk4_4(X1,X3,X2,X4))
    | ~ v1_waybel_0(X3,X1)
    | ~ r2_hidden(X4,X3)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_109,c_0_12]),c_0_12])).

cnf(c_0_114,plain,
    ( r2_hidden(esk4_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_115,negated_conjecture,
    ( k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)) = k3_waybel_0(esk8_0,esk9_0)
    | r2_hidden(esk2_3(esk8_0,esk9_0,k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0))),k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0))))
    | r2_hidden(esk2_3(esk8_0,esk9_0,k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0))),k3_waybel_0(esk8_0,esk9_0))
    | ~ m1_subset_1(k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)),k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(er,[status(thm)],[c_0_110])).

cnf(c_0_116,negated_conjecture,
    ( X1 = k3_waybel_0(esk8_0,esk9_0)
    | r2_hidden(esk2_3(esk8_0,esk9_0,X1),k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,X2)))
    | r2_hidden(esk2_3(esk8_0,esk9_0,X1),X1)
    | k3_waybel_0(esk8_0,X2) != k3_waybel_0(esk8_0,esk9_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_36]),c_0_13]),c_0_22])])).

cnf(c_0_117,negated_conjecture,
    ( v1_waybel_0(esk9_0,esk8_0)
    | X1 != k3_waybel_0(esk8_0,esk9_0)
    | ~ v1_waybel_0(X2,esk8_0)
    | ~ r1_orders_2(esk8_0,esk6_2(esk8_0,esk9_0),X3)
    | ~ r2_hidden(esk4_4(esk8_0,X2,esk5_2(esk8_0,esk9_0),X3),X1)
    | ~ r2_hidden(esk5_2(esk8_0,esk9_0),X2)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_22])])).

cnf(c_0_118,plain,
    ( r2_hidden(esk4_4(X1,X2,X3,X4),X2)
    | ~ v1_waybel_0(X2,X1)
    | ~ r2_hidden(X4,X2)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_114,c_0_12]),c_0_12])).

cnf(c_0_119,negated_conjecture,
    ( k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)) = k3_waybel_0(esk8_0,esk9_0)
    | r2_hidden(esk2_3(esk8_0,esk9_0,k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0))),k3_waybel_0(esk8_0,esk9_0))
    | m1_subset_1(esk2_3(esk8_0,esk9_0,k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | ~ m1_subset_1(k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)),k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_115]),c_0_22])])).

cnf(c_0_120,negated_conjecture,
    ( X1 = k3_waybel_0(esk8_0,esk9_0)
    | r2_hidden(esk2_3(esk8_0,esk9_0,X1),k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)))
    | r2_hidden(esk2_3(esk8_0,esk9_0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_116,c_0_13])).

cnf(c_0_121,negated_conjecture,
    ( v1_waybel_0(esk9_0,esk8_0)
    | X1 != k3_waybel_0(esk8_0,esk9_0)
    | ~ v1_waybel_0(X1,esk8_0)
    | ~ r1_orders_2(esk8_0,esk6_2(esk8_0,esk9_0),X2)
    | ~ r2_hidden(esk5_2(esk8_0,esk9_0),X1)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_118]),c_0_22])])).

cnf(c_0_122,plain,
    ( v2_struct_0(X1)
    | v1_waybel_0(X2,X1)
    | r1_orders_2(X1,esk6_2(X1,X2),esk6_2(X1,X2))
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_44])).

cnf(c_0_123,negated_conjecture,
    ( v1_waybel_0(esk9_0,esk8_0)
    | r2_hidden(esk5_2(esk8_0,esk9_0),k3_waybel_0(esk8_0,X1))
    | k3_waybel_0(esk8_0,X1) != k3_waybel_0(esk8_0,X2)
    | ~ r2_hidden(esk5_2(esk8_0,esk9_0),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_86]),c_0_22])]),c_0_12])).

cnf(c_0_124,negated_conjecture,
    ( k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)) = k3_waybel_0(esk8_0,esk9_0)
    | m1_subset_1(esk2_3(esk8_0,esk9_0,k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | ~ m1_subset_1(k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)),k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_119]),c_0_13]),c_0_22])])).

cnf(c_0_125,negated_conjecture,
    ( k3_waybel_0(esk8_0,X1) = k3_waybel_0(esk8_0,esk9_0)
    | r2_hidden(esk2_3(esk8_0,esk9_0,k3_waybel_0(esk8_0,X1)),k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)))
    | r2_hidden(esk2_3(esk8_0,esk9_0,k3_waybel_0(esk8_0,X1)),k3_waybel_0(esk8_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_36]),c_0_22])])).

cnf(c_0_126,negated_conjecture,
    ( v1_waybel_0(esk9_0,esk8_0)
    | X1 != k3_waybel_0(esk8_0,esk9_0)
    | ~ v1_waybel_0(X1,esk8_0)
    | ~ r2_hidden(esk5_2(esk8_0,esk9_0),X1)
    | ~ r2_hidden(esk6_2(esk8_0,esk9_0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_122]),c_0_21]),c_0_13]),c_0_22])]),c_0_23])).

cnf(c_0_127,negated_conjecture,
    ( v1_waybel_0(esk9_0,esk8_0)
    | r2_hidden(esk5_2(esk8_0,esk9_0),k3_waybel_0(esk8_0,X1))
    | k3_waybel_0(esk8_0,X1) != k3_waybel_0(esk8_0,esk9_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_32]),c_0_13]),c_0_22])])).

cnf(c_0_128,plain,
    ( X3 = k3_waybel_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r1_orders_2(X1,esk2_3(X1,X2,X3),X4)
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_129,negated_conjecture,
    ( k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)) = k3_waybel_0(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk2_3(esk8_0,esk9_0,k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0))),esk2_3(esk8_0,esk9_0,k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)),k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_124]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_130,negated_conjecture,
    ( k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,X1)) = k3_waybel_0(esk8_0,esk9_0)
    | r2_hidden(esk2_3(esk8_0,esk9_0,k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,X1))),k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)))
    | r2_hidden(esk2_3(esk8_0,esk9_0,k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,X1))),k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_36]),c_0_22])])).

cnf(c_0_131,negated_conjecture,
    ( v1_waybel_0(esk9_0,esk8_0)
    | k3_waybel_0(esk8_0,X1) != k3_waybel_0(esk8_0,esk9_0)
    | ~ v1_waybel_0(k3_waybel_0(esk8_0,X1),esk8_0)
    | ~ m1_subset_1(k3_waybel_0(esk8_0,X1),k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_60]),c_0_13]),c_0_22])]),c_0_127])).

cnf(c_0_132,negated_conjecture,
    ( v1_waybel_0(esk9_0,esk8_0)
    | v1_waybel_0(k3_waybel_0(esk8_0,esk9_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_133,plain,
    ( X1 = k3_waybel_0(X2,X3)
    | ~ r1_orders_2(X2,esk2_3(X2,X3,X1),X4)
    | ~ r2_hidden(esk2_3(X2,X3,X1),X1)
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_128,c_0_12])).

cnf(c_0_134,negated_conjecture,
    ( k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)) = k3_waybel_0(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk2_3(esk8_0,esk9_0,k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0))),esk4_4(esk8_0,X1,X2,X3))
    | ~ v1_waybel_0(X1,esk8_0)
    | ~ r1_orders_2(esk8_0,esk2_3(esk8_0,esk9_0,k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0))),X3)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)),k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_129]),c_0_87]),c_0_22])]),c_0_124])).

cnf(c_0_135,negated_conjecture,
    ( k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)) = k3_waybel_0(esk8_0,esk9_0)
    | r2_hidden(esk2_3(esk8_0,esk9_0,k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0))),k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0))) ),
    inference(spm,[status(thm)],[c_0_130,c_0_13])).

cnf(c_0_136,negated_conjecture,
    ( v1_waybel_0(esk9_0,esk8_0)
    | ~ m1_subset_1(k3_waybel_0(esk8_0,esk9_0),k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_132]),c_0_13])])).

cnf(c_0_137,negated_conjecture,
    ( k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)) = k3_waybel_0(esk8_0,esk9_0)
    | ~ v1_waybel_0(X1,esk8_0)
    | ~ r1_orders_2(esk8_0,esk2_3(esk8_0,esk9_0,k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0))),X2)
    | ~ r2_hidden(esk4_4(esk8_0,X1,X3,X2),esk9_0)
    | ~ r2_hidden(X3,X1)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)),k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_134]),c_0_13]),c_0_22])]),c_0_135])).

cnf(c_0_138,negated_conjecture,
    ( v1_waybel_0(esk9_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_36]),c_0_13]),c_0_22])])).

cnf(c_0_139,negated_conjecture,
    ( k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)) = k3_waybel_0(esk8_0,esk9_0)
    | ~ r1_orders_2(esk8_0,esk2_3(esk8_0,esk9_0,k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0))),X1)
    | ~ r2_hidden(X2,esk9_0)
    | ~ r2_hidden(X1,esk9_0)
    | ~ m1_subset_1(k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)),k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_118]),c_0_138]),c_0_13]),c_0_22])])).

cnf(c_0_140,negated_conjecture,
    ( k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)) = k3_waybel_0(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk2_3(esk8_0,esk9_0,k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0))),esk1_4(esk8_0,X1,X2,X3))
    | X2 != k3_waybel_0(esk8_0,X1)
    | ~ r1_orders_2(esk8_0,esk2_3(esk8_0,esk9_0,k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0))),X3)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)),k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_129]),c_0_87]),c_0_22])]),c_0_124])).

cnf(c_0_141,negated_conjecture,
    ( k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)) = k3_waybel_0(esk8_0,esk9_0)
    | X1 != k3_waybel_0(esk8_0,X2)
    | ~ r1_orders_2(esk8_0,esk2_3(esk8_0,esk9_0,k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0))),X3)
    | ~ r2_hidden(esk1_4(esk8_0,X2,X1,X3),esk9_0)
    | ~ r2_hidden(X4,esk9_0)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)),k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_139,c_0_140])).

cnf(c_0_142,negated_conjecture,
    ( k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)) = k3_waybel_0(esk8_0,esk9_0)
    | X1 != k3_waybel_0(esk8_0,esk9_0)
    | ~ r1_orders_2(esk8_0,esk2_3(esk8_0,esk9_0,k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0))),X2)
    | ~ r2_hidden(X3,esk9_0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)),k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_102]),c_0_13]),c_0_22])])).

cnf(c_0_143,negated_conjecture,
    ( k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)) = k3_waybel_0(esk8_0,esk9_0)
    | X1 != k3_waybel_0(esk8_0,esk9_0)
    | X2 != k3_waybel_0(esk8_0,X3)
    | ~ r1_orders_2(esk8_0,esk2_3(esk8_0,esk9_0,k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0))),X4)
    | ~ r2_hidden(esk1_4(esk8_0,X3,X2,X4),X1)
    | ~ r2_hidden(X5,esk9_0)
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)),k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_142,c_0_140])).

cnf(c_0_144,negated_conjecture,
    ( k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)) = k3_waybel_0(esk8_0,esk9_0)
    | X1 != k3_waybel_0(esk8_0,esk9_0)
    | X2 != k3_waybel_0(esk8_0,X1)
    | ~ r1_orders_2(esk8_0,esk2_3(esk8_0,esk9_0,k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0))),X3)
    | ~ r2_hidden(X4,esk9_0)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)),k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_102]),c_0_22])])).

cnf(c_0_145,negated_conjecture,
    ( k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)) = k3_waybel_0(esk8_0,esk9_0)
    | X1 != k3_waybel_0(esk8_0,esk9_0)
    | X2 != k3_waybel_0(esk8_0,X1)
    | ~ r2_hidden(esk2_3(esk8_0,esk9_0,k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0))),X2)
    | ~ r2_hidden(X3,esk9_0)
    | ~ m1_subset_1(k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)),k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144,c_0_81]),c_0_21]),c_0_13]),c_0_22])]),c_0_23])).

cnf(c_0_146,negated_conjecture,
    ( k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)) = k3_waybel_0(esk8_0,esk9_0)
    | k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)) != k3_waybel_0(esk8_0,X1)
    | X1 != k3_waybel_0(esk8_0,esk9_0)
    | ~ r2_hidden(X2,esk9_0)
    | ~ m1_subset_1(k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)),k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_145,c_0_135])).

cnf(c_0_147,negated_conjecture,
    ( k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)) = k3_waybel_0(esk8_0,esk9_0)
    | k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)) != k3_waybel_0(esk8_0,X1)
    | X1 != k3_waybel_0(esk8_0,esk9_0)
    | ~ r2_hidden(X2,esk9_0)
    | ~ m1_subset_1(k3_waybel_0(esk8_0,esk9_0),k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_146,c_0_36]),c_0_22])])).

cnf(c_0_148,negated_conjecture,
    ( k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)) = k3_waybel_0(esk8_0,esk9_0)
    | ~ r2_hidden(X1,esk9_0)
    | ~ m1_subset_1(k3_waybel_0(esk8_0,esk9_0),k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(er,[status(thm)],[c_0_147])).

cnf(c_0_149,negated_conjecture,
    ( k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)) = k3_waybel_0(esk8_0,esk9_0)
    | X1 != k3_waybel_0(X2,esk9_0)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(k3_waybel_0(esk8_0,esk9_0),k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_148,c_0_102])).

cnf(c_0_150,negated_conjecture,
    ( m1_subset_1(esk1_4(X1,esk9_0,X2,X3),u1_struct_0(esk8_0))
    | X2 != k3_waybel_0(X1,esk9_0)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_102])).

cnf(c_0_151,negated_conjecture,
    ( m1_subset_1(esk4_4(X1,esk9_0,X2,X3),u1_struct_0(esk8_0))
    | ~ v1_waybel_0(esk9_0,X1)
    | ~ r2_hidden(X3,esk9_0)
    | ~ r2_hidden(X2,esk9_0)
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_118])).

cnf(c_0_152,negated_conjecture,
    ( k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)) = k3_waybel_0(esk8_0,esk9_0)
    | k3_waybel_0(X1,X2) != k3_waybel_0(X1,esk9_0)
    | ~ r2_hidden(X3,k3_waybel_0(X1,X2))
    | ~ m1_subset_1(k3_waybel_0(esk8_0,esk9_0),k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_149,c_0_36])).

cnf(c_0_153,plain,
    ( r1_orders_2(X1,X2,esk4_4(X1,X3,X4,X5))
    | ~ v4_orders_2(X1)
    | ~ v1_waybel_0(X3,X1)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ r2_hidden(X5,X3)
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_113]),c_0_12]),c_0_89])).

cnf(c_0_154,plain,
    ( r1_orders_2(X1,X2,esk4_4(X1,X3,X4,X5))
    | X6 != k3_waybel_0(X1,X7)
    | ~ v4_orders_2(X1)
    | ~ v1_waybel_0(X3,X1)
    | ~ r1_orders_2(X1,esk1_4(X1,X7,X6,X2),X5)
    | ~ r2_hidden(X4,X3)
    | ~ r2_hidden(X5,X3)
    | ~ r2_hidden(X2,X6)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_69]),c_0_12]),c_0_70])).

cnf(c_0_155,negated_conjecture,
    ( r1_orders_2(esk8_0,esk1_4(X1,esk9_0,X2,X3),esk1_4(X1,esk9_0,X2,X3))
    | X2 != k3_waybel_0(X1,esk9_0)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_150]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_156,negated_conjecture,
    ( r1_orders_2(esk8_0,esk4_4(X1,esk9_0,X2,X3),esk4_4(X1,esk9_0,X2,X3))
    | ~ v1_waybel_0(esk9_0,X1)
    | ~ r2_hidden(X3,esk9_0)
    | ~ r2_hidden(X2,esk9_0)
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_151]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_157,negated_conjecture,
    ( k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)) = k3_waybel_0(esk8_0,esk9_0)
    | v1_waybel_0(k3_waybel_0(X1,X2),X3)
    | k3_waybel_0(X1,X2) != k3_waybel_0(X1,esk9_0)
    | ~ m1_subset_1(k3_waybel_0(esk8_0,esk9_0),k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(k3_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X3) ),
    inference(spm,[status(thm)],[c_0_152,c_0_17])).

cnf(c_0_158,plain,
    ( v1_waybel_0(X1,X2)
    | ~ v4_orders_2(X2)
    | ~ v1_waybel_0(X3,X2)
    | ~ r1_orders_2(X2,esk5_2(X2,X1),esk4_4(X2,X3,X4,X5))
    | ~ r1_orders_2(X2,esk6_2(X2,X1),X4)
    | ~ r2_hidden(esk4_4(X2,X3,X4,X5),X1)
    | ~ r2_hidden(X5,X3)
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_153]),c_0_44])).

cnf(c_0_159,negated_conjecture,
    ( r1_orders_2(esk8_0,X1,esk4_4(esk8_0,X2,X3,esk1_4(esk8_0,esk9_0,X4,X1)))
    | X4 != k3_waybel_0(esk8_0,esk9_0)
    | ~ v1_waybel_0(X2,esk8_0)
    | ~ r2_hidden(esk1_4(esk8_0,esk9_0,X4,X1),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_154,c_0_155]),c_0_87]),c_0_13]),c_0_22])])).

cnf(c_0_160,negated_conjecture,
    ( r2_hidden(esk4_4(X1,esk9_0,X2,X3),k3_waybel_0(esk8_0,X4))
    | k3_waybel_0(esk8_0,X4) != k3_waybel_0(esk8_0,X5)
    | ~ v1_waybel_0(esk9_0,X1)
    | ~ r2_hidden(esk4_4(X1,esk9_0,X2,X3),X5)
    | ~ r2_hidden(X3,esk9_0)
    | ~ r2_hidden(X2,esk9_0)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_156]),c_0_22])]),c_0_12])).

cnf(c_0_161,negated_conjecture,
    ( k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)) = k3_waybel_0(esk8_0,esk9_0)
    | v1_waybel_0(k3_waybel_0(X1,esk9_0),X2)
    | ~ m1_subset_1(k3_waybel_0(esk8_0,esk9_0),k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(k3_waybel_0(X1,esk9_0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(er,[status(thm)],[c_0_157])).

cnf(c_0_162,negated_conjecture,
    ( v1_waybel_0(X1,esk8_0)
    | X2 != k3_waybel_0(esk8_0,esk9_0)
    | ~ v1_waybel_0(X3,esk8_0)
    | ~ r1_orders_2(esk8_0,esk6_2(esk8_0,X1),X4)
    | ~ r2_hidden(esk4_4(esk8_0,X3,X4,esk1_4(esk8_0,esk9_0,X2,esk5_2(esk8_0,X1))),X1)
    | ~ r2_hidden(esk1_4(esk8_0,esk9_0,X2,esk5_2(esk8_0,X1)),X3)
    | ~ r2_hidden(esk5_2(esk8_0,X1),X2)
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_158,c_0_159]),c_0_87]),c_0_22])])).

cnf(c_0_163,negated_conjecture,
    ( r2_hidden(esk4_4(X1,esk9_0,X2,X3),k3_waybel_0(esk8_0,X4))
    | k3_waybel_0(esk8_0,X4) != k3_waybel_0(esk8_0,esk9_0)
    | ~ v1_waybel_0(esk9_0,X1)
    | ~ r2_hidden(X3,esk9_0)
    | ~ r2_hidden(X2,esk9_0)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160,c_0_118]),c_0_13])])).

cnf(c_0_164,negated_conjecture,
    ( k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)) = k3_waybel_0(esk8_0,esk9_0)
    | v1_waybel_0(k3_waybel_0(X1,esk9_0),X2)
    | ~ m1_subset_1(k3_waybel_0(X1,esk9_0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_161,c_0_36]),c_0_13]),c_0_22])])).

cnf(c_0_165,negated_conjecture,
    ( ~ v1_waybel_0(esk9_0,esk8_0)
    | ~ v1_waybel_0(k3_waybel_0(esk8_0,esk9_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_166,plain,
    ( v2_struct_0(X1)
    | v1_waybel_0(X2,X1)
    | r1_orders_2(X1,esk5_2(X1,X2),esk5_2(X1,X2))
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_34])).

cnf(c_0_167,negated_conjecture,
    ( v1_waybel_0(k3_waybel_0(esk8_0,X1),esk8_0)
    | k3_waybel_0(esk8_0,X1) != k3_waybel_0(esk8_0,esk9_0)
    | X2 != k3_waybel_0(esk8_0,esk9_0)
    | ~ r1_orders_2(esk8_0,esk6_2(esk8_0,k3_waybel_0(esk8_0,X1)),X3)
    | ~ r2_hidden(esk1_4(esk8_0,esk9_0,X2,esk5_2(esk8_0,k3_waybel_0(esk8_0,X1))),esk9_0)
    | ~ r2_hidden(esk5_2(esk8_0,k3_waybel_0(esk8_0,X1)),X2)
    | ~ r2_hidden(X3,esk9_0)
    | ~ m1_subset_1(k3_waybel_0(esk8_0,X1),k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162,c_0_163]),c_0_138]),c_0_13]),c_0_22])])).

cnf(c_0_168,negated_conjecture,
    ( k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)) = k3_waybel_0(esk8_0,esk9_0)
    | v1_waybel_0(k3_waybel_0(X1,esk9_0),X1)
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_164,c_0_36])).

cnf(c_0_169,negated_conjecture,
    ( ~ v1_waybel_0(k3_waybel_0(esk8_0,esk9_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_165,c_0_138])])).

cnf(c_0_170,plain,
    ( v2_struct_0(X1)
    | v1_waybel_0(X2,X1)
    | r2_hidden(esk5_2(X1,X2),k3_waybel_0(X1,X3))
    | k3_waybel_0(X1,X3) != k3_waybel_0(X1,X4)
    | ~ v3_orders_2(X1)
    | ~ r2_hidden(esk5_2(X1,X2),X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_166]),c_0_12])).

cnf(c_0_171,negated_conjecture,
    ( v1_waybel_0(k3_waybel_0(esk8_0,X1),esk8_0)
    | k3_waybel_0(esk8_0,X1) != k3_waybel_0(esk8_0,esk9_0)
    | X2 != k3_waybel_0(esk8_0,esk9_0)
    | ~ r1_orders_2(esk8_0,esk6_2(esk8_0,k3_waybel_0(esk8_0,X1)),X3)
    | ~ r2_hidden(esk5_2(esk8_0,k3_waybel_0(esk8_0,X1)),X2)
    | ~ r2_hidden(X3,esk9_0)
    | ~ m1_subset_1(k3_waybel_0(esk8_0,X1),k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_167,c_0_102]),c_0_13]),c_0_22])])).

cnf(c_0_172,negated_conjecture,
    ( k3_waybel_0(esk8_0,k3_waybel_0(esk8_0,esk9_0)) = k3_waybel_0(esk8_0,esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_168,c_0_13]),c_0_22])]),c_0_169])).

cnf(c_0_173,plain,
    ( v2_struct_0(X1)
    | v1_waybel_0(X2,X1)
    | r2_hidden(esk5_2(X1,X2),k3_waybel_0(X1,X3))
    | k3_waybel_0(X1,X3) != k3_waybel_0(X1,X2)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_170,c_0_32])).

cnf(c_0_174,plain,
    ( v2_struct_0(X1)
    | v1_waybel_0(X2,X1)
    | r2_hidden(esk6_2(X1,X2),k3_waybel_0(X1,X3))
    | k3_waybel_0(X1,X3) != k3_waybel_0(X1,X4)
    | ~ v3_orders_2(X1)
    | ~ r2_hidden(esk6_2(X1,X2),X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_122]),c_0_12])).

cnf(c_0_175,negated_conjecture,
    ( X1 != k3_waybel_0(esk8_0,esk9_0)
    | ~ r1_orders_2(esk8_0,esk6_2(esk8_0,k3_waybel_0(esk8_0,esk9_0)),X2)
    | ~ r2_hidden(esk5_2(esk8_0,k3_waybel_0(esk8_0,esk9_0)),X1)
    | ~ r2_hidden(X2,esk9_0)
    | ~ m1_subset_1(k3_waybel_0(esk8_0,esk9_0),k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_171,c_0_172]),c_0_169])).

cnf(c_0_176,plain,
    ( v2_struct_0(X1)
    | v1_waybel_0(X2,X1)
    | r2_hidden(esk5_2(X1,X2),k3_waybel_0(X1,X3))
    | k3_waybel_0(X1,X3) != k3_waybel_0(X1,k3_waybel_0(X1,X4))
    | k3_waybel_0(X1,X4) != k3_waybel_0(X1,X2)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_170,c_0_173]),c_0_36])).

cnf(c_0_177,plain,
    ( v2_struct_0(X1)
    | v1_waybel_0(X2,X1)
    | r2_hidden(esk6_2(X1,X2),k3_waybel_0(X1,X3))
    | k3_waybel_0(X1,X3) != k3_waybel_0(X1,X2)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_174,c_0_17])).

cnf(c_0_178,negated_conjecture,
    ( X1 != k3_waybel_0(esk8_0,esk9_0)
    | X2 != k3_waybel_0(esk8_0,X3)
    | ~ r2_hidden(esk1_4(esk8_0,X3,X2,esk6_2(esk8_0,k3_waybel_0(esk8_0,esk9_0))),esk9_0)
    | ~ r2_hidden(esk5_2(esk8_0,k3_waybel_0(esk8_0,esk9_0)),X1)
    | ~ r2_hidden(esk6_2(esk8_0,k3_waybel_0(esk8_0,esk9_0)),X2)
    | ~ m1_subset_1(k3_waybel_0(esk8_0,esk9_0),k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_175,c_0_69]),c_0_22])])).

cnf(c_0_179,plain,
    ( v2_struct_0(X1)
    | v1_waybel_0(X2,X1)
    | r2_hidden(esk5_2(X1,X2),k3_waybel_0(X1,k3_waybel_0(X1,X3)))
    | k3_waybel_0(X1,X3) != k3_waybel_0(X1,X2)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_176]),c_0_36])).

cnf(c_0_180,plain,
    ( v2_struct_0(X1)
    | v1_waybel_0(X2,X1)
    | r2_hidden(esk6_2(X1,X2),k3_waybel_0(X1,X3))
    | k3_waybel_0(X1,X3) != k3_waybel_0(X1,k3_waybel_0(X1,X4))
    | k3_waybel_0(X1,X4) != k3_waybel_0(X1,X2)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_174,c_0_177]),c_0_36])).

cnf(c_0_181,negated_conjecture,
    ( X1 != k3_waybel_0(esk8_0,esk9_0)
    | X2 != k3_waybel_0(esk8_0,esk9_0)
    | ~ r2_hidden(esk5_2(esk8_0,k3_waybel_0(esk8_0,esk9_0)),X1)
    | ~ r2_hidden(esk6_2(esk8_0,k3_waybel_0(esk8_0,esk9_0)),X2)
    | ~ m1_subset_1(k3_waybel_0(esk8_0,esk9_0),k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_178,c_0_102]),c_0_13]),c_0_22])])).

cnf(c_0_182,negated_conjecture,
    ( v1_waybel_0(X1,esk8_0)
    | r2_hidden(esk5_2(esk8_0,X1),k3_waybel_0(esk8_0,esk9_0))
    | k3_waybel_0(esk8_0,esk9_0) != k3_waybel_0(esk8_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_179,c_0_172]),c_0_21]),c_0_13]),c_0_22])]),c_0_23])).

cnf(c_0_183,plain,
    ( v2_struct_0(X1)
    | v1_waybel_0(X2,X1)
    | r2_hidden(esk6_2(X1,X2),k3_waybel_0(X1,k3_waybel_0(X1,X3)))
    | k3_waybel_0(X1,X3) != k3_waybel_0(X1,X2)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_180]),c_0_36])).

cnf(c_0_184,negated_conjecture,
    ( X1 != k3_waybel_0(esk8_0,esk9_0)
    | ~ r2_hidden(esk6_2(esk8_0,k3_waybel_0(esk8_0,esk9_0)),X1)
    | ~ m1_subset_1(k3_waybel_0(esk8_0,esk9_0),k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_181,c_0_182]),c_0_172])]),c_0_169])).

cnf(c_0_185,negated_conjecture,
    ( v1_waybel_0(X1,esk8_0)
    | r2_hidden(esk6_2(esk8_0,X1),k3_waybel_0(esk8_0,esk9_0))
    | k3_waybel_0(esk8_0,esk9_0) != k3_waybel_0(esk8_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_183,c_0_172]),c_0_21]),c_0_13]),c_0_22])]),c_0_23])).

cnf(c_0_186,negated_conjecture,
    ( ~ m1_subset_1(k3_waybel_0(esk8_0,esk9_0),k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_184,c_0_185]),c_0_172])]),c_0_169])).

cnf(c_0_187,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_186,c_0_36]),c_0_13]),c_0_22])]),
    [proof]).

%------------------------------------------------------------------------------
