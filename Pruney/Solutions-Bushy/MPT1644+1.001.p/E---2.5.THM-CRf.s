%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1644+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:30 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 159 expanded)
%              Number of clauses        :   35 (  65 expanded)
%              Number of leaves         :    6 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :  305 (1156 expanded)
%              Number of equality atoms :   26 (  62 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal clause size      :   61 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d16_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = k4_waybel_0(X1,X2)
              <=> ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r2_hidden(X4,X3)
                    <=> ? [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                          & r1_orders_2(X1,X5,X4)
                          & r2_hidden(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_waybel_0)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(d20_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v13_waybel_0(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( ( r2_hidden(X3,X2)
                        & r1_orders_2(X1,X3,X4) )
                     => r2_hidden(X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).

fof(dt_k4_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k4_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_waybel_0)).

fof(t24_waybel_0,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v13_waybel_0(X2,X1)
          <=> r1_tarski(k4_waybel_0(X1,X2),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_waybel_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_6,plain,(
    ! [X6,X7,X8,X9,X11,X13] :
      ( ( m1_subset_1(esk1_4(X6,X7,X8,X9),u1_struct_0(X6))
        | ~ r2_hidden(X9,X8)
        | ~ m1_subset_1(X9,u1_struct_0(X6))
        | X8 != k4_waybel_0(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) )
      & ( r1_orders_2(X6,esk1_4(X6,X7,X8,X9),X9)
        | ~ r2_hidden(X9,X8)
        | ~ m1_subset_1(X9,u1_struct_0(X6))
        | X8 != k4_waybel_0(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) )
      & ( r2_hidden(esk1_4(X6,X7,X8,X9),X7)
        | ~ r2_hidden(X9,X8)
        | ~ m1_subset_1(X9,u1_struct_0(X6))
        | X8 != k4_waybel_0(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) )
      & ( ~ m1_subset_1(X11,u1_struct_0(X6))
        | ~ r1_orders_2(X6,X11,X9)
        | ~ r2_hidden(X11,X7)
        | r2_hidden(X9,X8)
        | ~ m1_subset_1(X9,u1_struct_0(X6))
        | X8 != k4_waybel_0(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) )
      & ( m1_subset_1(esk2_3(X6,X7,X8),u1_struct_0(X6))
        | X8 = k4_waybel_0(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) )
      & ( ~ r2_hidden(esk2_3(X6,X7,X8),X8)
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r1_orders_2(X6,X13,esk2_3(X6,X7,X8))
        | ~ r2_hidden(X13,X7)
        | X8 = k4_waybel_0(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) )
      & ( m1_subset_1(esk3_3(X6,X7,X8),u1_struct_0(X6))
        | r2_hidden(esk2_3(X6,X7,X8),X8)
        | X8 = k4_waybel_0(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) )
      & ( r1_orders_2(X6,esk3_3(X6,X7,X8),esk2_3(X6,X7,X8))
        | r2_hidden(esk2_3(X6,X7,X8),X8)
        | X8 = k4_waybel_0(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) )
      & ( r2_hidden(esk3_3(X6,X7,X8),X7)
        | r2_hidden(esk2_3(X6,X7,X8),X8)
        | X8 = k4_waybel_0(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_waybel_0])])])])])).

fof(c_0_7,plain,(
    ! [X29,X30,X31] :
      ( ~ r2_hidden(X29,X30)
      | ~ m1_subset_1(X30,k1_zfmisc_1(X31))
      | m1_subset_1(X29,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_8,plain,(
    ! [X15,X16,X17,X18] :
      ( ( ~ v13_waybel_0(X16,X15)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X18,u1_struct_0(X15))
        | ~ r2_hidden(X17,X16)
        | ~ r1_orders_2(X15,X17,X18)
        | r2_hidden(X18,X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_orders_2(X15) )
      & ( m1_subset_1(esk4_2(X15,X16),u1_struct_0(X15))
        | v13_waybel_0(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_orders_2(X15) )
      & ( m1_subset_1(esk5_2(X15,X16),u1_struct_0(X15))
        | v13_waybel_0(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_orders_2(X15) )
      & ( r2_hidden(esk4_2(X15,X16),X16)
        | v13_waybel_0(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_orders_2(X15) )
      & ( r1_orders_2(X15,esk4_2(X15,X16),esk5_2(X15,X16))
        | v13_waybel_0(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_orders_2(X15) )
      & ( ~ r2_hidden(esk5_2(X15,X16),X16)
        | v13_waybel_0(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_orders_2(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).

cnf(c_0_9,plain,
    ( r2_hidden(X3,X5)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,X1,X3)
    | ~ r2_hidden(X1,X4)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | X5 != k4_waybel_0(X2,X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X27,X28] :
      ( ~ l1_orders_2(X27)
      | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
      | m1_subset_1(k4_waybel_0(X27,X28),k1_zfmisc_1(u1_struct_0(X27))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_waybel_0])])).

cnf(c_0_12,plain,
    ( r2_hidden(X4,X1)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ r1_orders_2(X2,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r1_orders_2(X1,esk1_4(X1,X2,X3,X4),X4)
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | X3 != k4_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v13_waybel_0(X2,X1)
            <=> r1_tarski(k4_waybel_0(X1,X2),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t24_waybel_0])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X2)
    | X2 != k4_waybel_0(X3,X4)
    | ~ r1_orders_2(X3,X5,X1)
    | ~ r2_hidden(X5,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(csr,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_16,plain,
    ( m1_subset_1(k4_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X2)
    | ~ v13_waybel_0(X2,X3)
    | ~ r1_orders_2(X3,X4,X1)
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(csr,[status(thm)],[c_0_12,c_0_10])).

cnf(c_0_18,plain,
    ( r1_orders_2(X1,esk1_4(X1,X2,X3,X4),X4)
    | X3 != k4_waybel_0(X1,X2)
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[c_0_13,c_0_10])).

cnf(c_0_19,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | X3 != k4_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_20,plain,(
    ! [X21,X22,X23,X24,X25] :
      ( ( ~ r1_tarski(X21,X22)
        | ~ r2_hidden(X23,X21)
        | r2_hidden(X23,X22) )
      & ( r2_hidden(esk6_2(X24,X25),X24)
        | r1_tarski(X24,X25) )
      & ( ~ r2_hidden(esk6_2(X24,X25),X25)
        | r1_tarski(X24,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_21,negated_conjecture,
    ( l1_orders_2(esk7_0)
    & m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0)))
    & ( ~ v13_waybel_0(esk8_0,esk7_0)
      | ~ r1_tarski(k4_waybel_0(esk7_0,esk8_0),esk8_0) )
    & ( v13_waybel_0(esk8_0,esk7_0)
      | r1_tarski(k4_waybel_0(esk7_0,esk8_0),esk8_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,k4_waybel_0(X2,X3))
    | k4_waybel_0(X2,X3) != k4_waybel_0(X2,X4)
    | ~ r1_orders_2(X2,X5,X1)
    | ~ r2_hidden(X5,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,plain,
    ( r1_orders_2(X1,esk4_2(X1,X2),esk5_2(X1,X2))
    | v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,plain,
    ( m1_subset_1(esk5_2(X1,X2),u1_struct_0(X1))
    | v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | X3 != k4_waybel_0(X4,X5)
    | ~ v13_waybel_0(X2,X4)
    | ~ r2_hidden(esk1_4(X4,X5,X3,X1),X2)
    | ~ r2_hidden(X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ l1_orders_2(X4) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_10])).

cnf(c_0_26,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X2)
    | X3 != k4_waybel_0(X1,X2)
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[c_0_19,c_0_10])).

cnf(c_0_27,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( v13_waybel_0(esk8_0,esk7_0)
    | r1_tarski(k4_waybel_0(esk7_0,esk8_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( v13_waybel_0(X1,X2)
    | r2_hidden(esk5_2(X2,X1),k4_waybel_0(X2,X3))
    | k4_waybel_0(X2,X3) != k4_waybel_0(X2,X4)
    | ~ r2_hidden(esk4_2(X2,X1),X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_30,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X2)
    | X3 != k4_waybel_0(X4,X2)
    | ~ v13_waybel_0(X2,X4)
    | ~ r2_hidden(X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ l1_orders_2(X4) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( v13_waybel_0(esk8_0,esk7_0)
    | r2_hidden(X1,esk8_0)
    | ~ r2_hidden(X1,k4_waybel_0(esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( v13_waybel_0(X1,X2)
    | r2_hidden(esk5_2(X2,X1),k4_waybel_0(X2,X3))
    | k4_waybel_0(X2,X3) != k4_waybel_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,negated_conjecture,
    ( l1_orders_2(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X2)
    | k4_waybel_0(X3,X4) != k4_waybel_0(X3,X2)
    | ~ v13_waybel_0(X2,X3)
    | ~ r2_hidden(X1,k4_waybel_0(X3,X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_orders_2(X3) ),
    inference(spm,[status(thm)],[c_0_31,c_0_16])).

cnf(c_0_37,plain,
    ( r2_hidden(esk6_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_38,plain,
    ( v13_waybel_0(X2,X1)
    | ~ r2_hidden(esk5_2(X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_39,negated_conjecture,
    ( v13_waybel_0(esk8_0,esk7_0)
    | v13_waybel_0(X1,esk7_0)
    | r2_hidden(esk5_2(esk7_0,X1),esk8_0)
    | k4_waybel_0(esk7_0,esk8_0) != k4_waybel_0(esk7_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35])])).

cnf(c_0_40,plain,
    ( r1_tarski(k4_waybel_0(X1,X2),X3)
    | r2_hidden(esk6_2(k4_waybel_0(X1,X2),X3),X4)
    | k4_waybel_0(X1,X2) != k4_waybel_0(X1,X4)
    | ~ v13_waybel_0(X4,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( v13_waybel_0(esk8_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_34]),c_0_35])])).

cnf(c_0_42,negated_conjecture,
    ( ~ v13_waybel_0(esk8_0,esk7_0)
    | ~ r1_tarski(k4_waybel_0(esk7_0,esk8_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk6_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k4_waybel_0(esk7_0,X1),X2)
    | r2_hidden(esk6_2(k4_waybel_0(esk7_0,X1),X2),esk8_0)
    | k4_waybel_0(esk7_0,X1) != k4_waybel_0(esk7_0,esk8_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_34]),c_0_35])])).

cnf(c_0_45,negated_conjecture,
    ( ~ r1_tarski(k4_waybel_0(esk7_0,esk8_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_41])])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(k4_waybel_0(esk7_0,X1),esk8_0)
    | k4_waybel_0(esk7_0,X1) != k4_waybel_0(esk7_0,esk8_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_34])]),
    [proof]).

%------------------------------------------------------------------------------
