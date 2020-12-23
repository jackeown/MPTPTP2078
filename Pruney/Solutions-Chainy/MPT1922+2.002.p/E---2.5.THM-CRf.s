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
% DateTime   : Thu Dec  3 11:21:09 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 149 expanded)
%              Number of clauses        :   42 (  56 expanded)
%              Number of leaves         :   12 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :  228 ( 944 expanded)
%              Number of equality atoms :   22 ( 144 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d8_yellow_6,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => ! [X3] :
              ( l1_waybel_0(X3,X1)
             => ( m1_yellow_6(X3,X1,X2)
              <=> ( m1_yellow_0(X3,X2)
                  & u1_waybel_0(X1,X3) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),u1_struct_0(X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_yellow_6)).

fof(dt_m1_yellow_6,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_waybel_0(X2,X1) )
     => ! [X3] :
          ( m1_yellow_6(X3,X1,X2)
         => l1_waybel_0(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_yellow_6)).

fof(t20_yellow_6,conjecture,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => ! [X3] :
              ( m1_yellow_6(X3,X1,X2)
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X2))
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X3))
                         => ! [X7] :
                              ( m1_subset_1(X7,u1_struct_0(X3))
                             => ( ( X4 = X6
                                  & X5 = X7
                                  & r1_orders_2(X3,X6,X7) )
                               => r1_orders_2(X2,X4,X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_yellow_6)).

fof(d13_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( m1_yellow_0(X2,X1)
          <=> ( r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
              & r1_tarski(u1_orders_2(X2),u1_orders_2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_yellow_0)).

fof(dt_m1_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_yellow_0(X2,X1)
         => l1_orders_2(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_yellow_0)).

fof(dt_l1_waybel_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => l1_orders_2(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(d9_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_orders_2(X1,X2,X3)
              <=> r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

fof(t99_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(c_0_12,plain,(
    ! [X34,X35,X36] :
      ( ( m1_yellow_0(X36,X35)
        | ~ m1_yellow_6(X36,X34,X35)
        | ~ l1_waybel_0(X36,X34)
        | ~ l1_waybel_0(X35,X34)
        | ~ l1_struct_0(X34) )
      & ( u1_waybel_0(X34,X36) = k2_partfun1(u1_struct_0(X35),u1_struct_0(X34),u1_waybel_0(X34,X35),u1_struct_0(X36))
        | ~ m1_yellow_6(X36,X34,X35)
        | ~ l1_waybel_0(X36,X34)
        | ~ l1_waybel_0(X35,X34)
        | ~ l1_struct_0(X34) )
      & ( ~ m1_yellow_0(X36,X35)
        | u1_waybel_0(X34,X36) != k2_partfun1(u1_struct_0(X35),u1_struct_0(X34),u1_waybel_0(X34,X35),u1_struct_0(X36))
        | m1_yellow_6(X36,X34,X35)
        | ~ l1_waybel_0(X36,X34)
        | ~ l1_waybel_0(X35,X34)
        | ~ l1_struct_0(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_yellow_6])])])])).

fof(c_0_13,plain,(
    ! [X37,X38,X39] :
      ( ~ l1_struct_0(X37)
      | ~ l1_waybel_0(X38,X37)
      | ~ m1_yellow_6(X39,X37,X38)
      | l1_waybel_0(X39,X37) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_yellow_6])])])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( l1_waybel_0(X2,X1)
           => ! [X3] :
                ( m1_yellow_6(X3,X1,X2)
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X2))
                   => ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X2))
                       => ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X3))
                           => ! [X7] :
                                ( m1_subset_1(X7,u1_struct_0(X3))
                               => ( ( X4 = X6
                                    & X5 = X7
                                    & r1_orders_2(X3,X6,X7) )
                                 => r1_orders_2(X2,X4,X5) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t20_yellow_6])).

fof(c_0_15,plain,(
    ! [X28,X29] :
      ( ( r1_tarski(u1_struct_0(X29),u1_struct_0(X28))
        | ~ m1_yellow_0(X29,X28)
        | ~ l1_orders_2(X29)
        | ~ l1_orders_2(X28) )
      & ( r1_tarski(u1_orders_2(X29),u1_orders_2(X28))
        | ~ m1_yellow_0(X29,X28)
        | ~ l1_orders_2(X29)
        | ~ l1_orders_2(X28) )
      & ( ~ r1_tarski(u1_struct_0(X29),u1_struct_0(X28))
        | ~ r1_tarski(u1_orders_2(X29),u1_orders_2(X28))
        | m1_yellow_0(X29,X28)
        | ~ l1_orders_2(X29)
        | ~ l1_orders_2(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_yellow_0])])])])).

fof(c_0_16,plain,(
    ! [X30,X31] :
      ( ~ l1_orders_2(X30)
      | ~ m1_yellow_0(X31,X30)
      | l1_orders_2(X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_yellow_0])])])).

cnf(c_0_17,plain,
    ( m1_yellow_0(X1,X2)
    | ~ m1_yellow_6(X1,X3,X2)
    | ~ l1_waybel_0(X1,X3)
    | ~ l1_waybel_0(X2,X3)
    | ~ l1_struct_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( l1_waybel_0(X3,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_yellow_6(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,negated_conjecture,
    ( l1_struct_0(esk4_0)
    & l1_waybel_0(esk5_0,esk4_0)
    & m1_yellow_6(esk6_0,esk4_0,esk5_0)
    & m1_subset_1(esk7_0,u1_struct_0(esk5_0))
    & m1_subset_1(esk8_0,u1_struct_0(esk5_0))
    & m1_subset_1(esk9_0,u1_struct_0(esk6_0))
    & m1_subset_1(esk10_0,u1_struct_0(esk6_0))
    & esk7_0 = esk9_0
    & esk8_0 = esk10_0
    & r1_orders_2(esk6_0,esk9_0,esk10_0)
    & ~ r1_orders_2(esk5_0,esk7_0,esk8_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_20,plain,(
    ! [X32,X33] :
      ( ~ l1_struct_0(X32)
      | ~ l1_waybel_0(X33,X32)
      | l1_orders_2(X33) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).

cnf(c_0_21,plain,
    ( r1_tarski(u1_orders_2(X1),u1_orders_2(X2))
    | ~ m1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ m1_yellow_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( m1_yellow_0(X1,X2)
    | ~ m1_yellow_6(X1,X3,X2)
    | ~ l1_waybel_0(X2,X3)
    | ~ l1_struct_0(X3) ),
    inference(csr,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( m1_yellow_6(esk6_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( l1_waybel_0(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( l1_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( l1_orders_2(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_28,plain,(
    ! [X23,X24] :
      ( ( ~ m1_subset_1(X23,k1_zfmisc_1(X24))
        | r1_tarski(X23,X24) )
      & ( ~ r1_tarski(X23,X24)
        | m1_subset_1(X23,k1_zfmisc_1(X24)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_29,plain,
    ( r1_tarski(u1_orders_2(X1),u1_orders_2(X2))
    | ~ m1_yellow_0(X1,X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( m1_yellow_0(esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_31,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_25]),c_0_26])])).

fof(c_0_32,plain,(
    ! [X8,X9,X10,X12,X13,X14,X15,X17] :
      ( ( r2_hidden(X10,esk1_3(X8,X9,X10))
        | ~ r2_hidden(X10,X9)
        | X9 != k3_tarski(X8) )
      & ( r2_hidden(esk1_3(X8,X9,X10),X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k3_tarski(X8) )
      & ( ~ r2_hidden(X12,X13)
        | ~ r2_hidden(X13,X8)
        | r2_hidden(X12,X9)
        | X9 != k3_tarski(X8) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | ~ r2_hidden(esk2_2(X14,X15),X17)
        | ~ r2_hidden(X17,X14)
        | X15 = k3_tarski(X14) )
      & ( r2_hidden(esk2_2(X14,X15),esk3_2(X14,X15))
        | r2_hidden(esk2_2(X14,X15),X15)
        | X15 = k3_tarski(X14) )
      & ( r2_hidden(esk3_2(X14,X15),X14)
        | r2_hidden(esk2_2(X14,X15),X15)
        | X15 = k3_tarski(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

fof(c_0_33,plain,(
    ! [X21,X22] :
      ( ~ m1_subset_1(X21,X22)
      | v1_xboole_0(X22)
      | r2_hidden(X21,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_34,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(u1_orders_2(esk6_0),u1_orders_2(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])])).

fof(c_0_36,plain,(
    ! [X20] : ~ v1_xboole_0(k1_zfmisc_1(X20)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_37,plain,(
    ! [X25,X26,X27] :
      ( ( ~ r1_orders_2(X25,X26,X27)
        | r2_hidden(k4_tarski(X26,X27),u1_orders_2(X25))
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | ~ m1_subset_1(X26,u1_struct_0(X25))
        | ~ l1_orders_2(X25) )
      & ( ~ r2_hidden(k4_tarski(X26,X27),u1_orders_2(X25))
        | r1_orders_2(X25,X26,X27)
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | ~ m1_subset_1(X26,u1_struct_0(X25))
        | ~ l1_orders_2(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).

cnf(c_0_38,negated_conjecture,
    ( l1_waybel_0(esk6_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | X4 != k3_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk6_0),k1_zfmisc_1(u1_orders_2(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_42,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_43,plain,(
    ! [X19] : k3_tarski(k1_zfmisc_1(X19)) = X19 ),
    inference(variable_rename,[status(thm)],[t99_zfmisc_1])).

cnf(c_0_44,plain,
    ( r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk10_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_46,negated_conjecture,
    ( l1_orders_2(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_38]),c_0_26])])).

cnf(c_0_47,negated_conjecture,
    ( r1_orders_2(esk6_0,esk9_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_48,negated_conjecture,
    ( esk7_0 = esk9_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk9_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(u1_orders_2(esk6_0),k1_zfmisc_1(u1_orders_2(esk5_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_52,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk10_0),u1_orders_2(esk6_0))
    | ~ r1_orders_2(esk6_0,X1,esk10_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])])).

cnf(c_0_54,negated_conjecture,
    ( r1_orders_2(esk6_0,esk7_0,esk10_0) ),
    inference(rw,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk6_0)) ),
    inference(rw,[status(thm)],[c_0_49,c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(X1,u1_orders_2(esk5_0))
    | ~ r2_hidden(X1,u1_orders_2(esk6_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_0,esk10_0),u1_orders_2(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_59,negated_conjecture,
    ( esk8_0 = esk10_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_60,negated_conjecture,
    ( ~ r1_orders_2(esk5_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_61,plain,
    ( r1_orders_2(X3,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_0,esk10_0),u1_orders_2(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(esk10_0,u1_struct_0(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_65,negated_conjecture,
    ( ~ r1_orders_2(esk5_0,esk7_0,esk10_0) ),
    inference(rw,[status(thm)],[c_0_60,c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_31]),c_0_63]),c_0_64])]),c_0_65]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:42:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S064I
% 0.19/0.37  # and selection function SelectComplexG.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.028 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(d8_yellow_6, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_waybel_0(X2,X1)=>![X3]:(l1_waybel_0(X3,X1)=>(m1_yellow_6(X3,X1,X2)<=>(m1_yellow_0(X3,X2)&u1_waybel_0(X1,X3)=k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),u1_struct_0(X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_yellow_6)).
% 0.19/0.37  fof(dt_m1_yellow_6, axiom, ![X1, X2]:((l1_struct_0(X1)&l1_waybel_0(X2,X1))=>![X3]:(m1_yellow_6(X3,X1,X2)=>l1_waybel_0(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_yellow_6)).
% 0.19/0.37  fof(t20_yellow_6, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_waybel_0(X2,X1)=>![X3]:(m1_yellow_6(X3,X1,X2)=>![X4]:(m1_subset_1(X4,u1_struct_0(X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X3))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>(((X4=X6&X5=X7)&r1_orders_2(X3,X6,X7))=>r1_orders_2(X2,X4,X5))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_yellow_6)).
% 0.19/0.37  fof(d13_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(l1_orders_2(X2)=>(m1_yellow_0(X2,X1)<=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X1))&r1_tarski(u1_orders_2(X2),u1_orders_2(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_yellow_0)).
% 0.19/0.37  fof(dt_m1_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_yellow_0(X2,X1)=>l1_orders_2(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_yellow_0)).
% 0.19/0.37  fof(dt_l1_waybel_0, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_waybel_0(X2,X1)=>l1_orders_2(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 0.19/0.37  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.37  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 0.19/0.37  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.19/0.37  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.19/0.37  fof(d9_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_orders_2(X1,X2,X3)<=>r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_orders_2)).
% 0.19/0.37  fof(t99_zfmisc_1, axiom, ![X1]:k3_tarski(k1_zfmisc_1(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 0.19/0.37  fof(c_0_12, plain, ![X34, X35, X36]:(((m1_yellow_0(X36,X35)|~m1_yellow_6(X36,X34,X35)|~l1_waybel_0(X36,X34)|~l1_waybel_0(X35,X34)|~l1_struct_0(X34))&(u1_waybel_0(X34,X36)=k2_partfun1(u1_struct_0(X35),u1_struct_0(X34),u1_waybel_0(X34,X35),u1_struct_0(X36))|~m1_yellow_6(X36,X34,X35)|~l1_waybel_0(X36,X34)|~l1_waybel_0(X35,X34)|~l1_struct_0(X34)))&(~m1_yellow_0(X36,X35)|u1_waybel_0(X34,X36)!=k2_partfun1(u1_struct_0(X35),u1_struct_0(X34),u1_waybel_0(X34,X35),u1_struct_0(X36))|m1_yellow_6(X36,X34,X35)|~l1_waybel_0(X36,X34)|~l1_waybel_0(X35,X34)|~l1_struct_0(X34))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_yellow_6])])])])).
% 0.19/0.37  fof(c_0_13, plain, ![X37, X38, X39]:(~l1_struct_0(X37)|~l1_waybel_0(X38,X37)|(~m1_yellow_6(X39,X37,X38)|l1_waybel_0(X39,X37))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_yellow_6])])])).
% 0.19/0.37  fof(c_0_14, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:(l1_waybel_0(X2,X1)=>![X3]:(m1_yellow_6(X3,X1,X2)=>![X4]:(m1_subset_1(X4,u1_struct_0(X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X3))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>(((X4=X6&X5=X7)&r1_orders_2(X3,X6,X7))=>r1_orders_2(X2,X4,X5)))))))))), inference(assume_negation,[status(cth)],[t20_yellow_6])).
% 0.19/0.37  fof(c_0_15, plain, ![X28, X29]:(((r1_tarski(u1_struct_0(X29),u1_struct_0(X28))|~m1_yellow_0(X29,X28)|~l1_orders_2(X29)|~l1_orders_2(X28))&(r1_tarski(u1_orders_2(X29),u1_orders_2(X28))|~m1_yellow_0(X29,X28)|~l1_orders_2(X29)|~l1_orders_2(X28)))&(~r1_tarski(u1_struct_0(X29),u1_struct_0(X28))|~r1_tarski(u1_orders_2(X29),u1_orders_2(X28))|m1_yellow_0(X29,X28)|~l1_orders_2(X29)|~l1_orders_2(X28))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_yellow_0])])])])).
% 0.19/0.37  fof(c_0_16, plain, ![X30, X31]:(~l1_orders_2(X30)|(~m1_yellow_0(X31,X30)|l1_orders_2(X31))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_yellow_0])])])).
% 0.19/0.37  cnf(c_0_17, plain, (m1_yellow_0(X1,X2)|~m1_yellow_6(X1,X3,X2)|~l1_waybel_0(X1,X3)|~l1_waybel_0(X2,X3)|~l1_struct_0(X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  cnf(c_0_18, plain, (l1_waybel_0(X3,X1)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)|~m1_yellow_6(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  fof(c_0_19, negated_conjecture, (l1_struct_0(esk4_0)&(l1_waybel_0(esk5_0,esk4_0)&(m1_yellow_6(esk6_0,esk4_0,esk5_0)&(m1_subset_1(esk7_0,u1_struct_0(esk5_0))&(m1_subset_1(esk8_0,u1_struct_0(esk5_0))&(m1_subset_1(esk9_0,u1_struct_0(esk6_0))&(m1_subset_1(esk10_0,u1_struct_0(esk6_0))&(((esk7_0=esk9_0&esk8_0=esk10_0)&r1_orders_2(esk6_0,esk9_0,esk10_0))&~r1_orders_2(esk5_0,esk7_0,esk8_0))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.19/0.37  fof(c_0_20, plain, ![X32, X33]:(~l1_struct_0(X32)|(~l1_waybel_0(X33,X32)|l1_orders_2(X33))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).
% 0.19/0.37  cnf(c_0_21, plain, (r1_tarski(u1_orders_2(X1),u1_orders_2(X2))|~m1_yellow_0(X1,X2)|~l1_orders_2(X1)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.37  cnf(c_0_22, plain, (l1_orders_2(X2)|~l1_orders_2(X1)|~m1_yellow_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.37  cnf(c_0_23, plain, (m1_yellow_0(X1,X2)|~m1_yellow_6(X1,X3,X2)|~l1_waybel_0(X2,X3)|~l1_struct_0(X3)), inference(csr,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.37  cnf(c_0_24, negated_conjecture, (m1_yellow_6(esk6_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.37  cnf(c_0_25, negated_conjecture, (l1_waybel_0(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.37  cnf(c_0_26, negated_conjecture, (l1_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.37  cnf(c_0_27, plain, (l1_orders_2(X2)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.37  fof(c_0_28, plain, ![X23, X24]:((~m1_subset_1(X23,k1_zfmisc_1(X24))|r1_tarski(X23,X24))&(~r1_tarski(X23,X24)|m1_subset_1(X23,k1_zfmisc_1(X24)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.37  cnf(c_0_29, plain, (r1_tarski(u1_orders_2(X1),u1_orders_2(X2))|~m1_yellow_0(X1,X2)|~l1_orders_2(X2)), inference(csr,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.37  cnf(c_0_30, negated_conjecture, (m1_yellow_0(esk6_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26])])).
% 0.19/0.37  cnf(c_0_31, negated_conjecture, (l1_orders_2(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_25]), c_0_26])])).
% 0.19/0.37  fof(c_0_32, plain, ![X8, X9, X10, X12, X13, X14, X15, X17]:((((r2_hidden(X10,esk1_3(X8,X9,X10))|~r2_hidden(X10,X9)|X9!=k3_tarski(X8))&(r2_hidden(esk1_3(X8,X9,X10),X8)|~r2_hidden(X10,X9)|X9!=k3_tarski(X8)))&(~r2_hidden(X12,X13)|~r2_hidden(X13,X8)|r2_hidden(X12,X9)|X9!=k3_tarski(X8)))&((~r2_hidden(esk2_2(X14,X15),X15)|(~r2_hidden(esk2_2(X14,X15),X17)|~r2_hidden(X17,X14))|X15=k3_tarski(X14))&((r2_hidden(esk2_2(X14,X15),esk3_2(X14,X15))|r2_hidden(esk2_2(X14,X15),X15)|X15=k3_tarski(X14))&(r2_hidden(esk3_2(X14,X15),X14)|r2_hidden(esk2_2(X14,X15),X15)|X15=k3_tarski(X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 0.19/0.37  fof(c_0_33, plain, ![X21, X22]:(~m1_subset_1(X21,X22)|(v1_xboole_0(X22)|r2_hidden(X21,X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.19/0.37  cnf(c_0_34, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.37  cnf(c_0_35, negated_conjecture, (r1_tarski(u1_orders_2(esk6_0),u1_orders_2(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])])).
% 0.19/0.37  fof(c_0_36, plain, ![X20]:~v1_xboole_0(k1_zfmisc_1(X20)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.19/0.37  fof(c_0_37, plain, ![X25, X26, X27]:((~r1_orders_2(X25,X26,X27)|r2_hidden(k4_tarski(X26,X27),u1_orders_2(X25))|~m1_subset_1(X27,u1_struct_0(X25))|~m1_subset_1(X26,u1_struct_0(X25))|~l1_orders_2(X25))&(~r2_hidden(k4_tarski(X26,X27),u1_orders_2(X25))|r1_orders_2(X25,X26,X27)|~m1_subset_1(X27,u1_struct_0(X25))|~m1_subset_1(X26,u1_struct_0(X25))|~l1_orders_2(X25))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).
% 0.19/0.37  cnf(c_0_38, negated_conjecture, (l1_waybel_0(esk6_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_24]), c_0_25]), c_0_26])])).
% 0.19/0.37  cnf(c_0_39, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X2,X3)|X4!=k3_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.37  cnf(c_0_40, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.37  cnf(c_0_41, negated_conjecture, (m1_subset_1(u1_orders_2(esk6_0),k1_zfmisc_1(u1_orders_2(esk5_0)))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.37  cnf(c_0_42, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.37  fof(c_0_43, plain, ![X19]:k3_tarski(k1_zfmisc_1(X19))=X19, inference(variable_rename,[status(thm)],[t99_zfmisc_1])).
% 0.19/0.37  cnf(c_0_44, plain, (r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))|~r1_orders_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.37  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk10_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.37  cnf(c_0_46, negated_conjecture, (l1_orders_2(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_38]), c_0_26])])).
% 0.19/0.37  cnf(c_0_47, negated_conjecture, (r1_orders_2(esk6_0,esk9_0,esk10_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.37  cnf(c_0_48, negated_conjecture, (esk7_0=esk9_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.37  cnf(c_0_49, negated_conjecture, (m1_subset_1(esk9_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.37  cnf(c_0_50, plain, (r2_hidden(X1,k3_tarski(X2))|~r2_hidden(X3,X2)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_39])).
% 0.19/0.37  cnf(c_0_51, negated_conjecture, (r2_hidden(u1_orders_2(esk6_0),k1_zfmisc_1(u1_orders_2(esk5_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 0.19/0.37  cnf(c_0_52, plain, (k3_tarski(k1_zfmisc_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.37  cnf(c_0_53, negated_conjecture, (r2_hidden(k4_tarski(X1,esk10_0),u1_orders_2(esk6_0))|~r1_orders_2(esk6_0,X1,esk10_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])])).
% 0.19/0.37  cnf(c_0_54, negated_conjecture, (r1_orders_2(esk6_0,esk7_0,esk10_0)), inference(rw,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.37  cnf(c_0_55, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk6_0))), inference(rw,[status(thm)],[c_0_49, c_0_48])).
% 0.19/0.37  cnf(c_0_56, negated_conjecture, (r2_hidden(X1,u1_orders_2(esk5_0))|~r2_hidden(X1,u1_orders_2(esk6_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])).
% 0.19/0.37  cnf(c_0_57, negated_conjecture, (r2_hidden(k4_tarski(esk7_0,esk10_0),u1_orders_2(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])])).
% 0.19/0.37  cnf(c_0_58, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.37  cnf(c_0_59, negated_conjecture, (esk8_0=esk10_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.37  cnf(c_0_60, negated_conjecture, (~r1_orders_2(esk5_0,esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.37  cnf(c_0_61, plain, (r1_orders_2(X3,X1,X2)|~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.37  cnf(c_0_62, negated_conjecture, (r2_hidden(k4_tarski(esk7_0,esk10_0),u1_orders_2(esk5_0))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.37  cnf(c_0_63, negated_conjecture, (m1_subset_1(esk10_0,u1_struct_0(esk5_0))), inference(rw,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.37  cnf(c_0_64, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.37  cnf(c_0_65, negated_conjecture, (~r1_orders_2(esk5_0,esk7_0,esk10_0)), inference(rw,[status(thm)],[c_0_60, c_0_59])).
% 0.19/0.37  cnf(c_0_66, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_31]), c_0_63]), c_0_64])]), c_0_65]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 67
% 0.19/0.37  # Proof object clause steps            : 42
% 0.19/0.37  # Proof object formula steps           : 25
% 0.19/0.37  # Proof object conjectures             : 30
% 0.19/0.37  # Proof object clause conjectures      : 27
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 23
% 0.19/0.37  # Proof object initial formulas used   : 12
% 0.19/0.37  # Proof object generating inferences   : 12
% 0.19/0.37  # Proof object simplifying inferences  : 30
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 12
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 33
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 33
% 0.19/0.37  # Processed clauses                    : 92
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 0
% 0.19/0.37  # ...remaining for further processing  : 92
% 0.19/0.37  # Other redundant clauses eliminated   : 3
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 0
% 0.19/0.37  # Generated clauses                    : 62
% 0.19/0.37  # ...of the previous two non-trivial   : 55
% 0.19/0.37  # Contextual simplify-reflections      : 4
% 0.19/0.37  # Paramodulations                      : 59
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 3
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 56
% 0.19/0.37  #    Positive orientable unit clauses  : 25
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 2
% 0.19/0.37  #    Non-unit-clauses                  : 29
% 0.19/0.37  # Current number of unprocessed clauses: 27
% 0.19/0.37  # ...number of literals in the above   : 76
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 33
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 252
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 90
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 4
% 0.19/0.37  # Unit Clause-clause subsumption calls : 9
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 0
% 0.19/0.37  # BW rewrite match successes           : 0
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 3599
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.033 s
% 0.19/0.37  # System time              : 0.003 s
% 0.19/0.37  # Total time               : 0.036 s
% 0.19/0.37  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
