%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1628+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:28 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :  142 (621806 expanded)
%              Number of clauses        :  125 (204999 expanded)
%              Number of leaves         :    8 (149751 expanded)
%              Depth                    :   60
%              Number of atoms          :  491 (5256843 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   35 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t8_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3,X4] :
              ( r1_tarski(X3,X4)
             => ( ( r1_waybel_0(X1,X2,X3)
                 => r1_waybel_0(X1,X2,X4) )
                & ( r2_waybel_0(X1,X2,X3)
                 => r2_waybel_0(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_0)).

fof(d12_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( r2_waybel_0(X1,X2,X3)
            <=> ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X2))
                 => ? [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                      & r1_orders_2(X2,X4,X5)
                      & r2_hidden(k2_waybel_0(X1,X2,X5),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_waybel_0)).

fof(d11_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( r1_waybel_0(X1,X2,X3)
            <=> ? [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X2))
                  & ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                     => ( r1_orders_2(X2,X4,X5)
                       => r2_hidden(k2_waybel_0(X1,X2,X5),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_waybel_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & l1_waybel_0(X2,X1) )
           => ! [X3,X4] :
                ( r1_tarski(X3,X4)
               => ( ( r1_waybel_0(X1,X2,X3)
                   => r1_waybel_0(X1,X2,X4) )
                  & ( r2_waybel_0(X1,X2,X3)
                   => r2_waybel_0(X1,X2,X4) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t8_waybel_0])).

fof(c_0_9,plain,(
    ! [X14,X15,X16,X17,X19,X21] :
      ( ( m1_subset_1(esk3_4(X14,X15,X16,X17),u1_struct_0(X15))
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ r2_waybel_0(X14,X15,X16)
        | v2_struct_0(X15)
        | ~ l1_waybel_0(X15,X14)
        | v2_struct_0(X14)
        | ~ l1_struct_0(X14) )
      & ( r1_orders_2(X15,X17,esk3_4(X14,X15,X16,X17))
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ r2_waybel_0(X14,X15,X16)
        | v2_struct_0(X15)
        | ~ l1_waybel_0(X15,X14)
        | v2_struct_0(X14)
        | ~ l1_struct_0(X14) )
      & ( r2_hidden(k2_waybel_0(X14,X15,esk3_4(X14,X15,X16,X17)),X16)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ r2_waybel_0(X14,X15,X16)
        | v2_struct_0(X15)
        | ~ l1_waybel_0(X15,X14)
        | v2_struct_0(X14)
        | ~ l1_struct_0(X14) )
      & ( m1_subset_1(esk4_3(X14,X15,X19),u1_struct_0(X15))
        | r2_waybel_0(X14,X15,X19)
        | v2_struct_0(X15)
        | ~ l1_waybel_0(X15,X14)
        | v2_struct_0(X14)
        | ~ l1_struct_0(X14) )
      & ( ~ m1_subset_1(X21,u1_struct_0(X15))
        | ~ r1_orders_2(X15,esk4_3(X14,X15,X19),X21)
        | ~ r2_hidden(k2_waybel_0(X14,X15,X21),X19)
        | r2_waybel_0(X14,X15,X19)
        | v2_struct_0(X15)
        | ~ l1_waybel_0(X15,X14)
        | v2_struct_0(X14)
        | ~ l1_struct_0(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_waybel_0])])])])])])])).

fof(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    & l1_struct_0(esk6_0)
    & ~ v2_struct_0(esk7_0)
    & l1_waybel_0(esk7_0,esk6_0)
    & r1_tarski(esk8_0,esk9_0)
    & ( r2_waybel_0(esk6_0,esk7_0,esk8_0)
      | r1_waybel_0(esk6_0,esk7_0,esk8_0) )
    & ( ~ r2_waybel_0(esk6_0,esk7_0,esk9_0)
      | r1_waybel_0(esk6_0,esk7_0,esk8_0) )
    & ( r2_waybel_0(esk6_0,esk7_0,esk8_0)
      | ~ r1_waybel_0(esk6_0,esk7_0,esk9_0) )
    & ( ~ r2_waybel_0(esk6_0,esk7_0,esk9_0)
      | ~ r1_waybel_0(esk6_0,esk7_0,esk9_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])).

cnf(c_0_11,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X2))
    | r2_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( l1_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
    ! [X6,X7,X8,X10,X11,X12] :
      ( ( m1_subset_1(esk1_3(X6,X7,X8),u1_struct_0(X7))
        | ~ r1_waybel_0(X6,X7,X8)
        | v2_struct_0(X7)
        | ~ l1_waybel_0(X7,X6)
        | v2_struct_0(X6)
        | ~ l1_struct_0(X6) )
      & ( ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r1_orders_2(X7,esk1_3(X6,X7,X8),X10)
        | r2_hidden(k2_waybel_0(X6,X7,X10),X8)
        | ~ r1_waybel_0(X6,X7,X8)
        | v2_struct_0(X7)
        | ~ l1_waybel_0(X7,X6)
        | v2_struct_0(X6)
        | ~ l1_struct_0(X6) )
      & ( m1_subset_1(esk2_4(X6,X7,X11,X12),u1_struct_0(X7))
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | r1_waybel_0(X6,X7,X11)
        | v2_struct_0(X7)
        | ~ l1_waybel_0(X7,X6)
        | v2_struct_0(X6)
        | ~ l1_struct_0(X6) )
      & ( r1_orders_2(X7,X12,esk2_4(X6,X7,X11,X12))
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | r1_waybel_0(X6,X7,X11)
        | v2_struct_0(X7)
        | ~ l1_waybel_0(X7,X6)
        | v2_struct_0(X6)
        | ~ l1_struct_0(X6) )
      & ( ~ r2_hidden(k2_waybel_0(X6,X7,esk2_4(X6,X7,X11,X12)),X11)
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | r1_waybel_0(X6,X7,X11)
        | v2_struct_0(X7)
        | ~ l1_waybel_0(X7,X6)
        | v2_struct_0(X6)
        | ~ l1_struct_0(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_waybel_0])])])])])])])).

cnf(c_0_17,negated_conjecture,
    ( r1_waybel_0(esk6_0,esk7_0,esk8_0)
    | ~ r2_waybel_0(esk6_0,esk7_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( r2_waybel_0(esk6_0,esk7_0,X1)
    | m1_subset_1(esk4_3(esk6_0,esk7_0,X1),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])]),c_0_14]),c_0_15])).

cnf(c_0_19,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_waybel_0(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk4_3(esk6_0,esk7_0,esk9_0),u1_struct_0(esk7_0))
    | r1_waybel_0(esk6_0,esk7_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_21,plain,(
    ! [X26,X27] :
      ( ( ~ m1_subset_1(X26,k1_zfmisc_1(X27))
        | r1_tarski(X26,X27) )
      & ( ~ r1_tarski(X26,X27)
        | m1_subset_1(X26,k1_zfmisc_1(X27)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_22,plain,
    ( r1_orders_2(X1,X2,esk2_4(X3,X1,X4,X2))
    | r1_waybel_0(X3,X1,X4)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_waybel_0(X1,X3)
    | ~ l1_struct_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk4_3(esk6_0,esk7_0,esk9_0),u1_struct_0(esk7_0))
    | m1_subset_1(esk1_3(esk6_0,esk7_0,esk8_0),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_12]),c_0_13])]),c_0_14]),c_0_15])).

cnf(c_0_24,plain,
    ( m1_subset_1(esk2_4(X1,X2,X3,X4),u1_struct_0(X2))
    | r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_25,plain,(
    ! [X28,X29,X30] :
      ( ~ r2_hidden(X28,X29)
      | ~ m1_subset_1(X29,k1_zfmisc_1(X30))
      | m1_subset_1(X28,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_26,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_28,negated_conjecture,
    ( r1_orders_2(esk7_0,esk1_3(esk6_0,esk7_0,esk8_0),esk2_4(X1,esk7_0,X2,esk1_3(esk6_0,esk7_0,esk8_0)))
    | m1_subset_1(esk4_3(esk6_0,esk7_0,esk9_0),u1_struct_0(esk7_0))
    | r1_waybel_0(X1,esk7_0,X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(esk7_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_14])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk2_4(X1,esk7_0,X2,esk1_3(esk6_0,esk7_0,esk8_0)),u1_struct_0(esk7_0))
    | m1_subset_1(esk4_3(esk6_0,esk7_0,esk9_0),u1_struct_0(esk7_0))
    | r1_waybel_0(X1,esk7_0,X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(esk7_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_23]),c_0_14])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,plain,
    ( r2_hidden(k2_waybel_0(X3,X2,X1),X4)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,esk1_3(X3,X2,X4),X1)
    | ~ r1_waybel_0(X3,X2,X4)
    | ~ l1_waybel_0(X2,X3)
    | ~ l1_struct_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_33,negated_conjecture,
    ( r1_orders_2(esk7_0,esk1_3(esk6_0,esk7_0,esk8_0),esk2_4(esk6_0,esk7_0,X1,esk1_3(esk6_0,esk7_0,esk8_0)))
    | m1_subset_1(esk4_3(esk6_0,esk7_0,esk9_0),u1_struct_0(esk7_0))
    | r1_waybel_0(esk6_0,esk7_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_12]),c_0_13])]),c_0_15])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk2_4(esk6_0,esk7_0,X1,esk1_3(esk6_0,esk7_0,esk8_0)),u1_struct_0(esk7_0))
    | m1_subset_1(esk4_3(esk6_0,esk7_0,esk9_0),u1_struct_0(esk7_0))
    | r1_waybel_0(esk6_0,esk7_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_12]),c_0_13])]),c_0_15])).

cnf(c_0_35,negated_conjecture,
    ( ~ r2_waybel_0(esk6_0,esk7_0,esk9_0)
    | ~ r1_waybel_0(esk6_0,esk7_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(X1,esk9_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk2_4(esk6_0,esk7_0,X1,esk1_3(esk6_0,esk7_0,esk8_0))),esk8_0)
    | m1_subset_1(esk4_3(esk6_0,esk7_0,esk9_0),u1_struct_0(esk7_0))
    | r1_waybel_0(esk6_0,esk7_0,X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_12]),c_0_13])]),c_0_15]),c_0_14]),c_0_20]),c_0_34])).

fof(c_0_38,plain,(
    ! [X31,X32,X33] :
      ( ~ r2_hidden(X31,X32)
      | ~ m1_subset_1(X32,k1_zfmisc_1(X33))
      | ~ v1_xboole_0(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_39,plain,(
    ! [X24,X25] :
      ( ~ m1_subset_1(X24,X25)
      | v1_xboole_0(X25)
      | r2_hidden(X24,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk4_3(esk6_0,esk7_0,esk9_0),u1_struct_0(esk7_0))
    | ~ r1_waybel_0(esk6_0,esk7_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_18])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(k2_waybel_0(esk6_0,esk7_0,esk2_4(esk6_0,esk7_0,X1,esk1_3(esk6_0,esk7_0,esk8_0))),esk9_0)
    | m1_subset_1(esk4_3(esk6_0,esk7_0,esk9_0),u1_struct_0(esk7_0))
    | r1_waybel_0(esk6_0,esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_43,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(k2_waybel_0(esk6_0,esk7_0,esk2_4(esk6_0,esk7_0,esk9_0,esk1_3(esk6_0,esk7_0,esk8_0))),esk9_0)
    | m1_subset_1(esk4_3(esk6_0,esk7_0,esk9_0),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( ~ v1_xboole_0(esk9_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_31])).

cnf(c_0_46,negated_conjecture,
    ( v1_xboole_0(esk9_0)
    | r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk2_4(esk6_0,esk7_0,esk9_0,esk1_3(esk6_0,esk7_0,esk8_0))),esk9_0)
    | m1_subset_1(esk4_3(esk6_0,esk7_0,esk9_0),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk2_4(esk6_0,esk7_0,esk9_0,esk1_3(esk6_0,esk7_0,esk8_0))),esk9_0)
    | m1_subset_1(esk4_3(esk6_0,esk7_0,esk9_0),u1_struct_0(esk7_0))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_48,plain,
    ( r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(k2_waybel_0(X1,X2,esk2_4(X1,X2,X3,X4)),X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk2_4(esk6_0,esk7_0,esk9_0,esk1_3(esk6_0,esk7_0,esk8_0))),esk9_0)
    | m1_subset_1(esk4_3(esk6_0,esk7_0,esk9_0),u1_struct_0(esk7_0))
    | r1_waybel_0(esk6_0,esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_37])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk4_3(esk6_0,esk7_0,esk9_0),u1_struct_0(esk7_0))
    | r1_waybel_0(esk6_0,esk7_0,X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_12]),c_0_13])]),c_0_14]),c_0_15]),c_0_23]),c_0_40])).

cnf(c_0_51,plain,
    ( r2_hidden(k2_waybel_0(X1,X2,esk3_4(X1,X2,X3,X4)),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_waybel_0(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk4_3(esk6_0,esk7_0,esk9_0),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(k2_waybel_0(X1,esk7_0,esk3_4(X1,esk7_0,X2,esk4_3(esk6_0,esk7_0,esk9_0))),X2)
    | v2_struct_0(X1)
    | ~ r2_waybel_0(X1,esk7_0,X2)
    | ~ l1_waybel_0(esk7_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_14])).

cnf(c_0_54,negated_conjecture,
    ( r2_waybel_0(esk6_0,esk7_0,esk8_0)
    | r1_waybel_0(esk6_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk3_4(esk6_0,esk7_0,esk8_0,esk4_3(esk6_0,esk7_0,esk9_0))),esk8_0)
    | r1_waybel_0(esk6_0,esk7_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_12]),c_0_13])]),c_0_15])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(k2_waybel_0(esk6_0,esk7_0,esk3_4(esk6_0,esk7_0,esk8_0,esk4_3(esk6_0,esk7_0,esk9_0))),esk9_0)
    | r1_waybel_0(esk6_0,esk7_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_55])).

cnf(c_0_57,plain,
    ( r1_orders_2(X1,X2,esk3_4(X3,X1,X4,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_waybel_0(X3,X1,X4)
    | ~ l1_waybel_0(X1,X3)
    | ~ l1_struct_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_58,plain,
    ( m1_subset_1(esk3_4(X1,X2,X3,X4),u1_struct_0(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_waybel_0(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(k2_waybel_0(esk6_0,esk7_0,esk3_4(esk6_0,esk7_0,esk8_0,esk4_3(esk6_0,esk7_0,esk9_0))),esk9_0)
    | m1_subset_1(esk1_3(esk6_0,esk7_0,esk8_0),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_56]),c_0_12]),c_0_13])]),c_0_14]),c_0_15])).

cnf(c_0_60,negated_conjecture,
    ( r1_orders_2(esk7_0,esk4_3(esk6_0,esk7_0,esk9_0),esk3_4(X1,esk7_0,X2,esk4_3(esk6_0,esk7_0,esk9_0)))
    | v2_struct_0(X1)
    | ~ r2_waybel_0(X1,esk7_0,X2)
    | ~ l1_waybel_0(esk7_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_52]),c_0_14])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(esk3_4(X1,esk7_0,X2,esk4_3(esk6_0,esk7_0,esk9_0)),u1_struct_0(esk7_0))
    | v2_struct_0(X1)
    | ~ r2_waybel_0(X1,esk7_0,X2)
    | ~ l1_waybel_0(esk7_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_52]),c_0_14])).

cnf(c_0_62,negated_conjecture,
    ( v1_xboole_0(esk9_0)
    | r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk3_4(esk6_0,esk7_0,esk8_0,esk4_3(esk6_0,esk7_0,esk9_0))),esk9_0)
    | m1_subset_1(esk1_3(esk6_0,esk7_0,esk8_0),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_59])).

cnf(c_0_63,plain,
    ( r2_waybel_0(X3,X2,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,esk4_3(X3,X2,X4),X1)
    | ~ r2_hidden(k2_waybel_0(X3,X2,X1),X4)
    | ~ l1_waybel_0(X2,X3)
    | ~ l1_struct_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_64,negated_conjecture,
    ( r1_orders_2(esk7_0,esk4_3(esk6_0,esk7_0,esk9_0),esk3_4(esk6_0,esk7_0,esk8_0,esk4_3(esk6_0,esk7_0,esk9_0)))
    | r1_waybel_0(esk6_0,esk7_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_54]),c_0_12]),c_0_13])]),c_0_15])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(esk3_4(esk6_0,esk7_0,esk8_0,esk4_3(esk6_0,esk7_0,esk9_0)),u1_struct_0(esk7_0))
    | r1_waybel_0(esk6_0,esk7_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_54]),c_0_12]),c_0_13])]),c_0_15])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk3_4(esk6_0,esk7_0,esk8_0,esk4_3(esk6_0,esk7_0,esk9_0))),esk9_0)
    | m1_subset_1(esk1_3(esk6_0,esk7_0,esk8_0),u1_struct_0(esk7_0))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( r1_waybel_0(esk6_0,esk7_0,esk8_0)
    | ~ r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk3_4(esk6_0,esk7_0,esk8_0,esk4_3(esk6_0,esk7_0,esk9_0))),esk9_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_12]),c_0_13])]),c_0_15]),c_0_14]),c_0_65]),c_0_17])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk2_4(X1,esk7_0,X2,esk4_3(esk6_0,esk7_0,esk9_0)),u1_struct_0(esk7_0))
    | r1_waybel_0(X1,esk7_0,X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(esk7_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_52]),c_0_14])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(esk1_3(esk6_0,esk7_0,esk8_0),u1_struct_0(esk7_0))
    | r1_waybel_0(esk6_0,esk7_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_55]),c_0_67])).

cnf(c_0_70,negated_conjecture,
    ( r2_waybel_0(esk6_0,esk7_0,esk8_0)
    | ~ r1_waybel_0(esk6_0,esk7_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(esk2_4(esk6_0,esk7_0,X1,esk4_3(esk6_0,esk7_0,esk9_0)),u1_struct_0(esk7_0))
    | r1_waybel_0(esk6_0,esk7_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_12]),c_0_13])]),c_0_15])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(esk1_3(esk6_0,esk7_0,esk8_0),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_69]),c_0_12]),c_0_13])]),c_0_14]),c_0_15])).

cnf(c_0_73,negated_conjecture,
    ( r2_waybel_0(esk6_0,esk7_0,esk8_0)
    | m1_subset_1(esk2_4(esk6_0,esk7_0,esk9_0,esk4_3(esk6_0,esk7_0,esk9_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( r1_orders_2(esk7_0,esk1_3(esk6_0,esk7_0,esk8_0),esk2_4(X1,esk7_0,X2,esk1_3(esk6_0,esk7_0,esk8_0)))
    | r1_waybel_0(X1,esk7_0,X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(esk7_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_72]),c_0_14])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(esk2_4(X1,esk7_0,X2,esk1_3(esk6_0,esk7_0,esk8_0)),u1_struct_0(esk7_0))
    | r1_waybel_0(X1,esk7_0,X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(esk7_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_72]),c_0_14])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk3_4(esk6_0,esk7_0,esk8_0,esk4_3(esk6_0,esk7_0,esk9_0))),esk8_0)
    | m1_subset_1(esk2_4(esk6_0,esk7_0,esk9_0,esk4_3(esk6_0,esk7_0,esk9_0)),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_73]),c_0_12]),c_0_13])]),c_0_15])).

cnf(c_0_77,negated_conjecture,
    ( r1_orders_2(esk7_0,esk1_3(esk6_0,esk7_0,esk8_0),esk2_4(esk6_0,esk7_0,X1,esk1_3(esk6_0,esk7_0,esk8_0)))
    | r1_waybel_0(esk6_0,esk7_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_12]),c_0_13])]),c_0_15])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(esk2_4(esk6_0,esk7_0,X1,esk1_3(esk6_0,esk7_0,esk8_0)),u1_struct_0(esk7_0))
    | r1_waybel_0(esk6_0,esk7_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_12]),c_0_13])]),c_0_15])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(k2_waybel_0(esk6_0,esk7_0,esk3_4(esk6_0,esk7_0,esk8_0,esk4_3(esk6_0,esk7_0,esk9_0))),esk9_0)
    | m1_subset_1(esk2_4(esk6_0,esk7_0,esk9_0,esk4_3(esk6_0,esk7_0,esk9_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_76])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk2_4(esk6_0,esk7_0,X1,esk1_3(esk6_0,esk7_0,esk8_0))),esk8_0)
    | r1_waybel_0(esk6_0,esk7_0,X1)
    | ~ r1_waybel_0(esk6_0,esk7_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_77]),c_0_12]),c_0_13])]),c_0_15]),c_0_14]),c_0_78])).

cnf(c_0_81,negated_conjecture,
    ( v1_xboole_0(esk9_0)
    | r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk3_4(esk6_0,esk7_0,esk8_0,esk4_3(esk6_0,esk7_0,esk9_0))),esk9_0)
    | m1_subset_1(esk2_4(esk6_0,esk7_0,esk9_0,esk4_3(esk6_0,esk7_0,esk9_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_79])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(k2_waybel_0(X1,esk7_0,esk3_4(X1,esk7_0,X2,esk1_3(esk6_0,esk7_0,esk8_0))),X2)
    | v2_struct_0(X1)
    | ~ r2_waybel_0(X1,esk7_0,X2)
    | ~ l1_waybel_0(esk7_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_72]),c_0_14])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk2_4(esk6_0,esk7_0,X1,esk1_3(esk6_0,esk7_0,esk8_0))),esk8_0)
    | m1_subset_1(k2_waybel_0(esk6_0,esk7_0,esk3_4(esk6_0,esk7_0,esk8_0,esk4_3(esk6_0,esk7_0,esk9_0))),esk9_0)
    | r1_waybel_0(esk6_0,esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_56])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk3_4(esk6_0,esk7_0,esk8_0,esk4_3(esk6_0,esk7_0,esk9_0))),esk9_0)
    | m1_subset_1(esk2_4(esk6_0,esk7_0,esk9_0,esk4_3(esk6_0,esk7_0,esk9_0)),u1_struct_0(esk7_0))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_81])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk3_4(esk6_0,esk7_0,esk8_0,esk1_3(esk6_0,esk7_0,esk8_0))),esk8_0)
    | m1_subset_1(esk2_4(esk6_0,esk7_0,esk9_0,esk4_3(esk6_0,esk7_0,esk9_0)),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_73]),c_0_12]),c_0_13])]),c_0_15])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk2_4(esk6_0,esk7_0,X1,esk1_3(esk6_0,esk7_0,esk8_0))),esk8_0)
    | m1_subset_1(esk3_4(esk6_0,esk7_0,esk8_0,esk4_3(esk6_0,esk7_0,esk9_0)),u1_struct_0(esk7_0))
    | r1_waybel_0(esk6_0,esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_65])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(k2_waybel_0(esk6_0,esk7_0,esk3_4(esk6_0,esk7_0,esk8_0,esk4_3(esk6_0,esk7_0,esk9_0))),esk9_0)
    | m1_subset_1(k2_waybel_0(esk6_0,esk7_0,esk2_4(esk6_0,esk7_0,X1,esk1_3(esk6_0,esk7_0,esk8_0))),esk9_0)
    | r1_waybel_0(esk6_0,esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_83])).

cnf(c_0_88,negated_conjecture,
    ( r1_orders_2(esk7_0,esk4_3(esk6_0,esk7_0,esk9_0),esk3_4(esk6_0,esk7_0,esk8_0,esk4_3(esk6_0,esk7_0,esk9_0)))
    | m1_subset_1(esk2_4(esk6_0,esk7_0,esk9_0,esk4_3(esk6_0,esk7_0,esk9_0)),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_73]),c_0_12]),c_0_13])]),c_0_15])).

cnf(c_0_89,negated_conjecture,
    ( m1_subset_1(esk2_4(esk6_0,esk7_0,esk9_0,esk4_3(esk6_0,esk7_0,esk9_0)),u1_struct_0(esk7_0))
    | m1_subset_1(esk3_4(esk6_0,esk7_0,esk8_0,esk4_3(esk6_0,esk7_0,esk9_0)),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_73]),c_0_12]),c_0_13])]),c_0_15])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk3_4(esk6_0,esk7_0,esk8_0,esk4_3(esk6_0,esk7_0,esk9_0))),esk9_0)
    | m1_subset_1(esk2_4(esk6_0,esk7_0,esk9_0,esk4_3(esk6_0,esk7_0,esk9_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_91,negated_conjecture,
    ( m1_subset_1(k2_waybel_0(esk6_0,esk7_0,esk2_4(esk6_0,esk7_0,X1,esk1_3(esk6_0,esk7_0,esk8_0))),esk9_0)
    | m1_subset_1(esk3_4(esk6_0,esk7_0,esk8_0,esk4_3(esk6_0,esk7_0,esk9_0)),u1_struct_0(esk7_0))
    | r1_waybel_0(esk6_0,esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_86])).

cnf(c_0_92,negated_conjecture,
    ( r2_waybel_0(esk6_0,esk7_0,esk8_0)
    | m1_subset_1(k2_waybel_0(esk6_0,esk7_0,esk2_4(esk6_0,esk7_0,esk9_0,esk1_3(esk6_0,esk7_0,esk8_0))),esk9_0)
    | m1_subset_1(k2_waybel_0(esk6_0,esk7_0,esk3_4(esk6_0,esk7_0,esk8_0,esk4_3(esk6_0,esk7_0,esk9_0))),esk9_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_87])).

cnf(c_0_93,negated_conjecture,
    ( r2_waybel_0(esk6_0,esk7_0,esk9_0)
    | m1_subset_1(esk2_4(esk6_0,esk7_0,esk9_0,esk4_3(esk6_0,esk7_0,esk9_0)),u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_88]),c_0_12]),c_0_13])]),c_0_15]),c_0_14]),c_0_89]),c_0_90])).

cnf(c_0_94,negated_conjecture,
    ( r2_waybel_0(esk6_0,esk7_0,esk8_0)
    | m1_subset_1(k2_waybel_0(esk6_0,esk7_0,esk2_4(esk6_0,esk7_0,esk9_0,esk1_3(esk6_0,esk7_0,esk8_0))),esk9_0)
    | m1_subset_1(esk3_4(esk6_0,esk7_0,esk8_0,esk4_3(esk6_0,esk7_0,esk9_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_91])).

cnf(c_0_95,negated_conjecture,
    ( m1_subset_1(k2_waybel_0(esk6_0,esk7_0,esk3_4(esk6_0,esk7_0,esk8_0,esk4_3(esk6_0,esk7_0,esk9_0))),esk9_0)
    | m1_subset_1(k2_waybel_0(esk6_0,esk7_0,esk2_4(esk6_0,esk7_0,esk9_0,esk1_3(esk6_0,esk7_0,esk8_0))),esk9_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_92]),c_0_12]),c_0_13])]),c_0_15]),c_0_36])).

cnf(c_0_96,negated_conjecture,
    ( m1_subset_1(esk2_4(esk6_0,esk7_0,esk9_0,esk4_3(esk6_0,esk7_0,esk9_0)),u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_93]),c_0_71])).

cnf(c_0_97,negated_conjecture,
    ( m1_subset_1(k2_waybel_0(esk6_0,esk7_0,esk2_4(esk6_0,esk7_0,esk9_0,esk1_3(esk6_0,esk7_0,esk8_0))),esk9_0)
    | m1_subset_1(esk3_4(esk6_0,esk7_0,esk8_0,esk4_3(esk6_0,esk7_0,esk9_0)),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_94]),c_0_12]),c_0_13])]),c_0_15])).

cnf(c_0_98,negated_conjecture,
    ( v1_xboole_0(esk9_0)
    | r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk3_4(esk6_0,esk7_0,esk8_0,esk4_3(esk6_0,esk7_0,esk9_0))),esk9_0)
    | m1_subset_1(k2_waybel_0(esk6_0,esk7_0,esk2_4(esk6_0,esk7_0,esk9_0,esk1_3(esk6_0,esk7_0,esk8_0))),esk9_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_95])).

cnf(c_0_99,negated_conjecture,
    ( r2_hidden(k2_waybel_0(X1,esk7_0,esk3_4(X1,esk7_0,X2,esk2_4(esk6_0,esk7_0,esk9_0,esk4_3(esk6_0,esk7_0,esk9_0)))),X2)
    | v2_struct_0(X1)
    | ~ r2_waybel_0(X1,esk7_0,X2)
    | ~ l1_waybel_0(esk7_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_96]),c_0_14])).

cnf(c_0_100,negated_conjecture,
    ( v1_xboole_0(esk9_0)
    | r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk2_4(esk6_0,esk7_0,esk9_0,esk1_3(esk6_0,esk7_0,esk8_0))),esk9_0)
    | m1_subset_1(esk3_4(esk6_0,esk7_0,esk8_0,esk4_3(esk6_0,esk7_0,esk9_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_97])).

cnf(c_0_101,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk3_4(esk6_0,esk7_0,esk8_0,esk4_3(esk6_0,esk7_0,esk9_0))),esk9_0)
    | m1_subset_1(k2_waybel_0(esk6_0,esk7_0,esk2_4(esk6_0,esk7_0,esk9_0,esk1_3(esk6_0,esk7_0,esk8_0))),esk9_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_98])).

cnf(c_0_102,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk3_4(esk6_0,esk7_0,esk8_0,esk2_4(esk6_0,esk7_0,esk9_0,esk4_3(esk6_0,esk7_0,esk9_0)))),esk8_0)
    | r1_waybel_0(esk6_0,esk7_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_54]),c_0_12]),c_0_13])]),c_0_15])).

cnf(c_0_103,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk2_4(esk6_0,esk7_0,esk9_0,esk1_3(esk6_0,esk7_0,esk8_0))),esk9_0)
    | m1_subset_1(esk3_4(esk6_0,esk7_0,esk8_0,esk4_3(esk6_0,esk7_0,esk9_0)),u1_struct_0(esk7_0))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_100])).

cnf(c_0_104,negated_conjecture,
    ( m1_subset_1(k2_waybel_0(esk6_0,esk7_0,esk2_4(esk6_0,esk7_0,esk9_0,esk1_3(esk6_0,esk7_0,esk8_0))),esk9_0)
    | r1_waybel_0(esk6_0,esk7_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_67])).

cnf(c_0_105,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk2_4(esk6_0,esk7_0,esk9_0,esk1_3(esk6_0,esk7_0,esk8_0))),esk9_0)
    | m1_subset_1(esk3_4(esk6_0,esk7_0,esk8_0,esk4_3(esk6_0,esk7_0,esk9_0)),u1_struct_0(esk7_0))
    | r1_waybel_0(esk6_0,esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_103,c_0_86])).

fof(c_0_106,plain,(
    ! [X22] : m1_subset_1(esk5_1(X22),X22) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_107,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk2_4(esk6_0,esk7_0,X1,esk1_3(esk6_0,esk7_0,esk8_0))),esk8_0)
    | m1_subset_1(k2_waybel_0(esk6_0,esk7_0,esk2_4(esk6_0,esk7_0,esk9_0,esk1_3(esk6_0,esk7_0,esk8_0))),esk9_0)
    | r1_waybel_0(esk6_0,esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_104])).

cnf(c_0_108,negated_conjecture,
    ( m1_subset_1(esk3_4(esk6_0,esk7_0,esk8_0,esk4_3(esk6_0,esk7_0,esk9_0)),u1_struct_0(esk7_0))
    | r1_waybel_0(esk6_0,esk7_0,esk9_0)
    | r1_waybel_0(esk6_0,esk7_0,X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_105]),c_0_72]),c_0_12]),c_0_13])]),c_0_14]),c_0_15])).

cnf(c_0_109,plain,
    ( m1_subset_1(esk5_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_106])).

cnf(c_0_110,negated_conjecture,
    ( m1_subset_1(k2_waybel_0(esk6_0,esk7_0,esk2_4(esk6_0,esk7_0,esk9_0,esk1_3(esk6_0,esk7_0,esk8_0))),esk9_0)
    | m1_subset_1(k2_waybel_0(esk6_0,esk7_0,esk2_4(esk6_0,esk7_0,X1,esk1_3(esk6_0,esk7_0,esk8_0))),esk9_0)
    | r1_waybel_0(esk6_0,esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_107])).

cnf(c_0_111,negated_conjecture,
    ( m1_subset_1(esk3_4(esk6_0,esk7_0,esk8_0,esk4_3(esk6_0,esk7_0,esk9_0)),u1_struct_0(esk7_0))
    | r1_waybel_0(esk6_0,esk7_0,esk9_0) ),
    inference(ef,[status(thm)],[c_0_108])).

cnf(c_0_112,plain,
    ( r2_hidden(k2_waybel_0(X1,X2,esk3_4(X1,X2,X3,esk5_1(u1_struct_0(X2)))),X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r2_waybel_0(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_109])).

cnf(c_0_113,negated_conjecture,
    ( r2_waybel_0(esk6_0,esk7_0,esk8_0)
    | m1_subset_1(k2_waybel_0(esk6_0,esk7_0,esk2_4(esk6_0,esk7_0,esk9_0,esk1_3(esk6_0,esk7_0,esk8_0))),esk9_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_110])).

cnf(c_0_114,negated_conjecture,
    ( r2_waybel_0(esk6_0,esk7_0,esk8_0)
    | m1_subset_1(esk3_4(esk6_0,esk7_0,esk8_0,esk4_3(esk6_0,esk7_0,esk9_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_111])).

cnf(c_0_115,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk3_4(esk6_0,esk7_0,esk8_0,esk5_1(u1_struct_0(esk7_0)))),esk8_0)
    | m1_subset_1(k2_waybel_0(esk6_0,esk7_0,esk2_4(esk6_0,esk7_0,esk9_0,esk1_3(esk6_0,esk7_0,esk8_0))),esk9_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_12]),c_0_13])]),c_0_15]),c_0_14])).

cnf(c_0_116,negated_conjecture,
    ( r1_orders_2(esk7_0,esk4_3(esk6_0,esk7_0,esk9_0),esk3_4(esk6_0,esk7_0,esk8_0,esk4_3(esk6_0,esk7_0,esk9_0)))
    | m1_subset_1(k2_waybel_0(esk6_0,esk7_0,esk2_4(esk6_0,esk7_0,esk9_0,esk1_3(esk6_0,esk7_0,esk8_0))),esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_113]),c_0_12]),c_0_13])]),c_0_15])).

cnf(c_0_117,negated_conjecture,
    ( m1_subset_1(esk3_4(esk6_0,esk7_0,esk8_0,esk4_3(esk6_0,esk7_0,esk9_0)),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_114]),c_0_12]),c_0_13])]),c_0_15])).

cnf(c_0_118,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk3_4(esk6_0,esk7_0,esk8_0,esk4_3(esk6_0,esk7_0,esk9_0))),esk9_0)
    | m1_subset_1(k2_waybel_0(esk6_0,esk7_0,esk2_4(esk6_0,esk7_0,esk9_0,esk1_3(esk6_0,esk7_0,esk8_0))),esk9_0) ),
    inference(spm,[status(thm)],[c_0_101,c_0_115])).

cnf(c_0_119,negated_conjecture,
    ( r2_waybel_0(esk6_0,esk7_0,esk9_0)
    | m1_subset_1(k2_waybel_0(esk6_0,esk7_0,esk2_4(esk6_0,esk7_0,esk9_0,esk1_3(esk6_0,esk7_0,esk8_0))),esk9_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_116]),c_0_117]),c_0_12]),c_0_13])]),c_0_15]),c_0_14]),c_0_118])).

cnf(c_0_120,negated_conjecture,
    ( m1_subset_1(k2_waybel_0(esk6_0,esk7_0,esk2_4(esk6_0,esk7_0,esk9_0,esk1_3(esk6_0,esk7_0,esk8_0))),esk9_0)
    | ~ r1_waybel_0(esk6_0,esk7_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_119])).

cnf(c_0_121,negated_conjecture,
    ( m1_subset_1(k2_waybel_0(esk6_0,esk7_0,esk2_4(esk6_0,esk7_0,esk9_0,esk1_3(esk6_0,esk7_0,esk8_0))),esk9_0) ),
    inference(spm,[status(thm)],[c_0_120,c_0_110])).

cnf(c_0_122,negated_conjecture,
    ( v1_xboole_0(esk9_0)
    | r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk2_4(esk6_0,esk7_0,esk9_0,esk1_3(esk6_0,esk7_0,esk8_0))),esk9_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_121])).

cnf(c_0_123,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk2_4(esk6_0,esk7_0,esk9_0,esk1_3(esk6_0,esk7_0,esk8_0))),esk9_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_122])).

cnf(c_0_124,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk2_4(esk6_0,esk7_0,esk9_0,esk1_3(esk6_0,esk7_0,esk8_0))),esk9_0)
    | m1_subset_1(k2_waybel_0(esk6_0,esk7_0,esk3_4(esk6_0,esk7_0,esk8_0,esk4_3(esk6_0,esk7_0,esk9_0))),esk9_0)
    | r1_waybel_0(esk6_0,esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_123,c_0_83])).

cnf(c_0_125,negated_conjecture,
    ( m1_subset_1(k2_waybel_0(esk6_0,esk7_0,esk3_4(esk6_0,esk7_0,esk8_0,esk4_3(esk6_0,esk7_0,esk9_0))),esk9_0)
    | r1_waybel_0(esk6_0,esk7_0,esk9_0)
    | r1_waybel_0(esk6_0,esk7_0,X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_124]),c_0_72]),c_0_12]),c_0_13])]),c_0_14]),c_0_15])).

cnf(c_0_126,negated_conjecture,
    ( m1_subset_1(k2_waybel_0(esk6_0,esk7_0,esk3_4(esk6_0,esk7_0,esk8_0,esk4_3(esk6_0,esk7_0,esk9_0))),esk9_0)
    | r1_waybel_0(esk6_0,esk7_0,esk9_0) ),
    inference(ef,[status(thm)],[c_0_125])).

cnf(c_0_127,negated_conjecture,
    ( r2_waybel_0(esk6_0,esk7_0,esk8_0)
    | m1_subset_1(k2_waybel_0(esk6_0,esk7_0,esk3_4(esk6_0,esk7_0,esk8_0,esk4_3(esk6_0,esk7_0,esk9_0))),esk9_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_126])).

cnf(c_0_128,negated_conjecture,
    ( m1_subset_1(k2_waybel_0(esk6_0,esk7_0,esk3_4(esk6_0,esk7_0,esk8_0,esk4_3(esk6_0,esk7_0,esk9_0))),esk9_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_127]),c_0_12]),c_0_13])]),c_0_15]),c_0_36])).

cnf(c_0_129,negated_conjecture,
    ( v1_xboole_0(esk9_0)
    | r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk3_4(esk6_0,esk7_0,esk8_0,esk4_3(esk6_0,esk7_0,esk9_0))),esk9_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_128])).

cnf(c_0_130,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk3_4(esk6_0,esk7_0,esk8_0,esk4_3(esk6_0,esk7_0,esk9_0))),esk9_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_129])).

cnf(c_0_131,negated_conjecture,
    ( r1_waybel_0(esk6_0,esk7_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_102]),c_0_67])).

cnf(c_0_132,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk2_4(esk6_0,esk7_0,X1,esk1_3(esk6_0,esk7_0,esk8_0))),esk8_0)
    | r1_waybel_0(esk6_0,esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_131])])).

cnf(c_0_133,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk2_4(esk6_0,esk7_0,esk9_0,esk1_3(esk6_0,esk7_0,esk8_0))),esk9_0)
    | r1_waybel_0(esk6_0,esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_123,c_0_132])).

cnf(c_0_134,negated_conjecture,
    ( r1_waybel_0(esk6_0,esk7_0,esk9_0)
    | r1_waybel_0(esk6_0,esk7_0,X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_133]),c_0_72]),c_0_12]),c_0_13])]),c_0_14]),c_0_15])).

cnf(c_0_135,negated_conjecture,
    ( r1_waybel_0(esk6_0,esk7_0,esk9_0) ),
    inference(ef,[status(thm)],[c_0_134])).

cnf(c_0_136,negated_conjecture,
    ( r2_waybel_0(esk6_0,esk7_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_135])])).

cnf(c_0_137,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk3_4(esk6_0,esk7_0,esk8_0,esk5_1(u1_struct_0(esk7_0)))),esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_136]),c_0_12]),c_0_13])]),c_0_15]),c_0_14])).

cnf(c_0_138,negated_conjecture,
    ( r1_orders_2(esk7_0,esk4_3(esk6_0,esk7_0,esk9_0),esk3_4(esk6_0,esk7_0,esk8_0,esk4_3(esk6_0,esk7_0,esk9_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_136]),c_0_12]),c_0_13])]),c_0_15])).

cnf(c_0_139,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk3_4(esk6_0,esk7_0,esk8_0,esk4_3(esk6_0,esk7_0,esk9_0))),esk9_0) ),
    inference(spm,[status(thm)],[c_0_130,c_0_137])).

cnf(c_0_140,negated_conjecture,
    ( ~ r2_waybel_0(esk6_0,esk7_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_135])])).

cnf(c_0_141,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_138]),c_0_139]),c_0_117]),c_0_12]),c_0_13])]),c_0_140]),c_0_15]),c_0_14]),
    [proof]).

%------------------------------------------------------------------------------
