%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1656+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:32 EST 2020

% Result     : Theorem 0.98s
% Output     : CNFRefutation 0.98s
% Verified   : 
% Statistics : Number of formulae       :   99 (32867 expanded)
%              Number of clauses        :   82 (12175 expanded)
%              Number of leaves         :    8 (7887 expanded)
%              Depth                    :   32
%              Number of atoms          :  409 (229471 expanded)
%              Number of equality atoms :   14 (4719 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   61 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t36_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_lattice3(X1,X2,X3)
              <=> r1_lattice3(X1,k4_waybel_0(X1,X2),X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_waybel_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_waybel_0)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(dt_k4_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k4_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_waybel_0)).

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

fof(reflexivity_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => r3_orders_2(X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

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

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r1_lattice3(X1,X2,X3)
                <=> r1_lattice3(X1,k4_waybel_0(X1,X2),X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t36_waybel_0])).

fof(c_0_9,plain,(
    ! [X15,X16,X17,X18] :
      ( ( ~ r1_lattice3(X15,X16,X17)
        | ~ m1_subset_1(X18,u1_struct_0(X15))
        | ~ r2_hidden(X18,X16)
        | r1_orders_2(X15,X17,X18)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ l1_orders_2(X15) )
      & ( m1_subset_1(esk4_3(X15,X16,X17),u1_struct_0(X15))
        | r1_lattice3(X15,X16,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ l1_orders_2(X15) )
      & ( r2_hidden(esk4_3(X15,X16,X17),X16)
        | r1_lattice3(X15,X16,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ l1_orders_2(X15) )
      & ( ~ r1_orders_2(X15,X17,esk4_3(X15,X16,X17))
        | r1_lattice3(X15,X16,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ l1_orders_2(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).

fof(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v3_orders_2(esk5_0)
    & v4_orders_2(esk5_0)
    & l1_orders_2(esk5_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    & m1_subset_1(esk7_0,u1_struct_0(esk5_0))
    & ( ~ r1_lattice3(esk5_0,esk6_0,esk7_0)
      | ~ r1_lattice3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0) )
    & ( r1_lattice3(esk5_0,esk6_0,esk7_0)
      | r1_lattice3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

cnf(c_0_11,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
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

fof(c_0_15,plain,(
    ! [X32,X33,X34] :
      ( ~ r2_hidden(X32,X33)
      | ~ m1_subset_1(X33,k1_zfmisc_1(X34))
      | m1_subset_1(X32,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_16,plain,(
    ! [X20,X21] :
      ( ~ l1_orders_2(X20)
      | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
      | m1_subset_1(k4_waybel_0(X20,X21),k1_zfmisc_1(u1_struct_0(X20))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_waybel_0])])).

cnf(c_0_17,negated_conjecture,
    ( ~ r1_lattice3(esk5_0,esk6_0,esk7_0)
    | ~ r1_lattice3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( r1_lattice3(esk5_0,X1,esk7_0)
    | m1_subset_1(esk4_3(esk5_0,X1,esk7_0),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])])).

cnf(c_0_19,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X2)
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,plain,
    ( m1_subset_1(esk1_4(X1,X2,X3,X4),u1_struct_0(X1))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | X3 != k4_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( m1_subset_1(k4_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ r1_lattice3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( r1_lattice3(esk5_0,X1,esk7_0)
    | r2_hidden(esk4_3(esk5_0,X1,esk7_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_12]),c_0_13])])).

cnf(c_0_25,plain,
    ( m1_subset_1(esk1_4(X1,X2,k4_waybel_0(X1,X2),X3),u1_struct_0(X1))
    | ~ r2_hidden(X3,k4_waybel_0(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_20,c_0_21])]),c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0),k4_waybel_0(esk5_0,esk6_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_28,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | X3 != k4_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_29,plain,
    ( r1_orders_2(X1,X3,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk1_4(esk5_0,esk6_0,k4_waybel_0(esk5_0,esk6_0),esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0)),u1_struct_0(esk5_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_13])])).

cnf(c_0_31,plain,
    ( r2_hidden(esk1_4(X1,X2,k4_waybel_0(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k4_waybel_0(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_28,c_0_21])]),c_0_22])).

fof(c_0_32,plain,(
    ! [X28,X29,X30,X31] :
      ( ~ v4_orders_2(X28)
      | ~ l1_orders_2(X28)
      | ~ m1_subset_1(X29,u1_struct_0(X28))
      | ~ m1_subset_1(X30,u1_struct_0(X28))
      | ~ m1_subset_1(X31,u1_struct_0(X28))
      | ~ r1_orders_2(X28,X29,X30)
      | ~ r1_orders_2(X28,X30,X31)
      | r1_orders_2(X28,X29,X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_orders_2])])])).

cnf(c_0_33,negated_conjecture,
    ( r1_orders_2(esk5_0,X1,esk1_4(esk5_0,esk6_0,k4_waybel_0(esk5_0,esk6_0),esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0)))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ r1_lattice3(esk5_0,X2,X1)
    | ~ r2_hidden(esk1_4(esk5_0,esk6_0,k4_waybel_0(esk5_0,esk6_0),esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0)),X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_13])])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk1_4(esk5_0,esk6_0,k4_waybel_0(esk5_0,esk6_0),X1),esk6_0)
    | ~ r2_hidden(X1,k4_waybel_0(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_27]),c_0_13])])).

cnf(c_0_35,plain,
    ( r1_orders_2(X1,esk1_4(X1,X2,X3,X4),X4)
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | X3 != k4_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_36,plain,
    ( r1_orders_2(X1,X2,X4)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0),u1_struct_0(esk5_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_18])).

cnf(c_0_38,negated_conjecture,
    ( v4_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_39,negated_conjecture,
    ( r1_orders_2(esk5_0,esk7_0,esk1_4(esk5_0,esk6_0,k4_waybel_0(esk5_0,esk6_0),esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0)))
    | r2_hidden(esk4_3(esk5_0,X1,esk7_0),X1)
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ r2_hidden(esk1_4(esk5_0,esk6_0,k4_waybel_0(esk5_0,esk6_0),esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_24]),c_0_12])])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk1_4(esk5_0,esk6_0,k4_waybel_0(esk5_0,esk6_0),esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0)),esk6_0)
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_26])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_27])).

cnf(c_0_42,plain,
    ( r1_orders_2(X1,esk1_4(X1,X2,k4_waybel_0(X1,X2),X3),X3)
    | ~ r2_hidden(X3,k4_waybel_0(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_35,c_0_21])]),c_0_22])).

cnf(c_0_43,plain,
    ( r1_lattice3(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,esk4_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_44,negated_conjecture,
    ( r1_orders_2(esk5_0,X1,esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ r1_orders_2(esk5_0,X2,esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0))
    | ~ r1_orders_2(esk5_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_13])])).

cnf(c_0_45,negated_conjecture,
    ( r1_orders_2(esk5_0,esk7_0,esk1_4(esk5_0,esk6_0,k4_waybel_0(esk5_0,esk6_0),esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0)))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( r1_orders_2(esk5_0,esk1_4(esk5_0,esk6_0,k4_waybel_0(esk5_0,esk6_0),esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0)),esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_26]),c_0_27]),c_0_13])])).

fof(c_0_47,plain,(
    ! [X25,X26,X27] :
      ( v2_struct_0(X25)
      | ~ v3_orders_2(X25)
      | ~ l1_orders_2(X25)
      | ~ m1_subset_1(X26,u1_struct_0(X25))
      | ~ m1_subset_1(X27,u1_struct_0(X25))
      | r3_orders_2(X25,X26,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).

cnf(c_0_48,plain,
    ( r2_hidden(X3,X5)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,X1,X3)
    | ~ r2_hidden(X1,X4)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | X5 != k4_waybel_0(X2,X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_49,negated_conjecture,
    ( r1_lattice3(esk5_0,X1,esk7_0)
    | ~ r1_orders_2(esk5_0,esk7_0,esk4_3(esk5_0,X1,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_12]),c_0_13])])).

cnf(c_0_50,negated_conjecture,
    ( r1_orders_2(esk5_0,esk7_0,esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_12])]),c_0_30]),c_0_46])).

fof(c_0_51,plain,(
    ! [X22,X23,X24] :
      ( ( ~ r3_orders_2(X22,X23,X24)
        | r1_orders_2(X22,X23,X24)
        | v2_struct_0(X22)
        | ~ v3_orders_2(X22)
        | ~ l1_orders_2(X22)
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | ~ m1_subset_1(X24,u1_struct_0(X22)) )
      & ( ~ r1_orders_2(X22,X23,X24)
        | r3_orders_2(X22,X23,X24)
        | v2_struct_0(X22)
        | ~ v3_orders_2(X22)
        | ~ l1_orders_2(X22)
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | ~ m1_subset_1(X24,u1_struct_0(X22)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_52,plain,
    ( v2_struct_0(X1)
    | r3_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( v3_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_54,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,k4_waybel_0(X2,X3))
    | ~ r1_orders_2(X2,X4,X1)
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_48,c_0_21])]),c_0_22])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_23])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk4_3(esk5_0,esk6_0,esk7_0),esk6_0)
    | ~ r1_lattice3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_24])).

cnf(c_0_58,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( r3_orders_2(esk5_0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_12]),c_0_53]),c_0_13])]),c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk4_3(esk5_0,esk6_0,esk7_0),k4_waybel_0(esk5_0,X1))
    | ~ r1_orders_2(esk5_0,X2,esk4_3(esk5_0,esk6_0,esk7_0))
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_13])])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0),k4_waybel_0(esk5_0,esk6_0))
    | r2_hidden(esk4_3(esk5_0,esk6_0,esk7_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_24])).

cnf(c_0_62,negated_conjecture,
    ( r1_orders_2(esk5_0,X1,esk4_3(esk5_0,esk6_0,esk7_0))
    | ~ r3_orders_2(esk5_0,X1,esk4_3(esk5_0,esk6_0,esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_56]),c_0_53]),c_0_13])]),c_0_54])).

cnf(c_0_63,negated_conjecture,
    ( r3_orders_2(esk5_0,esk4_3(esk5_0,esk6_0,esk7_0),esk4_3(esk5_0,esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( r1_orders_2(esk5_0,X1,esk4_3(esk5_0,esk6_0,esk7_0))
    | ~ r1_lattice3(esk5_0,X2,X1)
    | ~ r2_hidden(esk4_3(esk5_0,esk6_0,esk7_0),X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_56]),c_0_13])])).

cnf(c_0_65,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,esk7_0)
    | r1_lattice3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk4_3(esk5_0,esk6_0,esk7_0),k4_waybel_0(esk5_0,esk6_0))
    | ~ r1_orders_2(esk5_0,X1,esk4_3(esk5_0,esk6_0,esk7_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_27])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk4_3(esk5_0,esk6_0,esk7_0),esk6_0)
    | m1_subset_1(esk1_4(esk5_0,esk6_0,k4_waybel_0(esk5_0,esk6_0),esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0)),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_61]),c_0_27]),c_0_13])])).

cnf(c_0_68,negated_conjecture,
    ( r1_orders_2(esk5_0,esk4_3(esk5_0,esk6_0,esk7_0),esk4_3(esk5_0,esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_56]),c_0_63])])).

cnf(c_0_69,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,esk7_0)
    | ~ r2_hidden(esk4_3(esk5_0,esk6_0,esk7_0),k4_waybel_0(esk5_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_12])]),c_0_49])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk4_3(esk5_0,esk6_0,esk7_0),k4_waybel_0(esk5_0,esk6_0))
    | m1_subset_1(esk1_4(esk5_0,esk6_0,k4_waybel_0(esk5_0,esk6_0),esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0)),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68])])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk4_3(esk5_0,esk6_0,esk7_0),esk6_0)
    | m1_subset_1(esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_18])).

cnf(c_0_72,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,esk7_0)
    | m1_subset_1(esk1_4(esk5_0,esk6_0,k4_waybel_0(esk5_0,esk6_0),esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0)),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk4_3(esk5_0,esk6_0,esk7_0),k4_waybel_0(esk5_0,esk6_0))
    | m1_subset_1(esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_71]),c_0_68])])).

cnf(c_0_74,negated_conjecture,
    ( m1_subset_1(esk1_4(esk5_0,esk6_0,k4_waybel_0(esk5_0,esk6_0),esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0)),u1_struct_0(esk5_0))
    | ~ r1_lattice3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_72])).

cnf(c_0_75,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,esk7_0)
    | m1_subset_1(esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_73])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0),k4_waybel_0(esk5_0,esk6_0))
    | m1_subset_1(esk1_4(esk5_0,esk6_0,k4_waybel_0(esk5_0,esk6_0),esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0)),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_24])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_75]),c_0_18])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(esk1_4(esk5_0,esk6_0,k4_waybel_0(esk5_0,esk6_0),esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0)),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_76]),c_0_27]),c_0_13])])).

cnf(c_0_79,negated_conjecture,
    ( r1_orders_2(esk5_0,X1,esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0))
    | ~ r1_orders_2(esk5_0,X2,esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0))
    | ~ r1_orders_2(esk5_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_77]),c_0_38]),c_0_13])])).

cnf(c_0_80,negated_conjecture,
    ( r1_orders_2(esk5_0,X1,esk1_4(esk5_0,esk6_0,k4_waybel_0(esk5_0,esk6_0),esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0)))
    | ~ r1_lattice3(esk5_0,X2,X1)
    | ~ r2_hidden(esk1_4(esk5_0,esk6_0,k4_waybel_0(esk5_0,esk6_0),esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0)),X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_78]),c_0_13])])).

cnf(c_0_81,negated_conjecture,
    ( r1_orders_2(esk5_0,X1,esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0))
    | ~ r1_orders_2(esk5_0,esk1_4(esk5_0,esk6_0,k4_waybel_0(esk5_0,esk6_0),esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0)),esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0))
    | ~ r1_orders_2(esk5_0,X1,esk1_4(esk5_0,esk6_0,k4_waybel_0(esk5_0,esk6_0),esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_78])).

cnf(c_0_82,negated_conjecture,
    ( r1_orders_2(esk5_0,esk1_4(esk5_0,esk6_0,k4_waybel_0(esk5_0,esk6_0),esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0)),esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0))
    | r2_hidden(esk4_3(esk5_0,esk6_0,esk7_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_61]),c_0_27]),c_0_13])])).

cnf(c_0_83,negated_conjecture,
    ( r1_orders_2(esk5_0,esk7_0,esk1_4(esk5_0,esk6_0,k4_waybel_0(esk5_0,esk6_0),esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0)))
    | r2_hidden(esk4_3(esk5_0,X1,esk7_0),X1)
    | ~ r2_hidden(esk1_4(esk5_0,esk6_0,k4_waybel_0(esk5_0,esk6_0),esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_24]),c_0_12])])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(esk1_4(esk5_0,esk6_0,k4_waybel_0(esk5_0,esk6_0),esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0)),esk6_0)
    | r2_hidden(esk4_3(esk5_0,esk6_0,esk7_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_61])).

cnf(c_0_85,negated_conjecture,
    ( r1_orders_2(esk5_0,X1,esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0))
    | r2_hidden(esk4_3(esk5_0,esk6_0,esk7_0),esk6_0)
    | ~ r1_orders_2(esk5_0,X1,esk1_4(esk5_0,esk6_0,k4_waybel_0(esk5_0,esk6_0),esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_86,negated_conjecture,
    ( r1_orders_2(esk5_0,esk7_0,esk1_4(esk5_0,esk6_0,k4_waybel_0(esk5_0,esk6_0),esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0)))
    | r2_hidden(esk4_3(esk5_0,esk6_0,esk7_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_87,negated_conjecture,
    ( r1_orders_2(esk5_0,esk7_0,esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0))
    | r2_hidden(esk4_3(esk5_0,esk6_0,esk7_0),esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_12]),c_0_86])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(esk4_3(esk5_0,esk6_0,esk7_0),esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_87]),c_0_57])).

cnf(c_0_89,negated_conjecture,
    ( r2_hidden(esk4_3(esk5_0,esk6_0,esk7_0),k4_waybel_0(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_88]),c_0_68])])).

cnf(c_0_90,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_89])])).

cnf(c_0_91,negated_conjecture,
    ( ~ r1_lattice3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_90])])).

cnf(c_0_92,negated_conjecture,
    ( r2_hidden(esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0),k4_waybel_0(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_91,c_0_24])).

cnf(c_0_93,negated_conjecture,
    ( r1_orders_2(esk5_0,esk1_4(esk5_0,esk6_0,k4_waybel_0(esk5_0,esk6_0),esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0)),esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_92]),c_0_27]),c_0_13])])).

cnf(c_0_94,negated_conjecture,
    ( r2_hidden(esk1_4(esk5_0,esk6_0,k4_waybel_0(esk5_0,esk6_0),esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_92])).

cnf(c_0_95,negated_conjecture,
    ( r1_orders_2(esk5_0,X1,esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0))
    | ~ r1_orders_2(esk5_0,X1,esk1_4(esk5_0,esk6_0,k4_waybel_0(esk5_0,esk6_0),esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_93])])).

cnf(c_0_96,negated_conjecture,
    ( r1_orders_2(esk5_0,esk7_0,esk1_4(esk5_0,esk6_0,k4_waybel_0(esk5_0,esk6_0),esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_90]),c_0_12])]),c_0_94])])).

cnf(c_0_97,negated_conjecture,
    ( r1_orders_2(esk5_0,esk7_0,esk4_3(esk5_0,k4_waybel_0(esk5_0,esk6_0),esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_12]),c_0_96])])).

cnf(c_0_98,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_97]),c_0_91]),
    [proof]).

%------------------------------------------------------------------------------
