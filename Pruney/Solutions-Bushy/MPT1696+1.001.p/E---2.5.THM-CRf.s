%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1696+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:36 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 466 expanded)
%              Number of clauses        :   56 ( 169 expanded)
%              Number of leaves         :    4 ( 125 expanded)
%              Depth                    :    9
%              Number of atoms          :  587 (9104 expanded)
%              Number of equality atoms :   24 ( 277 expanded)
%              Maximal formula depth    :   33 (   8 average)
%              Maximal clause size      :  107 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t25_orders_2,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ( r1_orders_2(X1,X2,X3)
                  & r1_orders_2(X1,X3,X2) )
               => X2 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_orders_2)).

fof(d40_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ( v25_waybel_0(X1)
      <=> ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => ? [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
                & r1_lattice3(X1,X2,X3)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r1_lattice3(X1,X2,X4)
                     => r1_orders_2(X1,X4,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d40_waybel_0)).

fof(d8_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( r2_yellow_0(X1,X2)
        <=> ? [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
              & r1_lattice3(X1,X2,X3)
              & ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r1_lattice3(X1,X2,X4)
                   => r1_orders_2(X1,X4,X3) ) )
              & ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( ( r1_lattice3(X1,X2,X4)
                      & ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( r1_lattice3(X1,X2,X5)
                           => r1_orders_2(X1,X5,X4) ) ) )
                   => X4 = X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_yellow_0)).

fof(t76_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ( v25_waybel_0(X1)
      <=> ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => r2_yellow_0(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_waybel_0)).

fof(c_0_4,plain,(
    ! [X24,X25,X26] :
      ( ~ v5_orders_2(X24)
      | ~ l1_orders_2(X24)
      | ~ m1_subset_1(X25,u1_struct_0(X24))
      | ~ m1_subset_1(X26,u1_struct_0(X24))
      | ~ r1_orders_2(X24,X25,X26)
      | ~ r1_orders_2(X24,X26,X25)
      | X25 = X26 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_orders_2])])])).

fof(c_0_5,plain,(
    ! [X6,X7,X9,X11] :
      ( ( m1_subset_1(esk1_2(X6,X7),u1_struct_0(X6))
        | v1_xboole_0(X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ v25_waybel_0(X6)
        | v2_struct_0(X6)
        | ~ v3_orders_2(X6)
        | ~ l1_orders_2(X6) )
      & ( r1_lattice3(X6,X7,esk1_2(X6,X7))
        | v1_xboole_0(X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ v25_waybel_0(X6)
        | v2_struct_0(X6)
        | ~ v3_orders_2(X6)
        | ~ l1_orders_2(X6) )
      & ( ~ m1_subset_1(X9,u1_struct_0(X6))
        | ~ r1_lattice3(X6,X7,X9)
        | r1_orders_2(X6,X9,esk1_2(X6,X7))
        | v1_xboole_0(X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ v25_waybel_0(X6)
        | v2_struct_0(X6)
        | ~ v3_orders_2(X6)
        | ~ l1_orders_2(X6) )
      & ( ~ v1_xboole_0(esk2_1(X6))
        | v25_waybel_0(X6)
        | v2_struct_0(X6)
        | ~ v3_orders_2(X6)
        | ~ l1_orders_2(X6) )
      & ( m1_subset_1(esk2_1(X6),k1_zfmisc_1(u1_struct_0(X6)))
        | v25_waybel_0(X6)
        | v2_struct_0(X6)
        | ~ v3_orders_2(X6)
        | ~ l1_orders_2(X6) )
      & ( m1_subset_1(esk3_2(X6,X11),u1_struct_0(X6))
        | ~ m1_subset_1(X11,u1_struct_0(X6))
        | ~ r1_lattice3(X6,esk2_1(X6),X11)
        | v25_waybel_0(X6)
        | v2_struct_0(X6)
        | ~ v3_orders_2(X6)
        | ~ l1_orders_2(X6) )
      & ( r1_lattice3(X6,esk2_1(X6),esk3_2(X6,X11))
        | ~ m1_subset_1(X11,u1_struct_0(X6))
        | ~ r1_lattice3(X6,esk2_1(X6),X11)
        | v25_waybel_0(X6)
        | v2_struct_0(X6)
        | ~ v3_orders_2(X6)
        | ~ l1_orders_2(X6) )
      & ( ~ r1_orders_2(X6,esk3_2(X6,X11),X11)
        | ~ m1_subset_1(X11,u1_struct_0(X6))
        | ~ r1_lattice3(X6,esk2_1(X6),X11)
        | v25_waybel_0(X6)
        | v2_struct_0(X6)
        | ~ v3_orders_2(X6)
        | ~ l1_orders_2(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d40_waybel_0])])])])])])).

cnf(c_0_6,plain,
    ( X2 = X3
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( r1_orders_2(X2,X1,esk1_2(X2,X3))
    | v1_xboole_0(X3)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v25_waybel_0(X2)
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( m1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v25_waybel_0(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_9,plain,(
    ! [X13,X14,X16,X17,X19,X20,X23] :
      ( ( m1_subset_1(esk4_2(X13,X14),u1_struct_0(X13))
        | ~ r2_yellow_0(X13,X14)
        | ~ l1_orders_2(X13) )
      & ( r1_lattice3(X13,X14,esk4_2(X13,X14))
        | ~ r2_yellow_0(X13,X14)
        | ~ l1_orders_2(X13) )
      & ( ~ m1_subset_1(X16,u1_struct_0(X13))
        | ~ r1_lattice3(X13,X14,X16)
        | r1_orders_2(X13,X16,esk4_2(X13,X14))
        | ~ r2_yellow_0(X13,X14)
        | ~ l1_orders_2(X13) )
      & ( m1_subset_1(esk5_3(X13,X14,X17),u1_struct_0(X13))
        | ~ r1_lattice3(X13,X14,X17)
        | X17 = esk4_2(X13,X14)
        | ~ m1_subset_1(X17,u1_struct_0(X13))
        | ~ r2_yellow_0(X13,X14)
        | ~ l1_orders_2(X13) )
      & ( r1_lattice3(X13,X14,esk5_3(X13,X14,X17))
        | ~ r1_lattice3(X13,X14,X17)
        | X17 = esk4_2(X13,X14)
        | ~ m1_subset_1(X17,u1_struct_0(X13))
        | ~ r2_yellow_0(X13,X14)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_orders_2(X13,esk5_3(X13,X14,X17),X17)
        | ~ r1_lattice3(X13,X14,X17)
        | X17 = esk4_2(X13,X14)
        | ~ m1_subset_1(X17,u1_struct_0(X13))
        | ~ r2_yellow_0(X13,X14)
        | ~ l1_orders_2(X13) )
      & ( m1_subset_1(esk7_3(X13,X19,X20),u1_struct_0(X13))
        | m1_subset_1(esk6_3(X13,X19,X20),u1_struct_0(X13))
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r1_lattice3(X13,X19,X20)
        | r2_yellow_0(X13,X19)
        | ~ l1_orders_2(X13) )
      & ( r1_lattice3(X13,X19,esk7_3(X13,X19,X20))
        | m1_subset_1(esk6_3(X13,X19,X20),u1_struct_0(X13))
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r1_lattice3(X13,X19,X20)
        | r2_yellow_0(X13,X19)
        | ~ l1_orders_2(X13) )
      & ( ~ m1_subset_1(X23,u1_struct_0(X13))
        | ~ r1_lattice3(X13,X19,X23)
        | r1_orders_2(X13,X23,esk7_3(X13,X19,X20))
        | m1_subset_1(esk6_3(X13,X19,X20),u1_struct_0(X13))
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r1_lattice3(X13,X19,X20)
        | r2_yellow_0(X13,X19)
        | ~ l1_orders_2(X13) )
      & ( esk7_3(X13,X19,X20) != X20
        | m1_subset_1(esk6_3(X13,X19,X20),u1_struct_0(X13))
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r1_lattice3(X13,X19,X20)
        | r2_yellow_0(X13,X19)
        | ~ l1_orders_2(X13) )
      & ( m1_subset_1(esk7_3(X13,X19,X20),u1_struct_0(X13))
        | r1_lattice3(X13,X19,esk6_3(X13,X19,X20))
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r1_lattice3(X13,X19,X20)
        | r2_yellow_0(X13,X19)
        | ~ l1_orders_2(X13) )
      & ( r1_lattice3(X13,X19,esk7_3(X13,X19,X20))
        | r1_lattice3(X13,X19,esk6_3(X13,X19,X20))
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r1_lattice3(X13,X19,X20)
        | r2_yellow_0(X13,X19)
        | ~ l1_orders_2(X13) )
      & ( ~ m1_subset_1(X23,u1_struct_0(X13))
        | ~ r1_lattice3(X13,X19,X23)
        | r1_orders_2(X13,X23,esk7_3(X13,X19,X20))
        | r1_lattice3(X13,X19,esk6_3(X13,X19,X20))
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r1_lattice3(X13,X19,X20)
        | r2_yellow_0(X13,X19)
        | ~ l1_orders_2(X13) )
      & ( esk7_3(X13,X19,X20) != X20
        | r1_lattice3(X13,X19,esk6_3(X13,X19,X20))
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r1_lattice3(X13,X19,X20)
        | r2_yellow_0(X13,X19)
        | ~ l1_orders_2(X13) )
      & ( m1_subset_1(esk7_3(X13,X19,X20),u1_struct_0(X13))
        | ~ r1_orders_2(X13,esk6_3(X13,X19,X20),X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r1_lattice3(X13,X19,X20)
        | r2_yellow_0(X13,X19)
        | ~ l1_orders_2(X13) )
      & ( r1_lattice3(X13,X19,esk7_3(X13,X19,X20))
        | ~ r1_orders_2(X13,esk6_3(X13,X19,X20),X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r1_lattice3(X13,X19,X20)
        | r2_yellow_0(X13,X19)
        | ~ l1_orders_2(X13) )
      & ( ~ m1_subset_1(X23,u1_struct_0(X13))
        | ~ r1_lattice3(X13,X19,X23)
        | r1_orders_2(X13,X23,esk7_3(X13,X19,X20))
        | ~ r1_orders_2(X13,esk6_3(X13,X19,X20),X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r1_lattice3(X13,X19,X20)
        | r2_yellow_0(X13,X19)
        | ~ l1_orders_2(X13) )
      & ( esk7_3(X13,X19,X20) != X20
        | ~ r1_orders_2(X13,esk6_3(X13,X19,X20),X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r1_lattice3(X13,X19,X20)
        | r2_yellow_0(X13,X19)
        | ~ l1_orders_2(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_yellow_0])])])])])])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ( v25_waybel_0(X1)
        <=> ! [X2] :
              ( ( ~ v1_xboole_0(X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
             => r2_yellow_0(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t76_waybel_0])).

cnf(c_0_11,plain,
    ( esk1_2(X1,X2) = X3
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ r1_orders_2(X1,esk1_2(X1,X2),X3)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v25_waybel_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_7]),c_0_8])).

cnf(c_0_12,plain,
    ( r1_orders_2(X2,X1,esk7_3(X2,X3,X4))
    | r2_yellow_0(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | ~ r1_orders_2(X2,esk6_3(X2,X3,X4),X4)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X4)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( m1_subset_1(esk7_3(X1,X2,X3),u1_struct_0(X1))
    | r2_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,esk6_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r1_orders_2(X2,X1,esk7_3(X2,X3,X4))
    | r1_lattice3(X2,X3,esk6_3(X2,X3,X4))
    | r2_yellow_0(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X4)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( m1_subset_1(esk7_3(X1,X2,X3),u1_struct_0(X1))
    | r1_lattice3(X1,X2,esk6_3(X1,X2,X3))
    | r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( r1_orders_2(X2,X1,esk7_3(X2,X3,X4))
    | m1_subset_1(esk6_3(X2,X3,X4),u1_struct_0(X2))
    | r2_yellow_0(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X4)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( m1_subset_1(esk7_3(X1,X2,X3),u1_struct_0(X1))
    | m1_subset_1(esk6_3(X1,X2,X3),u1_struct_0(X1))
    | r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( v25_waybel_0(X1)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,esk3_2(X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r1_lattice3(X1,esk2_1(X1),X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_19,plain,
    ( r1_orders_2(X2,X1,esk4_2(X2,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | ~ r2_yellow_0(X2,X3)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,plain,
    ( m1_subset_1(esk4_2(X1,X2),u1_struct_0(X1))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_21,negated_conjecture,(
    ! [X29] :
      ( ~ v2_struct_0(esk8_0)
      & v3_orders_2(esk8_0)
      & v5_orders_2(esk8_0)
      & l1_orders_2(esk8_0)
      & ( ~ v1_xboole_0(esk9_0)
        | ~ v25_waybel_0(esk8_0) )
      & ( m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(esk8_0)))
        | ~ v25_waybel_0(esk8_0) )
      & ( ~ r2_yellow_0(esk8_0,esk9_0)
        | ~ v25_waybel_0(esk8_0) )
      & ( v25_waybel_0(esk8_0)
        | v1_xboole_0(X29)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(esk8_0)))
        | r2_yellow_0(esk8_0,X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])])).

cnf(c_0_22,plain,
    ( esk1_2(X1,X2) = esk7_3(X1,X3,X4)
    | r2_yellow_0(X1,X3)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ r1_orders_2(X1,esk6_3(X1,X3,X4),X4)
    | ~ r1_lattice3(X1,X2,esk7_3(X1,X3,X4))
    | ~ r1_lattice3(X1,X3,esk1_2(X1,X2))
    | ~ r1_lattice3(X1,X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v25_waybel_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_8]),c_0_13])).

cnf(c_0_23,plain,
    ( r1_lattice3(X1,X2,esk7_3(X1,X2,X3))
    | r2_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,esk6_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,plain,
    ( r1_lattice3(X1,X2,esk1_2(X1,X2))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v25_waybel_0(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_25,plain,
    ( esk1_2(X1,X2) = esk7_3(X1,X3,X4)
    | r2_yellow_0(X1,X3)
    | r1_lattice3(X1,X3,esk6_3(X1,X3,X4))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ r1_lattice3(X1,X2,esk7_3(X1,X3,X4))
    | ~ r1_lattice3(X1,X3,esk1_2(X1,X2))
    | ~ r1_lattice3(X1,X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v25_waybel_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_14]),c_0_8]),c_0_15])).

cnf(c_0_26,plain,
    ( r1_lattice3(X1,X2,esk7_3(X1,X2,X3))
    | r1_lattice3(X1,X2,esk6_3(X1,X2,X3))
    | r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_27,plain,
    ( esk1_2(X1,X2) = esk7_3(X1,X3,X4)
    | r2_yellow_0(X1,X3)
    | m1_subset_1(esk6_3(X1,X3,X4),u1_struct_0(X1))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ r1_lattice3(X1,X2,esk7_3(X1,X3,X4))
    | ~ r1_lattice3(X1,X3,esk1_2(X1,X2))
    | ~ r1_lattice3(X1,X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v25_waybel_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_16]),c_0_8]),c_0_17])).

cnf(c_0_28,plain,
    ( r1_lattice3(X1,X2,esk7_3(X1,X2,X3))
    | m1_subset_1(esk6_3(X1,X2,X3),u1_struct_0(X1))
    | r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_29,plain,
    ( v25_waybel_0(X1)
    | v2_struct_0(X1)
    | ~ r2_yellow_0(X1,X2)
    | ~ r1_lattice3(X1,X2,esk3_2(X1,esk4_2(X1,X2)))
    | ~ r1_lattice3(X1,esk2_1(X1),esk4_2(X1,X2))
    | ~ m1_subset_1(esk3_2(X1,esk4_2(X1,X2)),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_30,plain,
    ( r1_lattice3(X1,esk2_1(X1),esk3_2(X1,X2))
    | v25_waybel_0(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r1_lattice3(X1,esk2_1(X1),X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_31,plain,
    ( r1_lattice3(X1,X2,esk4_2(X1,X2))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_32,negated_conjecture,
    ( v25_waybel_0(esk8_0)
    | v1_xboole_0(X1)
    | r2_yellow_0(esk8_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( m1_subset_1(esk2_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v25_waybel_0(X1)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_34,negated_conjecture,
    ( l1_orders_2(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,negated_conjecture,
    ( v3_orders_2(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_36,negated_conjecture,
    ( ~ v2_struct_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_37,plain,
    ( r2_yellow_0(X1,X2)
    | esk7_3(X1,X2,X3) != X3
    | ~ r1_orders_2(X1,esk6_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_38,plain,
    ( esk1_2(X1,X2) = esk7_3(X1,X2,X3)
    | r2_yellow_0(X1,X2)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ r1_orders_2(X1,esk6_3(X1,X2,X3),X3)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v25_waybel_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_39,plain,
    ( r1_lattice3(X1,X2,esk6_3(X1,X2,X3))
    | r2_yellow_0(X1,X2)
    | esk7_3(X1,X2,X3) != X3
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_40,plain,
    ( esk1_2(X1,X2) = esk7_3(X1,X2,X3)
    | r2_yellow_0(X1,X2)
    | r1_lattice3(X1,X2,esk6_3(X1,X2,X3))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v25_waybel_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_24])).

cnf(c_0_41,plain,
    ( m1_subset_1(esk6_3(X1,X2,X3),u1_struct_0(X1))
    | r2_yellow_0(X1,X2)
    | esk7_3(X1,X2,X3) != X3
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_42,plain,
    ( esk1_2(X1,X2) = esk7_3(X1,X2,X3)
    | r2_yellow_0(X1,X2)
    | m1_subset_1(esk6_3(X1,X2,X3),u1_struct_0(X1))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v25_waybel_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_24])).

cnf(c_0_43,plain,
    ( v25_waybel_0(X1)
    | v2_struct_0(X1)
    | ~ r2_yellow_0(X1,esk2_1(X1))
    | ~ m1_subset_1(esk3_2(X1,esk4_2(X1,esk2_1(X1))),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_20]),c_0_31])).

cnf(c_0_44,plain,
    ( m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | v25_waybel_0(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r1_lattice3(X1,esk2_1(X1),X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_45,plain,
    ( v25_waybel_0(X1)
    | v2_struct_0(X1)
    | ~ v1_xboole_0(esk2_1(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_46,negated_conjecture,
    ( r2_yellow_0(esk8_0,esk2_1(esk8_0))
    | v1_xboole_0(esk2_1(esk8_0))
    | v25_waybel_0(esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_47,plain,
    ( r2_yellow_0(X1,X2)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | esk1_2(X1,X2) != X3
    | ~ v5_orders_2(X1)
    | ~ r1_orders_2(X1,esk6_3(X1,X2,X3),X3)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v25_waybel_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_48,plain,
    ( r2_yellow_0(X1,X2)
    | r1_lattice3(X1,X2,esk6_3(X1,X2,X3))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | esk1_2(X1,X2) != X3
    | ~ v5_orders_2(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v25_waybel_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_49,plain,
    ( r2_yellow_0(X1,X2)
    | m1_subset_1(esk6_3(X1,X2,X3),u1_struct_0(X1))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | esk1_2(X1,X2) != X3
    | ~ v5_orders_2(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v25_waybel_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,plain,
    ( v25_waybel_0(X1)
    | v2_struct_0(X1)
    | ~ r2_yellow_0(X1,esk2_1(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_20]),c_0_31])).

cnf(c_0_51,negated_conjecture,
    ( r2_yellow_0(esk8_0,esk2_1(esk8_0))
    | v25_waybel_0(esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_52,plain,
    ( r2_yellow_0(X1,X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | esk1_2(X1,X2) != esk1_2(X1,X3)
    | ~ v5_orders_2(X1)
    | ~ r1_lattice3(X1,X3,esk6_3(X1,X2,esk1_2(X1,X3)))
    | ~ r1_lattice3(X1,X2,esk1_2(X1,X3))
    | ~ m1_subset_1(esk6_3(X1,X2,esk1_2(X1,X3)),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v25_waybel_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_7]),c_0_8])).

cnf(c_0_53,plain,
    ( r2_yellow_0(X1,X2)
    | r1_lattice3(X1,X2,esk6_3(X1,X2,esk1_2(X1,X2)))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v25_waybel_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_48]),c_0_8]),c_0_24])).

cnf(c_0_54,plain,
    ( r2_yellow_0(X1,X2)
    | m1_subset_1(esk6_3(X1,X2,esk1_2(X1,X2)),u1_struct_0(X1))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v25_waybel_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_49]),c_0_8]),c_0_24])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ v25_waybel_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_56,negated_conjecture,
    ( v25_waybel_0(esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_57,negated_conjecture,
    ( ~ r2_yellow_0(esk8_0,esk9_0)
    | ~ v25_waybel_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_58,negated_conjecture,
    ( ~ v1_xboole_0(esk9_0)
    | ~ v25_waybel_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_59,plain,
    ( r2_yellow_0(X1,X2)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v25_waybel_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_24])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56])])).

cnf(c_0_61,negated_conjecture,
    ( v5_orders_2(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_62,negated_conjecture,
    ( ~ r2_yellow_0(esk8_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_56])])).

cnf(c_0_63,negated_conjecture,
    ( ~ v1_xboole_0(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_56])])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_56]),c_0_34]),c_0_35])]),c_0_62]),c_0_63]),c_0_36]),
    [proof]).

%------------------------------------------------------------------------------
