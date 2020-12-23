%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1695+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:36 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 814 expanded)
%              Number of clauses        :   75 ( 301 expanded)
%              Number of leaves         :    5 ( 220 expanded)
%              Depth                    :   12
%              Number of atoms          :  802 (17282 expanded)
%              Number of equality atoms :   31 ( 523 expanded)
%              Maximal formula depth    :   33 (   9 average)
%              Maximal clause size      :  107 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(d39_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ( v24_waybel_0(X1)
      <=> ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v1_waybel_0(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => ? [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
                & r2_lattice3(X1,X2,X3)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r2_lattice3(X1,X2,X4)
                     => r3_orders_2(X1,X3,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d39_waybel_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_orders_2)).

fof(d7_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( r1_yellow_0(X1,X2)
        <=> ? [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
              & r2_lattice3(X1,X2,X3)
              & ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r2_lattice3(X1,X2,X4)
                   => r1_orders_2(X1,X3,X4) ) )
              & ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( ( r2_lattice3(X1,X2,X4)
                      & ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( r2_lattice3(X1,X2,X5)
                           => r1_orders_2(X1,X4,X5) ) ) )
                   => X4 = X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_yellow_0)).

fof(t75_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ( v24_waybel_0(X1)
      <=> ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v1_waybel_0(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => r1_yellow_0(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_waybel_0)).

fof(c_0_5,plain,(
    ! [X24,X25,X26] :
      ( ( ~ r3_orders_2(X24,X25,X26)
        | r1_orders_2(X24,X25,X26)
        | v2_struct_0(X24)
        | ~ v3_orders_2(X24)
        | ~ l1_orders_2(X24)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | ~ m1_subset_1(X26,u1_struct_0(X24)) )
      & ( ~ r1_orders_2(X24,X25,X26)
        | r3_orders_2(X24,X25,X26)
        | v2_struct_0(X24)
        | ~ v3_orders_2(X24)
        | ~ l1_orders_2(X24)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | ~ m1_subset_1(X26,u1_struct_0(X24)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

fof(c_0_6,plain,(
    ! [X6,X7,X9,X11] :
      ( ( m1_subset_1(esk1_2(X6,X7),u1_struct_0(X6))
        | v1_xboole_0(X7)
        | ~ v1_waybel_0(X7,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ v24_waybel_0(X6)
        | v2_struct_0(X6)
        | ~ v3_orders_2(X6)
        | ~ l1_orders_2(X6) )
      & ( r2_lattice3(X6,X7,esk1_2(X6,X7))
        | v1_xboole_0(X7)
        | ~ v1_waybel_0(X7,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ v24_waybel_0(X6)
        | v2_struct_0(X6)
        | ~ v3_orders_2(X6)
        | ~ l1_orders_2(X6) )
      & ( ~ m1_subset_1(X9,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X7,X9)
        | r3_orders_2(X6,esk1_2(X6,X7),X9)
        | v1_xboole_0(X7)
        | ~ v1_waybel_0(X7,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ v24_waybel_0(X6)
        | v2_struct_0(X6)
        | ~ v3_orders_2(X6)
        | ~ l1_orders_2(X6) )
      & ( ~ v1_xboole_0(esk2_1(X6))
        | v24_waybel_0(X6)
        | v2_struct_0(X6)
        | ~ v3_orders_2(X6)
        | ~ l1_orders_2(X6) )
      & ( v1_waybel_0(esk2_1(X6),X6)
        | v24_waybel_0(X6)
        | v2_struct_0(X6)
        | ~ v3_orders_2(X6)
        | ~ l1_orders_2(X6) )
      & ( m1_subset_1(esk2_1(X6),k1_zfmisc_1(u1_struct_0(X6)))
        | v24_waybel_0(X6)
        | v2_struct_0(X6)
        | ~ v3_orders_2(X6)
        | ~ l1_orders_2(X6) )
      & ( m1_subset_1(esk3_2(X6,X11),u1_struct_0(X6))
        | ~ m1_subset_1(X11,u1_struct_0(X6))
        | ~ r2_lattice3(X6,esk2_1(X6),X11)
        | v24_waybel_0(X6)
        | v2_struct_0(X6)
        | ~ v3_orders_2(X6)
        | ~ l1_orders_2(X6) )
      & ( r2_lattice3(X6,esk2_1(X6),esk3_2(X6,X11))
        | ~ m1_subset_1(X11,u1_struct_0(X6))
        | ~ r2_lattice3(X6,esk2_1(X6),X11)
        | v24_waybel_0(X6)
        | v2_struct_0(X6)
        | ~ v3_orders_2(X6)
        | ~ l1_orders_2(X6) )
      & ( ~ r3_orders_2(X6,X11,esk3_2(X6,X11))
        | ~ m1_subset_1(X11,u1_struct_0(X6))
        | ~ r2_lattice3(X6,esk2_1(X6),X11)
        | v24_waybel_0(X6)
        | v2_struct_0(X6)
        | ~ v3_orders_2(X6)
        | ~ l1_orders_2(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d39_waybel_0])])])])])])).

fof(c_0_7,plain,(
    ! [X27,X28,X29] :
      ( ~ v5_orders_2(X27)
      | ~ l1_orders_2(X27)
      | ~ m1_subset_1(X28,u1_struct_0(X27))
      | ~ m1_subset_1(X29,u1_struct_0(X27))
      | ~ r1_orders_2(X27,X28,X29)
      | ~ r1_orders_2(X27,X29,X28)
      | X28 = X29 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_orders_2])])])).

cnf(c_0_8,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r3_orders_2(X2,esk1_2(X2,X3),X1)
    | v1_xboole_0(X3)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ v1_waybel_0(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v24_waybel_0(X2)
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( m1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v1_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v24_waybel_0(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_11,plain,(
    ! [X13,X14,X16,X17,X19,X20,X23] :
      ( ( m1_subset_1(esk4_2(X13,X14),u1_struct_0(X13))
        | ~ r1_yellow_0(X13,X14)
        | ~ l1_orders_2(X13) )
      & ( r2_lattice3(X13,X14,esk4_2(X13,X14))
        | ~ r1_yellow_0(X13,X14)
        | ~ l1_orders_2(X13) )
      & ( ~ m1_subset_1(X16,u1_struct_0(X13))
        | ~ r2_lattice3(X13,X14,X16)
        | r1_orders_2(X13,esk4_2(X13,X14),X16)
        | ~ r1_yellow_0(X13,X14)
        | ~ l1_orders_2(X13) )
      & ( m1_subset_1(esk5_3(X13,X14,X17),u1_struct_0(X13))
        | ~ r2_lattice3(X13,X14,X17)
        | X17 = esk4_2(X13,X14)
        | ~ m1_subset_1(X17,u1_struct_0(X13))
        | ~ r1_yellow_0(X13,X14)
        | ~ l1_orders_2(X13) )
      & ( r2_lattice3(X13,X14,esk5_3(X13,X14,X17))
        | ~ r2_lattice3(X13,X14,X17)
        | X17 = esk4_2(X13,X14)
        | ~ m1_subset_1(X17,u1_struct_0(X13))
        | ~ r1_yellow_0(X13,X14)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_orders_2(X13,X17,esk5_3(X13,X14,X17))
        | ~ r2_lattice3(X13,X14,X17)
        | X17 = esk4_2(X13,X14)
        | ~ m1_subset_1(X17,u1_struct_0(X13))
        | ~ r1_yellow_0(X13,X14)
        | ~ l1_orders_2(X13) )
      & ( m1_subset_1(esk7_3(X13,X19,X20),u1_struct_0(X13))
        | m1_subset_1(esk6_3(X13,X19,X20),u1_struct_0(X13))
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r2_lattice3(X13,X19,X20)
        | r1_yellow_0(X13,X19)
        | ~ l1_orders_2(X13) )
      & ( r2_lattice3(X13,X19,esk7_3(X13,X19,X20))
        | m1_subset_1(esk6_3(X13,X19,X20),u1_struct_0(X13))
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r2_lattice3(X13,X19,X20)
        | r1_yellow_0(X13,X19)
        | ~ l1_orders_2(X13) )
      & ( ~ m1_subset_1(X23,u1_struct_0(X13))
        | ~ r2_lattice3(X13,X19,X23)
        | r1_orders_2(X13,esk7_3(X13,X19,X20),X23)
        | m1_subset_1(esk6_3(X13,X19,X20),u1_struct_0(X13))
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r2_lattice3(X13,X19,X20)
        | r1_yellow_0(X13,X19)
        | ~ l1_orders_2(X13) )
      & ( esk7_3(X13,X19,X20) != X20
        | m1_subset_1(esk6_3(X13,X19,X20),u1_struct_0(X13))
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r2_lattice3(X13,X19,X20)
        | r1_yellow_0(X13,X19)
        | ~ l1_orders_2(X13) )
      & ( m1_subset_1(esk7_3(X13,X19,X20),u1_struct_0(X13))
        | r2_lattice3(X13,X19,esk6_3(X13,X19,X20))
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r2_lattice3(X13,X19,X20)
        | r1_yellow_0(X13,X19)
        | ~ l1_orders_2(X13) )
      & ( r2_lattice3(X13,X19,esk7_3(X13,X19,X20))
        | r2_lattice3(X13,X19,esk6_3(X13,X19,X20))
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r2_lattice3(X13,X19,X20)
        | r1_yellow_0(X13,X19)
        | ~ l1_orders_2(X13) )
      & ( ~ m1_subset_1(X23,u1_struct_0(X13))
        | ~ r2_lattice3(X13,X19,X23)
        | r1_orders_2(X13,esk7_3(X13,X19,X20),X23)
        | r2_lattice3(X13,X19,esk6_3(X13,X19,X20))
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r2_lattice3(X13,X19,X20)
        | r1_yellow_0(X13,X19)
        | ~ l1_orders_2(X13) )
      & ( esk7_3(X13,X19,X20) != X20
        | r2_lattice3(X13,X19,esk6_3(X13,X19,X20))
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r2_lattice3(X13,X19,X20)
        | r1_yellow_0(X13,X19)
        | ~ l1_orders_2(X13) )
      & ( m1_subset_1(esk7_3(X13,X19,X20),u1_struct_0(X13))
        | ~ r1_orders_2(X13,X20,esk6_3(X13,X19,X20))
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r2_lattice3(X13,X19,X20)
        | r1_yellow_0(X13,X19)
        | ~ l1_orders_2(X13) )
      & ( r2_lattice3(X13,X19,esk7_3(X13,X19,X20))
        | ~ r1_orders_2(X13,X20,esk6_3(X13,X19,X20))
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r2_lattice3(X13,X19,X20)
        | r1_yellow_0(X13,X19)
        | ~ l1_orders_2(X13) )
      & ( ~ m1_subset_1(X23,u1_struct_0(X13))
        | ~ r2_lattice3(X13,X19,X23)
        | r1_orders_2(X13,esk7_3(X13,X19,X20),X23)
        | ~ r1_orders_2(X13,X20,esk6_3(X13,X19,X20))
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r2_lattice3(X13,X19,X20)
        | r1_yellow_0(X13,X19)
        | ~ l1_orders_2(X13) )
      & ( esk7_3(X13,X19,X20) != X20
        | ~ r1_orders_2(X13,X20,esk6_3(X13,X19,X20))
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r2_lattice3(X13,X19,X20)
        | r1_yellow_0(X13,X19)
        | ~ l1_orders_2(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_yellow_0])])])])])])).

cnf(c_0_12,plain,
    ( X2 = X3
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( r1_orders_2(X1,esk1_2(X1,X2),X3)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_waybel_0(X2,X1)
    | ~ v24_waybel_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10])).

cnf(c_0_14,plain,
    ( r1_orders_2(X2,esk7_3(X2,X3,X4),X1)
    | r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ r1_orders_2(X2,X4,esk6_3(X2,X3,X4))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X4)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( m1_subset_1(esk7_3(X1,X2,X3),u1_struct_0(X1))
    | r1_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,X3,esk6_3(X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( X1 = esk1_2(X2,X3)
    | v1_xboole_0(X3)
    | v2_struct_0(X2)
    | ~ v5_orders_2(X2)
    | ~ r1_orders_2(X2,X1,esk1_2(X2,X3))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v1_waybel_0(X3,X2)
    | ~ v24_waybel_0(X2)
    | ~ l1_orders_2(X2)
    | ~ v3_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_10])).

cnf(c_0_17,plain,
    ( X1 = esk7_3(X2,X3,X4)
    | r1_yellow_0(X2,X3)
    | ~ v5_orders_2(X2)
    | ~ r1_orders_2(X2,X1,esk7_3(X2,X3,X4))
    | ~ r1_orders_2(X2,X4,esk6_3(X2,X3,X4))
    | ~ r2_lattice3(X2,X3,X4)
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_14]),c_0_15])).

cnf(c_0_18,plain,
    ( r1_orders_2(X2,esk7_3(X2,X3,X4),X1)
    | r2_lattice3(X2,X3,esk6_3(X2,X3,X4))
    | r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X4)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( m1_subset_1(esk7_3(X1,X2,X3),u1_struct_0(X1))
    | r2_lattice3(X1,X2,esk6_3(X1,X2,X3))
    | r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( r1_orders_2(X2,esk7_3(X2,X3,X4),X1)
    | m1_subset_1(esk6_3(X2,X3,X4),u1_struct_0(X2))
    | r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X4)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,plain,
    ( m1_subset_1(esk7_3(X1,X2,X3),u1_struct_0(X1))
    | m1_subset_1(esk6_3(X1,X2,X3),u1_struct_0(X1))
    | r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,plain,
    ( v24_waybel_0(X1)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,esk3_2(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_lattice3(X1,esk2_1(X1),X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_23,plain,
    ( r3_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_24,plain,
    ( m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | v24_waybel_0(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_lattice3(X1,esk2_1(X1),X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ( v24_waybel_0(X1)
        <=> ! [X2] :
              ( ( ~ v1_xboole_0(X2)
                & v1_waybel_0(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
             => r1_yellow_0(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t75_waybel_0])).

cnf(c_0_26,plain,
    ( esk7_3(X1,X2,X3) = esk1_2(X1,X4)
    | r1_yellow_0(X1,X2)
    | v1_xboole_0(X4)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ r1_orders_2(X1,X3,esk6_3(X1,X2,X3))
    | ~ r2_lattice3(X1,X4,esk7_3(X1,X2,X3))
    | ~ r2_lattice3(X1,X2,esk1_2(X1,X4))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_waybel_0(X4,X1)
    | ~ v24_waybel_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_14]),c_0_10]),c_0_15])).

cnf(c_0_27,plain,
    ( r2_lattice3(X1,X2,esk7_3(X1,X2,X3))
    | r1_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,X3,esk6_3(X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,plain,
    ( r2_lattice3(X1,X2,esk1_2(X1,X2))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v1_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v24_waybel_0(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_29,plain,
    ( esk7_3(X1,X2,X3) = esk7_3(X1,X4,X5)
    | r1_yellow_0(X1,X2)
    | r1_yellow_0(X1,X4)
    | r2_lattice3(X1,X2,esk6_3(X1,X2,X3))
    | ~ v5_orders_2(X1)
    | ~ r1_orders_2(X1,X5,esk6_3(X1,X4,X5))
    | ~ r2_lattice3(X1,X4,esk7_3(X1,X2,X3))
    | ~ r2_lattice3(X1,X2,esk7_3(X1,X4,X5))
    | ~ r2_lattice3(X1,X4,X5)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_15]),c_0_19])).

cnf(c_0_30,plain,
    ( r2_lattice3(X1,X2,esk7_3(X1,X2,X3))
    | r2_lattice3(X1,X2,esk6_3(X1,X2,X3))
    | r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_31,plain,
    ( esk7_3(X1,X2,X3) = esk7_3(X1,X4,X5)
    | r1_yellow_0(X1,X2)
    | r1_yellow_0(X1,X4)
    | m1_subset_1(esk6_3(X1,X2,X3),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ r1_orders_2(X1,X5,esk6_3(X1,X4,X5))
    | ~ r2_lattice3(X1,X4,esk7_3(X1,X2,X3))
    | ~ r2_lattice3(X1,X2,esk7_3(X1,X4,X5))
    | ~ r2_lattice3(X1,X4,X5)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_20]),c_0_15]),c_0_21])).

cnf(c_0_32,plain,
    ( r2_lattice3(X1,X2,esk7_3(X1,X2,X3))
    | m1_subset_1(esk6_3(X1,X2,X3),u1_struct_0(X1))
    | r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_33,plain,
    ( v24_waybel_0(X1)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,esk3_2(X1,X2))
    | ~ r2_lattice3(X1,esk2_1(X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_34,plain,
    ( r1_orders_2(X2,esk4_2(X2,X3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ r1_yellow_0(X2,X3)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_35,plain,
    ( m1_subset_1(esk4_2(X1,X2),u1_struct_0(X1))
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_36,negated_conjecture,(
    ! [X32] :
      ( ~ v2_struct_0(esk8_0)
      & v3_orders_2(esk8_0)
      & v5_orders_2(esk8_0)
      & l1_orders_2(esk8_0)
      & ( ~ v1_xboole_0(esk9_0)
        | ~ v24_waybel_0(esk8_0) )
      & ( v1_waybel_0(esk9_0,esk8_0)
        | ~ v24_waybel_0(esk8_0) )
      & ( m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(esk8_0)))
        | ~ v24_waybel_0(esk8_0) )
      & ( ~ r1_yellow_0(esk8_0,esk9_0)
        | ~ v24_waybel_0(esk8_0) )
      & ( v24_waybel_0(esk8_0)
        | v1_xboole_0(X32)
        | ~ v1_waybel_0(X32,esk8_0)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(esk8_0)))
        | r1_yellow_0(esk8_0,X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_25])])])])])])).

cnf(c_0_37,plain,
    ( r1_yellow_0(X1,X2)
    | esk7_3(X1,X2,X3) != X3
    | ~ r1_orders_2(X1,X3,esk6_3(X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_38,plain,
    ( esk7_3(X1,X2,X3) = esk1_2(X1,X2)
    | r1_yellow_0(X1,X2)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ r1_orders_2(X1,X3,esk6_3(X1,X2,X3))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_waybel_0(X2,X1)
    | ~ v24_waybel_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_39,plain,
    ( r2_lattice3(X1,X2,esk6_3(X1,X2,X3))
    | r1_yellow_0(X1,X2)
    | esk7_3(X1,X2,X3) != X3
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_40,plain,
    ( esk7_3(X1,X2,X3) = esk7_3(X1,X2,X4)
    | r1_yellow_0(X1,X2)
    | r2_lattice3(X1,X2,esk6_3(X1,X2,X3))
    | ~ v5_orders_2(X1)
    | ~ r1_orders_2(X1,X4,esk6_3(X1,X2,X4))
    | ~ r2_lattice3(X1,X2,X4)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_27])).

cnf(c_0_41,plain,
    ( m1_subset_1(esk6_3(X1,X2,X3),u1_struct_0(X1))
    | r1_yellow_0(X1,X2)
    | esk7_3(X1,X2,X3) != X3
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_42,plain,
    ( esk7_3(X1,X2,X3) = esk7_3(X1,X2,X4)
    | r1_yellow_0(X1,X2)
    | m1_subset_1(esk6_3(X1,X2,X3),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ r1_orders_2(X1,X4,esk6_3(X1,X2,X4))
    | ~ r2_lattice3(X1,X2,X4)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_27])).

cnf(c_0_43,plain,
    ( v24_waybel_0(X1)
    | v2_struct_0(X1)
    | ~ r1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,esk3_2(X1,esk4_2(X1,X2)))
    | ~ r2_lattice3(X1,esk2_1(X1),esk4_2(X1,X2))
    | ~ m1_subset_1(esk3_2(X1,esk4_2(X1,X2)),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_44,plain,
    ( r2_lattice3(X1,esk2_1(X1),esk3_2(X1,X2))
    | v24_waybel_0(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_lattice3(X1,esk2_1(X1),X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_45,plain,
    ( r2_lattice3(X1,X2,esk4_2(X1,X2))
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_46,negated_conjecture,
    ( v24_waybel_0(esk8_0)
    | v1_xboole_0(X1)
    | r1_yellow_0(esk8_0,X1)
    | ~ v1_waybel_0(X1,esk8_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,plain,
    ( v1_waybel_0(esk2_1(X1),X1)
    | v24_waybel_0(X1)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_48,negated_conjecture,
    ( l1_orders_2(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_49,negated_conjecture,
    ( v3_orders_2(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_50,negated_conjecture,
    ( ~ v2_struct_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_51,plain,
    ( r1_yellow_0(X1,X2)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | esk1_2(X1,X2) != X3
    | ~ v5_orders_2(X1)
    | ~ r1_orders_2(X1,X3,esk6_3(X1,X2,X3))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_waybel_0(X2,X1)
    | ~ v24_waybel_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_52,plain,
    ( r1_yellow_0(X1,X2)
    | r2_lattice3(X1,X2,esk6_3(X1,X2,X3))
    | esk7_3(X1,X2,X4) != X3
    | ~ v5_orders_2(X1)
    | ~ r1_orders_2(X1,X4,esk6_3(X1,X2,X4))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r2_lattice3(X1,X2,X4)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_53,plain,
    ( r1_yellow_0(X1,X2)
    | m1_subset_1(esk6_3(X1,X2,X3),u1_struct_0(X1))
    | esk7_3(X1,X2,X4) != X3
    | ~ v5_orders_2(X1)
    | ~ r1_orders_2(X1,X4,esk6_3(X1,X2,X4))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r2_lattice3(X1,X2,X4)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_54,plain,
    ( esk7_3(X1,X2,X3) = esk1_2(X1,X4)
    | r1_yellow_0(X1,X2)
    | r2_lattice3(X1,X2,esk6_3(X1,X2,X3))
    | v1_xboole_0(X4)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ r2_lattice3(X1,X4,esk7_3(X1,X2,X3))
    | ~ r2_lattice3(X1,X2,esk1_2(X1,X4))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_waybel_0(X4,X1)
    | ~ v24_waybel_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_18]),c_0_10]),c_0_19])).

cnf(c_0_55,plain,
    ( esk7_3(X1,X2,X3) = esk1_2(X1,X4)
    | r1_yellow_0(X1,X2)
    | m1_subset_1(esk6_3(X1,X2,X3),u1_struct_0(X1))
    | v1_xboole_0(X4)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ r2_lattice3(X1,X4,esk7_3(X1,X2,X3))
    | ~ r2_lattice3(X1,X2,esk1_2(X1,X4))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_waybel_0(X4,X1)
    | ~ v24_waybel_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_20]),c_0_10]),c_0_21])).

cnf(c_0_56,plain,
    ( v24_waybel_0(X1)
    | v2_struct_0(X1)
    | ~ r1_yellow_0(X1,esk2_1(X1))
    | ~ m1_subset_1(esk3_2(X1,esk4_2(X1,esk2_1(X1))),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_35]),c_0_45])).

cnf(c_0_57,plain,
    ( v24_waybel_0(X1)
    | v2_struct_0(X1)
    | ~ v1_xboole_0(esk2_1(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_58,negated_conjecture,
    ( r1_yellow_0(esk8_0,esk2_1(esk8_0))
    | v1_xboole_0(esk2_1(esk8_0))
    | v24_waybel_0(esk8_0)
    | ~ m1_subset_1(esk2_1(esk8_0),k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_49])]),c_0_50])).

cnf(c_0_59,plain,
    ( r1_yellow_0(X1,X2)
    | r1_yellow_0(X1,X3)
    | v1_xboole_0(X3)
    | v2_struct_0(X1)
    | esk1_2(X1,X3) != esk7_3(X1,X2,X4)
    | ~ v5_orders_2(X1)
    | ~ r1_orders_2(X1,X4,esk6_3(X1,X2,X4))
    | ~ r2_lattice3(X1,X2,esk6_3(X1,X3,esk7_3(X1,X2,X4)))
    | ~ r2_lattice3(X1,X3,esk7_3(X1,X2,X4))
    | ~ r2_lattice3(X1,X2,X4)
    | ~ m1_subset_1(esk6_3(X1,X3,esk7_3(X1,X2,X4)),u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v1_waybel_0(X3,X1)
    | ~ v24_waybel_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_14]),c_0_15])).

cnf(c_0_60,plain,
    ( r1_yellow_0(X1,X2)
    | r2_lattice3(X1,X2,esk6_3(X1,X2,esk7_3(X1,X2,X3)))
    | ~ v5_orders_2(X1)
    | ~ r1_orders_2(X1,X3,esk6_3(X1,X2,X3))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_52]),c_0_15]),c_0_27])).

cnf(c_0_61,plain,
    ( r1_yellow_0(X1,X2)
    | m1_subset_1(esk6_3(X1,X2,esk7_3(X1,X2,X3)),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ r1_orders_2(X1,X3,esk6_3(X1,X2,X3))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_53]),c_0_15]),c_0_27])).

cnf(c_0_62,plain,
    ( esk7_3(X1,X2,X3) = esk1_2(X1,X2)
    | r1_yellow_0(X1,X2)
    | r2_lattice3(X1,X2,esk6_3(X1,X2,X3))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_waybel_0(X2,X1)
    | ~ v24_waybel_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_30]),c_0_28])).

cnf(c_0_63,plain,
    ( esk7_3(X1,X2,X3) = esk1_2(X1,X2)
    | r1_yellow_0(X1,X2)
    | m1_subset_1(esk6_3(X1,X2,X3),u1_struct_0(X1))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_waybel_0(X2,X1)
    | ~ v24_waybel_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_32]),c_0_28])).

cnf(c_0_64,plain,
    ( v24_waybel_0(X1)
    | v2_struct_0(X1)
    | ~ r1_yellow_0(X1,esk2_1(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_24]),c_0_35]),c_0_45])).

cnf(c_0_65,negated_conjecture,
    ( r1_yellow_0(esk8_0,esk2_1(esk8_0))
    | v24_waybel_0(esk8_0)
    | ~ m1_subset_1(esk2_1(esk8_0),k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_48]),c_0_49])]),c_0_50])).

cnf(c_0_66,plain,
    ( r1_yellow_0(X1,X2)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ r1_orders_2(X1,X3,esk6_3(X1,X2,X3))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_waybel_0(X2,X1)
    | ~ v24_waybel_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_27]),c_0_38])).

cnf(c_0_67,plain,
    ( r1_yellow_0(X1,X2)
    | r2_lattice3(X1,X2,esk6_3(X1,X2,X3))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | esk1_2(X1,X2) != X3
    | ~ v5_orders_2(X1)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_waybel_0(X2,X1)
    | ~ v24_waybel_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_62])).

cnf(c_0_68,plain,
    ( r1_yellow_0(X1,X2)
    | m1_subset_1(esk6_3(X1,X2,X3),u1_struct_0(X1))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | esk1_2(X1,X2) != X3
    | ~ v5_orders_2(X1)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_waybel_0(X2,X1)
    | ~ v24_waybel_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( v24_waybel_0(esk8_0)
    | ~ m1_subset_1(esk2_1(esk8_0),k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_48]),c_0_49])]),c_0_50])).

cnf(c_0_70,plain,
    ( m1_subset_1(esk2_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v24_waybel_0(X1)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_71,plain,
    ( r1_yellow_0(X1,X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ r2_lattice3(X1,X3,esk6_3(X1,X2,esk1_2(X1,X3)))
    | ~ r2_lattice3(X1,X2,esk1_2(X1,X3))
    | ~ m1_subset_1(esk6_3(X1,X2,esk1_2(X1,X3)),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_waybel_0(X2,X1)
    | ~ v1_waybel_0(X3,X1)
    | ~ v24_waybel_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_13]),c_0_10])).

cnf(c_0_72,plain,
    ( r1_yellow_0(X1,X2)
    | r2_lattice3(X1,X2,esk6_3(X1,X2,esk1_2(X1,X2)))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_waybel_0(X2,X1)
    | ~ v24_waybel_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_67]),c_0_10]),c_0_28])).

cnf(c_0_73,plain,
    ( r1_yellow_0(X1,X2)
    | m1_subset_1(esk6_3(X1,X2,esk1_2(X1,X2)),u1_struct_0(X1))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_waybel_0(X2,X1)
    | ~ v24_waybel_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_68]),c_0_10]),c_0_28])).

cnf(c_0_74,negated_conjecture,
    ( v1_waybel_0(esk9_0,esk8_0)
    | ~ v24_waybel_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_75,negated_conjecture,
    ( v24_waybel_0(esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_48]),c_0_49])]),c_0_50])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ v24_waybel_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_77,negated_conjecture,
    ( ~ r1_yellow_0(esk8_0,esk9_0)
    | ~ v24_waybel_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_78,negated_conjecture,
    ( ~ v1_xboole_0(esk9_0)
    | ~ v24_waybel_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_79,plain,
    ( r1_yellow_0(X1,X2)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_waybel_0(X2,X1)
    | ~ v24_waybel_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73]),c_0_28])).

cnf(c_0_80,negated_conjecture,
    ( v1_waybel_0(esk9_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_75])])).

cnf(c_0_81,negated_conjecture,
    ( v5_orders_2(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_75])])).

cnf(c_0_83,negated_conjecture,
    ( ~ r1_yellow_0(esk8_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_75])])).

cnf(c_0_84,negated_conjecture,
    ( ~ v1_xboole_0(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_75])])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81]),c_0_82]),c_0_75]),c_0_48]),c_0_49])]),c_0_83]),c_0_84]),c_0_50]),
    [proof]).

%------------------------------------------------------------------------------
