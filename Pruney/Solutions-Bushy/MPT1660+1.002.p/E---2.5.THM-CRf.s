%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1660+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:33 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 871 expanded)
%              Number of clauses        :   54 ( 328 expanded)
%              Number of leaves         :    8 ( 214 expanded)
%              Depth                    :   12
%              Number of atoms          :  513 (9048 expanded)
%              Number of equality atoms :   17 ( 143 expanded)
%              Maximal formula depth    :   22 (   7 average)
%              Maximal clause size      :   67 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k10_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_lattice3)).

fof(redefinition_k13_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k13_lattice3(X1,X2,X3) = k10_lattice3(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

fof(t40_waybel_0,conjecture,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( v12_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ( v1_waybel_0(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( ( r2_hidden(X3,X2)
                        & r2_hidden(X4,X2) )
                     => r2_hidden(k13_lattice3(X1,X3,X4),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_waybel_0)).

fof(t22_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( X4 = k13_lattice3(X1,X2,X3)
                  <=> ( r1_orders_2(X1,X2,X4)
                      & r1_orders_2(X1,X3,X4)
                      & ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r1_orders_2(X1,X2,X5)
                              & r1_orders_2(X1,X3,X5) )
                           => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_yellow_0)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_waybel_0)).

fof(commutativity_k13_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k13_lattice3(X1,X2,X3) = k13_lattice3(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k13_lattice3)).

fof(d19_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v12_waybel_0(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( ( r2_hidden(X3,X2)
                        & r1_orders_2(X1,X4,X3) )
                     => r2_hidden(X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_waybel_0)).

fof(c_0_8,plain,(
    ! [X23,X24,X25] :
      ( ~ l1_orders_2(X23)
      | ~ m1_subset_1(X24,u1_struct_0(X23))
      | ~ m1_subset_1(X25,u1_struct_0(X23))
      | m1_subset_1(k10_lattice3(X23,X24,X25),u1_struct_0(X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k10_lattice3])])).

fof(c_0_9,plain,(
    ! [X26,X27,X28] :
      ( ~ v5_orders_2(X26)
      | ~ v1_lattice3(X26)
      | ~ l1_orders_2(X26)
      | ~ m1_subset_1(X27,u1_struct_0(X26))
      | ~ m1_subset_1(X28,u1_struct_0(X26))
      | k13_lattice3(X26,X27,X28) = k10_lattice3(X26,X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k13_lattice3])])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( v5_orders_2(X1)
          & v1_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( v12_waybel_0(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => ( v1_waybel_0(X2,X1)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( ( r2_hidden(X3,X2)
                          & r2_hidden(X4,X2) )
                       => r2_hidden(k13_lattice3(X1,X3,X4),X2) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t40_waybel_0])).

fof(c_0_11,plain,(
    ! [X29,X30,X31,X32,X33] :
      ( ( r1_orders_2(X29,X30,X32)
        | X32 != k13_lattice3(X29,X30,X31)
        | ~ m1_subset_1(X32,u1_struct_0(X29))
        | ~ m1_subset_1(X31,u1_struct_0(X29))
        | ~ m1_subset_1(X30,u1_struct_0(X29))
        | ~ v5_orders_2(X29)
        | ~ v1_lattice3(X29)
        | ~ l1_orders_2(X29) )
      & ( r1_orders_2(X29,X31,X32)
        | X32 != k13_lattice3(X29,X30,X31)
        | ~ m1_subset_1(X32,u1_struct_0(X29))
        | ~ m1_subset_1(X31,u1_struct_0(X29))
        | ~ m1_subset_1(X30,u1_struct_0(X29))
        | ~ v5_orders_2(X29)
        | ~ v1_lattice3(X29)
        | ~ l1_orders_2(X29) )
      & ( ~ m1_subset_1(X33,u1_struct_0(X29))
        | ~ r1_orders_2(X29,X30,X33)
        | ~ r1_orders_2(X29,X31,X33)
        | r1_orders_2(X29,X32,X33)
        | X32 != k13_lattice3(X29,X30,X31)
        | ~ m1_subset_1(X32,u1_struct_0(X29))
        | ~ m1_subset_1(X31,u1_struct_0(X29))
        | ~ m1_subset_1(X30,u1_struct_0(X29))
        | ~ v5_orders_2(X29)
        | ~ v1_lattice3(X29)
        | ~ l1_orders_2(X29) )
      & ( m1_subset_1(esk6_4(X29,X30,X31,X32),u1_struct_0(X29))
        | ~ r1_orders_2(X29,X30,X32)
        | ~ r1_orders_2(X29,X31,X32)
        | X32 = k13_lattice3(X29,X30,X31)
        | ~ m1_subset_1(X32,u1_struct_0(X29))
        | ~ m1_subset_1(X31,u1_struct_0(X29))
        | ~ m1_subset_1(X30,u1_struct_0(X29))
        | ~ v5_orders_2(X29)
        | ~ v1_lattice3(X29)
        | ~ l1_orders_2(X29) )
      & ( r1_orders_2(X29,X30,esk6_4(X29,X30,X31,X32))
        | ~ r1_orders_2(X29,X30,X32)
        | ~ r1_orders_2(X29,X31,X32)
        | X32 = k13_lattice3(X29,X30,X31)
        | ~ m1_subset_1(X32,u1_struct_0(X29))
        | ~ m1_subset_1(X31,u1_struct_0(X29))
        | ~ m1_subset_1(X30,u1_struct_0(X29))
        | ~ v5_orders_2(X29)
        | ~ v1_lattice3(X29)
        | ~ l1_orders_2(X29) )
      & ( r1_orders_2(X29,X31,esk6_4(X29,X30,X31,X32))
        | ~ r1_orders_2(X29,X30,X32)
        | ~ r1_orders_2(X29,X31,X32)
        | X32 = k13_lattice3(X29,X30,X31)
        | ~ m1_subset_1(X32,u1_struct_0(X29))
        | ~ m1_subset_1(X31,u1_struct_0(X29))
        | ~ m1_subset_1(X30,u1_struct_0(X29))
        | ~ v5_orders_2(X29)
        | ~ v1_lattice3(X29)
        | ~ l1_orders_2(X29) )
      & ( ~ r1_orders_2(X29,X32,esk6_4(X29,X30,X31,X32))
        | ~ r1_orders_2(X29,X30,X32)
        | ~ r1_orders_2(X29,X31,X32)
        | X32 = k13_lattice3(X29,X30,X31)
        | ~ m1_subset_1(X32,u1_struct_0(X29))
        | ~ m1_subset_1(X31,u1_struct_0(X29))
        | ~ m1_subset_1(X30,u1_struct_0(X29))
        | ~ v5_orders_2(X29)
        | ~ v1_lattice3(X29)
        | ~ l1_orders_2(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_yellow_0])])])])])).

cnf(c_0_12,plain,
    ( m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k13_lattice3(X1,X2,X3) = k10_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X35,X36,X37] :
      ( ~ r2_hidden(X35,X36)
      | ~ m1_subset_1(X36,k1_zfmisc_1(X37))
      | m1_subset_1(X35,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_15,negated_conjecture,(
    ! [X42,X43] :
      ( v5_orders_2(esk7_0)
      & v1_lattice3(esk7_0)
      & l1_orders_2(esk7_0)
      & v12_waybel_0(esk8_0,esk7_0)
      & m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0)))
      & ( m1_subset_1(esk9_0,u1_struct_0(esk7_0))
        | ~ v1_waybel_0(esk8_0,esk7_0) )
      & ( m1_subset_1(esk10_0,u1_struct_0(esk7_0))
        | ~ v1_waybel_0(esk8_0,esk7_0) )
      & ( r2_hidden(esk9_0,esk8_0)
        | ~ v1_waybel_0(esk8_0,esk7_0) )
      & ( r2_hidden(esk10_0,esk8_0)
        | ~ v1_waybel_0(esk8_0,esk7_0) )
      & ( ~ r2_hidden(k13_lattice3(esk7_0,esk9_0,esk10_0),esk8_0)
        | ~ v1_waybel_0(esk8_0,esk7_0) )
      & ( v1_waybel_0(esk8_0,esk7_0)
        | ~ m1_subset_1(X42,u1_struct_0(esk7_0))
        | ~ m1_subset_1(X43,u1_struct_0(esk7_0))
        | ~ r2_hidden(X42,esk8_0)
        | ~ r2_hidden(X43,esk8_0)
        | r2_hidden(k13_lattice3(esk7_0,X42,X43),esk8_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])])).

fof(c_0_16,plain,(
    ! [X15,X16,X17,X18,X22] :
      ( ( m1_subset_1(esk3_4(X15,X16,X17,X18),u1_struct_0(X15))
        | ~ r2_hidden(X17,X16)
        | ~ r2_hidden(X18,X16)
        | ~ m1_subset_1(X18,u1_struct_0(X15))
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ v1_waybel_0(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_orders_2(X15) )
      & ( r2_hidden(esk3_4(X15,X16,X17,X18),X16)
        | ~ r2_hidden(X17,X16)
        | ~ r2_hidden(X18,X16)
        | ~ m1_subset_1(X18,u1_struct_0(X15))
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ v1_waybel_0(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_orders_2(X15) )
      & ( r1_orders_2(X15,X17,esk3_4(X15,X16,X17,X18))
        | ~ r2_hidden(X17,X16)
        | ~ r2_hidden(X18,X16)
        | ~ m1_subset_1(X18,u1_struct_0(X15))
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ v1_waybel_0(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_orders_2(X15) )
      & ( r1_orders_2(X15,X18,esk3_4(X15,X16,X17,X18))
        | ~ r2_hidden(X17,X16)
        | ~ r2_hidden(X18,X16)
        | ~ m1_subset_1(X18,u1_struct_0(X15))
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ v1_waybel_0(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_orders_2(X15) )
      & ( m1_subset_1(esk4_2(X15,X16),u1_struct_0(X15))
        | v1_waybel_0(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_orders_2(X15) )
      & ( m1_subset_1(esk5_2(X15,X16),u1_struct_0(X15))
        | v1_waybel_0(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_orders_2(X15) )
      & ( r2_hidden(esk4_2(X15,X16),X16)
        | v1_waybel_0(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_orders_2(X15) )
      & ( r2_hidden(esk5_2(X15,X16),X16)
        | v1_waybel_0(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_orders_2(X15) )
      & ( ~ m1_subset_1(X22,u1_struct_0(X15))
        | ~ r2_hidden(X22,X16)
        | ~ r1_orders_2(X15,esk4_2(X15,X16),X22)
        | ~ r1_orders_2(X15,esk5_2(X15,X16),X22)
        | v1_waybel_0(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_orders_2(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_waybel_0])])])])])).

cnf(c_0_17,plain,
    ( r1_orders_2(X1,X2,X3)
    | X3 != k13_lattice3(X1,X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( m1_subset_1(k13_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_19,plain,(
    ! [X6,X7,X8] :
      ( ~ v5_orders_2(X6)
      | ~ v1_lattice3(X6)
      | ~ l1_orders_2(X6)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | k13_lattice3(X6,X7,X8) = k13_lattice3(X6,X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k13_lattice3])])).

cnf(c_0_20,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( v1_waybel_0(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(X1,X3)
    | ~ r1_orders_2(X2,esk4_2(X2,X3),X1)
    | ~ r1_orders_2(X2,esk5_2(X2,X3),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( r1_orders_2(X1,X2,k13_lattice3(X1,X3,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_17]),c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( v1_lattice3(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( l1_orders_2(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( v5_orders_2(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,plain,
    ( k13_lattice3(X1,X2,X3) = k13_lattice3(X1,X3,X2)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_29,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | v1_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_30,plain,(
    ! [X9,X10,X11,X12] :
      ( ( ~ v12_waybel_0(X10,X9)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ m1_subset_1(X12,u1_struct_0(X9))
        | ~ r2_hidden(X11,X10)
        | ~ r1_orders_2(X9,X12,X11)
        | r2_hidden(X12,X10)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_orders_2(X9) )
      & ( m1_subset_1(esk1_2(X9,X10),u1_struct_0(X9))
        | v12_waybel_0(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_orders_2(X9) )
      & ( m1_subset_1(esk2_2(X9,X10),u1_struct_0(X9))
        | v12_waybel_0(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_orders_2(X9) )
      & ( r2_hidden(esk1_2(X9,X10),X10)
        | v12_waybel_0(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_orders_2(X9) )
      & ( r1_orders_2(X9,esk2_2(X9,X10),esk1_2(X9,X10))
        | v12_waybel_0(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_orders_2(X9) )
      & ( ~ r2_hidden(esk2_2(X9,X10),X10)
        | v12_waybel_0(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_orders_2(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_waybel_0])])])])])).

cnf(c_0_31,plain,
    ( r1_orders_2(X2,X5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ r1_orders_2(X2,X4,X1)
    | X5 != k13_lattice3(X2,X3,X4)
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ v1_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_32,plain,
    ( v1_waybel_0(X1,X2)
    | ~ r1_orders_2(X2,esk4_2(X2,X1),X3)
    | ~ r1_orders_2(X2,esk5_2(X2,X1),X3)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_22,c_0_20])).

cnf(c_0_33,negated_conjecture,
    ( r1_orders_2(esk7_0,X1,k13_lattice3(esk7_0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_34,negated_conjecture,
    ( k13_lattice3(esk7_0,X1,X2) = k13_lattice3(esk7_0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_35,negated_conjecture,
    ( v1_waybel_0(esk8_0,esk7_0)
    | r2_hidden(k13_lattice3(esk7_0,X1,X2),esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0))
    | ~ r2_hidden(X1,esk8_0)
    | ~ r2_hidden(X2,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_36,negated_conjecture,
    ( v1_waybel_0(esk8_0,X1)
    | m1_subset_1(esk4_2(X1,esk8_0),u1_struct_0(esk7_0))
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_37,plain,
    ( r2_hidden(X4,X1)
    | ~ v12_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ r1_orders_2(X2,X4,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( r1_orders_2(X1,k13_lattice3(X1,X2,X3),X4)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_31]),c_0_18])).

cnf(c_0_39,negated_conjecture,
    ( v1_waybel_0(X1,esk7_0)
    | ~ r1_orders_2(esk7_0,esk4_2(esk7_0,X1),k13_lattice3(esk7_0,X2,esk5_2(esk7_0,X1)))
    | ~ r2_hidden(k13_lattice3(esk7_0,X2,esk5_2(esk7_0,X1)),X1)
    | ~ m1_subset_1(esk5_2(esk7_0,X1),u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_25])])).

cnf(c_0_40,negated_conjecture,
    ( r1_orders_2(esk7_0,X1,k13_lattice3(esk7_0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( v1_waybel_0(esk8_0,esk7_0)
    | v1_waybel_0(esk8_0,X1)
    | r2_hidden(k13_lattice3(esk7_0,X2,esk4_2(X1,esk8_0)),esk8_0)
    | ~ r2_hidden(X2,esk8_0)
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_28]),c_0_29])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_orders_2(X3,X1,X4)
    | ~ r2_hidden(X4,X2)
    | ~ v12_waybel_0(X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(csr,[status(thm)],[c_0_37,c_0_20])).

cnf(c_0_43,negated_conjecture,
    ( r1_orders_2(esk7_0,k13_lattice3(esk7_0,X1,X2),X3)
    | ~ r1_orders_2(esk7_0,X2,X3)
    | ~ r1_orders_2(esk7_0,X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(k13_lattice3(esk7_0,X1,X2),u1_struct_0(esk7_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_45,plain,
    ( r1_orders_2(X1,X2,esk3_4(X1,X3,X4,X2))
    | ~ r2_hidden(X4,X3)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v1_waybel_0(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_46,negated_conjecture,
    ( v1_waybel_0(X1,esk7_0)
    | ~ r2_hidden(k13_lattice3(esk7_0,esk4_2(esk7_0,X1),esk5_2(esk7_0,X1)),X1)
    | ~ m1_subset_1(esk5_2(esk7_0,X1),u1_struct_0(esk7_0))
    | ~ m1_subset_1(esk4_2(esk7_0,X1),u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( v1_waybel_0(esk8_0,esk7_0)
    | v1_waybel_0(esk8_0,X1)
    | r2_hidden(k13_lattice3(esk7_0,esk4_2(X1,esk8_0),X2),esk8_0)
    | ~ r2_hidden(X2,esk8_0)
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_34]),c_0_28]),c_0_36])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(k13_lattice3(esk7_0,X1,X2),X3)
    | ~ r1_orders_2(esk7_0,X2,X4)
    | ~ r1_orders_2(esk7_0,X1,X4)
    | ~ r2_hidden(X4,X3)
    | ~ v12_waybel_0(X3,esk7_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_25])]),c_0_20]),c_0_44])).

cnf(c_0_49,plain,
    ( r1_orders_2(X1,X2,esk3_4(X1,X3,X4,X2))
    | ~ v1_waybel_0(X3,X1)
    | ~ r2_hidden(X4,X3)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_45,c_0_20]),c_0_20])).

cnf(c_0_50,plain,
    ( r1_orders_2(X1,X2,esk3_4(X1,X3,X2,X4))
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_waybel_0(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_51,negated_conjecture,
    ( v1_waybel_0(esk8_0,esk7_0)
    | ~ r2_hidden(esk5_2(esk7_0,esk8_0),esk8_0)
    | ~ m1_subset_1(esk4_2(esk7_0,esk8_0),u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_21]),c_0_25])]),c_0_28])).

cnf(c_0_52,plain,
    ( r2_hidden(esk5_2(X1,X2),X2)
    | v1_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(k13_lattice3(esk7_0,X1,X2),X3)
    | ~ v1_waybel_0(X4,esk7_0)
    | ~ r1_orders_2(esk7_0,X1,esk3_4(esk7_0,X4,X5,X2))
    | ~ r2_hidden(esk3_4(esk7_0,X4,X5,X2),X3)
    | ~ r2_hidden(X5,X4)
    | ~ r2_hidden(X2,X4)
    | ~ v12_waybel_0(X3,esk7_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_25])]),c_0_20])).

cnf(c_0_54,plain,
    ( r1_orders_2(X1,X2,esk3_4(X1,X3,X2,X4))
    | ~ v1_waybel_0(X3,X1)
    | ~ r2_hidden(X4,X3)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_50,c_0_20]),c_0_20])).

cnf(c_0_55,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_56,negated_conjecture,
    ( v1_waybel_0(esk8_0,esk7_0)
    | ~ m1_subset_1(esk4_2(esk7_0,esk8_0),u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_21]),c_0_25])])).

cnf(c_0_57,plain,
    ( m1_subset_1(esk4_2(X1,X2),u1_struct_0(X1))
    | v1_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(k13_lattice3(esk7_0,X1,X2),X3)
    | ~ v1_waybel_0(X4,esk7_0)
    | ~ r2_hidden(esk3_4(esk7_0,X4,X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | ~ r2_hidden(X2,X4)
    | ~ v12_waybel_0(X3,esk7_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_25])]),c_0_20])).

cnf(c_0_59,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X2)
    | ~ v1_waybel_0(X2,X1)
    | ~ r2_hidden(X4,X2)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_55,c_0_20]),c_0_20])).

cnf(c_0_60,negated_conjecture,
    ( ~ r2_hidden(k13_lattice3(esk7_0,esk9_0,esk10_0),esk8_0)
    | ~ v1_waybel_0(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_61,negated_conjecture,
    ( v1_waybel_0(esk8_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_21]),c_0_25])])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(k13_lattice3(esk7_0,X1,X2),X3)
    | ~ v1_waybel_0(X3,esk7_0)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X2,X3)
    | ~ v12_waybel_0(X3,esk7_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_25])])).

cnf(c_0_63,negated_conjecture,
    ( v12_waybel_0(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk9_0,esk8_0)
    | ~ v1_waybel_0(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk10_0,esk8_0)
    | ~ v1_waybel_0(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_66,negated_conjecture,
    ( ~ r2_hidden(k13_lattice3(esk7_0,esk9_0,esk10_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61])])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(k13_lattice3(esk7_0,X1,X2),esk8_0)
    | ~ r2_hidden(X1,esk8_0)
    | ~ r2_hidden(X2,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_61]),c_0_21])])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk9_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_61])])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk10_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_61])])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68]),c_0_69])]),
    [proof]).

%------------------------------------------------------------------------------
