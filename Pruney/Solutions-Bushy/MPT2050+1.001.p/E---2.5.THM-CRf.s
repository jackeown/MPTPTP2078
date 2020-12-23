%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT2050+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:10 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  109 (1547 expanded)
%              Number of clauses        :   72 ( 519 expanded)
%              Number of leaves         :   19 ( 380 expanded)
%              Depth                    :   16
%              Number of atoms          :  686 (10800 expanded)
%              Number of equality atoms :   66 ( 243 expanded)
%              Maximal formula depth    :   30 (   6 average)
%              Maximal clause size      :  110 (   4 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_yellow19,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( m1_yellow19(X3,X1,X2)
              <=> ? [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X2))
                    & X3 = k2_relset_1(u1_struct_0(k4_waybel_9(X1,X2,X4)),u1_struct_0(X1),u1_waybel_0(X1,k4_waybel_9(X1,X2,X4))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow19)).

fof(dt_m1_yellow19,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X2)
        & l1_waybel_0(X2,X1) )
     => ! [X3] :
          ( m1_yellow19(X3,X1,X2)
         => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_yellow19)).

fof(t9_yellow19,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m1_yellow19(X3,X1,X2)
             => r1_waybel_0(X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow19)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_waybel_0)).

fof(d7_waybel_9,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => ! [X4] :
                  ( ( v6_waybel_0(X4,X1)
                    & l1_waybel_0(X4,X1) )
                 => ( X4 = k4_waybel_9(X1,X2,X3)
                  <=> ( ! [X5] :
                          ( r2_hidden(X5,u1_struct_0(X4))
                        <=> ? [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X2))
                              & X6 = X5
                              & r1_orders_2(X2,X3,X6) ) )
                      & r2_relset_1(u1_struct_0(X4),u1_struct_0(X4),u1_orders_2(X4),k1_toler_1(u1_orders_2(X2),u1_struct_0(X4)))
                      & u1_waybel_0(X1,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),u1_struct_0(X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_waybel_9)).

fof(dt_k4_waybel_9,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X2)
        & l1_waybel_0(X2,X1)
        & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( v6_waybel_0(k4_waybel_9(X1,X2,X3),X1)
        & l1_waybel_0(k4_waybel_9(X1,X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_waybel_9)).

fof(dt_k5_waybel_9,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X2)
        & v4_orders_2(X2)
        & v7_waybel_0(X2)
        & l1_waybel_0(X2,X1)
        & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( v6_waybel_0(k5_waybel_9(X1,X2,X3),X1)
        & m2_yellow_6(k5_waybel_9(X1,X2,X3),X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_waybel_9)).

fof(redefinition_k5_waybel_9,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X2)
        & v4_orders_2(X2)
        & v7_waybel_0(X2)
        & l1_waybel_0(X2,X1)
        & m1_subset_1(X3,u1_struct_0(X2)) )
     => k5_waybel_9(X1,X2,X3) = k4_waybel_9(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_waybel_9)).

fof(dt_m2_yellow_6,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X2)
        & v4_orders_2(X2)
        & v7_waybel_0(X2)
        & l1_waybel_0(X2,X1) )
     => ! [X3] :
          ( m2_yellow_6(X3,X1,X2)
         => ( ~ v2_struct_0(X3)
            & v4_orders_2(X3)
            & v7_waybel_0(X3)
            & l1_waybel_0(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_yellow_6)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(dt_u1_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_waybel_0(X2,X1) )
     => ( v1_funct_1(u1_waybel_0(X1,X2))
        & v1_funct_2(u1_waybel_0(X1,X2),u1_struct_0(X2),u1_struct_0(X1))
        & m1_subset_1(u1_waybel_0(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_waybel_0)).

fof(d8_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => k2_waybel_0(X1,X2,X3) = k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_waybel_0)).

fof(redefinition_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => k3_funct_2(X1,X2,X3,X4) = k1_funct_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(t16_waybel_9,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v7_waybel_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X2))
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(k4_waybel_9(X1,X2,X3)))
                     => ( X4 = X5
                       => k2_waybel_0(X1,X2,X4) = k2_waybel_0(X1,k4_waybel_9(X1,X2,X3),X5) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_waybel_9)).

fof(t6_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_hidden(X3,X1)
       => ( X2 = k1_xboole_0
          | r2_hidden(k1_funct_1(X4,X3),k2_relset_1(X1,X2,X4)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

fof(c_0_19,plain,(
    ! [X15,X16,X17,X19] :
      ( ( m1_subset_1(esk3_3(X15,X16,X17),u1_struct_0(X16))
        | ~ m1_yellow19(X17,X15,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X16)
        | ~ l1_waybel_0(X16,X15)
        | v2_struct_0(X15)
        | ~ l1_struct_0(X15) )
      & ( X17 = k2_relset_1(u1_struct_0(k4_waybel_9(X15,X16,esk3_3(X15,X16,X17))),u1_struct_0(X15),u1_waybel_0(X15,k4_waybel_9(X15,X16,esk3_3(X15,X16,X17))))
        | ~ m1_yellow19(X17,X15,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X16)
        | ~ l1_waybel_0(X16,X15)
        | v2_struct_0(X15)
        | ~ l1_struct_0(X15) )
      & ( ~ m1_subset_1(X19,u1_struct_0(X16))
        | X17 != k2_relset_1(u1_struct_0(k4_waybel_9(X15,X16,X19)),u1_struct_0(X15),u1_waybel_0(X15,k4_waybel_9(X15,X16,X19)))
        | m1_yellow19(X17,X15,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X16)
        | ~ l1_waybel_0(X16,X15)
        | v2_struct_0(X15)
        | ~ l1_struct_0(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_yellow19])])])])])])).

fof(c_0_20,plain,(
    ! [X40,X41,X42] :
      ( v2_struct_0(X40)
      | ~ l1_struct_0(X40)
      | v2_struct_0(X41)
      | ~ l1_waybel_0(X41,X40)
      | ~ m1_yellow19(X42,X40,X41)
      | m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X40))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_yellow19])])])])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_orders_2(X2)
              & v7_waybel_0(X2)
              & l1_waybel_0(X2,X1) )
           => ! [X3] :
                ( m1_yellow19(X3,X1,X2)
               => r1_waybel_0(X1,X2,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t9_yellow19])).

cnf(c_0_22,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_yellow19(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_yellow19(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk7_0)
    & l1_struct_0(esk7_0)
    & ~ v2_struct_0(esk8_0)
    & v4_orders_2(esk8_0)
    & v7_waybel_0(esk8_0)
    & l1_waybel_0(esk8_0,esk7_0)
    & m1_yellow19(esk9_0,esk7_0,esk8_0)
    & ~ r1_waybel_0(esk7_0,esk8_0,esk9_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).

fof(c_0_25,plain,(
    ! [X7,X8,X9,X11,X12,X13] :
      ( ( m1_subset_1(esk1_3(X7,X8,X9),u1_struct_0(X8))
        | ~ r1_waybel_0(X7,X8,X9)
        | v2_struct_0(X8)
        | ~ l1_waybel_0(X8,X7)
        | v2_struct_0(X7)
        | ~ l1_struct_0(X7) )
      & ( ~ m1_subset_1(X11,u1_struct_0(X8))
        | ~ r1_orders_2(X8,esk1_3(X7,X8,X9),X11)
        | r2_hidden(k2_waybel_0(X7,X8,X11),X9)
        | ~ r1_waybel_0(X7,X8,X9)
        | v2_struct_0(X8)
        | ~ l1_waybel_0(X8,X7)
        | v2_struct_0(X7)
        | ~ l1_struct_0(X7) )
      & ( m1_subset_1(esk2_4(X7,X8,X12,X13),u1_struct_0(X8))
        | ~ m1_subset_1(X13,u1_struct_0(X8))
        | r1_waybel_0(X7,X8,X12)
        | v2_struct_0(X8)
        | ~ l1_waybel_0(X8,X7)
        | v2_struct_0(X7)
        | ~ l1_struct_0(X7) )
      & ( r1_orders_2(X8,X13,esk2_4(X7,X8,X12,X13))
        | ~ m1_subset_1(X13,u1_struct_0(X8))
        | r1_waybel_0(X7,X8,X12)
        | v2_struct_0(X8)
        | ~ l1_waybel_0(X8,X7)
        | v2_struct_0(X7)
        | ~ l1_struct_0(X7) )
      & ( ~ r2_hidden(k2_waybel_0(X7,X8,esk2_4(X7,X8,X12,X13)),X12)
        | ~ m1_subset_1(X13,u1_struct_0(X8))
        | r1_waybel_0(X7,X8,X12)
        | v2_struct_0(X8)
        | ~ l1_waybel_0(X8,X7)
        | v2_struct_0(X7)
        | ~ l1_struct_0(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_waybel_0])])])])])])])).

cnf(c_0_26,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_yellow19(X3,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(csr,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( m1_yellow19(esk9_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( l1_waybel_0(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( l1_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_32,plain,(
    ! [X20,X21,X22,X23,X24,X26,X27,X29] :
      ( ( m1_subset_1(esk4_5(X20,X21,X22,X23,X24),u1_struct_0(X21))
        | ~ r2_hidden(X24,u1_struct_0(X23))
        | X23 != k4_waybel_9(X20,X21,X22)
        | ~ v6_waybel_0(X23,X20)
        | ~ l1_waybel_0(X23,X20)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ l1_waybel_0(X21,X20)
        | v2_struct_0(X20)
        | ~ l1_struct_0(X20) )
      & ( esk4_5(X20,X21,X22,X23,X24) = X24
        | ~ r2_hidden(X24,u1_struct_0(X23))
        | X23 != k4_waybel_9(X20,X21,X22)
        | ~ v6_waybel_0(X23,X20)
        | ~ l1_waybel_0(X23,X20)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ l1_waybel_0(X21,X20)
        | v2_struct_0(X20)
        | ~ l1_struct_0(X20) )
      & ( r1_orders_2(X21,X22,esk4_5(X20,X21,X22,X23,X24))
        | ~ r2_hidden(X24,u1_struct_0(X23))
        | X23 != k4_waybel_9(X20,X21,X22)
        | ~ v6_waybel_0(X23,X20)
        | ~ l1_waybel_0(X23,X20)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ l1_waybel_0(X21,X20)
        | v2_struct_0(X20)
        | ~ l1_struct_0(X20) )
      & ( ~ m1_subset_1(X27,u1_struct_0(X21))
        | X27 != X26
        | ~ r1_orders_2(X21,X22,X27)
        | r2_hidden(X26,u1_struct_0(X23))
        | X23 != k4_waybel_9(X20,X21,X22)
        | ~ v6_waybel_0(X23,X20)
        | ~ l1_waybel_0(X23,X20)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ l1_waybel_0(X21,X20)
        | v2_struct_0(X20)
        | ~ l1_struct_0(X20) )
      & ( r2_relset_1(u1_struct_0(X23),u1_struct_0(X23),u1_orders_2(X23),k1_toler_1(u1_orders_2(X21),u1_struct_0(X23)))
        | X23 != k4_waybel_9(X20,X21,X22)
        | ~ v6_waybel_0(X23,X20)
        | ~ l1_waybel_0(X23,X20)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ l1_waybel_0(X21,X20)
        | v2_struct_0(X20)
        | ~ l1_struct_0(X20) )
      & ( u1_waybel_0(X20,X23) = k2_partfun1(u1_struct_0(X21),u1_struct_0(X20),u1_waybel_0(X20,X21),u1_struct_0(X23))
        | X23 != k4_waybel_9(X20,X21,X22)
        | ~ v6_waybel_0(X23,X20)
        | ~ l1_waybel_0(X23,X20)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ l1_waybel_0(X21,X20)
        | v2_struct_0(X20)
        | ~ l1_struct_0(X20) )
      & ( ~ r2_hidden(esk5_4(X20,X21,X22,X23),u1_struct_0(X23))
        | ~ m1_subset_1(X29,u1_struct_0(X21))
        | X29 != esk5_4(X20,X21,X22,X23)
        | ~ r1_orders_2(X21,X22,X29)
        | ~ r2_relset_1(u1_struct_0(X23),u1_struct_0(X23),u1_orders_2(X23),k1_toler_1(u1_orders_2(X21),u1_struct_0(X23)))
        | u1_waybel_0(X20,X23) != k2_partfun1(u1_struct_0(X21),u1_struct_0(X20),u1_waybel_0(X20,X21),u1_struct_0(X23))
        | X23 = k4_waybel_9(X20,X21,X22)
        | ~ v6_waybel_0(X23,X20)
        | ~ l1_waybel_0(X23,X20)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ l1_waybel_0(X21,X20)
        | v2_struct_0(X20)
        | ~ l1_struct_0(X20) )
      & ( m1_subset_1(esk6_4(X20,X21,X22,X23),u1_struct_0(X21))
        | r2_hidden(esk5_4(X20,X21,X22,X23),u1_struct_0(X23))
        | ~ r2_relset_1(u1_struct_0(X23),u1_struct_0(X23),u1_orders_2(X23),k1_toler_1(u1_orders_2(X21),u1_struct_0(X23)))
        | u1_waybel_0(X20,X23) != k2_partfun1(u1_struct_0(X21),u1_struct_0(X20),u1_waybel_0(X20,X21),u1_struct_0(X23))
        | X23 = k4_waybel_9(X20,X21,X22)
        | ~ v6_waybel_0(X23,X20)
        | ~ l1_waybel_0(X23,X20)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ l1_waybel_0(X21,X20)
        | v2_struct_0(X20)
        | ~ l1_struct_0(X20) )
      & ( esk6_4(X20,X21,X22,X23) = esk5_4(X20,X21,X22,X23)
        | r2_hidden(esk5_4(X20,X21,X22,X23),u1_struct_0(X23))
        | ~ r2_relset_1(u1_struct_0(X23),u1_struct_0(X23),u1_orders_2(X23),k1_toler_1(u1_orders_2(X21),u1_struct_0(X23)))
        | u1_waybel_0(X20,X23) != k2_partfun1(u1_struct_0(X21),u1_struct_0(X20),u1_waybel_0(X20,X21),u1_struct_0(X23))
        | X23 = k4_waybel_9(X20,X21,X22)
        | ~ v6_waybel_0(X23,X20)
        | ~ l1_waybel_0(X23,X20)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ l1_waybel_0(X21,X20)
        | v2_struct_0(X20)
        | ~ l1_struct_0(X20) )
      & ( r1_orders_2(X21,X22,esk6_4(X20,X21,X22,X23))
        | r2_hidden(esk5_4(X20,X21,X22,X23),u1_struct_0(X23))
        | ~ r2_relset_1(u1_struct_0(X23),u1_struct_0(X23),u1_orders_2(X23),k1_toler_1(u1_orders_2(X21),u1_struct_0(X23)))
        | u1_waybel_0(X20,X23) != k2_partfun1(u1_struct_0(X21),u1_struct_0(X20),u1_waybel_0(X20,X21),u1_struct_0(X23))
        | X23 = k4_waybel_9(X20,X21,X22)
        | ~ v6_waybel_0(X23,X20)
        | ~ l1_waybel_0(X23,X20)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ l1_waybel_0(X21,X20)
        | v2_struct_0(X20)
        | ~ l1_struct_0(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_waybel_9])])])])])])])).

fof(c_0_33,plain,(
    ! [X34,X35,X36] :
      ( ( v6_waybel_0(k4_waybel_9(X34,X35,X36),X34)
        | v2_struct_0(X34)
        | ~ l1_struct_0(X34)
        | v2_struct_0(X35)
        | ~ l1_waybel_0(X35,X34)
        | ~ m1_subset_1(X36,u1_struct_0(X35)) )
      & ( l1_waybel_0(k4_waybel_9(X34,X35,X36),X34)
        | v2_struct_0(X34)
        | ~ l1_struct_0(X34)
        | v2_struct_0(X35)
        | ~ l1_waybel_0(X35,X34)
        | ~ m1_subset_1(X36,u1_struct_0(X35)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_waybel_9])])])])).

cnf(c_0_34,plain,
    ( r1_orders_2(X1,X2,esk2_4(X3,X1,X4,X2))
    | r1_waybel_0(X3,X1,X4)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_waybel_0(X1,X3)
    | ~ l1_struct_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk3_3(esk7_0,esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])]),c_0_30]),c_0_31])).

cnf(c_0_36,plain,
    ( m1_subset_1(esk2_4(X1,X2,X3,X4),u1_struct_0(X2))
    | r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_37,plain,(
    ! [X37,X38,X39] :
      ( ( v6_waybel_0(k5_waybel_9(X37,X38,X39),X37)
        | v2_struct_0(X37)
        | ~ l1_struct_0(X37)
        | v2_struct_0(X38)
        | ~ v4_orders_2(X38)
        | ~ v7_waybel_0(X38)
        | ~ l1_waybel_0(X38,X37)
        | ~ m1_subset_1(X39,u1_struct_0(X38)) )
      & ( m2_yellow_6(k5_waybel_9(X37,X38,X39),X37,X38)
        | v2_struct_0(X37)
        | ~ l1_struct_0(X37)
        | v2_struct_0(X38)
        | ~ v4_orders_2(X38)
        | ~ v7_waybel_0(X38)
        | ~ l1_waybel_0(X38,X37)
        | ~ m1_subset_1(X39,u1_struct_0(X38)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_waybel_9])])])])).

cnf(c_0_38,plain,
    ( r2_hidden(X3,u1_struct_0(X5))
    | v2_struct_0(X2)
    | v2_struct_0(X6)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X1 != X3
    | ~ r1_orders_2(X2,X4,X1)
    | X5 != k4_waybel_9(X6,X2,X4)
    | ~ v6_waybel_0(X5,X6)
    | ~ l1_waybel_0(X5,X6)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X6)
    | ~ l1_struct_0(X6) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( l1_waybel_0(k4_waybel_9(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,plain,
    ( v6_waybel_0(k4_waybel_9(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( r1_orders_2(esk8_0,esk3_3(esk7_0,esk8_0,esk9_0),esk2_4(X1,esk8_0,X2,esk3_3(esk7_0,esk8_0,esk9_0)))
    | r1_waybel_0(X1,esk8_0,X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(esk8_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk2_4(X1,esk8_0,X2,esk3_3(esk7_0,esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | r1_waybel_0(X1,esk8_0,X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(esk8_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_35]),c_0_30])).

cnf(c_0_43,plain,
    ( m2_yellow_6(k5_waybel_9(X1,X2,X3),X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( v7_waybel_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_45,negated_conjecture,
    ( v4_orders_2(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_46,plain,(
    ! [X53,X54,X55] :
      ( v2_struct_0(X53)
      | ~ l1_struct_0(X53)
      | v2_struct_0(X54)
      | ~ v4_orders_2(X54)
      | ~ v7_waybel_0(X54)
      | ~ l1_waybel_0(X54,X53)
      | ~ m1_subset_1(X55,u1_struct_0(X54))
      | k5_waybel_9(X53,X54,X55) = k4_waybel_9(X53,X54,X55) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k5_waybel_9])])])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,u1_struct_0(k4_waybel_9(X2,X3,X4)))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_orders_2(X3,X4,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_waybel_0(X3,X2)
    | ~ l1_struct_0(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_38])]),c_0_39]),c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( r1_orders_2(esk8_0,esk3_3(esk7_0,esk8_0,esk9_0),esk2_4(esk7_0,esk8_0,X1,esk3_3(esk7_0,esk8_0,esk9_0)))
    | r1_waybel_0(esk7_0,esk8_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_28]),c_0_29])]),c_0_31])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk2_4(esk7_0,esk8_0,X1,esk3_3(esk7_0,esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | r1_waybel_0(esk7_0,esk8_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_28]),c_0_29])]),c_0_31])).

fof(c_0_50,plain,(
    ! [X43,X44,X45] :
      ( ( ~ v2_struct_0(X45)
        | ~ m2_yellow_6(X45,X43,X44)
        | v2_struct_0(X43)
        | ~ l1_struct_0(X43)
        | v2_struct_0(X44)
        | ~ v4_orders_2(X44)
        | ~ v7_waybel_0(X44)
        | ~ l1_waybel_0(X44,X43) )
      & ( v4_orders_2(X45)
        | ~ m2_yellow_6(X45,X43,X44)
        | v2_struct_0(X43)
        | ~ l1_struct_0(X43)
        | v2_struct_0(X44)
        | ~ v4_orders_2(X44)
        | ~ v7_waybel_0(X44)
        | ~ l1_waybel_0(X44,X43) )
      & ( v7_waybel_0(X45)
        | ~ m2_yellow_6(X45,X43,X44)
        | v2_struct_0(X43)
        | ~ l1_struct_0(X43)
        | v2_struct_0(X44)
        | ~ v4_orders_2(X44)
        | ~ v7_waybel_0(X44)
        | ~ l1_waybel_0(X44,X43) )
      & ( l1_waybel_0(X45,X43)
        | ~ m2_yellow_6(X45,X43,X44)
        | v2_struct_0(X43)
        | ~ l1_struct_0(X43)
        | v2_struct_0(X44)
        | ~ v4_orders_2(X44)
        | ~ v7_waybel_0(X44)
        | ~ l1_waybel_0(X44,X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_yellow_6])])])])])).

cnf(c_0_51,negated_conjecture,
    ( m2_yellow_6(k5_waybel_9(X1,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0)),X1,esk8_0)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(esk8_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_35]),c_0_44]),c_0_45])]),c_0_30])).

cnf(c_0_52,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k5_waybel_9(X1,X2,X3) = k4_waybel_9(X1,X2,X3)
    | ~ l1_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_53,plain,(
    ! [X61,X62] :
      ( ~ r2_hidden(X61,X62)
      | m1_subset_1(X61,X62) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk2_4(esk7_0,esk8_0,X1,esk3_3(esk7_0,esk8_0,esk9_0)),u1_struct_0(k4_waybel_9(X2,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0))))
    | r1_waybel_0(esk7_0,esk8_0,X1)
    | v2_struct_0(X2)
    | ~ l1_waybel_0(esk8_0,X2)
    | ~ l1_struct_0(X2) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_35])]),c_0_30]),c_0_49])).

cnf(c_0_55,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(X1)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( m2_yellow_6(k5_waybel_9(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0)),esk7_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_28]),c_0_29])]),c_0_31])).

cnf(c_0_57,negated_conjecture,
    ( k5_waybel_9(X1,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0)) = k4_waybel_9(X1,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(esk8_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_35]),c_0_44]),c_0_45])]),c_0_30])).

fof(c_0_58,plain,(
    ! [X46,X47] :
      ( ( v1_funct_1(u1_waybel_0(X46,X47))
        | ~ l1_struct_0(X46)
        | ~ l1_waybel_0(X47,X46) )
      & ( v1_funct_2(u1_waybel_0(X46,X47),u1_struct_0(X47),u1_struct_0(X46))
        | ~ l1_struct_0(X46)
        | ~ l1_waybel_0(X47,X46) )
      & ( m1_subset_1(u1_waybel_0(X46,X47),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X46))))
        | ~ l1_struct_0(X46)
        | ~ l1_waybel_0(X47,X46) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_waybel_0])])])).

cnf(c_0_59,negated_conjecture,
    ( l1_waybel_0(k4_waybel_9(X1,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0)),X1)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(esk8_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_35]),c_0_30])).

cnf(c_0_60,plain,
    ( X1 = k2_relset_1(u1_struct_0(k4_waybel_9(X2,X3,esk3_3(X2,X3,X1))),u1_struct_0(X2),u1_waybel_0(X2,k4_waybel_9(X2,X3,esk3_3(X2,X3,X1))))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ m1_yellow19(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_waybel_0(X3,X2)
    | ~ l1_struct_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_61,plain,(
    ! [X31,X32,X33] :
      ( v2_struct_0(X31)
      | ~ l1_struct_0(X31)
      | v2_struct_0(X32)
      | ~ l1_waybel_0(X32,X31)
      | ~ m1_subset_1(X33,u1_struct_0(X32))
      | k2_waybel_0(X31,X32,X33) = k3_funct_2(u1_struct_0(X32),u1_struct_0(X31),u1_waybel_0(X31,X32),X33) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_waybel_0])])])])).

cnf(c_0_62,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk2_4(esk7_0,esk8_0,X1,esk3_3(esk7_0,esk8_0,esk9_0)),u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0))))
    | r1_waybel_0(esk7_0,esk8_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_28]),c_0_29])]),c_0_31])).

cnf(c_0_64,negated_conjecture,
    ( ~ v2_struct_0(k5_waybel_9(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_44]),c_0_45]),c_0_28]),c_0_29])]),c_0_30]),c_0_31])).

cnf(c_0_65,negated_conjecture,
    ( k5_waybel_9(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0)) = k4_waybel_9(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_28]),c_0_29])]),c_0_31])).

fof(c_0_66,plain,(
    ! [X49,X50,X51,X52] :
      ( v1_xboole_0(X49)
      | ~ v1_funct_1(X51)
      | ~ v1_funct_2(X51,X49,X50)
      | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))
      | ~ m1_subset_1(X52,X49)
      | k3_funct_2(X49,X50,X51,X52) = k1_funct_1(X51,X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).

cnf(c_0_67,plain,
    ( v1_funct_2(u1_waybel_0(X1,X2),u1_struct_0(X2),u1_struct_0(X1))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_68,negated_conjecture,
    ( l1_waybel_0(k4_waybel_9(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0)),esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_28]),c_0_29])]),c_0_31])).

cnf(c_0_69,plain,
    ( v1_funct_1(u1_waybel_0(X1,X2))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_70,plain,
    ( m1_subset_1(u1_waybel_0(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_71,plain,(
    ! [X69,X70] :
      ( ~ r2_hidden(X69,X70)
      | ~ v1_xboole_0(X70) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_72,plain,(
    ! [X56,X57,X58,X59,X60] :
      ( v2_struct_0(X56)
      | ~ l1_struct_0(X56)
      | v2_struct_0(X57)
      | ~ v7_waybel_0(X57)
      | ~ l1_waybel_0(X57,X56)
      | ~ m1_subset_1(X58,u1_struct_0(X57))
      | ~ m1_subset_1(X59,u1_struct_0(X57))
      | ~ m1_subset_1(X60,u1_struct_0(k4_waybel_9(X56,X57,X58)))
      | X59 != X60
      | k2_waybel_0(X56,X57,X59) = k2_waybel_0(X56,k4_waybel_9(X56,X57,X58),X60) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t16_waybel_9])])])])).

fof(c_0_73,plain,(
    ! [X65,X66,X67,X68] :
      ( ~ v1_funct_1(X68)
      | ~ v1_funct_2(X68,X65,X66)
      | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X65,X66)))
      | ~ r2_hidden(X67,X65)
      | X66 = k1_xboole_0
      | r2_hidden(k1_funct_1(X68,X67),k2_relset_1(X65,X66,X68)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_funct_2])])).

cnf(c_0_74,plain,
    ( k2_relset_1(u1_struct_0(k4_waybel_9(X1,X2,esk3_3(X1,X2,X3))),u1_struct_0(X1),u1_waybel_0(X1,k4_waybel_9(X1,X2,esk3_3(X1,X2,X3)))) = X3
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_yellow19(X3,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(csr,[status(thm)],[c_0_60,c_0_23])).

cnf(c_0_75,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_waybel_0(X1,X2,X3) = k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),X3)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(esk2_4(esk7_0,esk8_0,X1,esk3_3(esk7_0,esk8_0,esk9_0)),u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0))))
    | r1_waybel_0(esk7_0,esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_77,negated_conjecture,
    ( ~ v2_struct_0(k4_waybel_9(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0))) ),
    inference(rw,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_78,plain,
    ( v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X4) = k1_funct_1(X2,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_79,negated_conjecture,
    ( v1_funct_2(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0))),u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0))),u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_29])])).

cnf(c_0_80,negated_conjecture,
    ( v1_funct_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_68]),c_0_29])])).

cnf(c_0_81,negated_conjecture,
    ( m1_subset_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0))),u1_struct_0(esk7_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_68]),c_0_29])])).

cnf(c_0_82,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_83,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_waybel_0(X1,X2,X4) = k2_waybel_0(X1,k4_waybel_9(X1,X2,X3),X5)
    | ~ l1_struct_0(X1)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X5,u1_struct_0(k4_waybel_9(X1,X2,X3)))
    | X4 != X5 ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_84,plain,
    ( X3 = k1_xboole_0
    | r2_hidden(k1_funct_1(X1,X4),k2_relset_1(X2,X3,X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_85,negated_conjecture,
    ( k2_relset_1(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0))),u1_struct_0(esk7_0),u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0)))) = esk9_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_27]),c_0_28]),c_0_29])]),c_0_30]),c_0_31])).

cnf(c_0_86,negated_conjecture,
    ( k3_funct_2(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0))),u1_struct_0(X1),u1_waybel_0(X1,k4_waybel_9(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0))),esk2_4(esk7_0,esk8_0,X2,esk3_3(esk7_0,esk8_0,esk9_0))) = k2_waybel_0(X1,k4_waybel_9(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0)),esk2_4(esk7_0,esk8_0,X2,esk3_3(esk7_0,esk8_0,esk9_0)))
    | r1_waybel_0(esk7_0,esk8_0,X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(k4_waybel_9(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0)),X1)
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77])).

cnf(c_0_87,negated_conjecture,
    ( k3_funct_2(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0))),u1_struct_0(esk7_0),u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0))),X1) = k1_funct_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0))),X1)
    | v1_xboole_0(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80])]),c_0_81])])).

cnf(c_0_88,negated_conjecture,
    ( r1_waybel_0(esk7_0,esk8_0,X1)
    | ~ v1_xboole_0(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_82,c_0_63])).

cnf(c_0_89,plain,
    ( k2_waybel_0(X1,k4_waybel_9(X1,X2,X3),X4) = k2_waybel_0(X1,X2,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v7_waybel_0(X2)
    | ~ m1_subset_1(X4,u1_struct_0(k4_waybel_9(X1,X2,X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(er,[status(thm)],[c_0_83])).

cnf(c_0_90,negated_conjecture,
    ( u1_struct_0(esk7_0) = k1_xboole_0
    | r2_hidden(k1_funct_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0))),X1),esk9_0)
    | ~ r2_hidden(X1,u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_79]),c_0_80])]),c_0_85]),c_0_81])])).

cnf(c_0_91,negated_conjecture,
    ( k3_funct_2(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0))),u1_struct_0(esk7_0),u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0))),esk2_4(esk7_0,esk8_0,X1,esk3_3(esk7_0,esk8_0,esk9_0))) = k2_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0)),esk2_4(esk7_0,esk8_0,X1,esk3_3(esk7_0,esk8_0,esk9_0)))
    | r1_waybel_0(esk7_0,esk8_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_68]),c_0_29])]),c_0_31])).

cnf(c_0_92,negated_conjecture,
    ( k3_funct_2(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0))),u1_struct_0(esk7_0),u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0))),esk2_4(esk7_0,esk8_0,X1,esk3_3(esk7_0,esk8_0,esk9_0))) = k1_funct_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0))),esk2_4(esk7_0,esk8_0,X1,esk3_3(esk7_0,esk8_0,esk9_0)))
    | r1_waybel_0(esk7_0,esk8_0,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_76]),c_0_88])).

cnf(c_0_93,negated_conjecture,
    ( k2_waybel_0(X1,k4_waybel_9(X1,esk8_0,X2),esk2_4(esk7_0,esk8_0,X3,esk3_3(esk7_0,esk8_0,esk9_0))) = k2_waybel_0(X1,esk8_0,esk2_4(esk7_0,esk8_0,X3,esk3_3(esk7_0,esk8_0,esk9_0)))
    | r1_waybel_0(esk7_0,esk8_0,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(esk2_4(esk7_0,esk8_0,X3,esk3_3(esk7_0,esk8_0,esk9_0)),u1_struct_0(k4_waybel_9(X1,esk8_0,X2)))
    | ~ m1_subset_1(X2,u1_struct_0(esk8_0))
    | ~ l1_waybel_0(esk8_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_49]),c_0_44])]),c_0_30])).

cnf(c_0_94,negated_conjecture,
    ( u1_struct_0(esk7_0) = k1_xboole_0
    | r2_hidden(k1_funct_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0))),esk2_4(esk7_0,esk8_0,X1,esk3_3(esk7_0,esk8_0,esk9_0))),esk9_0)
    | r1_waybel_0(esk7_0,esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_90,c_0_63])).

cnf(c_0_95,negated_conjecture,
    ( k1_funct_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0))),esk2_4(esk7_0,esk8_0,X1,esk3_3(esk7_0,esk8_0,esk9_0))) = k2_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0)),esk2_4(esk7_0,esk8_0,X1,esk3_3(esk7_0,esk8_0,esk9_0)))
    | r1_waybel_0(esk7_0,esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_96,negated_conjecture,
    ( k2_waybel_0(X1,k4_waybel_9(X1,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0)),esk2_4(esk7_0,esk8_0,X2,esk3_3(esk7_0,esk8_0,esk9_0))) = k2_waybel_0(X1,esk8_0,esk2_4(esk7_0,esk8_0,X2,esk3_3(esk7_0,esk8_0,esk9_0)))
    | r1_waybel_0(esk7_0,esk8_0,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(esk2_4(esk7_0,esk8_0,X2,esk3_3(esk7_0,esk8_0,esk9_0)),u1_struct_0(k4_waybel_9(X1,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0))))
    | ~ l1_waybel_0(esk8_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_93,c_0_35])).

cnf(c_0_97,negated_conjecture,
    ( u1_struct_0(esk7_0) = k1_xboole_0
    | r2_hidden(k2_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0)),esk2_4(esk7_0,esk8_0,X1,esk3_3(esk7_0,esk8_0,esk9_0))),esk9_0)
    | r1_waybel_0(esk7_0,esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_98,negated_conjecture,
    ( k2_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,esk9_0)),esk2_4(esk7_0,esk8_0,X1,esk3_3(esk7_0,esk8_0,esk9_0))) = k2_waybel_0(esk7_0,esk8_0,esk2_4(esk7_0,esk8_0,X1,esk3_3(esk7_0,esk8_0,esk9_0)))
    | r1_waybel_0(esk7_0,esk8_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_76]),c_0_28]),c_0_29])]),c_0_31])).

fof(c_0_99,plain,(
    ! [X48] :
      ( v2_struct_0(X48)
      | ~ l1_struct_0(X48)
      | ~ v1_xboole_0(u1_struct_0(X48)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_100,plain,
    ( r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(k2_waybel_0(X1,X2,esk2_4(X1,X2,X3,X4)),X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_101,negated_conjecture,
    ( u1_struct_0(esk7_0) = k1_xboole_0
    | r2_hidden(k2_waybel_0(esk7_0,esk8_0,esk2_4(esk7_0,esk8_0,X1,esk3_3(esk7_0,esk8_0,esk9_0))),esk9_0)
    | r1_waybel_0(esk7_0,esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_102,negated_conjecture,
    ( ~ r1_waybel_0(esk7_0,esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_103,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_104,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(split_conjunct,[status(thm)],[d2_xboole_0])).

cnf(c_0_105,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_106,negated_conjecture,
    ( u1_struct_0(esk7_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_35]),c_0_28]),c_0_29])]),c_0_102]),c_0_30]),c_0_31])).

cnf(c_0_107,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_108,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_107]),c_0_29])]),c_0_31]),
    [proof]).

%------------------------------------------------------------------------------
