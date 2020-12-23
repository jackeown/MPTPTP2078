%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:02 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   68 (1004 expanded)
%              Number of clauses        :   49 ( 322 expanded)
%              Number of leaves         :    9 ( 241 expanded)
%              Depth                    :   13
%              Number of atoms          :  358 (7439 expanded)
%              Number of equality atoms :   24 (1266 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   31 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t81_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_orders_1(X3,k1_orders_1(u1_struct_0(X1)))
             => ! [X4] :
                  ( m2_orders_2(X4,X1,X3)
                 => ( X2 = k1_funct_1(X3,u1_struct_0(X1))
                   => k3_orders_2(X1,X4,X2) = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_orders_2)).

fof(dt_m2_orders_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1)
        & m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))) )
     => ! [X3] :
          ( m2_orders_2(X3,X1,X2)
         => ( v6_orders_2(X3,X1)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).

fof(dt_k3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_orders_2)).

fof(t80_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_orders_1(X4,k1_orders_1(u1_struct_0(X1)))
                 => ! [X5] :
                      ( m2_orders_2(X5,X1,X4)
                     => ( ( r2_hidden(X2,X5)
                          & X3 = k1_funct_1(X4,u1_struct_0(X1)) )
                       => r3_orders_2(X1,X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_orders_2)).

fof(t10_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ~ ( X2 != k1_xboole_0
          & ! [X3] :
              ( m1_subset_1(X3,X1)
             => ~ r2_hidden(X3,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

fof(t57_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,k3_orders_2(X1,X4,X3))
                  <=> ( r2_orders_2(X1,X2,X3)
                      & r2_hidden(X2,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).

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

fof(t28_orders_2,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ~ ( r2_orders_2(X1,X2,X3)
                  & r2_orders_2(X1,X3,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_orders_2)).

fof(d10_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_orders_2(X1,X2,X3)
              <=> ( r1_orders_2(X1,X2,X3)
                  & X2 != X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_orders_1(X3,k1_orders_1(u1_struct_0(X1)))
               => ! [X4] :
                    ( m2_orders_2(X4,X1,X3)
                   => ( X2 = k1_funct_1(X3,u1_struct_0(X1))
                     => k3_orders_2(X1,X4,X2) = k1_xboole_0 ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t81_orders_2])).

fof(c_0_10,plain,(
    ! [X15,X16,X17] :
      ( ( v6_orders_2(X17,X15)
        | ~ m2_orders_2(X17,X15,X16)
        | v2_struct_0(X15)
        | ~ v3_orders_2(X15)
        | ~ v4_orders_2(X15)
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15)
        | ~ m1_orders_1(X16,k1_orders_1(u1_struct_0(X15))) )
      & ( m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ m2_orders_2(X17,X15,X16)
        | v2_struct_0(X15)
        | ~ v3_orders_2(X15)
        | ~ v4_orders_2(X15)
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15)
        | ~ m1_orders_1(X16,k1_orders_1(u1_struct_0(X15))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_orders_2])])])])])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v3_orders_2(esk2_0)
    & v4_orders_2(esk2_0)
    & v5_orders_2(esk2_0)
    & l1_orders_2(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & m1_orders_1(esk4_0,k1_orders_1(u1_struct_0(esk2_0)))
    & m2_orders_2(esk5_0,esk2_0,esk4_0)
    & esk3_0 = k1_funct_1(esk4_0,u1_struct_0(esk2_0))
    & k3_orders_2(esk2_0,esk5_0,esk3_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

fof(c_0_12,plain,(
    ! [X12,X13,X14] :
      ( v2_struct_0(X12)
      | ~ v3_orders_2(X12)
      | ~ v4_orders_2(X12)
      | ~ v5_orders_2(X12)
      | ~ l1_orders_2(X12)
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
      | ~ m1_subset_1(X14,u1_struct_0(X12))
      | m1_subset_1(k3_orders_2(X12,X13,X14),k1_zfmisc_1(u1_struct_0(X12))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_orders_2])])])).

cnf(c_0_13,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v2_struct_0(X2)
    | ~ m2_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( m1_orders_1(esk4_0,k1_orders_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m2_orders_2(X1,esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( m2_orders_2(esk5_0,esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_24,plain,(
    ! [X28,X29,X30,X31,X32] :
      ( v2_struct_0(X28)
      | ~ v3_orders_2(X28)
      | ~ v4_orders_2(X28)
      | ~ v5_orders_2(X28)
      | ~ l1_orders_2(X28)
      | ~ m1_subset_1(X29,u1_struct_0(X28))
      | ~ m1_subset_1(X30,u1_struct_0(X28))
      | ~ m1_orders_1(X31,k1_orders_1(u1_struct_0(X28)))
      | ~ m2_orders_2(X32,X28,X31)
      | ~ r2_hidden(X29,X32)
      | X30 != k1_funct_1(X31,u1_struct_0(X28))
      | r3_orders_2(X28,X30,X29) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t80_orders_2])])])])).

fof(c_0_25,plain,(
    ! [X6,X7] :
      ( ( m1_subset_1(esk1_2(X6,X7),X6)
        | X7 = k1_xboole_0
        | ~ m1_subset_1(X7,k1_zfmisc_1(X6)) )
      & ( r2_hidden(esk1_2(X6,X7),X7)
        | X7 = k1_xboole_0
        | ~ m1_subset_1(X7,k1_zfmisc_1(X6)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_subset_1])])])])])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(k3_orders_2(esk2_0,X1,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_28,plain,(
    ! [X24,X25,X26,X27] :
      ( ( r2_orders_2(X24,X25,X26)
        | ~ r2_hidden(X25,k3_orders_2(X24,X27,X26))
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | v2_struct_0(X24)
        | ~ v3_orders_2(X24)
        | ~ v4_orders_2(X24)
        | ~ v5_orders_2(X24)
        | ~ l1_orders_2(X24) )
      & ( r2_hidden(X25,X27)
        | ~ r2_hidden(X25,k3_orders_2(X24,X27,X26))
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | v2_struct_0(X24)
        | ~ v3_orders_2(X24)
        | ~ v4_orders_2(X24)
        | ~ v5_orders_2(X24)
        | ~ l1_orders_2(X24) )
      & ( ~ r2_orders_2(X24,X25,X26)
        | ~ r2_hidden(X25,X27)
        | r2_hidden(X25,k3_orders_2(X24,X27,X26))
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | v2_struct_0(X24)
        | ~ v3_orders_2(X24)
        | ~ v4_orders_2(X24)
        | ~ v5_orders_2(X24)
        | ~ l1_orders_2(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_orders_2])])])])])).

cnf(c_0_29,plain,
    ( v2_struct_0(X1)
    | r3_orders_2(X1,X3,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_orders_1(X4,k1_orders_1(u1_struct_0(X1)))
    | ~ m2_orders_2(X5,X1,X4)
    | ~ r2_hidden(X2,X5)
    | X3 != k1_funct_1(X4,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( m1_subset_1(esk1_2(X1,X2),X1)
    | X2 = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(k3_orders_2(esk2_0,esk5_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( k3_orders_2(esk2_0,esk5_0,esk3_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X2)
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,k3_orders_2(X3,X2,X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ v3_orders_2(X3)
    | ~ v4_orders_2(X3)
    | ~ v5_orders_2(X3)
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_34,plain,(
    ! [X18,X19,X20] :
      ( ( ~ r3_orders_2(X18,X19,X20)
        | r1_orders_2(X18,X19,X20)
        | v2_struct_0(X18)
        | ~ v3_orders_2(X18)
        | ~ l1_orders_2(X18)
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | ~ m1_subset_1(X20,u1_struct_0(X18)) )
      & ( ~ r1_orders_2(X18,X19,X20)
        | r3_orders_2(X18,X19,X20)
        | v2_struct_0(X18)
        | ~ v3_orders_2(X18)
        | ~ l1_orders_2(X18)
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | ~ m1_subset_1(X20,u1_struct_0(X18)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_35,plain,
    ( r3_orders_2(X1,k1_funct_1(X2,u1_struct_0(X1)),X3)
    | v2_struct_0(X1)
    | ~ m2_orders_2(X4,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ r2_hidden(X3,X4)
    | ~ m1_subset_1(k1_funct_1(X2,u1_struct_0(X1)),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_orders_2(esk2_0,X2,esk3_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_21]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_38,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | X2 = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_39,plain,(
    ! [X21,X22,X23] :
      ( ~ v5_orders_2(X21)
      | ~ l1_orders_2(X21)
      | ~ m1_subset_1(X22,u1_struct_0(X21))
      | ~ m1_subset_1(X23,u1_struct_0(X21))
      | ~ r2_orders_2(X21,X22,X23)
      | ~ r2_orders_2(X21,X23,X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_orders_2])])])).

cnf(c_0_40,plain,
    ( r2_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,k3_orders_2(X1,X4,X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_41,plain,(
    ! [X9,X10,X11] :
      ( ( r1_orders_2(X9,X10,X11)
        | ~ r2_orders_2(X9,X10,X11)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | ~ l1_orders_2(X9) )
      & ( X10 != X11
        | ~ r2_orders_2(X9,X10,X11)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | ~ l1_orders_2(X9) )
      & ( ~ r1_orders_2(X9,X10,X11)
        | X10 = X11
        | r2_orders_2(X9,X10,X11)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | ~ l1_orders_2(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_orders_2])])])])).

cnf(c_0_42,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( r3_orders_2(esk2_0,k1_funct_1(X1,u1_struct_0(esk2_0)),esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)))
    | ~ m2_orders_2(X2,esk2_0,X1)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)),X2)
    | ~ m1_subset_1(k1_funct_1(X1,u1_struct_0(esk2_0)),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_44,negated_conjecture,
    ( esk3_0 = k1_funct_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)),X1)
    | ~ r2_hidden(esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)),k3_orders_2(esk2_0,X1,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)),k3_orders_2(esk2_0,esk5_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_31]),c_0_32])).

cnf(c_0_47,plain,
    ( ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_orders_2(X1,X2,X3)
    | ~ r2_orders_2(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( r2_orders_2(esk2_0,X1,esk3_0)
    | ~ r2_hidden(X1,k3_orders_2(esk2_0,X2,esk3_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_21]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_49,plain,
    ( X2 = X3
    | r2_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)))
    | ~ r3_orders_2(esk2_0,X1,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_36]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_51,negated_conjecture,
    ( r3_orders_2(esk2_0,esk3_0,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)))
    | ~ r2_hidden(esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_23]),c_0_44]),c_0_14]),c_0_44]),c_0_21])])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_27]),c_0_46])])).

cnf(c_0_53,negated_conjecture,
    ( ~ r2_orders_2(esk2_0,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)),X1)
    | ~ r2_orders_2(esk2_0,X1,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_36]),c_0_15]),c_0_18])])).

cnf(c_0_54,negated_conjecture,
    ( r2_orders_2(esk2_0,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)),esk3_0)
    | ~ r2_hidden(esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)),k3_orders_2(esk2_0,X1,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_36])).

cnf(c_0_55,negated_conjecture,
    ( X1 = esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0))
    | r2_orders_2(esk2_0,X1,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)))
    | ~ r1_orders_2(esk2_0,X1,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_36]),c_0_18])])).

cnf(c_0_56,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_0,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)))
    | ~ r3_orders_2(esk2_0,esk3_0,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_21])).

cnf(c_0_57,negated_conjecture,
    ( r3_orders_2(esk2_0,esk3_0,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52])])).

cnf(c_0_58,negated_conjecture,
    ( ~ r2_orders_2(esk2_0,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)),esk3_0)
    | ~ r2_orders_2(esk2_0,esk3_0,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_21])).

cnf(c_0_59,negated_conjecture,
    ( r2_orders_2(esk2_0,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_27]),c_0_46])])).

cnf(c_0_60,plain,
    ( X1 != X2
    | ~ r2_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_61,negated_conjecture,
    ( esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)) = esk3_0
    | r2_orders_2(esk2_0,esk3_0,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)))
    | ~ r1_orders_2(esk2_0,esk3_0,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_21])).

cnf(c_0_62,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_0,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57])])).

cnf(c_0_63,negated_conjecture,
    ( ~ r2_orders_2(esk2_0,esk3_0,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59])])).

cnf(c_0_64,plain,
    ( ~ r2_orders_2(X1,X2,X2)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)) = esk3_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62])]),c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( ~ r2_orders_2(esk2_0,esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_21]),c_0_18])])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_65]),c_0_66]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:51:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.20/0.35  # No SInE strategy applied
% 0.20/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.57  # AutoSched0-Mode selected heuristic G_E___008_C18_F1_PI_SE_CS_SP_CO_S4S
% 0.20/0.57  # and selection function SelectNewComplexAHPNS.
% 0.20/0.57  #
% 0.20/0.57  # Preprocessing time       : 0.028 s
% 0.20/0.57  
% 0.20/0.57  # Proof found!
% 0.20/0.57  # SZS status Theorem
% 0.20/0.57  # SZS output start CNFRefutation
% 0.20/0.57  fof(t81_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_orders_1(X3,k1_orders_1(u1_struct_0(X1)))=>![X4]:(m2_orders_2(X4,X1,X3)=>(X2=k1_funct_1(X3,u1_struct_0(X1))=>k3_orders_2(X1,X4,X2)=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_orders_2)).
% 0.20/0.57  fof(dt_m2_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))))=>![X3]:(m2_orders_2(X3,X1,X2)=>(v6_orders_2(X3,X1)&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 0.20/0.57  fof(dt_k3_orders_2, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 0.20/0.57  fof(t80_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_orders_1(X4,k1_orders_1(u1_struct_0(X1)))=>![X5]:(m2_orders_2(X5,X1,X4)=>((r2_hidden(X2,X5)&X3=k1_funct_1(X4,u1_struct_0(X1)))=>r3_orders_2(X1,X3,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_orders_2)).
% 0.20/0.57  fof(t10_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>~((X2!=k1_xboole_0&![X3]:(m1_subset_1(X3,X1)=>~(r2_hidden(X3,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_subset_1)).
% 0.20/0.57  fof(t57_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,k3_orders_2(X1,X4,X3))<=>(r2_orders_2(X1,X2,X3)&r2_hidden(X2,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 0.20/0.57  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.20/0.57  fof(t28_orders_2, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r2_orders_2(X1,X2,X3)&r2_orders_2(X1,X3,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_orders_2)).
% 0.20/0.57  fof(d10_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_orders_2(X1,X2,X3)<=>(r1_orders_2(X1,X2,X3)&X2!=X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 0.20/0.57  fof(c_0_9, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_orders_1(X3,k1_orders_1(u1_struct_0(X1)))=>![X4]:(m2_orders_2(X4,X1,X3)=>(X2=k1_funct_1(X3,u1_struct_0(X1))=>k3_orders_2(X1,X4,X2)=k1_xboole_0)))))), inference(assume_negation,[status(cth)],[t81_orders_2])).
% 0.20/0.57  fof(c_0_10, plain, ![X15, X16, X17]:((v6_orders_2(X17,X15)|~m2_orders_2(X17,X15,X16)|(v2_struct_0(X15)|~v3_orders_2(X15)|~v4_orders_2(X15)|~v5_orders_2(X15)|~l1_orders_2(X15)|~m1_orders_1(X16,k1_orders_1(u1_struct_0(X15)))))&(m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))|~m2_orders_2(X17,X15,X16)|(v2_struct_0(X15)|~v3_orders_2(X15)|~v4_orders_2(X15)|~v5_orders_2(X15)|~l1_orders_2(X15)|~m1_orders_1(X16,k1_orders_1(u1_struct_0(X15)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_orders_2])])])])])).
% 0.20/0.57  fof(c_0_11, negated_conjecture, (((((~v2_struct_0(esk2_0)&v3_orders_2(esk2_0))&v4_orders_2(esk2_0))&v5_orders_2(esk2_0))&l1_orders_2(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&(m1_orders_1(esk4_0,k1_orders_1(u1_struct_0(esk2_0)))&(m2_orders_2(esk5_0,esk2_0,esk4_0)&(esk3_0=k1_funct_1(esk4_0,u1_struct_0(esk2_0))&k3_orders_2(esk2_0,esk5_0,esk3_0)!=k1_xboole_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).
% 0.20/0.57  fof(c_0_12, plain, ![X12, X13, X14]:(v2_struct_0(X12)|~v3_orders_2(X12)|~v4_orders_2(X12)|~v5_orders_2(X12)|~l1_orders_2(X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|~m1_subset_1(X14,u1_struct_0(X12))|m1_subset_1(k3_orders_2(X12,X13,X14),k1_zfmisc_1(u1_struct_0(X12)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_orders_2])])])).
% 0.20/0.57  cnf(c_0_13, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|v2_struct_0(X2)|~m2_orders_2(X1,X2,X3)|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.57  cnf(c_0_14, negated_conjecture, (m1_orders_1(esk4_0,k1_orders_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.57  cnf(c_0_15, negated_conjecture, (v5_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.57  cnf(c_0_16, negated_conjecture, (v4_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.57  cnf(c_0_17, negated_conjecture, (v3_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.57  cnf(c_0_18, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.57  cnf(c_0_19, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.57  cnf(c_0_20, plain, (v2_struct_0(X1)|m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.57  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.57  cnf(c_0_22, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m2_orders_2(X1,esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15]), c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 0.20/0.57  cnf(c_0_23, negated_conjecture, (m2_orders_2(esk5_0,esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.57  fof(c_0_24, plain, ![X28, X29, X30, X31, X32]:(v2_struct_0(X28)|~v3_orders_2(X28)|~v4_orders_2(X28)|~v5_orders_2(X28)|~l1_orders_2(X28)|(~m1_subset_1(X29,u1_struct_0(X28))|(~m1_subset_1(X30,u1_struct_0(X28))|(~m1_orders_1(X31,k1_orders_1(u1_struct_0(X28)))|(~m2_orders_2(X32,X28,X31)|(~r2_hidden(X29,X32)|X30!=k1_funct_1(X31,u1_struct_0(X28))|r3_orders_2(X28,X30,X29))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t80_orders_2])])])])).
% 0.20/0.57  fof(c_0_25, plain, ![X6, X7]:((m1_subset_1(esk1_2(X6,X7),X6)|X7=k1_xboole_0|~m1_subset_1(X7,k1_zfmisc_1(X6)))&(r2_hidden(esk1_2(X6,X7),X7)|X7=k1_xboole_0|~m1_subset_1(X7,k1_zfmisc_1(X6)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_subset_1])])])])])).
% 0.20/0.57  cnf(c_0_26, negated_conjecture, (m1_subset_1(k3_orders_2(esk2_0,X1,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_15]), c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 0.20/0.57  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.57  fof(c_0_28, plain, ![X24, X25, X26, X27]:(((r2_orders_2(X24,X25,X26)|~r2_hidden(X25,k3_orders_2(X24,X27,X26))|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X24)))|~m1_subset_1(X26,u1_struct_0(X24))|~m1_subset_1(X25,u1_struct_0(X24))|(v2_struct_0(X24)|~v3_orders_2(X24)|~v4_orders_2(X24)|~v5_orders_2(X24)|~l1_orders_2(X24)))&(r2_hidden(X25,X27)|~r2_hidden(X25,k3_orders_2(X24,X27,X26))|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X24)))|~m1_subset_1(X26,u1_struct_0(X24))|~m1_subset_1(X25,u1_struct_0(X24))|(v2_struct_0(X24)|~v3_orders_2(X24)|~v4_orders_2(X24)|~v5_orders_2(X24)|~l1_orders_2(X24))))&(~r2_orders_2(X24,X25,X26)|~r2_hidden(X25,X27)|r2_hidden(X25,k3_orders_2(X24,X27,X26))|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X24)))|~m1_subset_1(X26,u1_struct_0(X24))|~m1_subset_1(X25,u1_struct_0(X24))|(v2_struct_0(X24)|~v3_orders_2(X24)|~v4_orders_2(X24)|~v5_orders_2(X24)|~l1_orders_2(X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_orders_2])])])])])).
% 0.20/0.57  cnf(c_0_29, plain, (v2_struct_0(X1)|r3_orders_2(X1,X3,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_orders_1(X4,k1_orders_1(u1_struct_0(X1)))|~m2_orders_2(X5,X1,X4)|~r2_hidden(X2,X5)|X3!=k1_funct_1(X4,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.57  cnf(c_0_30, plain, (m1_subset_1(esk1_2(X1,X2),X1)|X2=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.57  cnf(c_0_31, negated_conjecture, (m1_subset_1(k3_orders_2(esk2_0,esk5_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.57  cnf(c_0_32, negated_conjecture, (k3_orders_2(esk2_0,esk5_0,esk3_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.57  cnf(c_0_33, plain, (r2_hidden(X1,X2)|v2_struct_0(X3)|~r2_hidden(X1,k3_orders_2(X3,X2,X4))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X4,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~v3_orders_2(X3)|~v4_orders_2(X3)|~v5_orders_2(X3)|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.57  fof(c_0_34, plain, ![X18, X19, X20]:((~r3_orders_2(X18,X19,X20)|r1_orders_2(X18,X19,X20)|(v2_struct_0(X18)|~v3_orders_2(X18)|~l1_orders_2(X18)|~m1_subset_1(X19,u1_struct_0(X18))|~m1_subset_1(X20,u1_struct_0(X18))))&(~r1_orders_2(X18,X19,X20)|r3_orders_2(X18,X19,X20)|(v2_struct_0(X18)|~v3_orders_2(X18)|~l1_orders_2(X18)|~m1_subset_1(X19,u1_struct_0(X18))|~m1_subset_1(X20,u1_struct_0(X18))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.20/0.57  cnf(c_0_35, plain, (r3_orders_2(X1,k1_funct_1(X2,u1_struct_0(X1)),X3)|v2_struct_0(X1)|~m2_orders_2(X4,X1,X2)|~m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~r2_hidden(X3,X4)|~m1_subset_1(k1_funct_1(X2,u1_struct_0(X1)),u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_29])).
% 0.20/0.57  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 0.20/0.57  cnf(c_0_37, negated_conjecture, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_orders_2(esk2_0,X2,esk3_0))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_21]), c_0_15]), c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 0.20/0.57  cnf(c_0_38, plain, (r2_hidden(esk1_2(X1,X2),X2)|X2=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.57  fof(c_0_39, plain, ![X21, X22, X23]:(~v5_orders_2(X21)|~l1_orders_2(X21)|(~m1_subset_1(X22,u1_struct_0(X21))|(~m1_subset_1(X23,u1_struct_0(X21))|(~r2_orders_2(X21,X22,X23)|~r2_orders_2(X21,X23,X22))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_orders_2])])])).
% 0.20/0.57  cnf(c_0_40, plain, (r2_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r2_hidden(X2,k3_orders_2(X1,X4,X3))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.57  fof(c_0_41, plain, ![X9, X10, X11]:(((r1_orders_2(X9,X10,X11)|~r2_orders_2(X9,X10,X11)|~m1_subset_1(X11,u1_struct_0(X9))|~m1_subset_1(X10,u1_struct_0(X9))|~l1_orders_2(X9))&(X10!=X11|~r2_orders_2(X9,X10,X11)|~m1_subset_1(X11,u1_struct_0(X9))|~m1_subset_1(X10,u1_struct_0(X9))|~l1_orders_2(X9)))&(~r1_orders_2(X9,X10,X11)|X10=X11|r2_orders_2(X9,X10,X11)|~m1_subset_1(X11,u1_struct_0(X9))|~m1_subset_1(X10,u1_struct_0(X9))|~l1_orders_2(X9))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_orders_2])])])])).
% 0.20/0.57  cnf(c_0_42, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r3_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.57  cnf(c_0_43, negated_conjecture, (r3_orders_2(esk2_0,k1_funct_1(X1,u1_struct_0(esk2_0)),esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)))|~m2_orders_2(X2,esk2_0,X1)|~m1_orders_1(X1,k1_orders_1(u1_struct_0(esk2_0)))|~r2_hidden(esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)),X2)|~m1_subset_1(k1_funct_1(X1,u1_struct_0(esk2_0)),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_15]), c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 0.20/0.57  cnf(c_0_44, negated_conjecture, (esk3_0=k1_funct_1(esk4_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.57  cnf(c_0_45, negated_conjecture, (r2_hidden(esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)),X1)|~r2_hidden(esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)),k3_orders_2(esk2_0,X1,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_37, c_0_36])).
% 0.20/0.57  cnf(c_0_46, negated_conjecture, (r2_hidden(esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)),k3_orders_2(esk2_0,esk5_0,esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_31]), c_0_32])).
% 0.20/0.57  cnf(c_0_47, plain, (~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~r2_orders_2(X1,X2,X3)|~r2_orders_2(X1,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.57  cnf(c_0_48, negated_conjecture, (r2_orders_2(esk2_0,X1,esk3_0)|~r2_hidden(X1,k3_orders_2(esk2_0,X2,esk3_0))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_21]), c_0_15]), c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 0.20/0.57  cnf(c_0_49, plain, (X2=X3|r2_orders_2(X1,X2,X3)|~r1_orders_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.57  cnf(c_0_50, negated_conjecture, (r1_orders_2(esk2_0,X1,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)))|~r3_orders_2(esk2_0,X1,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_36]), c_0_17]), c_0_18])]), c_0_19])).
% 0.20/0.57  cnf(c_0_51, negated_conjecture, (r3_orders_2(esk2_0,esk3_0,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)))|~r2_hidden(esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_23]), c_0_44]), c_0_14]), c_0_44]), c_0_21])])).
% 0.20/0.57  cnf(c_0_52, negated_conjecture, (r2_hidden(esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_27]), c_0_46])])).
% 0.20/0.57  cnf(c_0_53, negated_conjecture, (~r2_orders_2(esk2_0,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)),X1)|~r2_orders_2(esk2_0,X1,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_36]), c_0_15]), c_0_18])])).
% 0.20/0.57  cnf(c_0_54, negated_conjecture, (r2_orders_2(esk2_0,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)),esk3_0)|~r2_hidden(esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)),k3_orders_2(esk2_0,X1,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_48, c_0_36])).
% 0.20/0.57  cnf(c_0_55, negated_conjecture, (X1=esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0))|r2_orders_2(esk2_0,X1,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)))|~r1_orders_2(esk2_0,X1,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_36]), c_0_18])])).
% 0.20/0.57  cnf(c_0_56, negated_conjecture, (r1_orders_2(esk2_0,esk3_0,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)))|~r3_orders_2(esk2_0,esk3_0,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)))), inference(spm,[status(thm)],[c_0_50, c_0_21])).
% 0.20/0.57  cnf(c_0_57, negated_conjecture, (r3_orders_2(esk2_0,esk3_0,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_52])])).
% 0.20/0.57  cnf(c_0_58, negated_conjecture, (~r2_orders_2(esk2_0,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)),esk3_0)|~r2_orders_2(esk2_0,esk3_0,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)))), inference(spm,[status(thm)],[c_0_53, c_0_21])).
% 0.20/0.57  cnf(c_0_59, negated_conjecture, (r2_orders_2(esk2_0,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_27]), c_0_46])])).
% 0.20/0.57  cnf(c_0_60, plain, (X1!=X2|~r2_orders_2(X3,X1,X2)|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.57  cnf(c_0_61, negated_conjecture, (esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0))=esk3_0|r2_orders_2(esk2_0,esk3_0,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)))|~r1_orders_2(esk2_0,esk3_0,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)))), inference(spm,[status(thm)],[c_0_55, c_0_21])).
% 0.20/0.57  cnf(c_0_62, negated_conjecture, (r1_orders_2(esk2_0,esk3_0,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57])])).
% 0.20/0.57  cnf(c_0_63, negated_conjecture, (~r2_orders_2(esk2_0,esk3_0,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59])])).
% 0.20/0.57  cnf(c_0_64, plain, (~r2_orders_2(X1,X2,X2)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_60])).
% 0.20/0.57  cnf(c_0_65, negated_conjecture, (esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0))=esk3_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62])]), c_0_63])).
% 0.20/0.57  cnf(c_0_66, negated_conjecture, (~r2_orders_2(esk2_0,esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_21]), c_0_18])])).
% 0.20/0.57  cnf(c_0_67, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_65]), c_0_66]), ['proof']).
% 0.20/0.57  # SZS output end CNFRefutation
% 0.20/0.57  # Proof object total steps             : 68
% 0.20/0.57  # Proof object clause steps            : 49
% 0.20/0.57  # Proof object formula steps           : 19
% 0.20/0.57  # Proof object conjectures             : 39
% 0.20/0.57  # Proof object clause conjectures      : 36
% 0.20/0.57  # Proof object formula conjectures     : 3
% 0.20/0.57  # Proof object initial clauses used    : 21
% 0.20/0.57  # Proof object initial formulas used   : 9
% 0.20/0.57  # Proof object generating inferences   : 21
% 0.20/0.57  # Proof object simplifying inferences  : 65
% 0.20/0.57  # Training examples: 0 positive, 0 negative
% 0.20/0.57  # Parsed axioms                        : 9
% 0.20/0.57  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.57  # Initial clauses                      : 25
% 0.20/0.57  # Removed in clause preprocessing      : 0
% 0.20/0.57  # Initial clauses in saturation        : 25
% 0.20/0.57  # Processed clauses                    : 1126
% 0.20/0.57  # ...of these trivial                  : 0
% 0.20/0.57  # ...subsumed                          : 59
% 0.20/0.57  # ...remaining for further processing  : 1067
% 0.20/0.57  # Other redundant clauses eliminated   : 2
% 0.20/0.57  # Clauses deleted for lack of memory   : 0
% 0.20/0.57  # Backward-subsumed                    : 14
% 0.20/0.57  # Backward-rewritten                   : 569
% 0.20/0.57  # Generated clauses                    : 4946
% 0.20/0.57  # ...of the previous two non-trivial   : 5444
% 0.20/0.57  # Contextual simplify-reflections      : 7
% 0.20/0.57  # Paramodulations                      : 4944
% 0.20/0.57  # Factorizations                       : 0
% 0.20/0.57  # Equation resolutions                 : 2
% 0.20/0.57  # Propositional unsat checks           : 0
% 0.20/0.57  #    Propositional check models        : 0
% 0.20/0.57  #    Propositional check unsatisfiable : 0
% 0.20/0.57  #    Propositional clauses             : 0
% 0.20/0.57  #    Propositional clauses after purity: 0
% 0.20/0.57  #    Propositional unsat core size     : 0
% 0.20/0.57  #    Propositional preprocessing time  : 0.000
% 0.20/0.57  #    Propositional encoding time       : 0.000
% 0.20/0.57  #    Propositional solver time         : 0.000
% 0.20/0.57  #    Success case prop preproc time    : 0.000
% 0.20/0.57  #    Success case prop encoding time   : 0.000
% 0.20/0.57  #    Success case prop solver time     : 0.000
% 0.20/0.57  # Current number of processed clauses  : 482
% 0.20/0.57  #    Positive orientable unit clauses  : 24
% 0.20/0.57  #    Positive unorientable unit clauses: 0
% 0.20/0.57  #    Negative unit clauses             : 17
% 0.20/0.57  #    Non-unit-clauses                  : 441
% 0.20/0.57  # Current number of unprocessed clauses: 3808
% 0.20/0.57  # ...number of literals in the above   : 13115
% 0.20/0.57  # Current number of archived formulas  : 0
% 0.20/0.57  # Current number of archived clauses   : 583
% 0.20/0.57  # Clause-clause subsumption calls (NU) : 93535
% 0.20/0.57  # Rec. Clause-clause subsumption calls : 78033
% 0.20/0.57  # Non-unit clause-clause subsumptions  : 45
% 0.20/0.57  # Unit Clause-clause subsumption calls : 5676
% 0.20/0.57  # Rewrite failures with RHS unbound    : 0
% 0.20/0.57  # BW rewrite match attempts            : 3593
% 0.20/0.57  # BW rewrite match successes           : 5
% 0.20/0.57  # Condensation attempts                : 1126
% 0.20/0.57  # Condensation successes               : 0
% 0.20/0.57  # Termbank termtop insertions          : 295175
% 0.20/0.57  
% 0.20/0.57  # -------------------------------------------------
% 0.20/0.57  # User time                : 0.212 s
% 0.20/0.57  # System time              : 0.011 s
% 0.20/0.57  # Total time               : 0.222 s
% 0.20/0.57  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
