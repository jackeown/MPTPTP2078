%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:03 EST 2020

% Result     : Theorem 0.34s
% Output     : CNFRefutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 598 expanded)
%              Number of clauses        :   42 ( 195 expanded)
%              Number of leaves         :    9 ( 144 expanded)
%              Depth                    :   13
%              Number of atoms          :  323 (4352 expanded)
%              Number of equality atoms :   19 ( 758 expanded)
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

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

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

fof(t29_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k3_mcart_1(X3,X4,X5) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

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

fof(t30_orders_2,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ~ ( r1_orders_2(X1,X2,X3)
                  & r2_orders_2(X1,X3,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_orders_2)).

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
    ! [X17,X18,X19] :
      ( ( v6_orders_2(X19,X17)
        | ~ m2_orders_2(X19,X17,X18)
        | v2_struct_0(X17)
        | ~ v3_orders_2(X17)
        | ~ v4_orders_2(X17)
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17)
        | ~ m1_orders_1(X18,k1_orders_1(u1_struct_0(X17))) )
      & ( m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ m2_orders_2(X19,X17,X18)
        | v2_struct_0(X17)
        | ~ v3_orders_2(X17)
        | ~ v4_orders_2(X17)
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17)
        | ~ m1_orders_1(X18,k1_orders_1(u1_struct_0(X17))) ) ) ),
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
    ! [X14,X15,X16] :
      ( v2_struct_0(X14)
      | ~ v3_orders_2(X14)
      | ~ v4_orders_2(X14)
      | ~ v5_orders_2(X14)
      | ~ l1_orders_2(X14)
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
      | ~ m1_subset_1(X16,u1_struct_0(X14))
      | m1_subset_1(k3_orders_2(X14,X15,X16),k1_zfmisc_1(u1_struct_0(X14))) ) ),
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
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
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
    ! [X6,X7,X8] :
      ( ~ r2_hidden(X6,X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X8))
      | m1_subset_1(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(k3_orders_2(esk2_0,X1,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_27,plain,(
    ! [X26,X27,X28,X29] :
      ( ( r2_orders_2(X26,X27,X28)
        | ~ r2_hidden(X27,k3_orders_2(X26,X29,X28))
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | v2_struct_0(X26)
        | ~ v3_orders_2(X26)
        | ~ v4_orders_2(X26)
        | ~ v5_orders_2(X26)
        | ~ l1_orders_2(X26) )
      & ( r2_hidden(X27,X29)
        | ~ r2_hidden(X27,k3_orders_2(X26,X29,X28))
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | v2_struct_0(X26)
        | ~ v3_orders_2(X26)
        | ~ v4_orders_2(X26)
        | ~ v5_orders_2(X26)
        | ~ l1_orders_2(X26) )
      & ( ~ r2_orders_2(X26,X27,X28)
        | ~ r2_hidden(X27,X29)
        | r2_hidden(X27,k3_orders_2(X26,X29,X28))
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | v2_struct_0(X26)
        | ~ v3_orders_2(X26)
        | ~ v4_orders_2(X26)
        | ~ v5_orders_2(X26)
        | ~ l1_orders_2(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_orders_2])])])])])).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(k3_orders_2(esk2_0,esk5_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_30,plain,(
    ! [X9,X11,X12,X13] :
      ( ( r2_hidden(esk1_1(X9),X9)
        | X9 = k1_xboole_0 )
      & ( ~ r2_hidden(X11,X9)
        | esk1_1(X9) != k3_mcart_1(X11,X12,X13)
        | X9 = k1_xboole_0 )
      & ( ~ r2_hidden(X12,X9)
        | esk1_1(X9) != k3_mcart_1(X11,X12,X13)
        | X9 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).

cnf(c_0_31,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,k3_orders_2(esk2_0,esk5_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( k3_orders_2(esk2_0,esk5_0,esk3_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_35,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_36,plain,(
    ! [X30,X31,X32,X33,X34] :
      ( v2_struct_0(X30)
      | ~ v3_orders_2(X30)
      | ~ v4_orders_2(X30)
      | ~ v5_orders_2(X30)
      | ~ l1_orders_2(X30)
      | ~ m1_subset_1(X31,u1_struct_0(X30))
      | ~ m1_subset_1(X32,u1_struct_0(X30))
      | ~ m1_orders_1(X33,k1_orders_1(u1_struct_0(X30)))
      | ~ m2_orders_2(X34,X30,X33)
      | ~ r2_hidden(X31,X34)
      | X32 != k1_funct_1(X33,u1_struct_0(X30))
      | r3_orders_2(X30,X32,X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t80_orders_2])])])])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,k3_orders_2(esk2_0,X2,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_21]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

fof(c_0_39,plain,(
    ! [X23,X24,X25] :
      ( ~ v5_orders_2(X23)
      | ~ l1_orders_2(X23)
      | ~ m1_subset_1(X24,u1_struct_0(X23))
      | ~ m1_subset_1(X25,u1_struct_0(X23))
      | ~ r1_orders_2(X23,X24,X25)
      | ~ r2_orders_2(X23,X25,X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_orders_2])])])).

cnf(c_0_40,negated_conjecture,
    ( r2_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,k3_orders_2(esk2_0,X2,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_21]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

fof(c_0_41,plain,(
    ! [X20,X21,X22] :
      ( ( ~ r3_orders_2(X20,X21,X22)
        | r1_orders_2(X20,X21,X22)
        | v2_struct_0(X20)
        | ~ v3_orders_2(X20)
        | ~ l1_orders_2(X20)
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | ~ m1_subset_1(X22,u1_struct_0(X20)) )
      & ( ~ r1_orders_2(X20,X21,X22)
        | r3_orders_2(X20,X21,X22)
        | v2_struct_0(X20)
        | ~ v3_orders_2(X20)
        | ~ l1_orders_2(X20)
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | ~ m1_subset_1(X22,u1_struct_0(X20)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_42,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),k3_orders_2(esk2_0,X1,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,plain,
    ( ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r2_orders_2(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( r2_orders_2(esk2_0,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),k3_orders_2(esk2_0,X1,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_38])).

cnf(c_0_46,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,plain,
    ( r3_orders_2(X1,k1_funct_1(X2,u1_struct_0(X1)),X3)
    | v2_struct_0(X1)
    | ~ m2_orders_2(X4,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(k1_funct_1(X2,u1_struct_0(X1)),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X3,X4) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),esk5_0)
    | ~ r2_hidden(esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),k3_orders_2(esk2_0,esk5_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_26])).

cnf(c_0_49,negated_conjecture,
    ( ~ r2_orders_2(esk2_0,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),X1)
    | ~ r1_orders_2(esk2_0,X1,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_38]),c_0_15]),c_0_16])])).

cnf(c_0_50,negated_conjecture,
    ( r2_orders_2(esk2_0,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),esk3_0)
    | ~ r2_hidden(esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),k3_orders_2(esk2_0,esk5_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_26])).

cnf(c_0_51,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)))
    | ~ r3_orders_2(esk2_0,X1,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_38]),c_0_15]),c_0_18])]),c_0_19])).

cnf(c_0_52,negated_conjecture,
    ( r3_orders_2(esk2_0,k1_funct_1(X1,u1_struct_0(esk2_0)),esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)))
    | ~ m2_orders_2(X2,esk2_0,X1)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(k1_funct_1(X1,u1_struct_0(esk2_0)),u1_struct_0(esk2_0))
    | ~ r2_hidden(esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_38]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_53,negated_conjecture,
    ( esk3_0 = k1_funct_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_33]),c_0_34])).

cnf(c_0_55,negated_conjecture,
    ( ~ r2_orders_2(esk2_0,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),esk3_0)
    | ~ r1_orders_2(esk2_0,esk3_0,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_21])).

cnf(c_0_56,negated_conjecture,
    ( r2_orders_2(esk2_0,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_33]),c_0_34])).

cnf(c_0_57,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_0,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)))
    | ~ r3_orders_2(esk2_0,esk3_0,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_21])).

cnf(c_0_58,negated_conjecture,
    ( r3_orders_2(esk2_0,esk3_0,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_23]),c_0_53]),c_0_14]),c_0_53]),c_0_21]),c_0_54])])).

cnf(c_0_59,negated_conjecture,
    ( ~ r1_orders_2(esk2_0,esk3_0,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56])])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_58])]),c_0_59]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:46:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.34/0.52  # AutoSched0-Mode selected heuristic G_E___008_C18_F1_PI_SE_CS_SP_CO_S4S
% 0.34/0.52  # and selection function SelectNewComplexAHPNS.
% 0.34/0.52  #
% 0.34/0.52  # Preprocessing time       : 0.028 s
% 0.34/0.52  
% 0.34/0.52  # Proof found!
% 0.34/0.52  # SZS status Theorem
% 0.34/0.52  # SZS output start CNFRefutation
% 0.34/0.52  fof(t81_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_orders_1(X3,k1_orders_1(u1_struct_0(X1)))=>![X4]:(m2_orders_2(X4,X1,X3)=>(X2=k1_funct_1(X3,u1_struct_0(X1))=>k3_orders_2(X1,X4,X2)=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_orders_2)).
% 0.34/0.52  fof(dt_m2_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))))=>![X3]:(m2_orders_2(X3,X1,X2)=>(v6_orders_2(X3,X1)&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 0.34/0.52  fof(dt_k3_orders_2, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 0.34/0.52  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.34/0.52  fof(t57_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,k3_orders_2(X1,X4,X3))<=>(r2_orders_2(X1,X2,X3)&r2_hidden(X2,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 0.34/0.52  fof(t29_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k3_mcart_1(X3,X4,X5))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 0.34/0.52  fof(t80_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_orders_1(X4,k1_orders_1(u1_struct_0(X1)))=>![X5]:(m2_orders_2(X5,X1,X4)=>((r2_hidden(X2,X5)&X3=k1_funct_1(X4,u1_struct_0(X1)))=>r3_orders_2(X1,X3,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_orders_2)).
% 0.34/0.52  fof(t30_orders_2, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r1_orders_2(X1,X2,X3)&r2_orders_2(X1,X3,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_orders_2)).
% 0.34/0.52  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.34/0.52  fof(c_0_9, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_orders_1(X3,k1_orders_1(u1_struct_0(X1)))=>![X4]:(m2_orders_2(X4,X1,X3)=>(X2=k1_funct_1(X3,u1_struct_0(X1))=>k3_orders_2(X1,X4,X2)=k1_xboole_0)))))), inference(assume_negation,[status(cth)],[t81_orders_2])).
% 0.34/0.52  fof(c_0_10, plain, ![X17, X18, X19]:((v6_orders_2(X19,X17)|~m2_orders_2(X19,X17,X18)|(v2_struct_0(X17)|~v3_orders_2(X17)|~v4_orders_2(X17)|~v5_orders_2(X17)|~l1_orders_2(X17)|~m1_orders_1(X18,k1_orders_1(u1_struct_0(X17)))))&(m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))|~m2_orders_2(X19,X17,X18)|(v2_struct_0(X17)|~v3_orders_2(X17)|~v4_orders_2(X17)|~v5_orders_2(X17)|~l1_orders_2(X17)|~m1_orders_1(X18,k1_orders_1(u1_struct_0(X17)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_orders_2])])])])])).
% 0.34/0.52  fof(c_0_11, negated_conjecture, (((((~v2_struct_0(esk2_0)&v3_orders_2(esk2_0))&v4_orders_2(esk2_0))&v5_orders_2(esk2_0))&l1_orders_2(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&(m1_orders_1(esk4_0,k1_orders_1(u1_struct_0(esk2_0)))&(m2_orders_2(esk5_0,esk2_0,esk4_0)&(esk3_0=k1_funct_1(esk4_0,u1_struct_0(esk2_0))&k3_orders_2(esk2_0,esk5_0,esk3_0)!=k1_xboole_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).
% 0.34/0.52  fof(c_0_12, plain, ![X14, X15, X16]:(v2_struct_0(X14)|~v3_orders_2(X14)|~v4_orders_2(X14)|~v5_orders_2(X14)|~l1_orders_2(X14)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|~m1_subset_1(X16,u1_struct_0(X14))|m1_subset_1(k3_orders_2(X14,X15,X16),k1_zfmisc_1(u1_struct_0(X14)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_orders_2])])])).
% 0.34/0.52  cnf(c_0_13, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|v2_struct_0(X2)|~m2_orders_2(X1,X2,X3)|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.34/0.52  cnf(c_0_14, negated_conjecture, (m1_orders_1(esk4_0,k1_orders_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.34/0.52  cnf(c_0_15, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.34/0.52  cnf(c_0_16, negated_conjecture, (v5_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.34/0.52  cnf(c_0_17, negated_conjecture, (v4_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.34/0.52  cnf(c_0_18, negated_conjecture, (v3_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.34/0.52  cnf(c_0_19, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.34/0.52  cnf(c_0_20, plain, (v2_struct_0(X1)|m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.34/0.52  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.34/0.52  cnf(c_0_22, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m2_orders_2(X1,esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15]), c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 0.34/0.52  cnf(c_0_23, negated_conjecture, (m2_orders_2(esk5_0,esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.34/0.52  fof(c_0_24, plain, ![X6, X7, X8]:(~r2_hidden(X6,X7)|~m1_subset_1(X7,k1_zfmisc_1(X8))|m1_subset_1(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.34/0.52  cnf(c_0_25, negated_conjecture, (m1_subset_1(k3_orders_2(esk2_0,X1,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_15]), c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 0.34/0.52  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.34/0.52  fof(c_0_27, plain, ![X26, X27, X28, X29]:(((r2_orders_2(X26,X27,X28)|~r2_hidden(X27,k3_orders_2(X26,X29,X28))|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X26)))|~m1_subset_1(X28,u1_struct_0(X26))|~m1_subset_1(X27,u1_struct_0(X26))|(v2_struct_0(X26)|~v3_orders_2(X26)|~v4_orders_2(X26)|~v5_orders_2(X26)|~l1_orders_2(X26)))&(r2_hidden(X27,X29)|~r2_hidden(X27,k3_orders_2(X26,X29,X28))|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X26)))|~m1_subset_1(X28,u1_struct_0(X26))|~m1_subset_1(X27,u1_struct_0(X26))|(v2_struct_0(X26)|~v3_orders_2(X26)|~v4_orders_2(X26)|~v5_orders_2(X26)|~l1_orders_2(X26))))&(~r2_orders_2(X26,X27,X28)|~r2_hidden(X27,X29)|r2_hidden(X27,k3_orders_2(X26,X29,X28))|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X26)))|~m1_subset_1(X28,u1_struct_0(X26))|~m1_subset_1(X27,u1_struct_0(X26))|(v2_struct_0(X26)|~v3_orders_2(X26)|~v4_orders_2(X26)|~v5_orders_2(X26)|~l1_orders_2(X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_orders_2])])])])])).
% 0.34/0.52  cnf(c_0_28, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.34/0.52  cnf(c_0_29, negated_conjecture, (m1_subset_1(k3_orders_2(esk2_0,esk5_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.34/0.52  fof(c_0_30, plain, ![X9, X11, X12, X13]:((r2_hidden(esk1_1(X9),X9)|X9=k1_xboole_0)&((~r2_hidden(X11,X9)|esk1_1(X9)!=k3_mcart_1(X11,X12,X13)|X9=k1_xboole_0)&(~r2_hidden(X12,X9)|esk1_1(X9)!=k3_mcart_1(X11,X12,X13)|X9=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).
% 0.34/0.52  cnf(c_0_31, plain, (r2_hidden(X1,X2)|v2_struct_0(X3)|~r2_hidden(X1,k3_orders_2(X3,X2,X4))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X4,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~v3_orders_2(X3)|~v4_orders_2(X3)|~v5_orders_2(X3)|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.34/0.52  cnf(c_0_32, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,k3_orders_2(esk2_0,esk5_0,esk3_0))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.34/0.52  cnf(c_0_33, plain, (r2_hidden(esk1_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.34/0.52  cnf(c_0_34, negated_conjecture, (k3_orders_2(esk2_0,esk5_0,esk3_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.34/0.52  cnf(c_0_35, plain, (r2_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r2_hidden(X2,k3_orders_2(X1,X4,X3))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.34/0.52  fof(c_0_36, plain, ![X30, X31, X32, X33, X34]:(v2_struct_0(X30)|~v3_orders_2(X30)|~v4_orders_2(X30)|~v5_orders_2(X30)|~l1_orders_2(X30)|(~m1_subset_1(X31,u1_struct_0(X30))|(~m1_subset_1(X32,u1_struct_0(X30))|(~m1_orders_1(X33,k1_orders_1(u1_struct_0(X30)))|(~m2_orders_2(X34,X30,X33)|(~r2_hidden(X31,X34)|X32!=k1_funct_1(X33,u1_struct_0(X30))|r3_orders_2(X30,X32,X31))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t80_orders_2])])])])).
% 0.34/0.52  cnf(c_0_37, negated_conjecture, (r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,k3_orders_2(esk2_0,X2,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_21]), c_0_15]), c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 0.34/0.52  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])).
% 0.34/0.52  fof(c_0_39, plain, ![X23, X24, X25]:(~v5_orders_2(X23)|~l1_orders_2(X23)|(~m1_subset_1(X24,u1_struct_0(X23))|(~m1_subset_1(X25,u1_struct_0(X23))|(~r1_orders_2(X23,X24,X25)|~r2_orders_2(X23,X25,X24))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_orders_2])])])).
% 0.34/0.52  cnf(c_0_40, negated_conjecture, (r2_orders_2(esk2_0,X1,esk3_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,k3_orders_2(esk2_0,X2,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_21]), c_0_15]), c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 0.34/0.52  fof(c_0_41, plain, ![X20, X21, X22]:((~r3_orders_2(X20,X21,X22)|r1_orders_2(X20,X21,X22)|(v2_struct_0(X20)|~v3_orders_2(X20)|~l1_orders_2(X20)|~m1_subset_1(X21,u1_struct_0(X20))|~m1_subset_1(X22,u1_struct_0(X20))))&(~r1_orders_2(X20,X21,X22)|r3_orders_2(X20,X21,X22)|(v2_struct_0(X20)|~v3_orders_2(X20)|~l1_orders_2(X20)|~m1_subset_1(X21,u1_struct_0(X20))|~m1_subset_1(X22,u1_struct_0(X20))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.34/0.52  cnf(c_0_42, plain, (v2_struct_0(X1)|r3_orders_2(X1,X3,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_orders_1(X4,k1_orders_1(u1_struct_0(X1)))|~m2_orders_2(X5,X1,X4)|~r2_hidden(X2,X5)|X3!=k1_funct_1(X4,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.34/0.52  cnf(c_0_43, negated_conjecture, (r2_hidden(esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),k3_orders_2(esk2_0,X1,esk3_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.34/0.52  cnf(c_0_44, plain, (~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~r1_orders_2(X1,X2,X3)|~r2_orders_2(X1,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.34/0.52  cnf(c_0_45, negated_conjecture, (r2_orders_2(esk2_0,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),k3_orders_2(esk2_0,X1,esk3_0))), inference(spm,[status(thm)],[c_0_40, c_0_38])).
% 0.34/0.52  cnf(c_0_46, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r3_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.34/0.52  cnf(c_0_47, plain, (r3_orders_2(X1,k1_funct_1(X2,u1_struct_0(X1)),X3)|v2_struct_0(X1)|~m2_orders_2(X4,X1,X2)|~m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(k1_funct_1(X2,u1_struct_0(X1)),u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~r2_hidden(X3,X4)), inference(er,[status(thm)],[c_0_42])).
% 0.34/0.52  cnf(c_0_48, negated_conjecture, (r2_hidden(esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),esk5_0)|~r2_hidden(esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),k3_orders_2(esk2_0,esk5_0,esk3_0))), inference(spm,[status(thm)],[c_0_43, c_0_26])).
% 0.34/0.52  cnf(c_0_49, negated_conjecture, (~r2_orders_2(esk2_0,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),X1)|~r1_orders_2(esk2_0,X1,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_38]), c_0_15]), c_0_16])])).
% 0.34/0.52  cnf(c_0_50, negated_conjecture, (r2_orders_2(esk2_0,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),esk3_0)|~r2_hidden(esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),k3_orders_2(esk2_0,esk5_0,esk3_0))), inference(spm,[status(thm)],[c_0_45, c_0_26])).
% 0.34/0.52  cnf(c_0_51, negated_conjecture, (r1_orders_2(esk2_0,X1,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)))|~r3_orders_2(esk2_0,X1,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_38]), c_0_15]), c_0_18])]), c_0_19])).
% 0.34/0.52  cnf(c_0_52, negated_conjecture, (r3_orders_2(esk2_0,k1_funct_1(X1,u1_struct_0(esk2_0)),esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)))|~m2_orders_2(X2,esk2_0,X1)|~m1_orders_1(X1,k1_orders_1(u1_struct_0(esk2_0)))|~m1_subset_1(k1_funct_1(X1,u1_struct_0(esk2_0)),u1_struct_0(esk2_0))|~r2_hidden(esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_38]), c_0_15]), c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 0.34/0.52  cnf(c_0_53, negated_conjecture, (esk3_0=k1_funct_1(esk4_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.34/0.52  cnf(c_0_54, negated_conjecture, (r2_hidden(esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_33]), c_0_34])).
% 0.34/0.52  cnf(c_0_55, negated_conjecture, (~r2_orders_2(esk2_0,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),esk3_0)|~r1_orders_2(esk2_0,esk3_0,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)))), inference(spm,[status(thm)],[c_0_49, c_0_21])).
% 0.34/0.52  cnf(c_0_56, negated_conjecture, (r2_orders_2(esk2_0,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_33]), c_0_34])).
% 0.34/0.52  cnf(c_0_57, negated_conjecture, (r1_orders_2(esk2_0,esk3_0,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)))|~r3_orders_2(esk2_0,esk3_0,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)))), inference(spm,[status(thm)],[c_0_51, c_0_21])).
% 0.34/0.52  cnf(c_0_58, negated_conjecture, (r3_orders_2(esk2_0,esk3_0,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_23]), c_0_53]), c_0_14]), c_0_53]), c_0_21]), c_0_54])])).
% 0.34/0.52  cnf(c_0_59, negated_conjecture, (~r1_orders_2(esk2_0,esk3_0,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_56])])).
% 0.34/0.52  cnf(c_0_60, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_58])]), c_0_59]), ['proof']).
% 0.34/0.52  # SZS output end CNFRefutation
% 0.34/0.52  # Proof object total steps             : 61
% 0.34/0.52  # Proof object clause steps            : 42
% 0.34/0.52  # Proof object formula steps           : 19
% 0.34/0.52  # Proof object conjectures             : 35
% 0.34/0.52  # Proof object clause conjectures      : 32
% 0.34/0.52  # Proof object formula conjectures     : 3
% 0.34/0.52  # Proof object initial clauses used    : 19
% 0.34/0.52  # Proof object initial formulas used   : 9
% 0.34/0.52  # Proof object generating inferences   : 20
% 0.34/0.52  # Proof object simplifying inferences  : 52
% 0.34/0.52  # Training examples: 0 positive, 0 negative
% 0.34/0.52  # Parsed axioms                        : 9
% 0.34/0.52  # Removed by relevancy pruning/SinE    : 0
% 0.34/0.52  # Initial clauses                      : 24
% 0.34/0.52  # Removed in clause preprocessing      : 0
% 0.34/0.52  # Initial clauses in saturation        : 24
% 0.34/0.52  # Processed clauses                    : 727
% 0.34/0.52  # ...of these trivial                  : 0
% 0.34/0.52  # ...subsumed                          : 3
% 0.34/0.52  # ...remaining for further processing  : 724
% 0.34/0.52  # Other redundant clauses eliminated   : 1
% 0.34/0.52  # Clauses deleted for lack of memory   : 0
% 0.34/0.52  # Backward-subsumed                    : 3
% 0.34/0.52  # Backward-rewritten                   : 6
% 0.34/0.52  # Generated clauses                    : 4751
% 0.34/0.52  # ...of the previous two non-trivial   : 4751
% 0.34/0.52  # Contextual simplify-reflections      : 3
% 0.34/0.52  # Paramodulations                      : 4750
% 0.34/0.52  # Factorizations                       : 0
% 0.34/0.52  # Equation resolutions                 : 1
% 0.34/0.52  # Propositional unsat checks           : 0
% 0.34/0.52  #    Propositional check models        : 0
% 0.34/0.52  #    Propositional check unsatisfiable : 0
% 0.34/0.52  #    Propositional clauses             : 0
% 0.34/0.52  #    Propositional clauses after purity: 0
% 0.34/0.52  #    Propositional unsat core size     : 0
% 0.34/0.52  #    Propositional preprocessing time  : 0.000
% 0.34/0.52  #    Propositional encoding time       : 0.000
% 0.34/0.52  #    Propositional solver time         : 0.000
% 0.34/0.52  #    Success case prop preproc time    : 0.000
% 0.34/0.52  #    Success case prop encoding time   : 0.000
% 0.34/0.52  #    Success case prop solver time     : 0.000
% 0.34/0.52  # Current number of processed clauses  : 714
% 0.34/0.52  #    Positive orientable unit clauses  : 58
% 0.34/0.52  #    Positive unorientable unit clauses: 0
% 0.34/0.52  #    Negative unit clauses             : 3
% 0.34/0.52  #    Non-unit-clauses                  : 653
% 0.34/0.52  # Current number of unprocessed clauses: 4032
% 0.34/0.52  # ...number of literals in the above   : 13881
% 0.34/0.52  # Current number of archived formulas  : 0
% 0.34/0.52  # Current number of archived clauses   : 9
% 0.34/0.52  # Clause-clause subsumption calls (NU) : 51429
% 0.34/0.52  # Rec. Clause-clause subsumption calls : 29591
% 0.34/0.52  # Non-unit clause-clause subsumptions  : 9
% 0.34/0.52  # Unit Clause-clause subsumption calls : 1032
% 0.34/0.52  # Rewrite failures with RHS unbound    : 0
% 0.34/0.52  # BW rewrite match attempts            : 2007
% 0.34/0.52  # BW rewrite match successes           : 3
% 0.34/0.52  # Condensation attempts                : 727
% 0.34/0.52  # Condensation successes               : 0
% 0.34/0.52  # Termbank termtop insertions          : 268936
% 0.34/0.52  
% 0.34/0.52  # -------------------------------------------------
% 0.34/0.52  # User time                : 0.159 s
% 0.34/0.52  # System time              : 0.009 s
% 0.34/0.52  # Total time               : 0.168 s
% 0.34/0.52  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
