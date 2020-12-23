%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:59 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   56 (1831 expanded)
%              Number of clauses        :   41 ( 608 expanded)
%              Number of leaves         :    7 ( 440 expanded)
%              Depth                    :   12
%              Number of atoms          :  386 (17739 expanded)
%              Number of equality atoms :   53 (3581 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal clause size      :   62 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d15_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( X2 != k1_xboole_0
                 => ( m1_orders_2(X3,X1,X2)
                  <=> ? [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                        & r2_hidden(X4,X2)
                        & X3 = k3_orders_2(X1,X2,X4) ) ) )
                & ( X2 = k1_xboole_0
                 => ( m1_orders_2(X3,X1,X2)
                  <=> X3 = k1_xboole_0 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_orders_2)).

fof(dt_m1_orders_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ! [X3] :
          ( m1_orders_2(X3,X1,X2)
         => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_orders_2)).

fof(t68_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ~ ( X2 != k1_xboole_0
                & m1_orders_2(X2,X1,X2) )
            & ~ ( ~ m1_orders_2(X2,X1,X2)
                & X2 = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_orders_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).

fof(reflexivity_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => r3_orders_2(X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_orders_2)).

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

fof(c_0_7,plain,(
    ! [X5,X6,X7,X9] :
      ( ( m1_subset_1(esk1_3(X5,X6,X7),u1_struct_0(X5))
        | ~ m1_orders_2(X7,X5,X6)
        | X6 = k1_xboole_0
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | v2_struct_0(X5)
        | ~ v3_orders_2(X5)
        | ~ v4_orders_2(X5)
        | ~ v5_orders_2(X5)
        | ~ l1_orders_2(X5) )
      & ( r2_hidden(esk1_3(X5,X6,X7),X6)
        | ~ m1_orders_2(X7,X5,X6)
        | X6 = k1_xboole_0
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | v2_struct_0(X5)
        | ~ v3_orders_2(X5)
        | ~ v4_orders_2(X5)
        | ~ v5_orders_2(X5)
        | ~ l1_orders_2(X5) )
      & ( X7 = k3_orders_2(X5,X6,esk1_3(X5,X6,X7))
        | ~ m1_orders_2(X7,X5,X6)
        | X6 = k1_xboole_0
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | v2_struct_0(X5)
        | ~ v3_orders_2(X5)
        | ~ v4_orders_2(X5)
        | ~ v5_orders_2(X5)
        | ~ l1_orders_2(X5) )
      & ( ~ m1_subset_1(X9,u1_struct_0(X5))
        | ~ r2_hidden(X9,X6)
        | X7 != k3_orders_2(X5,X6,X9)
        | m1_orders_2(X7,X5,X6)
        | X6 = k1_xboole_0
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | v2_struct_0(X5)
        | ~ v3_orders_2(X5)
        | ~ v4_orders_2(X5)
        | ~ v5_orders_2(X5)
        | ~ l1_orders_2(X5) )
      & ( ~ m1_orders_2(X7,X5,X6)
        | X7 = k1_xboole_0
        | X6 != k1_xboole_0
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | v2_struct_0(X5)
        | ~ v3_orders_2(X5)
        | ~ v4_orders_2(X5)
        | ~ v5_orders_2(X5)
        | ~ l1_orders_2(X5) )
      & ( X7 != k1_xboole_0
        | m1_orders_2(X7,X5,X6)
        | X6 != k1_xboole_0
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | v2_struct_0(X5)
        | ~ v3_orders_2(X5)
        | ~ v4_orders_2(X5)
        | ~ v5_orders_2(X5)
        | ~ l1_orders_2(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d15_orders_2])])])])])])).

fof(c_0_8,plain,(
    ! [X10,X11,X12] :
      ( v2_struct_0(X10)
      | ~ v3_orders_2(X10)
      | ~ v4_orders_2(X10)
      | ~ v5_orders_2(X10)
      | ~ l1_orders_2(X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
      | ~ m1_orders_2(X12,X10,X11)
      | m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_orders_2])])])])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( ~ ( X2 != k1_xboole_0
                  & m1_orders_2(X2,X1,X2) )
              & ~ ( ~ m1_orders_2(X2,X1,X2)
                  & X2 = k1_xboole_0 ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t68_orders_2])).

cnf(c_0_10,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | X2 = k1_xboole_0
    | v2_struct_0(X1)
    | ~ m1_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_orders_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v3_orders_2(esk2_0)
    & v4_orders_2(esk2_0)
    & v5_orders_2(esk2_0)
    & l1_orders_2(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ( ~ m1_orders_2(esk3_0,esk2_0,esk3_0)
      | esk3_0 != k1_xboole_0 )
    & ( esk3_0 = k1_xboole_0
      | esk3_0 != k1_xboole_0 )
    & ( ~ m1_orders_2(esk3_0,esk2_0,esk3_0)
      | m1_orders_2(esk3_0,esk2_0,esk3_0) )
    & ( esk3_0 = k1_xboole_0
      | m1_orders_2(esk3_0,esk2_0,esk3_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])).

cnf(c_0_13,plain,
    ( X1 = k1_xboole_0
    | m1_subset_1(esk1_3(X2,X1,X3),u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ m1_orders_2(X3,X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_20,plain,(
    ! [X22,X23,X24,X25] :
      ( ( r2_orders_2(X22,X23,X24)
        | ~ r2_hidden(X23,k3_orders_2(X22,X25,X24))
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | v2_struct_0(X22)
        | ~ v3_orders_2(X22)
        | ~ v4_orders_2(X22)
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) )
      & ( r2_hidden(X23,X25)
        | ~ r2_hidden(X23,k3_orders_2(X22,X25,X24))
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | v2_struct_0(X22)
        | ~ v3_orders_2(X22)
        | ~ v4_orders_2(X22)
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) )
      & ( ~ r2_orders_2(X22,X23,X24)
        | ~ r2_hidden(X23,X25)
        | r2_hidden(X23,k3_orders_2(X22,X25,X24))
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | v2_struct_0(X22)
        | ~ v3_orders_2(X22)
        | ~ v4_orders_2(X22)
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_orders_2])])])])])).

cnf(c_0_21,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | m1_subset_1(esk1_3(esk2_0,esk3_0,X1),u1_struct_0(esk2_0))
    | ~ m1_orders_2(X1,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | m1_orders_2(esk3_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk3_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,plain,
    ( X1 = k3_orders_2(X2,X3,esk1_3(X2,X3,X1))
    | X3 = k1_xboole_0
    | v2_struct_0(X2)
    | ~ m1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_26,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | X2 = k1_xboole_0
    | v2_struct_0(X1)
    | ~ m1_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_27,plain,(
    ! [X16,X17,X18] :
      ( v2_struct_0(X16)
      | ~ v3_orders_2(X16)
      | ~ l1_orders_2(X16)
      | ~ m1_subset_1(X17,u1_struct_0(X16))
      | ~ m1_subset_1(X18,u1_struct_0(X16))
      | r3_orders_2(X16,X17,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).

fof(c_0_28,plain,(
    ! [X19,X20,X21] :
      ( ~ v5_orders_2(X19)
      | ~ l1_orders_2(X19)
      | ~ m1_subset_1(X20,u1_struct_0(X19))
      | ~ m1_subset_1(X21,u1_struct_0(X19))
      | ~ r1_orders_2(X19,X20,X21)
      | ~ r2_orders_2(X19,X21,X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_orders_2])])])).

cnf(c_0_29,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r2_orders_2(esk2_0,X1,esk1_3(esk2_0,esk3_0,esk3_0))
    | ~ r2_hidden(X1,k3_orders_2(esk2_0,X2,esk1_3(esk2_0,esk3_0,esk3_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_30,plain,
    ( k3_orders_2(X1,X2,esk1_3(X1,X2,X3)) = X3
    | X2 = k1_xboole_0
    | v2_struct_0(X1)
    | ~ m1_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[c_0_25,c_0_11])).

cnf(c_0_31,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_3(X2,X1,X3),X1)
    | v2_struct_0(X2)
    | ~ m1_orders_2(X3,X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_26,c_0_11])).

fof(c_0_32,plain,(
    ! [X13,X14,X15] :
      ( ( ~ r3_orders_2(X13,X14,X15)
        | r1_orders_2(X13,X14,X15)
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ l1_orders_2(X13)
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | ~ m1_subset_1(X15,u1_struct_0(X13)) )
      & ( ~ r1_orders_2(X13,X14,X15)
        | r3_orders_2(X13,X14,X15)
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ l1_orders_2(X13)
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | ~ m1_subset_1(X15,u1_struct_0(X13)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_33,plain,
    ( v2_struct_0(X1)
    | r3_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r2_orders_2(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r2_orders_2(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0),esk1_3(esk2_0,esk3_0,esk3_0))
    | ~ r2_hidden(esk1_3(esk2_0,esk3_0,esk3_0),k3_orders_2(esk2_0,X1,esk1_3(esk2_0,esk3_0,esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_24])).

cnf(c_0_36,negated_conjecture,
    ( k3_orders_2(esk2_0,esk3_0,esk1_3(esk2_0,esk3_0,X1)) = X1
    | esk3_0 = k1_xboole_0
    | ~ m1_orders_2(X1,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_37,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r2_hidden(esk1_3(esk2_0,esk3_0,X1),esk3_0)
    | ~ m1_orders_2(X1,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_38,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r3_orders_2(esk2_0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_24]),c_0_15]),c_0_18])]),c_0_19])).

cnf(c_0_40,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ r2_orders_2(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0),X1)
    | ~ r1_orders_2(esk2_0,X1,esk1_3(esk2_0,esk3_0,esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_24]),c_0_15]),c_0_16])])).

cnf(c_0_41,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r2_orders_2(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0),esk1_3(esk2_0,esk3_0,esk3_0))
    | ~ r2_hidden(esk1_3(esk2_0,esk3_0,esk3_0),k3_orders_2(esk2_0,esk3_0,esk1_3(esk2_0,esk3_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_14])).

cnf(c_0_42,negated_conjecture,
    ( k3_orders_2(esk2_0,esk3_0,esk1_3(esk2_0,esk3_0,esk3_0)) = esk3_0
    | esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_22])).

cnf(c_0_43,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r2_hidden(esk1_3(esk2_0,esk3_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_22])).

cnf(c_0_44,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r1_orders_2(esk2_0,X1,esk1_3(esk2_0,esk3_0,esk3_0))
    | ~ r3_orders_2(esk2_0,X1,esk1_3(esk2_0,esk3_0,esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_24]),c_0_15]),c_0_18])]),c_0_19])).

cnf(c_0_45,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r3_orders_2(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0),esk1_3(esk2_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_24])).

cnf(c_0_46,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ r2_orders_2(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0),esk1_3(esk2_0,esk3_0,esk3_0))
    | ~ r1_orders_2(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0),esk1_3(esk2_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_24])).

cnf(c_0_47,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r2_orders_2(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0),esk1_3(esk2_0,esk3_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r1_orders_2(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0),esk1_3(esk2_0,esk3_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_24]),c_0_45])).

cnf(c_0_49,plain,
    ( m1_orders_2(X1,X2,X3)
    | v2_struct_0(X2)
    | X1 != k1_xboole_0
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_50,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( ~ m1_orders_2(esk3_0,esk2_0,esk3_0)
    | esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_52,plain,
    ( m1_orders_2(k1_xboole_0,X1,k1_xboole_0)
    | v2_struct_0(X1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_49])])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(rw,[status(thm)],[c_0_14,c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( ~ m1_orders_2(k1_xboole_0,esk2_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_50]),c_0_50]),c_0_50])])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_54]),c_0_19]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:54:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.12/0.37  # and selection function SelectNewComplexAHP.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.028 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(d15_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((X2!=k1_xboole_0=>(m1_orders_2(X3,X1,X2)<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X1))&r2_hidden(X4,X2))&X3=k3_orders_2(X1,X2,X4))))&(X2=k1_xboole_0=>(m1_orders_2(X3,X1,X2)<=>X3=k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d15_orders_2)).
% 0.12/0.37  fof(dt_m1_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_orders_2(X3,X1,X2)=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_orders_2)).
% 0.12/0.37  fof(t68_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(~((X2!=k1_xboole_0&m1_orders_2(X2,X1,X2)))&~((~(m1_orders_2(X2,X1,X2))&X2=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_orders_2)).
% 0.12/0.37  fof(t57_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,k3_orders_2(X1,X4,X3))<=>(r2_orders_2(X1,X2,X3)&r2_hidden(X2,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_orders_2)).
% 0.12/0.37  fof(reflexivity_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>r3_orders_2(X1,X2,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r3_orders_2)).
% 0.12/0.37  fof(t30_orders_2, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r1_orders_2(X1,X2,X3)&r2_orders_2(X1,X3,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_orders_2)).
% 0.12/0.37  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.12/0.37  fof(c_0_7, plain, ![X5, X6, X7, X9]:(((((m1_subset_1(esk1_3(X5,X6,X7),u1_struct_0(X5))|~m1_orders_2(X7,X5,X6)|X6=k1_xboole_0|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X5)))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|(v2_struct_0(X5)|~v3_orders_2(X5)|~v4_orders_2(X5)|~v5_orders_2(X5)|~l1_orders_2(X5)))&(r2_hidden(esk1_3(X5,X6,X7),X6)|~m1_orders_2(X7,X5,X6)|X6=k1_xboole_0|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X5)))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|(v2_struct_0(X5)|~v3_orders_2(X5)|~v4_orders_2(X5)|~v5_orders_2(X5)|~l1_orders_2(X5))))&(X7=k3_orders_2(X5,X6,esk1_3(X5,X6,X7))|~m1_orders_2(X7,X5,X6)|X6=k1_xboole_0|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X5)))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|(v2_struct_0(X5)|~v3_orders_2(X5)|~v4_orders_2(X5)|~v5_orders_2(X5)|~l1_orders_2(X5))))&(~m1_subset_1(X9,u1_struct_0(X5))|~r2_hidden(X9,X6)|X7!=k3_orders_2(X5,X6,X9)|m1_orders_2(X7,X5,X6)|X6=k1_xboole_0|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X5)))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|(v2_struct_0(X5)|~v3_orders_2(X5)|~v4_orders_2(X5)|~v5_orders_2(X5)|~l1_orders_2(X5))))&((~m1_orders_2(X7,X5,X6)|X7=k1_xboole_0|X6!=k1_xboole_0|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X5)))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|(v2_struct_0(X5)|~v3_orders_2(X5)|~v4_orders_2(X5)|~v5_orders_2(X5)|~l1_orders_2(X5)))&(X7!=k1_xboole_0|m1_orders_2(X7,X5,X6)|X6!=k1_xboole_0|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X5)))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|(v2_struct_0(X5)|~v3_orders_2(X5)|~v4_orders_2(X5)|~v5_orders_2(X5)|~l1_orders_2(X5))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d15_orders_2])])])])])])).
% 0.12/0.37  fof(c_0_8, plain, ![X10, X11, X12]:(v2_struct_0(X10)|~v3_orders_2(X10)|~v4_orders_2(X10)|~v5_orders_2(X10)|~l1_orders_2(X10)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|(~m1_orders_2(X12,X10,X11)|m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_orders_2])])])])).
% 0.12/0.37  fof(c_0_9, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(~((X2!=k1_xboole_0&m1_orders_2(X2,X1,X2)))&~((~(m1_orders_2(X2,X1,X2))&X2=k1_xboole_0)))))), inference(assume_negation,[status(cth)],[t68_orders_2])).
% 0.12/0.37  cnf(c_0_10, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|X2=k1_xboole_0|v2_struct_0(X1)|~m1_orders_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_11, plain, (v2_struct_0(X1)|m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_orders_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  fof(c_0_12, negated_conjecture, (((((~v2_struct_0(esk2_0)&v3_orders_2(esk2_0))&v4_orders_2(esk2_0))&v5_orders_2(esk2_0))&l1_orders_2(esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(((~m1_orders_2(esk3_0,esk2_0,esk3_0)|esk3_0!=k1_xboole_0)&(esk3_0=k1_xboole_0|esk3_0!=k1_xboole_0))&((~m1_orders_2(esk3_0,esk2_0,esk3_0)|m1_orders_2(esk3_0,esk2_0,esk3_0))&(esk3_0=k1_xboole_0|m1_orders_2(esk3_0,esk2_0,esk3_0)))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])).
% 0.12/0.37  cnf(c_0_13, plain, (X1=k1_xboole_0|m1_subset_1(esk1_3(X2,X1,X3),u1_struct_0(X2))|v2_struct_0(X2)|~m1_orders_2(X3,X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_orders_2(X2)|~v5_orders_2(X2)|~v4_orders_2(X2)|~v3_orders_2(X2)), inference(csr,[status(thm)],[c_0_10, c_0_11])).
% 0.12/0.37  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_15, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_16, negated_conjecture, (v5_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_17, negated_conjecture, (v4_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_18, negated_conjecture, (v3_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_19, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  fof(c_0_20, plain, ![X22, X23, X24, X25]:(((r2_orders_2(X22,X23,X24)|~r2_hidden(X23,k3_orders_2(X22,X25,X24))|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X22)))|~m1_subset_1(X24,u1_struct_0(X22))|~m1_subset_1(X23,u1_struct_0(X22))|(v2_struct_0(X22)|~v3_orders_2(X22)|~v4_orders_2(X22)|~v5_orders_2(X22)|~l1_orders_2(X22)))&(r2_hidden(X23,X25)|~r2_hidden(X23,k3_orders_2(X22,X25,X24))|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X22)))|~m1_subset_1(X24,u1_struct_0(X22))|~m1_subset_1(X23,u1_struct_0(X22))|(v2_struct_0(X22)|~v3_orders_2(X22)|~v4_orders_2(X22)|~v5_orders_2(X22)|~l1_orders_2(X22))))&(~r2_orders_2(X22,X23,X24)|~r2_hidden(X23,X25)|r2_hidden(X23,k3_orders_2(X22,X25,X24))|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X22)))|~m1_subset_1(X24,u1_struct_0(X22))|~m1_subset_1(X23,u1_struct_0(X22))|(v2_struct_0(X22)|~v3_orders_2(X22)|~v4_orders_2(X22)|~v5_orders_2(X22)|~l1_orders_2(X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_orders_2])])])])])).
% 0.12/0.37  cnf(c_0_21, negated_conjecture, (esk3_0=k1_xboole_0|m1_subset_1(esk1_3(esk2_0,esk3_0,X1),u1_struct_0(esk2_0))|~m1_orders_2(X1,esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15]), c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 0.12/0.37  cnf(c_0_22, negated_conjecture, (esk3_0=k1_xboole_0|m1_orders_2(esk3_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_23, plain, (r2_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r2_hidden(X2,k3_orders_2(X1,X4,X3))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.37  cnf(c_0_24, negated_conjecture, (esk3_0=k1_xboole_0|m1_subset_1(esk1_3(esk2_0,esk3_0,esk3_0),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.12/0.37  cnf(c_0_25, plain, (X1=k3_orders_2(X2,X3,esk1_3(X2,X3,X1))|X3=k1_xboole_0|v2_struct_0(X2)|~m1_orders_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_26, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|X2=k1_xboole_0|v2_struct_0(X1)|~m1_orders_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  fof(c_0_27, plain, ![X16, X17, X18]:(v2_struct_0(X16)|~v3_orders_2(X16)|~l1_orders_2(X16)|~m1_subset_1(X17,u1_struct_0(X16))|~m1_subset_1(X18,u1_struct_0(X16))|r3_orders_2(X16,X17,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).
% 0.12/0.37  fof(c_0_28, plain, ![X19, X20, X21]:(~v5_orders_2(X19)|~l1_orders_2(X19)|(~m1_subset_1(X20,u1_struct_0(X19))|(~m1_subset_1(X21,u1_struct_0(X19))|(~r1_orders_2(X19,X20,X21)|~r2_orders_2(X19,X21,X20))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_orders_2])])])).
% 0.12/0.37  cnf(c_0_29, negated_conjecture, (esk3_0=k1_xboole_0|r2_orders_2(esk2_0,X1,esk1_3(esk2_0,esk3_0,esk3_0))|~r2_hidden(X1,k3_orders_2(esk2_0,X2,esk1_3(esk2_0,esk3_0,esk3_0)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_15]), c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 0.12/0.37  cnf(c_0_30, plain, (k3_orders_2(X1,X2,esk1_3(X1,X2,X3))=X3|X2=k1_xboole_0|v2_struct_0(X1)|~m1_orders_2(X3,X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)), inference(csr,[status(thm)],[c_0_25, c_0_11])).
% 0.12/0.37  cnf(c_0_31, plain, (X1=k1_xboole_0|r2_hidden(esk1_3(X2,X1,X3),X1)|v2_struct_0(X2)|~m1_orders_2(X3,X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_orders_2(X2)|~v5_orders_2(X2)|~v4_orders_2(X2)|~v3_orders_2(X2)), inference(csr,[status(thm)],[c_0_26, c_0_11])).
% 0.12/0.37  fof(c_0_32, plain, ![X13, X14, X15]:((~r3_orders_2(X13,X14,X15)|r1_orders_2(X13,X14,X15)|(v2_struct_0(X13)|~v3_orders_2(X13)|~l1_orders_2(X13)|~m1_subset_1(X14,u1_struct_0(X13))|~m1_subset_1(X15,u1_struct_0(X13))))&(~r1_orders_2(X13,X14,X15)|r3_orders_2(X13,X14,X15)|(v2_struct_0(X13)|~v3_orders_2(X13)|~l1_orders_2(X13)|~m1_subset_1(X14,u1_struct_0(X13))|~m1_subset_1(X15,u1_struct_0(X13))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.12/0.37  cnf(c_0_33, plain, (v2_struct_0(X1)|r3_orders_2(X1,X2,X2)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.37  cnf(c_0_34, plain, (~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~r1_orders_2(X1,X2,X3)|~r2_orders_2(X1,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.37  cnf(c_0_35, negated_conjecture, (esk3_0=k1_xboole_0|r2_orders_2(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0),esk1_3(esk2_0,esk3_0,esk3_0))|~r2_hidden(esk1_3(esk2_0,esk3_0,esk3_0),k3_orders_2(esk2_0,X1,esk1_3(esk2_0,esk3_0,esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_29, c_0_24])).
% 0.12/0.37  cnf(c_0_36, negated_conjecture, (k3_orders_2(esk2_0,esk3_0,esk1_3(esk2_0,esk3_0,X1))=X1|esk3_0=k1_xboole_0|~m1_orders_2(X1,esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_14]), c_0_15]), c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 0.12/0.37  cnf(c_0_37, negated_conjecture, (esk3_0=k1_xboole_0|r2_hidden(esk1_3(esk2_0,esk3_0,X1),esk3_0)|~m1_orders_2(X1,esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_14]), c_0_15]), c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 0.12/0.37  cnf(c_0_38, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r3_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.37  cnf(c_0_39, negated_conjecture, (esk3_0=k1_xboole_0|r3_orders_2(esk2_0,X1,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_24]), c_0_15]), c_0_18])]), c_0_19])).
% 0.12/0.37  cnf(c_0_40, negated_conjecture, (esk3_0=k1_xboole_0|~r2_orders_2(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0),X1)|~r1_orders_2(esk2_0,X1,esk1_3(esk2_0,esk3_0,esk3_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_24]), c_0_15]), c_0_16])])).
% 0.12/0.37  cnf(c_0_41, negated_conjecture, (esk3_0=k1_xboole_0|r2_orders_2(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0),esk1_3(esk2_0,esk3_0,esk3_0))|~r2_hidden(esk1_3(esk2_0,esk3_0,esk3_0),k3_orders_2(esk2_0,esk3_0,esk1_3(esk2_0,esk3_0,esk3_0)))), inference(spm,[status(thm)],[c_0_35, c_0_14])).
% 0.12/0.37  cnf(c_0_42, negated_conjecture, (k3_orders_2(esk2_0,esk3_0,esk1_3(esk2_0,esk3_0,esk3_0))=esk3_0|esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_22])).
% 0.12/0.37  cnf(c_0_43, negated_conjecture, (esk3_0=k1_xboole_0|r2_hidden(esk1_3(esk2_0,esk3_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_37, c_0_22])).
% 0.12/0.37  cnf(c_0_44, negated_conjecture, (esk3_0=k1_xboole_0|r1_orders_2(esk2_0,X1,esk1_3(esk2_0,esk3_0,esk3_0))|~r3_orders_2(esk2_0,X1,esk1_3(esk2_0,esk3_0,esk3_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_24]), c_0_15]), c_0_18])]), c_0_19])).
% 0.12/0.37  cnf(c_0_45, negated_conjecture, (esk3_0=k1_xboole_0|r3_orders_2(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0),esk1_3(esk2_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_39, c_0_24])).
% 0.12/0.37  cnf(c_0_46, negated_conjecture, (esk3_0=k1_xboole_0|~r2_orders_2(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0),esk1_3(esk2_0,esk3_0,esk3_0))|~r1_orders_2(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0),esk1_3(esk2_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_40, c_0_24])).
% 0.12/0.37  cnf(c_0_47, negated_conjecture, (esk3_0=k1_xboole_0|r2_orders_2(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0),esk1_3(esk2_0,esk3_0,esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])).
% 0.12/0.37  cnf(c_0_48, negated_conjecture, (esk3_0=k1_xboole_0|r1_orders_2(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0),esk1_3(esk2_0,esk3_0,esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_24]), c_0_45])).
% 0.12/0.37  cnf(c_0_49, plain, (m1_orders_2(X1,X2,X3)|v2_struct_0(X2)|X1!=k1_xboole_0|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_50, negated_conjecture, (esk3_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])).
% 0.12/0.37  cnf(c_0_51, negated_conjecture, (~m1_orders_2(esk3_0,esk2_0,esk3_0)|esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_52, plain, (m1_orders_2(k1_xboole_0,X1,k1_xboole_0)|v2_struct_0(X1)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_49])])).
% 0.12/0.37  cnf(c_0_53, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(rw,[status(thm)],[c_0_14, c_0_50])).
% 0.12/0.37  cnf(c_0_54, negated_conjecture, (~m1_orders_2(k1_xboole_0,esk2_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_50]), c_0_50]), c_0_50])])).
% 0.12/0.37  cnf(c_0_55, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_15]), c_0_16]), c_0_17]), c_0_18])]), c_0_54]), c_0_19]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 56
% 0.12/0.37  # Proof object clause steps            : 41
% 0.12/0.37  # Proof object formula steps           : 15
% 0.12/0.37  # Proof object conjectures             : 31
% 0.12/0.37  # Proof object clause conjectures      : 28
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 17
% 0.12/0.37  # Proof object initial formulas used   : 7
% 0.12/0.37  # Proof object generating inferences   : 18
% 0.12/0.37  # Proof object simplifying inferences  : 55
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 7
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 24
% 0.12/0.37  # Removed in clause preprocessing      : 2
% 0.12/0.37  # Initial clauses in saturation        : 22
% 0.12/0.37  # Processed clauses                    : 73
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 2
% 0.12/0.37  # ...remaining for further processing  : 71
% 0.12/0.37  # Other redundant clauses eliminated   : 4
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 2
% 0.12/0.37  # Backward-rewritten                   : 21
% 0.12/0.37  # Generated clauses                    : 31
% 0.12/0.37  # ...of the previous two non-trivial   : 32
% 0.12/0.37  # Contextual simplify-reflections      : 7
% 0.12/0.37  # Paramodulations                      : 28
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 4
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 23
% 0.12/0.37  #    Positive orientable unit clauses  : 6
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 2
% 0.12/0.37  #    Non-unit-clauses                  : 15
% 0.12/0.37  # Current number of unprocessed clauses: 2
% 0.12/0.37  # ...number of literals in the above   : 12
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 45
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 620
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 91
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 11
% 0.12/0.37  # Unit Clause-clause subsumption calls : 7
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 3
% 0.12/0.37  # BW rewrite match successes           : 1
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 4597
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.029 s
% 0.12/0.37  # System time              : 0.008 s
% 0.12/0.37  # Total time               : 0.037 s
% 0.12/0.37  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
