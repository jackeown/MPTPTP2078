%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:15 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   34 ( 130 expanded)
%              Number of clauses        :   21 (  41 expanded)
%              Number of leaves         :    6 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :  275 ( 844 expanded)
%              Number of equality atoms :   32 ( 104 expanded)
%              Maximal formula depth    :   22 (   7 average)
%              Maximal clause size      :   68 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d17_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
         => ! [X3] :
              ( X3 = k4_orders_2(X1,X2)
            <=> ! [X4] :
                  ( r2_hidden(X4,X3)
                <=> m2_orders_2(X4,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_orders_2)).

fof(t87_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
         => k3_tarski(k4_orders_2(X1,X2)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_orders_2)).

fof(t91_orders_1,axiom,(
    ! [X1] :
      ( ~ ( ? [X2] :
              ( X2 != k1_xboole_0
              & r2_hidden(X2,X1) )
          & k3_tarski(X1) = k1_xboole_0 )
      & ~ ( k3_tarski(X1) != k1_xboole_0
          & ! [X2] :
              ~ ( X2 != k1_xboole_0
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_orders_1)).

fof(existence_m2_orders_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1)
        & m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))) )
     => ? [X3] : m2_orders_2(X3,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m2_orders_2)).

fof(d16_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
         => ! [X3] :
              ( ( v6_orders_2(X3,X1)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
             => ( m2_orders_2(X3,X1,X2)
              <=> ( X3 != k1_xboole_0
                  & r2_wellord1(u1_orders_2(X1),X3)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r2_hidden(X4,X3)
                       => k1_funct_1(X2,k1_orders_2(X1,k3_orders_2(X1,X3,X4))) = X4 ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_orders_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_orders_2)).

fof(c_0_6,plain,(
    ! [X10,X11,X12,X13,X14,X15] :
      ( ( ~ r2_hidden(X13,X12)
        | m2_orders_2(X13,X10,X11)
        | X12 != k4_orders_2(X10,X11)
        | ~ m1_orders_1(X11,k1_orders_1(u1_struct_0(X10)))
        | v2_struct_0(X10)
        | ~ v3_orders_2(X10)
        | ~ v4_orders_2(X10)
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( ~ m2_orders_2(X14,X10,X11)
        | r2_hidden(X14,X12)
        | X12 != k4_orders_2(X10,X11)
        | ~ m1_orders_1(X11,k1_orders_1(u1_struct_0(X10)))
        | v2_struct_0(X10)
        | ~ v3_orders_2(X10)
        | ~ v4_orders_2(X10)
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( ~ r2_hidden(esk2_3(X10,X11,X15),X15)
        | ~ m2_orders_2(esk2_3(X10,X11,X15),X10,X11)
        | X15 = k4_orders_2(X10,X11)
        | ~ m1_orders_1(X11,k1_orders_1(u1_struct_0(X10)))
        | v2_struct_0(X10)
        | ~ v3_orders_2(X10)
        | ~ v4_orders_2(X10)
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( r2_hidden(esk2_3(X10,X11,X15),X15)
        | m2_orders_2(esk2_3(X10,X11,X15),X10,X11)
        | X15 = k4_orders_2(X10,X11)
        | ~ m1_orders_1(X11,k1_orders_1(u1_struct_0(X10)))
        | v2_struct_0(X10)
        | ~ v3_orders_2(X10)
        | ~ v4_orders_2(X10)
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_orders_2])])])])])])])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
           => k3_tarski(k4_orders_2(X1,X2)) != k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t87_orders_2])).

cnf(c_0_8,plain,
    ( r2_hidden(X1,X4)
    | v2_struct_0(X2)
    | ~ m2_orders_2(X1,X2,X3)
    | X4 != k4_orders_2(X2,X3)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v3_orders_2(esk5_0)
    & v4_orders_2(esk5_0)
    & v5_orders_2(esk5_0)
    & l1_orders_2(esk5_0)
    & m1_orders_1(esk6_0,k1_orders_1(u1_struct_0(esk5_0)))
    & k3_tarski(k4_orders_2(esk5_0,esk6_0)) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).

fof(c_0_10,plain,(
    ! [X23,X24,X25] :
      ( ( X24 = k1_xboole_0
        | ~ r2_hidden(X24,X23)
        | k3_tarski(X23) != k1_xboole_0 )
      & ( esk4_1(X25) != k1_xboole_0
        | k3_tarski(X25) = k1_xboole_0 )
      & ( r2_hidden(esk4_1(X25),X25)
        | k3_tarski(X25) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_orders_1])])])])])])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,k4_orders_2(X2,X3))
    | v2_struct_0(X2)
    | ~ m2_orders_2(X1,X2,X3)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( m1_orders_1(esk6_0,k1_orders_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( v5_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( v4_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( v3_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_18,plain,(
    ! [X20,X21] :
      ( v2_struct_0(X20)
      | ~ v3_orders_2(X20)
      | ~ v4_orders_2(X20)
      | ~ v5_orders_2(X20)
      | ~ l1_orders_2(X20)
      | ~ m1_orders_1(X21,k1_orders_1(u1_struct_0(X20)))
      | m2_orders_2(esk3_2(X20,X21),X20,X21) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[existence_m2_orders_2])])])])).

fof(c_0_19,plain,(
    ! [X5,X6,X7,X8] :
      ( ( X7 != k1_xboole_0
        | ~ m2_orders_2(X7,X5,X6)
        | ~ v6_orders_2(X7,X5)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ m1_orders_1(X6,k1_orders_1(u1_struct_0(X5)))
        | v2_struct_0(X5)
        | ~ v3_orders_2(X5)
        | ~ v4_orders_2(X5)
        | ~ v5_orders_2(X5)
        | ~ l1_orders_2(X5) )
      & ( r2_wellord1(u1_orders_2(X5),X7)
        | ~ m2_orders_2(X7,X5,X6)
        | ~ v6_orders_2(X7,X5)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ m1_orders_1(X6,k1_orders_1(u1_struct_0(X5)))
        | v2_struct_0(X5)
        | ~ v3_orders_2(X5)
        | ~ v4_orders_2(X5)
        | ~ v5_orders_2(X5)
        | ~ l1_orders_2(X5) )
      & ( ~ m1_subset_1(X8,u1_struct_0(X5))
        | ~ r2_hidden(X8,X7)
        | k1_funct_1(X6,k1_orders_2(X5,k3_orders_2(X5,X7,X8))) = X8
        | ~ m2_orders_2(X7,X5,X6)
        | ~ v6_orders_2(X7,X5)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ m1_orders_1(X6,k1_orders_1(u1_struct_0(X5)))
        | v2_struct_0(X5)
        | ~ v3_orders_2(X5)
        | ~ v4_orders_2(X5)
        | ~ v5_orders_2(X5)
        | ~ l1_orders_2(X5) )
      & ( m1_subset_1(esk1_3(X5,X6,X7),u1_struct_0(X5))
        | X7 = k1_xboole_0
        | ~ r2_wellord1(u1_orders_2(X5),X7)
        | m2_orders_2(X7,X5,X6)
        | ~ v6_orders_2(X7,X5)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ m1_orders_1(X6,k1_orders_1(u1_struct_0(X5)))
        | v2_struct_0(X5)
        | ~ v3_orders_2(X5)
        | ~ v4_orders_2(X5)
        | ~ v5_orders_2(X5)
        | ~ l1_orders_2(X5) )
      & ( r2_hidden(esk1_3(X5,X6,X7),X7)
        | X7 = k1_xboole_0
        | ~ r2_wellord1(u1_orders_2(X5),X7)
        | m2_orders_2(X7,X5,X6)
        | ~ v6_orders_2(X7,X5)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ m1_orders_1(X6,k1_orders_1(u1_struct_0(X5)))
        | v2_struct_0(X5)
        | ~ v3_orders_2(X5)
        | ~ v4_orders_2(X5)
        | ~ v5_orders_2(X5)
        | ~ l1_orders_2(X5) )
      & ( k1_funct_1(X6,k1_orders_2(X5,k3_orders_2(X5,X7,esk1_3(X5,X6,X7)))) != esk1_3(X5,X6,X7)
        | X7 = k1_xboole_0
        | ~ r2_wellord1(u1_orders_2(X5),X7)
        | m2_orders_2(X7,X5,X6)
        | ~ v6_orders_2(X7,X5)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ m1_orders_1(X6,k1_orders_1(u1_struct_0(X5)))
        | v2_struct_0(X5)
        | ~ v3_orders_2(X5)
        | ~ v4_orders_2(X5)
        | ~ v5_orders_2(X5)
        | ~ l1_orders_2(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_orders_2])])])])])])).

fof(c_0_20,plain,(
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

cnf(c_0_21,plain,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | k3_tarski(X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(X1,k4_orders_2(esk5_0,esk6_0))
    | ~ m2_orders_2(X1,esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_14]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( k3_tarski(k4_orders_2(esk5_0,esk6_0)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | m2_orders_2(esk3_2(X1,X2),X1,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( v2_struct_0(X2)
    | X1 != k1_xboole_0
    | ~ m2_orders_2(X1,X2,X3)
    | ~ v6_orders_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( v6_orders_2(X1,X2)
    | v2_struct_0(X2)
    | ~ m2_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v2_struct_0(X2)
    | ~ m2_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ m2_orders_2(X1,esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_29,negated_conjecture,
    ( m2_orders_2(esk3_2(esk5_0,esk6_0),esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_12]),c_0_13]),c_0_14]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_30,plain,
    ( v2_struct_0(X1)
    | ~ m2_orders_2(k1_xboole_0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

cnf(c_0_31,negated_conjecture,
    ( esk3_2(esk5_0,esk6_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( ~ m2_orders_2(k1_xboole_0,esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_12]),c_0_13]),c_0_14]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_31]),c_0_32]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:08:49 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 0.15/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.15/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.15/0.39  #
% 0.15/0.39  # Preprocessing time       : 0.029 s
% 0.15/0.39  # Presaturation interreduction done
% 0.15/0.39  
% 0.15/0.39  # Proof found!
% 0.15/0.39  # SZS status Theorem
% 0.15/0.39  # SZS output start CNFRefutation
% 0.15/0.39  fof(d17_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(X3=k4_orders_2(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>m2_orders_2(X4,X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_orders_2)).
% 0.15/0.39  fof(t87_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>k3_tarski(k4_orders_2(X1,X2))!=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_orders_2)).
% 0.15/0.39  fof(t91_orders_1, axiom, ![X1]:(~((?[X2]:(X2!=k1_xboole_0&r2_hidden(X2,X1))&k3_tarski(X1)=k1_xboole_0))&~((k3_tarski(X1)!=k1_xboole_0&![X2]:~((X2!=k1_xboole_0&r2_hidden(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_orders_1)).
% 0.15/0.39  fof(existence_m2_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))))=>?[X3]:m2_orders_2(X3,X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m2_orders_2)).
% 0.15/0.39  fof(d16_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:((v6_orders_2(X3,X1)&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))=>(m2_orders_2(X3,X1,X2)<=>((X3!=k1_xboole_0&r2_wellord1(u1_orders_2(X1),X3))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>k1_funct_1(X2,k1_orders_2(X1,k3_orders_2(X1,X3,X4)))=X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_orders_2)).
% 0.15/0.39  fof(dt_m2_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))))=>![X3]:(m2_orders_2(X3,X1,X2)=>(v6_orders_2(X3,X1)&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 0.15/0.39  fof(c_0_6, plain, ![X10, X11, X12, X13, X14, X15]:(((~r2_hidden(X13,X12)|m2_orders_2(X13,X10,X11)|X12!=k4_orders_2(X10,X11)|~m1_orders_1(X11,k1_orders_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v3_orders_2(X10)|~v4_orders_2(X10)|~v5_orders_2(X10)|~l1_orders_2(X10)))&(~m2_orders_2(X14,X10,X11)|r2_hidden(X14,X12)|X12!=k4_orders_2(X10,X11)|~m1_orders_1(X11,k1_orders_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v3_orders_2(X10)|~v4_orders_2(X10)|~v5_orders_2(X10)|~l1_orders_2(X10))))&((~r2_hidden(esk2_3(X10,X11,X15),X15)|~m2_orders_2(esk2_3(X10,X11,X15),X10,X11)|X15=k4_orders_2(X10,X11)|~m1_orders_1(X11,k1_orders_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v3_orders_2(X10)|~v4_orders_2(X10)|~v5_orders_2(X10)|~l1_orders_2(X10)))&(r2_hidden(esk2_3(X10,X11,X15),X15)|m2_orders_2(esk2_3(X10,X11,X15),X10,X11)|X15=k4_orders_2(X10,X11)|~m1_orders_1(X11,k1_orders_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v3_orders_2(X10)|~v4_orders_2(X10)|~v5_orders_2(X10)|~l1_orders_2(X10))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_orders_2])])])])])])])).
% 0.15/0.39  fof(c_0_7, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>k3_tarski(k4_orders_2(X1,X2))!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t87_orders_2])).
% 0.15/0.39  cnf(c_0_8, plain, (r2_hidden(X1,X4)|v2_struct_0(X2)|~m2_orders_2(X1,X2,X3)|X4!=k4_orders_2(X2,X3)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.15/0.39  fof(c_0_9, negated_conjecture, (((((~v2_struct_0(esk5_0)&v3_orders_2(esk5_0))&v4_orders_2(esk5_0))&v5_orders_2(esk5_0))&l1_orders_2(esk5_0))&(m1_orders_1(esk6_0,k1_orders_1(u1_struct_0(esk5_0)))&k3_tarski(k4_orders_2(esk5_0,esk6_0))=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).
% 0.15/0.39  fof(c_0_10, plain, ![X23, X24, X25]:((X24=k1_xboole_0|~r2_hidden(X24,X23)|k3_tarski(X23)!=k1_xboole_0)&((esk4_1(X25)!=k1_xboole_0|k3_tarski(X25)=k1_xboole_0)&(r2_hidden(esk4_1(X25),X25)|k3_tarski(X25)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_orders_1])])])])])])).
% 0.15/0.39  cnf(c_0_11, plain, (r2_hidden(X1,k4_orders_2(X2,X3))|v2_struct_0(X2)|~m2_orders_2(X1,X2,X3)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))|~l1_orders_2(X2)|~v5_orders_2(X2)|~v4_orders_2(X2)|~v3_orders_2(X2)), inference(er,[status(thm)],[c_0_8])).
% 0.15/0.39  cnf(c_0_12, negated_conjecture, (m1_orders_1(esk6_0,k1_orders_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.15/0.39  cnf(c_0_13, negated_conjecture, (l1_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.15/0.39  cnf(c_0_14, negated_conjecture, (v5_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.15/0.39  cnf(c_0_15, negated_conjecture, (v4_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.15/0.39  cnf(c_0_16, negated_conjecture, (v3_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.15/0.39  cnf(c_0_17, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.15/0.39  fof(c_0_18, plain, ![X20, X21]:(v2_struct_0(X20)|~v3_orders_2(X20)|~v4_orders_2(X20)|~v5_orders_2(X20)|~l1_orders_2(X20)|~m1_orders_1(X21,k1_orders_1(u1_struct_0(X20)))|m2_orders_2(esk3_2(X20,X21),X20,X21)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[existence_m2_orders_2])])])])).
% 0.15/0.39  fof(c_0_19, plain, ![X5, X6, X7, X8]:((((X7!=k1_xboole_0|~m2_orders_2(X7,X5,X6)|(~v6_orders_2(X7,X5)|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X5))))|~m1_orders_1(X6,k1_orders_1(u1_struct_0(X5)))|(v2_struct_0(X5)|~v3_orders_2(X5)|~v4_orders_2(X5)|~v5_orders_2(X5)|~l1_orders_2(X5)))&(r2_wellord1(u1_orders_2(X5),X7)|~m2_orders_2(X7,X5,X6)|(~v6_orders_2(X7,X5)|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X5))))|~m1_orders_1(X6,k1_orders_1(u1_struct_0(X5)))|(v2_struct_0(X5)|~v3_orders_2(X5)|~v4_orders_2(X5)|~v5_orders_2(X5)|~l1_orders_2(X5))))&(~m1_subset_1(X8,u1_struct_0(X5))|(~r2_hidden(X8,X7)|k1_funct_1(X6,k1_orders_2(X5,k3_orders_2(X5,X7,X8)))=X8)|~m2_orders_2(X7,X5,X6)|(~v6_orders_2(X7,X5)|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X5))))|~m1_orders_1(X6,k1_orders_1(u1_struct_0(X5)))|(v2_struct_0(X5)|~v3_orders_2(X5)|~v4_orders_2(X5)|~v5_orders_2(X5)|~l1_orders_2(X5))))&((m1_subset_1(esk1_3(X5,X6,X7),u1_struct_0(X5))|(X7=k1_xboole_0|~r2_wellord1(u1_orders_2(X5),X7))|m2_orders_2(X7,X5,X6)|(~v6_orders_2(X7,X5)|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X5))))|~m1_orders_1(X6,k1_orders_1(u1_struct_0(X5)))|(v2_struct_0(X5)|~v3_orders_2(X5)|~v4_orders_2(X5)|~v5_orders_2(X5)|~l1_orders_2(X5)))&((r2_hidden(esk1_3(X5,X6,X7),X7)|(X7=k1_xboole_0|~r2_wellord1(u1_orders_2(X5),X7))|m2_orders_2(X7,X5,X6)|(~v6_orders_2(X7,X5)|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X5))))|~m1_orders_1(X6,k1_orders_1(u1_struct_0(X5)))|(v2_struct_0(X5)|~v3_orders_2(X5)|~v4_orders_2(X5)|~v5_orders_2(X5)|~l1_orders_2(X5)))&(k1_funct_1(X6,k1_orders_2(X5,k3_orders_2(X5,X7,esk1_3(X5,X6,X7))))!=esk1_3(X5,X6,X7)|(X7=k1_xboole_0|~r2_wellord1(u1_orders_2(X5),X7))|m2_orders_2(X7,X5,X6)|(~v6_orders_2(X7,X5)|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X5))))|~m1_orders_1(X6,k1_orders_1(u1_struct_0(X5)))|(v2_struct_0(X5)|~v3_orders_2(X5)|~v4_orders_2(X5)|~v5_orders_2(X5)|~l1_orders_2(X5)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_orders_2])])])])])])).
% 0.15/0.39  fof(c_0_20, plain, ![X17, X18, X19]:((v6_orders_2(X19,X17)|~m2_orders_2(X19,X17,X18)|(v2_struct_0(X17)|~v3_orders_2(X17)|~v4_orders_2(X17)|~v5_orders_2(X17)|~l1_orders_2(X17)|~m1_orders_1(X18,k1_orders_1(u1_struct_0(X17)))))&(m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))|~m2_orders_2(X19,X17,X18)|(v2_struct_0(X17)|~v3_orders_2(X17)|~v4_orders_2(X17)|~v5_orders_2(X17)|~l1_orders_2(X17)|~m1_orders_1(X18,k1_orders_1(u1_struct_0(X17)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_orders_2])])])])])).
% 0.15/0.39  cnf(c_0_21, plain, (X1=k1_xboole_0|~r2_hidden(X1,X2)|k3_tarski(X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.15/0.39  cnf(c_0_22, negated_conjecture, (r2_hidden(X1,k4_orders_2(esk5_0,esk6_0))|~m2_orders_2(X1,esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13]), c_0_14]), c_0_15]), c_0_16])]), c_0_17])).
% 0.15/0.39  cnf(c_0_23, negated_conjecture, (k3_tarski(k4_orders_2(esk5_0,esk6_0))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.15/0.39  cnf(c_0_24, plain, (v2_struct_0(X1)|m2_orders_2(esk3_2(X1,X2),X1,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.15/0.39  cnf(c_0_25, plain, (v2_struct_0(X2)|X1!=k1_xboole_0|~m2_orders_2(X1,X2,X3)|~v6_orders_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.15/0.39  cnf(c_0_26, plain, (v6_orders_2(X1,X2)|v2_struct_0(X2)|~m2_orders_2(X1,X2,X3)|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.15/0.39  cnf(c_0_27, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|v2_struct_0(X2)|~m2_orders_2(X1,X2,X3)|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.15/0.39  cnf(c_0_28, negated_conjecture, (X1=k1_xboole_0|~m2_orders_2(X1,esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])])).
% 0.15/0.39  cnf(c_0_29, negated_conjecture, (m2_orders_2(esk3_2(esk5_0,esk6_0),esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_12]), c_0_13]), c_0_14]), c_0_15]), c_0_16])]), c_0_17])).
% 0.15/0.39  cnf(c_0_30, plain, (v2_struct_0(X1)|~m2_orders_2(k1_xboole_0,X1,X2)|~m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)), inference(er,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_25, c_0_26]), c_0_27])])).
% 0.15/0.39  cnf(c_0_31, negated_conjecture, (esk3_2(esk5_0,esk6_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.15/0.39  cnf(c_0_32, negated_conjecture, (~m2_orders_2(k1_xboole_0,esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_12]), c_0_13]), c_0_14]), c_0_15]), c_0_16])]), c_0_17])).
% 0.15/0.39  cnf(c_0_33, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_31]), c_0_32]), ['proof']).
% 0.15/0.39  # SZS output end CNFRefutation
% 0.15/0.39  # Proof object total steps             : 34
% 0.15/0.39  # Proof object clause steps            : 21
% 0.15/0.39  # Proof object formula steps           : 13
% 0.15/0.39  # Proof object conjectures             : 16
% 0.15/0.39  # Proof object clause conjectures      : 13
% 0.15/0.39  # Proof object formula conjectures     : 3
% 0.15/0.39  # Proof object initial clauses used    : 13
% 0.15/0.39  # Proof object initial formulas used   : 6
% 0.15/0.39  # Proof object generating inferences   : 5
% 0.15/0.39  # Proof object simplifying inferences  : 26
% 0.15/0.39  # Training examples: 0 positive, 0 negative
% 0.15/0.39  # Parsed axioms                        : 6
% 0.15/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.39  # Initial clauses                      : 23
% 0.15/0.39  # Removed in clause preprocessing      : 0
% 0.15/0.39  # Initial clauses in saturation        : 23
% 0.15/0.39  # Processed clauses                    : 48
% 0.15/0.39  # ...of these trivial                  : 0
% 0.15/0.39  # ...subsumed                          : 0
% 0.15/0.39  # ...remaining for further processing  : 48
% 0.15/0.39  # Other redundant clauses eliminated   : 3
% 0.15/0.39  # Clauses deleted for lack of memory   : 0
% 0.15/0.39  # Backward-subsumed                    : 0
% 0.15/0.39  # Backward-rewritten                   : 1
% 0.15/0.39  # Generated clauses                    : 13
% 0.15/0.39  # ...of the previous two non-trivial   : 10
% 0.15/0.39  # Contextual simplify-reflections      : 6
% 0.15/0.39  # Paramodulations                      : 10
% 0.15/0.39  # Factorizations                       : 0
% 0.15/0.39  # Equation resolutions                 : 3
% 0.15/0.39  # Propositional unsat checks           : 0
% 0.15/0.39  #    Propositional check models        : 0
% 0.15/0.39  #    Propositional check unsatisfiable : 0
% 0.15/0.39  #    Propositional clauses             : 0
% 0.15/0.39  #    Propositional clauses after purity: 0
% 0.15/0.39  #    Propositional unsat core size     : 0
% 0.15/0.39  #    Propositional preprocessing time  : 0.000
% 0.15/0.39  #    Propositional encoding time       : 0.000
% 0.15/0.39  #    Propositional solver time         : 0.000
% 0.15/0.39  #    Success case prop preproc time    : 0.000
% 0.15/0.39  #    Success case prop encoding time   : 0.000
% 0.15/0.39  #    Success case prop solver time     : 0.000
% 0.15/0.39  # Current number of processed clauses  : 21
% 0.15/0.39  #    Positive orientable unit clauses  : 7
% 0.15/0.39  #    Positive unorientable unit clauses: 0
% 0.15/0.39  #    Negative unit clauses             : 2
% 0.15/0.39  #    Non-unit-clauses                  : 12
% 0.15/0.39  # Current number of unprocessed clauses: 8
% 0.15/0.39  # ...number of literals in the above   : 80
% 0.15/0.39  # Current number of archived formulas  : 0
% 0.15/0.39  # Current number of archived clauses   : 24
% 0.15/0.39  # Clause-clause subsumption calls (NU) : 264
% 0.15/0.39  # Rec. Clause-clause subsumption calls : 8
% 0.15/0.39  # Non-unit clause-clause subsumptions  : 6
% 0.15/0.39  # Unit Clause-clause subsumption calls : 1
% 0.15/0.39  # Rewrite failures with RHS unbound    : 0
% 0.15/0.39  # BW rewrite match attempts            : 1
% 0.15/0.39  # BW rewrite match successes           : 1
% 0.15/0.39  # Condensation attempts                : 0
% 0.15/0.39  # Condensation successes               : 0
% 0.15/0.39  # Termbank termtop insertions          : 3211
% 0.15/0.39  
% 0.15/0.39  # -------------------------------------------------
% 0.15/0.39  # User time                : 0.032 s
% 0.15/0.39  # System time              : 0.004 s
% 0.15/0.39  # Total time               : 0.036 s
% 0.15/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
