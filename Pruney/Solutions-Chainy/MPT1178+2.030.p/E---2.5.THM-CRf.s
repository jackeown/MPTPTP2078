%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:16 EST 2020

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 111 expanded)
%              Number of clauses        :   24 (  37 expanded)
%              Number of leaves         :    8 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :  297 ( 727 expanded)
%              Number of equality atoms :   45 ( 107 expanded)
%              Maximal formula depth    :   22 (   7 average)
%              Maximal clause size      :   68 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t29_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k3_mcart_1(X3,X4,X5) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

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

fof(fc9_orders_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1)
        & m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))) )
     => ~ v1_xboole_0(k4_orders_2(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_orders_2)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_8,plain,(
    ! [X28,X29,X30] :
      ( ( X29 = k1_xboole_0
        | ~ r2_hidden(X29,X28)
        | k3_tarski(X28) != k1_xboole_0 )
      & ( esk4_1(X30) != k1_xboole_0
        | k3_tarski(X30) = k1_xboole_0 )
      & ( r2_hidden(esk4_1(X30),X30)
        | k3_tarski(X30) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_orders_1])])])])])])).

fof(c_0_9,plain,(
    ! [X6,X8,X9,X10] :
      ( ( r2_hidden(esk1_1(X6),X6)
        | X6 = k1_xboole_0 )
      & ( ~ r2_hidden(X8,X6)
        | esk1_1(X6) != k3_mcart_1(X8,X9,X10)
        | X6 = k1_xboole_0 )
      & ( ~ r2_hidden(X9,X6)
        | esk1_1(X6) != k3_mcart_1(X8,X9,X10)
        | X6 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).

fof(c_0_10,negated_conjecture,(
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

fof(c_0_11,plain,(
    ! [X16,X17,X18,X19,X20,X21] :
      ( ( ~ r2_hidden(X19,X18)
        | m2_orders_2(X19,X16,X17)
        | X18 != k4_orders_2(X16,X17)
        | ~ m1_orders_1(X17,k1_orders_1(u1_struct_0(X16)))
        | v2_struct_0(X16)
        | ~ v3_orders_2(X16)
        | ~ v4_orders_2(X16)
        | ~ v5_orders_2(X16)
        | ~ l1_orders_2(X16) )
      & ( ~ m2_orders_2(X20,X16,X17)
        | r2_hidden(X20,X18)
        | X18 != k4_orders_2(X16,X17)
        | ~ m1_orders_1(X17,k1_orders_1(u1_struct_0(X16)))
        | v2_struct_0(X16)
        | ~ v3_orders_2(X16)
        | ~ v4_orders_2(X16)
        | ~ v5_orders_2(X16)
        | ~ l1_orders_2(X16) )
      & ( ~ r2_hidden(esk3_3(X16,X17,X21),X21)
        | ~ m2_orders_2(esk3_3(X16,X17,X21),X16,X17)
        | X21 = k4_orders_2(X16,X17)
        | ~ m1_orders_1(X17,k1_orders_1(u1_struct_0(X16)))
        | v2_struct_0(X16)
        | ~ v3_orders_2(X16)
        | ~ v4_orders_2(X16)
        | ~ v5_orders_2(X16)
        | ~ l1_orders_2(X16) )
      & ( r2_hidden(esk3_3(X16,X17,X21),X21)
        | m2_orders_2(esk3_3(X16,X17,X21),X16,X17)
        | X21 = k4_orders_2(X16,X17)
        | ~ m1_orders_1(X17,k1_orders_1(u1_struct_0(X16)))
        | v2_struct_0(X16)
        | ~ v3_orders_2(X16)
        | ~ v4_orders_2(X16)
        | ~ v5_orders_2(X16)
        | ~ l1_orders_2(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_orders_2])])])])])])])).

cnf(c_0_12,plain,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | k3_tarski(X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v3_orders_2(esk5_0)
    & v4_orders_2(esk5_0)
    & v5_orders_2(esk5_0)
    & l1_orders_2(esk5_0)
    & m1_orders_1(esk6_0,k1_orders_1(u1_struct_0(esk5_0)))
    & k3_tarski(k4_orders_2(esk5_0,esk6_0)) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

cnf(c_0_15,plain,
    ( m2_orders_2(X1,X3,X4)
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k4_orders_2(X3,X4)
    | ~ m1_orders_1(X4,k1_orders_1(u1_struct_0(X3)))
    | ~ v3_orders_2(X3)
    | ~ v4_orders_2(X3)
    | ~ v5_orders_2(X3)
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( esk1_1(X1) = k1_xboole_0
    | X1 = k1_xboole_0
    | k3_tarski(X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( k3_tarski(k4_orders_2(esk5_0,esk6_0)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( m2_orders_2(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2)
    | ~ r2_hidden(X1,k4_orders_2(X2,X3)) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( m1_orders_1(esk6_0,k1_orders_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( v5_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( v4_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( v3_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,negated_conjecture,
    ( esk1_1(k4_orders_2(esk5_0,esk6_0)) = k1_xboole_0
    | k4_orders_2(esk5_0,esk6_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_26,plain,(
    ! [X11,X12,X13,X14] :
      ( ( X13 != k1_xboole_0
        | ~ m2_orders_2(X13,X11,X12)
        | ~ v6_orders_2(X13,X11)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ m1_orders_1(X12,k1_orders_1(u1_struct_0(X11)))
        | v2_struct_0(X11)
        | ~ v3_orders_2(X11)
        | ~ v4_orders_2(X11)
        | ~ v5_orders_2(X11)
        | ~ l1_orders_2(X11) )
      & ( r2_wellord1(u1_orders_2(X11),X13)
        | ~ m2_orders_2(X13,X11,X12)
        | ~ v6_orders_2(X13,X11)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ m1_orders_1(X12,k1_orders_1(u1_struct_0(X11)))
        | v2_struct_0(X11)
        | ~ v3_orders_2(X11)
        | ~ v4_orders_2(X11)
        | ~ v5_orders_2(X11)
        | ~ l1_orders_2(X11) )
      & ( ~ m1_subset_1(X14,u1_struct_0(X11))
        | ~ r2_hidden(X14,X13)
        | k1_funct_1(X12,k1_orders_2(X11,k3_orders_2(X11,X13,X14))) = X14
        | ~ m2_orders_2(X13,X11,X12)
        | ~ v6_orders_2(X13,X11)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ m1_orders_1(X12,k1_orders_1(u1_struct_0(X11)))
        | v2_struct_0(X11)
        | ~ v3_orders_2(X11)
        | ~ v4_orders_2(X11)
        | ~ v5_orders_2(X11)
        | ~ l1_orders_2(X11) )
      & ( m1_subset_1(esk2_3(X11,X12,X13),u1_struct_0(X11))
        | X13 = k1_xboole_0
        | ~ r2_wellord1(u1_orders_2(X11),X13)
        | m2_orders_2(X13,X11,X12)
        | ~ v6_orders_2(X13,X11)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ m1_orders_1(X12,k1_orders_1(u1_struct_0(X11)))
        | v2_struct_0(X11)
        | ~ v3_orders_2(X11)
        | ~ v4_orders_2(X11)
        | ~ v5_orders_2(X11)
        | ~ l1_orders_2(X11) )
      & ( r2_hidden(esk2_3(X11,X12,X13),X13)
        | X13 = k1_xboole_0
        | ~ r2_wellord1(u1_orders_2(X11),X13)
        | m2_orders_2(X13,X11,X12)
        | ~ v6_orders_2(X13,X11)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ m1_orders_1(X12,k1_orders_1(u1_struct_0(X11)))
        | v2_struct_0(X11)
        | ~ v3_orders_2(X11)
        | ~ v4_orders_2(X11)
        | ~ v5_orders_2(X11)
        | ~ l1_orders_2(X11) )
      & ( k1_funct_1(X12,k1_orders_2(X11,k3_orders_2(X11,X13,esk2_3(X11,X12,X13)))) != esk2_3(X11,X12,X13)
        | X13 = k1_xboole_0
        | ~ r2_wellord1(u1_orders_2(X11),X13)
        | m2_orders_2(X13,X11,X12)
        | ~ v6_orders_2(X13,X11)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ m1_orders_1(X12,k1_orders_1(u1_struct_0(X11)))
        | v2_struct_0(X11)
        | ~ v3_orders_2(X11)
        | ~ v4_orders_2(X11)
        | ~ v5_orders_2(X11)
        | ~ l1_orders_2(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_orders_2])])])])])])).

fof(c_0_27,plain,(
    ! [X23,X24,X25] :
      ( ( v6_orders_2(X25,X23)
        | ~ m2_orders_2(X25,X23,X24)
        | v2_struct_0(X23)
        | ~ v3_orders_2(X23)
        | ~ v4_orders_2(X23)
        | ~ v5_orders_2(X23)
        | ~ l1_orders_2(X23)
        | ~ m1_orders_1(X24,k1_orders_1(u1_struct_0(X23))) )
      & ( m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ m2_orders_2(X25,X23,X24)
        | v2_struct_0(X23)
        | ~ v3_orders_2(X23)
        | ~ v4_orders_2(X23)
        | ~ v5_orders_2(X23)
        | ~ l1_orders_2(X23)
        | ~ m1_orders_1(X24,k1_orders_1(u1_struct_0(X23))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_orders_2])])])])])).

fof(c_0_28,plain,(
    ! [X26,X27] :
      ( v2_struct_0(X26)
      | ~ v3_orders_2(X26)
      | ~ v4_orders_2(X26)
      | ~ v5_orders_2(X26)
      | ~ l1_orders_2(X26)
      | ~ m1_orders_1(X27,k1_orders_1(u1_struct_0(X26)))
      | ~ v1_xboole_0(k4_orders_2(X26,X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_orders_2])])])).

cnf(c_0_29,negated_conjecture,
    ( m2_orders_2(X1,esk5_0,esk6_0)
    | ~ r2_hidden(X1,k4_orders_2(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( k4_orders_2(esk5_0,esk6_0) = k1_xboole_0
    | r2_hidden(k1_xboole_0,k4_orders_2(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_25])).

cnf(c_0_31,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( v6_orders_2(X1,X2)
    | v2_struct_0(X2)
    | ~ m2_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v2_struct_0(X2)
    | ~ m2_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ v1_xboole_0(k4_orders_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( k4_orders_2(esk5_0,esk6_0) = k1_xboole_0
    | m2_orders_2(k1_xboole_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_37,plain,
    ( v2_struct_0(X1)
    | ~ m2_orders_2(k1_xboole_0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_31,c_0_32])]),c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( m2_orders_2(k1_xboole_0,esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_36])]),c_0_24])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_19]),c_0_38]),c_0_20]),c_0_21]),c_0_22]),c_0_23])]),c_0_24]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.33  % Computer   : n020.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 18:40:22 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 0.11/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.11/0.36  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.11/0.36  #
% 0.11/0.36  # Preprocessing time       : 0.029 s
% 0.11/0.36  # Presaturation interreduction done
% 0.11/0.36  
% 0.11/0.36  # Proof found!
% 0.11/0.36  # SZS status Theorem
% 0.11/0.36  # SZS output start CNFRefutation
% 0.11/0.36  fof(t91_orders_1, axiom, ![X1]:(~((?[X2]:(X2!=k1_xboole_0&r2_hidden(X2,X1))&k3_tarski(X1)=k1_xboole_0))&~((k3_tarski(X1)!=k1_xboole_0&![X2]:~((X2!=k1_xboole_0&r2_hidden(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_orders_1)).
% 0.11/0.36  fof(t29_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k3_mcart_1(X3,X4,X5))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 0.11/0.36  fof(t87_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>k3_tarski(k4_orders_2(X1,X2))!=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_orders_2)).
% 0.11/0.36  fof(d17_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(X3=k4_orders_2(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>m2_orders_2(X4,X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_orders_2)).
% 0.11/0.36  fof(d16_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:((v6_orders_2(X3,X1)&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))=>(m2_orders_2(X3,X1,X2)<=>((X3!=k1_xboole_0&r2_wellord1(u1_orders_2(X1),X3))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>k1_funct_1(X2,k1_orders_2(X1,k3_orders_2(X1,X3,X4)))=X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_orders_2)).
% 0.11/0.36  fof(dt_m2_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))))=>![X3]:(m2_orders_2(X3,X1,X2)=>(v6_orders_2(X3,X1)&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 0.11/0.36  fof(fc9_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))))=>~(v1_xboole_0(k4_orders_2(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_orders_2)).
% 0.11/0.36  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.11/0.36  fof(c_0_8, plain, ![X28, X29, X30]:((X29=k1_xboole_0|~r2_hidden(X29,X28)|k3_tarski(X28)!=k1_xboole_0)&((esk4_1(X30)!=k1_xboole_0|k3_tarski(X30)=k1_xboole_0)&(r2_hidden(esk4_1(X30),X30)|k3_tarski(X30)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_orders_1])])])])])])).
% 0.11/0.36  fof(c_0_9, plain, ![X6, X8, X9, X10]:((r2_hidden(esk1_1(X6),X6)|X6=k1_xboole_0)&((~r2_hidden(X8,X6)|esk1_1(X6)!=k3_mcart_1(X8,X9,X10)|X6=k1_xboole_0)&(~r2_hidden(X9,X6)|esk1_1(X6)!=k3_mcart_1(X8,X9,X10)|X6=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).
% 0.11/0.36  fof(c_0_10, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>k3_tarski(k4_orders_2(X1,X2))!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t87_orders_2])).
% 0.11/0.36  fof(c_0_11, plain, ![X16, X17, X18, X19, X20, X21]:(((~r2_hidden(X19,X18)|m2_orders_2(X19,X16,X17)|X18!=k4_orders_2(X16,X17)|~m1_orders_1(X17,k1_orders_1(u1_struct_0(X16)))|(v2_struct_0(X16)|~v3_orders_2(X16)|~v4_orders_2(X16)|~v5_orders_2(X16)|~l1_orders_2(X16)))&(~m2_orders_2(X20,X16,X17)|r2_hidden(X20,X18)|X18!=k4_orders_2(X16,X17)|~m1_orders_1(X17,k1_orders_1(u1_struct_0(X16)))|(v2_struct_0(X16)|~v3_orders_2(X16)|~v4_orders_2(X16)|~v5_orders_2(X16)|~l1_orders_2(X16))))&((~r2_hidden(esk3_3(X16,X17,X21),X21)|~m2_orders_2(esk3_3(X16,X17,X21),X16,X17)|X21=k4_orders_2(X16,X17)|~m1_orders_1(X17,k1_orders_1(u1_struct_0(X16)))|(v2_struct_0(X16)|~v3_orders_2(X16)|~v4_orders_2(X16)|~v5_orders_2(X16)|~l1_orders_2(X16)))&(r2_hidden(esk3_3(X16,X17,X21),X21)|m2_orders_2(esk3_3(X16,X17,X21),X16,X17)|X21=k4_orders_2(X16,X17)|~m1_orders_1(X17,k1_orders_1(u1_struct_0(X16)))|(v2_struct_0(X16)|~v3_orders_2(X16)|~v4_orders_2(X16)|~v5_orders_2(X16)|~l1_orders_2(X16))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_orders_2])])])])])])])).
% 0.11/0.36  cnf(c_0_12, plain, (X1=k1_xboole_0|~r2_hidden(X1,X2)|k3_tarski(X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.11/0.36  cnf(c_0_13, plain, (r2_hidden(esk1_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.11/0.36  fof(c_0_14, negated_conjecture, (((((~v2_struct_0(esk5_0)&v3_orders_2(esk5_0))&v4_orders_2(esk5_0))&v5_orders_2(esk5_0))&l1_orders_2(esk5_0))&(m1_orders_1(esk6_0,k1_orders_1(u1_struct_0(esk5_0)))&k3_tarski(k4_orders_2(esk5_0,esk6_0))=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.11/0.36  cnf(c_0_15, plain, (m2_orders_2(X1,X3,X4)|v2_struct_0(X3)|~r2_hidden(X1,X2)|X2!=k4_orders_2(X3,X4)|~m1_orders_1(X4,k1_orders_1(u1_struct_0(X3)))|~v3_orders_2(X3)|~v4_orders_2(X3)|~v5_orders_2(X3)|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.11/0.36  cnf(c_0_16, plain, (esk1_1(X1)=k1_xboole_0|X1=k1_xboole_0|k3_tarski(X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.11/0.36  cnf(c_0_17, negated_conjecture, (k3_tarski(k4_orders_2(esk5_0,esk6_0))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.11/0.36  cnf(c_0_18, plain, (m2_orders_2(X1,X2,X3)|v2_struct_0(X2)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))|~l1_orders_2(X2)|~v5_orders_2(X2)|~v4_orders_2(X2)|~v3_orders_2(X2)|~r2_hidden(X1,k4_orders_2(X2,X3))), inference(er,[status(thm)],[c_0_15])).
% 0.11/0.36  cnf(c_0_19, negated_conjecture, (m1_orders_1(esk6_0,k1_orders_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.11/0.36  cnf(c_0_20, negated_conjecture, (l1_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.11/0.36  cnf(c_0_21, negated_conjecture, (v5_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.11/0.36  cnf(c_0_22, negated_conjecture, (v4_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.11/0.36  cnf(c_0_23, negated_conjecture, (v3_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.11/0.36  cnf(c_0_24, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.11/0.36  cnf(c_0_25, negated_conjecture, (esk1_1(k4_orders_2(esk5_0,esk6_0))=k1_xboole_0|k4_orders_2(esk5_0,esk6_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.11/0.36  fof(c_0_26, plain, ![X11, X12, X13, X14]:((((X13!=k1_xboole_0|~m2_orders_2(X13,X11,X12)|(~v6_orders_2(X13,X11)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11))))|~m1_orders_1(X12,k1_orders_1(u1_struct_0(X11)))|(v2_struct_0(X11)|~v3_orders_2(X11)|~v4_orders_2(X11)|~v5_orders_2(X11)|~l1_orders_2(X11)))&(r2_wellord1(u1_orders_2(X11),X13)|~m2_orders_2(X13,X11,X12)|(~v6_orders_2(X13,X11)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11))))|~m1_orders_1(X12,k1_orders_1(u1_struct_0(X11)))|(v2_struct_0(X11)|~v3_orders_2(X11)|~v4_orders_2(X11)|~v5_orders_2(X11)|~l1_orders_2(X11))))&(~m1_subset_1(X14,u1_struct_0(X11))|(~r2_hidden(X14,X13)|k1_funct_1(X12,k1_orders_2(X11,k3_orders_2(X11,X13,X14)))=X14)|~m2_orders_2(X13,X11,X12)|(~v6_orders_2(X13,X11)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11))))|~m1_orders_1(X12,k1_orders_1(u1_struct_0(X11)))|(v2_struct_0(X11)|~v3_orders_2(X11)|~v4_orders_2(X11)|~v5_orders_2(X11)|~l1_orders_2(X11))))&((m1_subset_1(esk2_3(X11,X12,X13),u1_struct_0(X11))|(X13=k1_xboole_0|~r2_wellord1(u1_orders_2(X11),X13))|m2_orders_2(X13,X11,X12)|(~v6_orders_2(X13,X11)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11))))|~m1_orders_1(X12,k1_orders_1(u1_struct_0(X11)))|(v2_struct_0(X11)|~v3_orders_2(X11)|~v4_orders_2(X11)|~v5_orders_2(X11)|~l1_orders_2(X11)))&((r2_hidden(esk2_3(X11,X12,X13),X13)|(X13=k1_xboole_0|~r2_wellord1(u1_orders_2(X11),X13))|m2_orders_2(X13,X11,X12)|(~v6_orders_2(X13,X11)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11))))|~m1_orders_1(X12,k1_orders_1(u1_struct_0(X11)))|(v2_struct_0(X11)|~v3_orders_2(X11)|~v4_orders_2(X11)|~v5_orders_2(X11)|~l1_orders_2(X11)))&(k1_funct_1(X12,k1_orders_2(X11,k3_orders_2(X11,X13,esk2_3(X11,X12,X13))))!=esk2_3(X11,X12,X13)|(X13=k1_xboole_0|~r2_wellord1(u1_orders_2(X11),X13))|m2_orders_2(X13,X11,X12)|(~v6_orders_2(X13,X11)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11))))|~m1_orders_1(X12,k1_orders_1(u1_struct_0(X11)))|(v2_struct_0(X11)|~v3_orders_2(X11)|~v4_orders_2(X11)|~v5_orders_2(X11)|~l1_orders_2(X11)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_orders_2])])])])])])).
% 0.11/0.36  fof(c_0_27, plain, ![X23, X24, X25]:((v6_orders_2(X25,X23)|~m2_orders_2(X25,X23,X24)|(v2_struct_0(X23)|~v3_orders_2(X23)|~v4_orders_2(X23)|~v5_orders_2(X23)|~l1_orders_2(X23)|~m1_orders_1(X24,k1_orders_1(u1_struct_0(X23)))))&(m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))|~m2_orders_2(X25,X23,X24)|(v2_struct_0(X23)|~v3_orders_2(X23)|~v4_orders_2(X23)|~v5_orders_2(X23)|~l1_orders_2(X23)|~m1_orders_1(X24,k1_orders_1(u1_struct_0(X23)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_orders_2])])])])])).
% 0.11/0.36  fof(c_0_28, plain, ![X26, X27]:(v2_struct_0(X26)|~v3_orders_2(X26)|~v4_orders_2(X26)|~v5_orders_2(X26)|~l1_orders_2(X26)|~m1_orders_1(X27,k1_orders_1(u1_struct_0(X26)))|~v1_xboole_0(k4_orders_2(X26,X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_orders_2])])])).
% 0.11/0.36  cnf(c_0_29, negated_conjecture, (m2_orders_2(X1,esk5_0,esk6_0)|~r2_hidden(X1,k4_orders_2(esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.11/0.36  cnf(c_0_30, negated_conjecture, (k4_orders_2(esk5_0,esk6_0)=k1_xboole_0|r2_hidden(k1_xboole_0,k4_orders_2(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_13, c_0_25])).
% 0.11/0.36  cnf(c_0_31, plain, (v2_struct_0(X2)|X1!=k1_xboole_0|~m2_orders_2(X1,X2,X3)|~v6_orders_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.11/0.36  cnf(c_0_32, plain, (v6_orders_2(X1,X2)|v2_struct_0(X2)|~m2_orders_2(X1,X2,X3)|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.11/0.36  cnf(c_0_33, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|v2_struct_0(X2)|~m2_orders_2(X1,X2,X3)|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.11/0.36  cnf(c_0_34, plain, (v2_struct_0(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))|~v1_xboole_0(k4_orders_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.11/0.36  cnf(c_0_35, negated_conjecture, (k4_orders_2(esk5_0,esk6_0)=k1_xboole_0|m2_orders_2(k1_xboole_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.11/0.36  cnf(c_0_36, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.11/0.36  cnf(c_0_37, plain, (v2_struct_0(X1)|~m2_orders_2(k1_xboole_0,X1,X2)|~m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_31, c_0_32])]), c_0_33])).
% 0.11/0.36  cnf(c_0_38, negated_conjecture, (m2_orders_2(k1_xboole_0,esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_19]), c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_36])]), c_0_24])).
% 0.11/0.36  cnf(c_0_39, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_19]), c_0_38]), c_0_20]), c_0_21]), c_0_22]), c_0_23])]), c_0_24]), ['proof']).
% 0.11/0.36  # SZS output end CNFRefutation
% 0.11/0.36  # Proof object total steps             : 40
% 0.11/0.36  # Proof object clause steps            : 24
% 0.11/0.36  # Proof object formula steps           : 16
% 0.11/0.36  # Proof object conjectures             : 16
% 0.11/0.36  # Proof object clause conjectures      : 13
% 0.11/0.36  # Proof object formula conjectures     : 3
% 0.11/0.36  # Proof object initial clauses used    : 15
% 0.11/0.36  # Proof object initial formulas used   : 8
% 0.11/0.36  # Proof object generating inferences   : 7
% 0.11/0.36  # Proof object simplifying inferences  : 25
% 0.11/0.36  # Training examples: 0 positive, 0 negative
% 0.11/0.36  # Parsed axioms                        : 8
% 0.11/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.11/0.36  # Initial clauses                      : 27
% 0.11/0.36  # Removed in clause preprocessing      : 0
% 0.11/0.36  # Initial clauses in saturation        : 27
% 0.11/0.36  # Processed clauses                    : 70
% 0.11/0.36  # ...of these trivial                  : 0
% 0.11/0.36  # ...subsumed                          : 3
% 0.11/0.36  # ...remaining for further processing  : 67
% 0.11/0.36  # Other redundant clauses eliminated   : 3
% 0.11/0.36  # Clauses deleted for lack of memory   : 0
% 0.11/0.36  # Backward-subsumed                    : 0
% 0.11/0.36  # Backward-rewritten                   : 1
% 0.11/0.36  # Generated clauses                    : 33
% 0.11/0.36  # ...of the previous two non-trivial   : 26
% 0.11/0.36  # Contextual simplify-reflections      : 6
% 0.11/0.36  # Paramodulations                      : 30
% 0.11/0.36  # Factorizations                       : 0
% 0.11/0.36  # Equation resolutions                 : 3
% 0.11/0.36  # Propositional unsat checks           : 0
% 0.11/0.36  #    Propositional check models        : 0
% 0.11/0.36  #    Propositional check unsatisfiable : 0
% 0.11/0.36  #    Propositional clauses             : 0
% 0.11/0.36  #    Propositional clauses after purity: 0
% 0.11/0.36  #    Propositional unsat core size     : 0
% 0.11/0.36  #    Propositional preprocessing time  : 0.000
% 0.11/0.36  #    Propositional encoding time       : 0.000
% 0.11/0.36  #    Propositional solver time         : 0.000
% 0.11/0.36  #    Success case prop preproc time    : 0.000
% 0.11/0.36  #    Success case prop encoding time   : 0.000
% 0.11/0.36  #    Success case prop solver time     : 0.000
% 0.11/0.36  # Current number of processed clauses  : 36
% 0.11/0.36  #    Positive orientable unit clauses  : 8
% 0.11/0.36  #    Positive unorientable unit clauses: 0
% 0.11/0.36  #    Negative unit clauses             : 1
% 0.11/0.36  #    Non-unit-clauses                  : 27
% 0.11/0.36  # Current number of unprocessed clauses: 8
% 0.11/0.36  # ...number of literals in the above   : 80
% 0.11/0.36  # Current number of archived formulas  : 0
% 0.11/0.36  # Current number of archived clauses   : 28
% 0.11/0.36  # Clause-clause subsumption calls (NU) : 627
% 0.11/0.36  # Rec. Clause-clause subsumption calls : 90
% 0.11/0.36  # Non-unit clause-clause subsumptions  : 9
% 0.11/0.36  # Unit Clause-clause subsumption calls : 1
% 0.11/0.36  # Rewrite failures with RHS unbound    : 0
% 0.11/0.36  # BW rewrite match attempts            : 1
% 0.11/0.36  # BW rewrite match successes           : 1
% 0.11/0.36  # Condensation attempts                : 0
% 0.11/0.36  # Condensation successes               : 0
% 0.11/0.36  # Termbank termtop insertions          : 3782
% 0.11/0.36  
% 0.11/0.36  # -------------------------------------------------
% 0.11/0.36  # User time                : 0.033 s
% 0.11/0.36  # System time              : 0.005 s
% 0.11/0.36  # Total time               : 0.037 s
% 0.11/0.36  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
