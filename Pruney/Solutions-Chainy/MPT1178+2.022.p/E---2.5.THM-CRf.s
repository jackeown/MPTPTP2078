%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:15 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 296 expanded)
%              Number of clauses        :   41 ( 103 expanded)
%              Number of leaves         :    9 (  72 expanded)
%              Depth                    :   11
%              Number of atoms          :  349 (1691 expanded)
%              Number of equality atoms :   51 ( 237 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal clause size      :   68 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_orders_2)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_orders_2)).

fof(existence_m2_orders_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1)
        & m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))) )
     => ? [X3] : m2_orders_2(X3,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m2_orders_2)).

fof(t6_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5,X6,X7] :
                  ( ( r2_hidden(X3,X4)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X6,X7)
                    & r2_hidden(X7,X2) )
                 => r1_xboole_0(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_orders_2)).

fof(c_0_9,plain,(
    ! [X20,X21] :
      ( ~ r2_hidden(X20,X21)
      | ~ r1_tarski(X21,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_10,plain,(
    ! [X8] : r1_tarski(k1_xboole_0,X8) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_11,negated_conjecture,(
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

cnf(c_0_12,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X9,X10,X11,X13,X14,X15,X16,X18] :
      ( ( r2_hidden(X11,esk1_3(X9,X10,X11))
        | ~ r2_hidden(X11,X10)
        | X10 != k3_tarski(X9) )
      & ( r2_hidden(esk1_3(X9,X10,X11),X9)
        | ~ r2_hidden(X11,X10)
        | X10 != k3_tarski(X9) )
      & ( ~ r2_hidden(X13,X14)
        | ~ r2_hidden(X14,X9)
        | r2_hidden(X13,X10)
        | X10 != k3_tarski(X9) )
      & ( ~ r2_hidden(esk2_2(X15,X16),X16)
        | ~ r2_hidden(esk2_2(X15,X16),X18)
        | ~ r2_hidden(X18,X15)
        | X16 = k3_tarski(X15) )
      & ( r2_hidden(esk2_2(X15,X16),esk3_2(X15,X16))
        | r2_hidden(esk2_2(X15,X16),X16)
        | X16 = k3_tarski(X15) )
      & ( r2_hidden(esk3_2(X15,X16),X15)
        | r2_hidden(esk2_2(X15,X16),X16)
        | X16 = k3_tarski(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

fof(c_0_15,plain,(
    ! [X34,X35,X36,X37,X38,X39] :
      ( ( ~ r2_hidden(X37,X36)
        | m2_orders_2(X37,X34,X35)
        | X36 != k4_orders_2(X34,X35)
        | ~ m1_orders_1(X35,k1_orders_1(u1_struct_0(X34)))
        | v2_struct_0(X34)
        | ~ v3_orders_2(X34)
        | ~ v4_orders_2(X34)
        | ~ v5_orders_2(X34)
        | ~ l1_orders_2(X34) )
      & ( ~ m2_orders_2(X38,X34,X35)
        | r2_hidden(X38,X36)
        | X36 != k4_orders_2(X34,X35)
        | ~ m1_orders_1(X35,k1_orders_1(u1_struct_0(X34)))
        | v2_struct_0(X34)
        | ~ v3_orders_2(X34)
        | ~ v4_orders_2(X34)
        | ~ v5_orders_2(X34)
        | ~ l1_orders_2(X34) )
      & ( ~ r2_hidden(esk6_3(X34,X35,X39),X39)
        | ~ m2_orders_2(esk6_3(X34,X35,X39),X34,X35)
        | X39 = k4_orders_2(X34,X35)
        | ~ m1_orders_1(X35,k1_orders_1(u1_struct_0(X34)))
        | v2_struct_0(X34)
        | ~ v3_orders_2(X34)
        | ~ v4_orders_2(X34)
        | ~ v5_orders_2(X34)
        | ~ l1_orders_2(X34) )
      & ( r2_hidden(esk6_3(X34,X35,X39),X39)
        | m2_orders_2(esk6_3(X34,X35,X39),X34,X35)
        | X39 = k4_orders_2(X34,X35)
        | ~ m1_orders_1(X35,k1_orders_1(u1_struct_0(X34)))
        | v2_struct_0(X34)
        | ~ v3_orders_2(X34)
        | ~ v4_orders_2(X34)
        | ~ v5_orders_2(X34)
        | ~ l1_orders_2(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_orders_2])])])])])])])).

fof(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk8_0)
    & v3_orders_2(esk8_0)
    & v4_orders_2(esk8_0)
    & v5_orders_2(esk8_0)
    & l1_orders_2(esk8_0)
    & m1_orders_1(esk9_0,k1_orders_1(u1_struct_0(esk8_0)))
    & k3_tarski(k4_orders_2(esk8_0,esk9_0)) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

fof(c_0_17,plain,(
    ! [X44,X45] :
      ( v2_struct_0(X44)
      | ~ v3_orders_2(X44)
      | ~ v4_orders_2(X44)
      | ~ v5_orders_2(X44)
      | ~ l1_orders_2(X44)
      | ~ m1_orders_1(X45,k1_orders_1(u1_struct_0(X44)))
      | m2_orders_2(esk7_2(X44,X45),X44,X45) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[existence_m2_orders_2])])])])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_20,plain,(
    ! [X22,X24,X25,X26,X27,X28] :
      ( ( r2_hidden(esk4_1(X22),X22)
        | X22 = k1_xboole_0 )
      & ( ~ r2_hidden(X24,X25)
        | ~ r2_hidden(X25,X26)
        | ~ r2_hidden(X26,X27)
        | ~ r2_hidden(X27,X28)
        | ~ r2_hidden(X28,esk4_1(X22))
        | r1_xboole_0(X24,X22)
        | X22 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_mcart_1])])])])])])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X4)
    | v2_struct_0(X2)
    | ~ m2_orders_2(X1,X2,X3)
    | X4 != k4_orders_2(X2,X3)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( m1_orders_1(esk9_0,k1_orders_1(u1_struct_0(esk8_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( l1_orders_2(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( v5_orders_2(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( v4_orders_2(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( v3_orders_2(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,plain,
    ( v2_struct_0(X1)
    | m2_orders_2(esk7_2(X1,X2),X1,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( X1 != k3_tarski(k1_xboole_0)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_30,plain,
    ( m2_orders_2(X1,X3,X4)
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k4_orders_2(X3,X4)
    | ~ m1_orders_1(X4,k1_orders_1(u1_struct_0(X3)))
    | ~ v3_orders_2(X3)
    | ~ v4_orders_2(X3)
    | ~ v5_orders_2(X3)
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | X4 != k3_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_32,plain,
    ( r2_hidden(esk4_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(X1,X2)
    | X2 != k4_orders_2(esk8_0,esk9_0)
    | ~ m2_orders_2(X1,esk8_0,esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( m2_orders_2(esk7_2(esk8_0,esk9_0),esk8_0,esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_35,plain,
    ( ~ r2_hidden(X1,k3_tarski(k1_xboole_0)) ),
    inference(er,[status(thm)],[c_0_29])).

fof(c_0_36,plain,(
    ! [X41,X42,X43] :
      ( ( v6_orders_2(X43,X41)
        | ~ m2_orders_2(X43,X41,X42)
        | v2_struct_0(X41)
        | ~ v3_orders_2(X41)
        | ~ v4_orders_2(X41)
        | ~ v5_orders_2(X41)
        | ~ l1_orders_2(X41)
        | ~ m1_orders_1(X42,k1_orders_1(u1_struct_0(X41))) )
      & ( m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X41)))
        | ~ m2_orders_2(X43,X41,X42)
        | v2_struct_0(X41)
        | ~ v3_orders_2(X41)
        | ~ v4_orders_2(X41)
        | ~ v5_orders_2(X41)
        | ~ l1_orders_2(X41)
        | ~ m1_orders_1(X42,k1_orders_1(u1_struct_0(X41))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_orders_2])])])])])).

cnf(c_0_37,negated_conjecture,
    ( m2_orders_2(X1,esk8_0,esk9_0)
    | X2 != k4_orders_2(esk8_0,esk9_0)
    | ~ r2_hidden(X1,X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_38,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,X3)
    | X3 != k3_tarski(X1)
    | ~ r2_hidden(X2,esk4_1(X1)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk7_2(esk8_0,esk9_0),X1)
    | X1 != k4_orders_2(esk8_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_32])).

fof(c_0_41,plain,(
    ! [X29,X30,X31,X32] :
      ( ( X31 != k1_xboole_0
        | ~ m2_orders_2(X31,X29,X30)
        | ~ v6_orders_2(X31,X29)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))
        | ~ m1_orders_1(X30,k1_orders_1(u1_struct_0(X29)))
        | v2_struct_0(X29)
        | ~ v3_orders_2(X29)
        | ~ v4_orders_2(X29)
        | ~ v5_orders_2(X29)
        | ~ l1_orders_2(X29) )
      & ( r2_wellord1(u1_orders_2(X29),X31)
        | ~ m2_orders_2(X31,X29,X30)
        | ~ v6_orders_2(X31,X29)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))
        | ~ m1_orders_1(X30,k1_orders_1(u1_struct_0(X29)))
        | v2_struct_0(X29)
        | ~ v3_orders_2(X29)
        | ~ v4_orders_2(X29)
        | ~ v5_orders_2(X29)
        | ~ l1_orders_2(X29) )
      & ( ~ m1_subset_1(X32,u1_struct_0(X29))
        | ~ r2_hidden(X32,X31)
        | k1_funct_1(X30,k1_orders_2(X29,k3_orders_2(X29,X31,X32))) = X32
        | ~ m2_orders_2(X31,X29,X30)
        | ~ v6_orders_2(X31,X29)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))
        | ~ m1_orders_1(X30,k1_orders_1(u1_struct_0(X29)))
        | v2_struct_0(X29)
        | ~ v3_orders_2(X29)
        | ~ v4_orders_2(X29)
        | ~ v5_orders_2(X29)
        | ~ l1_orders_2(X29) )
      & ( m1_subset_1(esk5_3(X29,X30,X31),u1_struct_0(X29))
        | X31 = k1_xboole_0
        | ~ r2_wellord1(u1_orders_2(X29),X31)
        | m2_orders_2(X31,X29,X30)
        | ~ v6_orders_2(X31,X29)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))
        | ~ m1_orders_1(X30,k1_orders_1(u1_struct_0(X29)))
        | v2_struct_0(X29)
        | ~ v3_orders_2(X29)
        | ~ v4_orders_2(X29)
        | ~ v5_orders_2(X29)
        | ~ l1_orders_2(X29) )
      & ( r2_hidden(esk5_3(X29,X30,X31),X31)
        | X31 = k1_xboole_0
        | ~ r2_wellord1(u1_orders_2(X29),X31)
        | m2_orders_2(X31,X29,X30)
        | ~ v6_orders_2(X31,X29)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))
        | ~ m1_orders_1(X30,k1_orders_1(u1_struct_0(X29)))
        | v2_struct_0(X29)
        | ~ v3_orders_2(X29)
        | ~ v4_orders_2(X29)
        | ~ v5_orders_2(X29)
        | ~ l1_orders_2(X29) )
      & ( k1_funct_1(X30,k1_orders_2(X29,k3_orders_2(X29,X31,esk5_3(X29,X30,X31)))) != esk5_3(X29,X30,X31)
        | X31 = k1_xboole_0
        | ~ r2_wellord1(u1_orders_2(X29),X31)
        | m2_orders_2(X31,X29,X30)
        | ~ v6_orders_2(X31,X29)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))
        | ~ m1_orders_1(X30,k1_orders_1(u1_struct_0(X29)))
        | v2_struct_0(X29)
        | ~ v3_orders_2(X29)
        | ~ v4_orders_2(X29)
        | ~ v5_orders_2(X29)
        | ~ l1_orders_2(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_orders_2])])])])])])).

cnf(c_0_42,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v2_struct_0(X2)
    | ~ m2_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,plain,
    ( v6_orders_2(X1,X2)
    | v2_struct_0(X2)
    | ~ m2_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( m2_orders_2(X1,esk8_0,esk9_0)
    | ~ r2_hidden(X1,k4_orders_2(esk8_0,esk9_0)) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_45,plain,
    ( esk4_1(X1) = k1_xboole_0
    | X1 = k1_xboole_0
    | r2_hidden(esk4_1(esk4_1(X1)),X2)
    | X2 != k3_tarski(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_32])).

cnf(c_0_46,negated_conjecture,
    ( k3_tarski(k4_orders_2(esk8_0,esk9_0)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_47,negated_conjecture,
    ( k4_orders_2(esk8_0,esk9_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_18,c_0_39])).

cnf(c_0_48,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[c_0_29,c_0_40])).

cnf(c_0_49,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m2_orders_2(X1,esk8_0,esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_51,negated_conjecture,
    ( v6_orders_2(X1,esk8_0)
    | ~ m2_orders_2(X1,esk8_0,esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_52,negated_conjecture,
    ( k4_orders_2(esk8_0,esk9_0) = k1_xboole_0
    | m2_orders_2(esk4_1(k4_orders_2(esk8_0,esk9_0)),esk8_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_32])).

cnf(c_0_53,negated_conjecture,
    ( esk4_1(k4_orders_2(esk8_0,esk9_0)) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( X1 != k1_xboole_0
    | ~ m2_orders_2(X1,esk8_0,esk9_0)
    | ~ m2_orders_2(X1,esk8_0,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(esk8_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_23]),c_0_24]),c_0_25]),c_0_26])]),c_0_27]),c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( m2_orders_2(esk4_1(k4_orders_2(esk8_0,esk9_0)),esk8_0,esk9_0) ),
    inference(sr,[status(thm)],[c_0_52,c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( esk4_1(k4_orders_2(esk8_0,esk9_0)) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( X1 != k1_xboole_0
    | ~ m2_orders_2(X1,esk8_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_22])).

cnf(c_0_58,negated_conjecture,
    ( m2_orders_2(k1_xboole_0,esk8_0,esk9_0) ),
    inference(rw,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_57,c_0_58]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:25:40 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.39  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.12/0.39  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.12/0.39  #
% 0.12/0.39  # Preprocessing time       : 0.029 s
% 0.12/0.39  
% 0.12/0.39  # Proof found!
% 0.12/0.39  # SZS status Theorem
% 0.12/0.39  # SZS output start CNFRefutation
% 0.12/0.39  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.12/0.39  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.12/0.39  fof(t87_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>k3_tarski(k4_orders_2(X1,X2))!=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_orders_2)).
% 0.12/0.39  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 0.12/0.39  fof(d17_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(X3=k4_orders_2(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>m2_orders_2(X4,X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_orders_2)).
% 0.12/0.39  fof(existence_m2_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))))=>?[X3]:m2_orders_2(X3,X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m2_orders_2)).
% 0.12/0.39  fof(t6_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5, X6, X7]:(((((r2_hidden(X3,X4)&r2_hidden(X4,X5))&r2_hidden(X5,X6))&r2_hidden(X6,X7))&r2_hidden(X7,X2))=>r1_xboole_0(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_mcart_1)).
% 0.12/0.39  fof(dt_m2_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))))=>![X3]:(m2_orders_2(X3,X1,X2)=>(v6_orders_2(X3,X1)&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 0.12/0.39  fof(d16_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:((v6_orders_2(X3,X1)&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))=>(m2_orders_2(X3,X1,X2)<=>((X3!=k1_xboole_0&r2_wellord1(u1_orders_2(X1),X3))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>k1_funct_1(X2,k1_orders_2(X1,k3_orders_2(X1,X3,X4)))=X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_orders_2)).
% 0.12/0.39  fof(c_0_9, plain, ![X20, X21]:(~r2_hidden(X20,X21)|~r1_tarski(X21,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.12/0.39  fof(c_0_10, plain, ![X8]:r1_tarski(k1_xboole_0,X8), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.12/0.39  fof(c_0_11, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>k3_tarski(k4_orders_2(X1,X2))!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t87_orders_2])).
% 0.12/0.39  cnf(c_0_12, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.39  cnf(c_0_13, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.39  fof(c_0_14, plain, ![X9, X10, X11, X13, X14, X15, X16, X18]:((((r2_hidden(X11,esk1_3(X9,X10,X11))|~r2_hidden(X11,X10)|X10!=k3_tarski(X9))&(r2_hidden(esk1_3(X9,X10,X11),X9)|~r2_hidden(X11,X10)|X10!=k3_tarski(X9)))&(~r2_hidden(X13,X14)|~r2_hidden(X14,X9)|r2_hidden(X13,X10)|X10!=k3_tarski(X9)))&((~r2_hidden(esk2_2(X15,X16),X16)|(~r2_hidden(esk2_2(X15,X16),X18)|~r2_hidden(X18,X15))|X16=k3_tarski(X15))&((r2_hidden(esk2_2(X15,X16),esk3_2(X15,X16))|r2_hidden(esk2_2(X15,X16),X16)|X16=k3_tarski(X15))&(r2_hidden(esk3_2(X15,X16),X15)|r2_hidden(esk2_2(X15,X16),X16)|X16=k3_tarski(X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 0.12/0.39  fof(c_0_15, plain, ![X34, X35, X36, X37, X38, X39]:(((~r2_hidden(X37,X36)|m2_orders_2(X37,X34,X35)|X36!=k4_orders_2(X34,X35)|~m1_orders_1(X35,k1_orders_1(u1_struct_0(X34)))|(v2_struct_0(X34)|~v3_orders_2(X34)|~v4_orders_2(X34)|~v5_orders_2(X34)|~l1_orders_2(X34)))&(~m2_orders_2(X38,X34,X35)|r2_hidden(X38,X36)|X36!=k4_orders_2(X34,X35)|~m1_orders_1(X35,k1_orders_1(u1_struct_0(X34)))|(v2_struct_0(X34)|~v3_orders_2(X34)|~v4_orders_2(X34)|~v5_orders_2(X34)|~l1_orders_2(X34))))&((~r2_hidden(esk6_3(X34,X35,X39),X39)|~m2_orders_2(esk6_3(X34,X35,X39),X34,X35)|X39=k4_orders_2(X34,X35)|~m1_orders_1(X35,k1_orders_1(u1_struct_0(X34)))|(v2_struct_0(X34)|~v3_orders_2(X34)|~v4_orders_2(X34)|~v5_orders_2(X34)|~l1_orders_2(X34)))&(r2_hidden(esk6_3(X34,X35,X39),X39)|m2_orders_2(esk6_3(X34,X35,X39),X34,X35)|X39=k4_orders_2(X34,X35)|~m1_orders_1(X35,k1_orders_1(u1_struct_0(X34)))|(v2_struct_0(X34)|~v3_orders_2(X34)|~v4_orders_2(X34)|~v5_orders_2(X34)|~l1_orders_2(X34))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_orders_2])])])])])])])).
% 0.12/0.39  fof(c_0_16, negated_conjecture, (((((~v2_struct_0(esk8_0)&v3_orders_2(esk8_0))&v4_orders_2(esk8_0))&v5_orders_2(esk8_0))&l1_orders_2(esk8_0))&(m1_orders_1(esk9_0,k1_orders_1(u1_struct_0(esk8_0)))&k3_tarski(k4_orders_2(esk8_0,esk9_0))=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).
% 0.12/0.39  fof(c_0_17, plain, ![X44, X45]:(v2_struct_0(X44)|~v3_orders_2(X44)|~v4_orders_2(X44)|~v5_orders_2(X44)|~l1_orders_2(X44)|~m1_orders_1(X45,k1_orders_1(u1_struct_0(X44)))|m2_orders_2(esk7_2(X44,X45),X44,X45)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[existence_m2_orders_2])])])])).
% 0.12/0.39  cnf(c_0_18, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.12/0.39  cnf(c_0_19, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|~r2_hidden(X3,X2)|X2!=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.39  fof(c_0_20, plain, ![X22, X24, X25, X26, X27, X28]:((r2_hidden(esk4_1(X22),X22)|X22=k1_xboole_0)&(~r2_hidden(X24,X25)|~r2_hidden(X25,X26)|~r2_hidden(X26,X27)|~r2_hidden(X27,X28)|~r2_hidden(X28,esk4_1(X22))|r1_xboole_0(X24,X22)|X22=k1_xboole_0)), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_mcart_1])])])])])])).
% 0.12/0.39  cnf(c_0_21, plain, (r2_hidden(X1,X4)|v2_struct_0(X2)|~m2_orders_2(X1,X2,X3)|X4!=k4_orders_2(X2,X3)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.39  cnf(c_0_22, negated_conjecture, (m1_orders_1(esk9_0,k1_orders_1(u1_struct_0(esk8_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.39  cnf(c_0_23, negated_conjecture, (l1_orders_2(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.39  cnf(c_0_24, negated_conjecture, (v5_orders_2(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.39  cnf(c_0_25, negated_conjecture, (v4_orders_2(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.39  cnf(c_0_26, negated_conjecture, (v3_orders_2(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.39  cnf(c_0_27, negated_conjecture, (~v2_struct_0(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.39  cnf(c_0_28, plain, (v2_struct_0(X1)|m2_orders_2(esk7_2(X1,X2),X1,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.39  cnf(c_0_29, plain, (X1!=k3_tarski(k1_xboole_0)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.12/0.39  cnf(c_0_30, plain, (m2_orders_2(X1,X3,X4)|v2_struct_0(X3)|~r2_hidden(X1,X2)|X2!=k4_orders_2(X3,X4)|~m1_orders_1(X4,k1_orders_1(u1_struct_0(X3)))|~v3_orders_2(X3)|~v4_orders_2(X3)|~v5_orders_2(X3)|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.39  cnf(c_0_31, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X2,X3)|X4!=k3_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.39  cnf(c_0_32, plain, (r2_hidden(esk4_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.39  cnf(c_0_33, negated_conjecture, (r2_hidden(X1,X2)|X2!=k4_orders_2(esk8_0,esk9_0)|~m2_orders_2(X1,esk8_0,esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26])]), c_0_27])).
% 0.12/0.39  cnf(c_0_34, negated_conjecture, (m2_orders_2(esk7_2(esk8_0,esk9_0),esk8_0,esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26])]), c_0_27])).
% 0.12/0.39  cnf(c_0_35, plain, (~r2_hidden(X1,k3_tarski(k1_xboole_0))), inference(er,[status(thm)],[c_0_29])).
% 0.12/0.39  fof(c_0_36, plain, ![X41, X42, X43]:((v6_orders_2(X43,X41)|~m2_orders_2(X43,X41,X42)|(v2_struct_0(X41)|~v3_orders_2(X41)|~v4_orders_2(X41)|~v5_orders_2(X41)|~l1_orders_2(X41)|~m1_orders_1(X42,k1_orders_1(u1_struct_0(X41)))))&(m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X41)))|~m2_orders_2(X43,X41,X42)|(v2_struct_0(X41)|~v3_orders_2(X41)|~v4_orders_2(X41)|~v5_orders_2(X41)|~l1_orders_2(X41)|~m1_orders_1(X42,k1_orders_1(u1_struct_0(X41)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_orders_2])])])])])).
% 0.12/0.39  cnf(c_0_37, negated_conjecture, (m2_orders_2(X1,esk8_0,esk9_0)|X2!=k4_orders_2(esk8_0,esk9_0)|~r2_hidden(X1,X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26])]), c_0_27])).
% 0.12/0.39  cnf(c_0_38, plain, (X1=k1_xboole_0|r2_hidden(X2,X3)|X3!=k3_tarski(X1)|~r2_hidden(X2,esk4_1(X1))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.12/0.39  cnf(c_0_39, negated_conjecture, (r2_hidden(esk7_2(esk8_0,esk9_0),X1)|X1!=k4_orders_2(esk8_0,esk9_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.12/0.39  cnf(c_0_40, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_35, c_0_32])).
% 0.12/0.39  fof(c_0_41, plain, ![X29, X30, X31, X32]:((((X31!=k1_xboole_0|~m2_orders_2(X31,X29,X30)|(~v6_orders_2(X31,X29)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29))))|~m1_orders_1(X30,k1_orders_1(u1_struct_0(X29)))|(v2_struct_0(X29)|~v3_orders_2(X29)|~v4_orders_2(X29)|~v5_orders_2(X29)|~l1_orders_2(X29)))&(r2_wellord1(u1_orders_2(X29),X31)|~m2_orders_2(X31,X29,X30)|(~v6_orders_2(X31,X29)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29))))|~m1_orders_1(X30,k1_orders_1(u1_struct_0(X29)))|(v2_struct_0(X29)|~v3_orders_2(X29)|~v4_orders_2(X29)|~v5_orders_2(X29)|~l1_orders_2(X29))))&(~m1_subset_1(X32,u1_struct_0(X29))|(~r2_hidden(X32,X31)|k1_funct_1(X30,k1_orders_2(X29,k3_orders_2(X29,X31,X32)))=X32)|~m2_orders_2(X31,X29,X30)|(~v6_orders_2(X31,X29)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29))))|~m1_orders_1(X30,k1_orders_1(u1_struct_0(X29)))|(v2_struct_0(X29)|~v3_orders_2(X29)|~v4_orders_2(X29)|~v5_orders_2(X29)|~l1_orders_2(X29))))&((m1_subset_1(esk5_3(X29,X30,X31),u1_struct_0(X29))|(X31=k1_xboole_0|~r2_wellord1(u1_orders_2(X29),X31))|m2_orders_2(X31,X29,X30)|(~v6_orders_2(X31,X29)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29))))|~m1_orders_1(X30,k1_orders_1(u1_struct_0(X29)))|(v2_struct_0(X29)|~v3_orders_2(X29)|~v4_orders_2(X29)|~v5_orders_2(X29)|~l1_orders_2(X29)))&((r2_hidden(esk5_3(X29,X30,X31),X31)|(X31=k1_xboole_0|~r2_wellord1(u1_orders_2(X29),X31))|m2_orders_2(X31,X29,X30)|(~v6_orders_2(X31,X29)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29))))|~m1_orders_1(X30,k1_orders_1(u1_struct_0(X29)))|(v2_struct_0(X29)|~v3_orders_2(X29)|~v4_orders_2(X29)|~v5_orders_2(X29)|~l1_orders_2(X29)))&(k1_funct_1(X30,k1_orders_2(X29,k3_orders_2(X29,X31,esk5_3(X29,X30,X31))))!=esk5_3(X29,X30,X31)|(X31=k1_xboole_0|~r2_wellord1(u1_orders_2(X29),X31))|m2_orders_2(X31,X29,X30)|(~v6_orders_2(X31,X29)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29))))|~m1_orders_1(X30,k1_orders_1(u1_struct_0(X29)))|(v2_struct_0(X29)|~v3_orders_2(X29)|~v4_orders_2(X29)|~v5_orders_2(X29)|~l1_orders_2(X29)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_orders_2])])])])])])).
% 0.12/0.39  cnf(c_0_42, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|v2_struct_0(X2)|~m2_orders_2(X1,X2,X3)|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.12/0.39  cnf(c_0_43, plain, (v6_orders_2(X1,X2)|v2_struct_0(X2)|~m2_orders_2(X1,X2,X3)|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.12/0.39  cnf(c_0_44, negated_conjecture, (m2_orders_2(X1,esk8_0,esk9_0)|~r2_hidden(X1,k4_orders_2(esk8_0,esk9_0))), inference(er,[status(thm)],[c_0_37])).
% 0.12/0.39  cnf(c_0_45, plain, (esk4_1(X1)=k1_xboole_0|X1=k1_xboole_0|r2_hidden(esk4_1(esk4_1(X1)),X2)|X2!=k3_tarski(X1)), inference(spm,[status(thm)],[c_0_38, c_0_32])).
% 0.12/0.39  cnf(c_0_46, negated_conjecture, (k3_tarski(k4_orders_2(esk8_0,esk9_0))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.39  cnf(c_0_47, negated_conjecture, (k4_orders_2(esk8_0,esk9_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_18, c_0_39])).
% 0.12/0.39  cnf(c_0_48, plain, (X1!=k1_xboole_0|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[c_0_29, c_0_40])).
% 0.12/0.39  cnf(c_0_49, plain, (v2_struct_0(X2)|X1!=k1_xboole_0|~m2_orders_2(X1,X2,X3)|~v6_orders_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.12/0.39  cnf(c_0_50, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0)))|~m2_orders_2(X1,esk8_0,esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26])]), c_0_27])).
% 0.12/0.39  cnf(c_0_51, negated_conjecture, (v6_orders_2(X1,esk8_0)|~m2_orders_2(X1,esk8_0,esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26])]), c_0_27])).
% 0.12/0.39  cnf(c_0_52, negated_conjecture, (k4_orders_2(esk8_0,esk9_0)=k1_xboole_0|m2_orders_2(esk4_1(k4_orders_2(esk8_0,esk9_0)),esk8_0,esk9_0)), inference(spm,[status(thm)],[c_0_44, c_0_32])).
% 0.12/0.39  cnf(c_0_53, negated_conjecture, (esk4_1(k4_orders_2(esk8_0,esk9_0))=k1_xboole_0|X1!=k1_xboole_0), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47]), c_0_48])).
% 0.12/0.39  cnf(c_0_54, negated_conjecture, (X1!=k1_xboole_0|~m2_orders_2(X1,esk8_0,esk9_0)|~m2_orders_2(X1,esk8_0,X2)|~m1_orders_1(X2,k1_orders_1(u1_struct_0(esk8_0)))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_23]), c_0_24]), c_0_25]), c_0_26])]), c_0_27]), c_0_51])).
% 0.12/0.39  cnf(c_0_55, negated_conjecture, (m2_orders_2(esk4_1(k4_orders_2(esk8_0,esk9_0)),esk8_0,esk9_0)), inference(sr,[status(thm)],[c_0_52, c_0_47])).
% 0.12/0.39  cnf(c_0_56, negated_conjecture, (esk4_1(k4_orders_2(esk8_0,esk9_0))=k1_xboole_0), inference(er,[status(thm)],[c_0_53])).
% 0.12/0.39  cnf(c_0_57, negated_conjecture, (X1!=k1_xboole_0|~m2_orders_2(X1,esk8_0,esk9_0)), inference(spm,[status(thm)],[c_0_54, c_0_22])).
% 0.12/0.39  cnf(c_0_58, negated_conjecture, (m2_orders_2(k1_xboole_0,esk8_0,esk9_0)), inference(rw,[status(thm)],[c_0_55, c_0_56])).
% 0.12/0.39  cnf(c_0_59, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_57, c_0_58]), ['proof']).
% 0.12/0.39  # SZS output end CNFRefutation
% 0.12/0.39  # Proof object total steps             : 60
% 0.12/0.39  # Proof object clause steps            : 41
% 0.12/0.39  # Proof object formula steps           : 19
% 0.12/0.39  # Proof object conjectures             : 26
% 0.12/0.39  # Proof object clause conjectures      : 23
% 0.12/0.39  # Proof object formula conjectures     : 3
% 0.12/0.39  # Proof object initial clauses used    : 18
% 0.12/0.39  # Proof object initial formulas used   : 9
% 0.12/0.39  # Proof object generating inferences   : 20
% 0.12/0.39  # Proof object simplifying inferences  : 42
% 0.12/0.39  # Training examples: 0 positive, 0 negative
% 0.12/0.39  # Parsed axioms                        : 9
% 0.12/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.39  # Initial clauses                      : 30
% 0.12/0.39  # Removed in clause preprocessing      : 0
% 0.12/0.39  # Initial clauses in saturation        : 30
% 0.12/0.39  # Processed clauses                    : 128
% 0.12/0.39  # ...of these trivial                  : 3
% 0.12/0.39  # ...subsumed                          : 28
% 0.12/0.39  # ...remaining for further processing  : 97
% 0.12/0.39  # Other redundant clauses eliminated   : 0
% 0.12/0.39  # Clauses deleted for lack of memory   : 0
% 0.12/0.39  # Backward-subsumed                    : 2
% 0.12/0.39  # Backward-rewritten                   : 4
% 0.12/0.39  # Generated clauses                    : 309
% 0.12/0.39  # ...of the previous two non-trivial   : 282
% 0.12/0.39  # Contextual simplify-reflections      : 7
% 0.12/0.39  # Paramodulations                      : 283
% 0.12/0.39  # Factorizations                       : 6
% 0.12/0.39  # Equation resolutions                 : 19
% 0.12/0.39  # Propositional unsat checks           : 0
% 0.12/0.39  #    Propositional check models        : 0
% 0.12/0.39  #    Propositional check unsatisfiable : 0
% 0.12/0.39  #    Propositional clauses             : 0
% 0.12/0.39  #    Propositional clauses after purity: 0
% 0.12/0.39  #    Propositional unsat core size     : 0
% 0.12/0.39  #    Propositional preprocessing time  : 0.000
% 0.12/0.39  #    Propositional encoding time       : 0.000
% 0.12/0.39  #    Propositional solver time         : 0.000
% 0.12/0.39  #    Success case prop preproc time    : 0.000
% 0.12/0.39  #    Success case prop encoding time   : 0.000
% 0.12/0.39  #    Success case prop solver time     : 0.000
% 0.12/0.39  # Current number of processed clauses  : 90
% 0.12/0.39  #    Positive orientable unit clauses  : 13
% 0.12/0.39  #    Positive unorientable unit clauses: 0
% 0.12/0.39  #    Negative unit clauses             : 3
% 0.12/0.39  #    Non-unit-clauses                  : 74
% 0.12/0.39  # Current number of unprocessed clauses: 177
% 0.12/0.39  # ...number of literals in the above   : 989
% 0.12/0.39  # Current number of archived formulas  : 0
% 0.12/0.39  # Current number of archived clauses   : 7
% 0.12/0.39  # Clause-clause subsumption calls (NU) : 3112
% 0.12/0.39  # Rec. Clause-clause subsumption calls : 600
% 0.12/0.39  # Non-unit clause-clause subsumptions  : 22
% 0.12/0.39  # Unit Clause-clause subsumption calls : 192
% 0.12/0.39  # Rewrite failures with RHS unbound    : 0
% 0.12/0.39  # BW rewrite match attempts            : 2
% 0.12/0.39  # BW rewrite match successes           : 2
% 0.12/0.39  # Condensation attempts                : 0
% 0.12/0.39  # Condensation successes               : 0
% 0.12/0.39  # Termbank termtop insertions          : 8322
% 0.12/0.39  
% 0.12/0.39  # -------------------------------------------------
% 0.12/0.39  # User time                : 0.043 s
% 0.12/0.39  # System time              : 0.005 s
% 0.12/0.39  # Total time               : 0.048 s
% 0.12/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
