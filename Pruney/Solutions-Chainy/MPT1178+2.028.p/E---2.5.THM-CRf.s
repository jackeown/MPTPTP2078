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

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 115 expanded)
%              Number of clauses        :   26 (  39 expanded)
%              Number of leaves         :    9 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  285 ( 706 expanded)
%              Number of equality atoms :   30 (  87 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal clause size      :   68 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

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

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

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

fof(c_0_9,negated_conjecture,(
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

fof(c_0_10,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X8,X9)
      | r1_tarski(X8,k3_tarski(X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v3_orders_2(esk4_0)
    & v4_orders_2(esk4_0)
    & v5_orders_2(esk4_0)
    & l1_orders_2(esk4_0)
    & m1_orders_1(esk5_0,k1_orders_1(u1_struct_0(esk4_0)))
    & k3_tarski(k4_orders_2(esk4_0,esk5_0)) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

cnf(c_0_12,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( k3_tarski(k4_orders_2(esk4_0,esk5_0)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X5] :
      ( X5 = k1_xboole_0
      | r2_hidden(esk1_1(X5),X5) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_15,plain,(
    ! [X15,X16,X17,X18,X19,X20] :
      ( ( ~ r2_hidden(X18,X17)
        | m2_orders_2(X18,X15,X16)
        | X17 != k4_orders_2(X15,X16)
        | ~ m1_orders_1(X16,k1_orders_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ v3_orders_2(X15)
        | ~ v4_orders_2(X15)
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) )
      & ( ~ m2_orders_2(X19,X15,X16)
        | r2_hidden(X19,X17)
        | X17 != k4_orders_2(X15,X16)
        | ~ m1_orders_1(X16,k1_orders_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ v3_orders_2(X15)
        | ~ v4_orders_2(X15)
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) )
      & ( ~ r2_hidden(esk3_3(X15,X16,X20),X20)
        | ~ m2_orders_2(esk3_3(X15,X16,X20),X15,X16)
        | X20 = k4_orders_2(X15,X16)
        | ~ m1_orders_1(X16,k1_orders_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ v3_orders_2(X15)
        | ~ v4_orders_2(X15)
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) )
      & ( r2_hidden(esk3_3(X15,X16,X20),X20)
        | m2_orders_2(esk3_3(X15,X16,X20),X15,X16)
        | X20 = k4_orders_2(X15,X16)
        | ~ m1_orders_1(X16,k1_orders_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ v3_orders_2(X15)
        | ~ v4_orders_2(X15)
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_orders_2])])])])])])])).

fof(c_0_16,plain,(
    ! [X7] :
      ( ~ r1_tarski(X7,k1_xboole_0)
      | X7 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(X1,k1_xboole_0)
    | ~ r2_hidden(X1,k4_orders_2(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
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

cnf(c_0_20,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( k4_orders_2(esk4_0,esk5_0) = k1_xboole_0
    | r1_tarski(esk1_1(k4_orders_2(esk4_0,esk5_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,plain,
    ( m2_orders_2(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2)
    | ~ r2_hidden(X1,k4_orders_2(X2,X3)) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( m1_orders_1(esk5_0,k1_orders_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_25,negated_conjecture,
    ( v5_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_26,negated_conjecture,
    ( v4_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_27,negated_conjecture,
    ( v3_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_29,negated_conjecture,
    ( esk1_1(k4_orders_2(esk4_0,esk5_0)) = k1_xboole_0
    | k4_orders_2(esk4_0,esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_30,plain,(
    ! [X10,X11,X12,X13] :
      ( ( X12 != k1_xboole_0
        | ~ m2_orders_2(X12,X10,X11)
        | ~ v6_orders_2(X12,X10)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ m1_orders_1(X11,k1_orders_1(u1_struct_0(X10)))
        | v2_struct_0(X10)
        | ~ v3_orders_2(X10)
        | ~ v4_orders_2(X10)
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( r2_wellord1(u1_orders_2(X10),X12)
        | ~ m2_orders_2(X12,X10,X11)
        | ~ v6_orders_2(X12,X10)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ m1_orders_1(X11,k1_orders_1(u1_struct_0(X10)))
        | v2_struct_0(X10)
        | ~ v3_orders_2(X10)
        | ~ v4_orders_2(X10)
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r2_hidden(X13,X12)
        | k1_funct_1(X11,k1_orders_2(X10,k3_orders_2(X10,X12,X13))) = X13
        | ~ m2_orders_2(X12,X10,X11)
        | ~ v6_orders_2(X12,X10)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ m1_orders_1(X11,k1_orders_1(u1_struct_0(X10)))
        | v2_struct_0(X10)
        | ~ v3_orders_2(X10)
        | ~ v4_orders_2(X10)
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( m1_subset_1(esk2_3(X10,X11,X12),u1_struct_0(X10))
        | X12 = k1_xboole_0
        | ~ r2_wellord1(u1_orders_2(X10),X12)
        | m2_orders_2(X12,X10,X11)
        | ~ v6_orders_2(X12,X10)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ m1_orders_1(X11,k1_orders_1(u1_struct_0(X10)))
        | v2_struct_0(X10)
        | ~ v3_orders_2(X10)
        | ~ v4_orders_2(X10)
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( r2_hidden(esk2_3(X10,X11,X12),X12)
        | X12 = k1_xboole_0
        | ~ r2_wellord1(u1_orders_2(X10),X12)
        | m2_orders_2(X12,X10,X11)
        | ~ v6_orders_2(X12,X10)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ m1_orders_1(X11,k1_orders_1(u1_struct_0(X10)))
        | v2_struct_0(X10)
        | ~ v3_orders_2(X10)
        | ~ v4_orders_2(X10)
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( k1_funct_1(X11,k1_orders_2(X10,k3_orders_2(X10,X12,esk2_3(X10,X11,X12)))) != esk2_3(X10,X11,X12)
        | X12 = k1_xboole_0
        | ~ r2_wellord1(u1_orders_2(X10),X12)
        | m2_orders_2(X12,X10,X11)
        | ~ v6_orders_2(X12,X10)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ m1_orders_1(X11,k1_orders_1(u1_struct_0(X10)))
        | v2_struct_0(X10)
        | ~ v3_orders_2(X10)
        | ~ v4_orders_2(X10)
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_orders_2])])])])])])).

fof(c_0_31,plain,(
    ! [X22,X23,X24] :
      ( ( v6_orders_2(X24,X22)
        | ~ m2_orders_2(X24,X22,X23)
        | v2_struct_0(X22)
        | ~ v3_orders_2(X22)
        | ~ v4_orders_2(X22)
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22)
        | ~ m1_orders_1(X23,k1_orders_1(u1_struct_0(X22))) )
      & ( m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ m2_orders_2(X24,X22,X23)
        | v2_struct_0(X22)
        | ~ v3_orders_2(X22)
        | ~ v4_orders_2(X22)
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22)
        | ~ m1_orders_1(X23,k1_orders_1(u1_struct_0(X22))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_orders_2])])])])])).

fof(c_0_32,plain,(
    ! [X25,X26] :
      ( v2_struct_0(X25)
      | ~ v3_orders_2(X25)
      | ~ v4_orders_2(X25)
      | ~ v5_orders_2(X25)
      | ~ l1_orders_2(X25)
      | ~ m1_orders_1(X26,k1_orders_1(u1_struct_0(X25)))
      | ~ v1_xboole_0(k4_orders_2(X25,X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_orders_2])])])).

cnf(c_0_33,negated_conjecture,
    ( m2_orders_2(X1,esk4_0,esk5_0)
    | ~ r2_hidden(X1,k4_orders_2(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( k4_orders_2(esk4_0,esk5_0) = k1_xboole_0
    | r2_hidden(k1_xboole_0,k4_orders_2(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_29])).

cnf(c_0_35,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( v6_orders_2(X1,X2)
    | v2_struct_0(X2)
    | ~ m2_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v2_struct_0(X2)
    | ~ m2_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ v1_xboole_0(k4_orders_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( k4_orders_2(esk4_0,esk5_0) = k1_xboole_0
    | m2_orders_2(k1_xboole_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_41,plain,
    ( v2_struct_0(X1)
    | ~ m2_orders_2(k1_xboole_0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_35,c_0_36]),c_0_37])])).

cnf(c_0_42,negated_conjecture,
    ( m2_orders_2(k1_xboole_0,esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_40])]),c_0_28])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_23]),c_0_42]),c_0_24]),c_0_25]),c_0_26]),c_0_27])]),c_0_28]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:32:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.042 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t87_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>k3_tarski(k4_orders_2(X1,X2))!=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_orders_2)).
% 0.19/0.40  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 0.19/0.40  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.19/0.40  fof(d17_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(X3=k4_orders_2(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>m2_orders_2(X4,X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_orders_2)).
% 0.19/0.40  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.19/0.40  fof(d16_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:((v6_orders_2(X3,X1)&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))=>(m2_orders_2(X3,X1,X2)<=>((X3!=k1_xboole_0&r2_wellord1(u1_orders_2(X1),X3))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>k1_funct_1(X2,k1_orders_2(X1,k3_orders_2(X1,X3,X4)))=X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_orders_2)).
% 0.19/0.40  fof(dt_m2_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))))=>![X3]:(m2_orders_2(X3,X1,X2)=>(v6_orders_2(X3,X1)&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 0.19/0.40  fof(fc9_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))))=>~(v1_xboole_0(k4_orders_2(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_orders_2)).
% 0.19/0.40  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.40  fof(c_0_9, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>k3_tarski(k4_orders_2(X1,X2))!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t87_orders_2])).
% 0.19/0.40  fof(c_0_10, plain, ![X8, X9]:(~r2_hidden(X8,X9)|r1_tarski(X8,k3_tarski(X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 0.19/0.40  fof(c_0_11, negated_conjecture, (((((~v2_struct_0(esk4_0)&v3_orders_2(esk4_0))&v4_orders_2(esk4_0))&v5_orders_2(esk4_0))&l1_orders_2(esk4_0))&(m1_orders_1(esk5_0,k1_orders_1(u1_struct_0(esk4_0)))&k3_tarski(k4_orders_2(esk4_0,esk5_0))=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).
% 0.19/0.40  cnf(c_0_12, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.40  cnf(c_0_13, negated_conjecture, (k3_tarski(k4_orders_2(esk4_0,esk5_0))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  fof(c_0_14, plain, ![X5]:(X5=k1_xboole_0|r2_hidden(esk1_1(X5),X5)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.19/0.40  fof(c_0_15, plain, ![X15, X16, X17, X18, X19, X20]:(((~r2_hidden(X18,X17)|m2_orders_2(X18,X15,X16)|X17!=k4_orders_2(X15,X16)|~m1_orders_1(X16,k1_orders_1(u1_struct_0(X15)))|(v2_struct_0(X15)|~v3_orders_2(X15)|~v4_orders_2(X15)|~v5_orders_2(X15)|~l1_orders_2(X15)))&(~m2_orders_2(X19,X15,X16)|r2_hidden(X19,X17)|X17!=k4_orders_2(X15,X16)|~m1_orders_1(X16,k1_orders_1(u1_struct_0(X15)))|(v2_struct_0(X15)|~v3_orders_2(X15)|~v4_orders_2(X15)|~v5_orders_2(X15)|~l1_orders_2(X15))))&((~r2_hidden(esk3_3(X15,X16,X20),X20)|~m2_orders_2(esk3_3(X15,X16,X20),X15,X16)|X20=k4_orders_2(X15,X16)|~m1_orders_1(X16,k1_orders_1(u1_struct_0(X15)))|(v2_struct_0(X15)|~v3_orders_2(X15)|~v4_orders_2(X15)|~v5_orders_2(X15)|~l1_orders_2(X15)))&(r2_hidden(esk3_3(X15,X16,X20),X20)|m2_orders_2(esk3_3(X15,X16,X20),X15,X16)|X20=k4_orders_2(X15,X16)|~m1_orders_1(X16,k1_orders_1(u1_struct_0(X15)))|(v2_struct_0(X15)|~v3_orders_2(X15)|~v4_orders_2(X15)|~v5_orders_2(X15)|~l1_orders_2(X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_orders_2])])])])])])])).
% 0.19/0.40  fof(c_0_16, plain, ![X7]:(~r1_tarski(X7,k1_xboole_0)|X7=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.19/0.40  cnf(c_0_17, negated_conjecture, (r1_tarski(X1,k1_xboole_0)|~r2_hidden(X1,k4_orders_2(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.19/0.40  cnf(c_0_18, plain, (X1=k1_xboole_0|r2_hidden(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.40  cnf(c_0_19, plain, (m2_orders_2(X1,X3,X4)|v2_struct_0(X3)|~r2_hidden(X1,X2)|X2!=k4_orders_2(X3,X4)|~m1_orders_1(X4,k1_orders_1(u1_struct_0(X3)))|~v3_orders_2(X3)|~v4_orders_2(X3)|~v5_orders_2(X3)|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.40  cnf(c_0_20, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  cnf(c_0_21, negated_conjecture, (k4_orders_2(esk4_0,esk5_0)=k1_xboole_0|r1_tarski(esk1_1(k4_orders_2(esk4_0,esk5_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.40  cnf(c_0_22, plain, (m2_orders_2(X1,X2,X3)|v2_struct_0(X2)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))|~l1_orders_2(X2)|~v5_orders_2(X2)|~v4_orders_2(X2)|~v3_orders_2(X2)|~r2_hidden(X1,k4_orders_2(X2,X3))), inference(er,[status(thm)],[c_0_19])).
% 0.19/0.40  cnf(c_0_23, negated_conjecture, (m1_orders_1(esk5_0,k1_orders_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  cnf(c_0_24, negated_conjecture, (l1_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  cnf(c_0_25, negated_conjecture, (v5_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  cnf(c_0_26, negated_conjecture, (v4_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  cnf(c_0_27, negated_conjecture, (v3_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  cnf(c_0_28, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  cnf(c_0_29, negated_conjecture, (esk1_1(k4_orders_2(esk4_0,esk5_0))=k1_xboole_0|k4_orders_2(esk4_0,esk5_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.40  fof(c_0_30, plain, ![X10, X11, X12, X13]:((((X12!=k1_xboole_0|~m2_orders_2(X12,X10,X11)|(~v6_orders_2(X12,X10)|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10))))|~m1_orders_1(X11,k1_orders_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v3_orders_2(X10)|~v4_orders_2(X10)|~v5_orders_2(X10)|~l1_orders_2(X10)))&(r2_wellord1(u1_orders_2(X10),X12)|~m2_orders_2(X12,X10,X11)|(~v6_orders_2(X12,X10)|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10))))|~m1_orders_1(X11,k1_orders_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v3_orders_2(X10)|~v4_orders_2(X10)|~v5_orders_2(X10)|~l1_orders_2(X10))))&(~m1_subset_1(X13,u1_struct_0(X10))|(~r2_hidden(X13,X12)|k1_funct_1(X11,k1_orders_2(X10,k3_orders_2(X10,X12,X13)))=X13)|~m2_orders_2(X12,X10,X11)|(~v6_orders_2(X12,X10)|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10))))|~m1_orders_1(X11,k1_orders_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v3_orders_2(X10)|~v4_orders_2(X10)|~v5_orders_2(X10)|~l1_orders_2(X10))))&((m1_subset_1(esk2_3(X10,X11,X12),u1_struct_0(X10))|(X12=k1_xboole_0|~r2_wellord1(u1_orders_2(X10),X12))|m2_orders_2(X12,X10,X11)|(~v6_orders_2(X12,X10)|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10))))|~m1_orders_1(X11,k1_orders_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v3_orders_2(X10)|~v4_orders_2(X10)|~v5_orders_2(X10)|~l1_orders_2(X10)))&((r2_hidden(esk2_3(X10,X11,X12),X12)|(X12=k1_xboole_0|~r2_wellord1(u1_orders_2(X10),X12))|m2_orders_2(X12,X10,X11)|(~v6_orders_2(X12,X10)|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10))))|~m1_orders_1(X11,k1_orders_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v3_orders_2(X10)|~v4_orders_2(X10)|~v5_orders_2(X10)|~l1_orders_2(X10)))&(k1_funct_1(X11,k1_orders_2(X10,k3_orders_2(X10,X12,esk2_3(X10,X11,X12))))!=esk2_3(X10,X11,X12)|(X12=k1_xboole_0|~r2_wellord1(u1_orders_2(X10),X12))|m2_orders_2(X12,X10,X11)|(~v6_orders_2(X12,X10)|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10))))|~m1_orders_1(X11,k1_orders_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v3_orders_2(X10)|~v4_orders_2(X10)|~v5_orders_2(X10)|~l1_orders_2(X10)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_orders_2])])])])])])).
% 0.19/0.40  fof(c_0_31, plain, ![X22, X23, X24]:((v6_orders_2(X24,X22)|~m2_orders_2(X24,X22,X23)|(v2_struct_0(X22)|~v3_orders_2(X22)|~v4_orders_2(X22)|~v5_orders_2(X22)|~l1_orders_2(X22)|~m1_orders_1(X23,k1_orders_1(u1_struct_0(X22)))))&(m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))|~m2_orders_2(X24,X22,X23)|(v2_struct_0(X22)|~v3_orders_2(X22)|~v4_orders_2(X22)|~v5_orders_2(X22)|~l1_orders_2(X22)|~m1_orders_1(X23,k1_orders_1(u1_struct_0(X22)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_orders_2])])])])])).
% 0.19/0.40  fof(c_0_32, plain, ![X25, X26]:(v2_struct_0(X25)|~v3_orders_2(X25)|~v4_orders_2(X25)|~v5_orders_2(X25)|~l1_orders_2(X25)|~m1_orders_1(X26,k1_orders_1(u1_struct_0(X25)))|~v1_xboole_0(k4_orders_2(X25,X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_orders_2])])])).
% 0.19/0.40  cnf(c_0_33, negated_conjecture, (m2_orders_2(X1,esk4_0,esk5_0)|~r2_hidden(X1,k4_orders_2(esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27])]), c_0_28])).
% 0.19/0.40  cnf(c_0_34, negated_conjecture, (k4_orders_2(esk4_0,esk5_0)=k1_xboole_0|r2_hidden(k1_xboole_0,k4_orders_2(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_18, c_0_29])).
% 0.19/0.40  cnf(c_0_35, plain, (v2_struct_0(X2)|X1!=k1_xboole_0|~m2_orders_2(X1,X2,X3)|~v6_orders_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.40  cnf(c_0_36, plain, (v6_orders_2(X1,X2)|v2_struct_0(X2)|~m2_orders_2(X1,X2,X3)|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.40  cnf(c_0_37, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|v2_struct_0(X2)|~m2_orders_2(X1,X2,X3)|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.40  cnf(c_0_38, plain, (v2_struct_0(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))|~v1_xboole_0(k4_orders_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.40  cnf(c_0_39, negated_conjecture, (k4_orders_2(esk4_0,esk5_0)=k1_xboole_0|m2_orders_2(k1_xboole_0,esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.40  cnf(c_0_40, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.40  cnf(c_0_41, plain, (v2_struct_0(X1)|~m2_orders_2(k1_xboole_0,X1,X2)|~m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)), inference(er,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_35, c_0_36]), c_0_37])])).
% 0.19/0.40  cnf(c_0_42, negated_conjecture, (m2_orders_2(k1_xboole_0,esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_40])]), c_0_28])).
% 0.19/0.40  cnf(c_0_43, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_23]), c_0_42]), c_0_24]), c_0_25]), c_0_26]), c_0_27])]), c_0_28]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 44
% 0.19/0.40  # Proof object clause steps            : 26
% 0.19/0.40  # Proof object formula steps           : 18
% 0.19/0.40  # Proof object conjectures             : 18
% 0.19/0.40  # Proof object clause conjectures      : 15
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 16
% 0.19/0.40  # Proof object initial formulas used   : 9
% 0.19/0.40  # Proof object generating inferences   : 8
% 0.19/0.40  # Proof object simplifying inferences  : 25
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 9
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 24
% 0.19/0.40  # Removed in clause preprocessing      : 0
% 0.19/0.40  # Initial clauses in saturation        : 24
% 0.19/0.40  # Processed clauses                    : 60
% 0.19/0.40  # ...of these trivial                  : 0
% 0.19/0.40  # ...subsumed                          : 2
% 0.19/0.40  # ...remaining for further processing  : 58
% 0.19/0.40  # Other redundant clauses eliminated   : 3
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 0
% 0.19/0.40  # Backward-rewritten                   : 1
% 0.19/0.40  # Generated clauses                    : 25
% 0.19/0.40  # ...of the previous two non-trivial   : 22
% 0.19/0.40  # Contextual simplify-reflections      : 6
% 0.19/0.40  # Paramodulations                      : 22
% 0.19/0.40  # Factorizations                       : 0
% 0.19/0.40  # Equation resolutions                 : 3
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 30
% 0.19/0.40  #    Positive orientable unit clauses  : 8
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 1
% 0.19/0.40  #    Non-unit-clauses                  : 21
% 0.19/0.40  # Current number of unprocessed clauses: 7
% 0.19/0.40  # ...number of literals in the above   : 72
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 25
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 562
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 47
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 8
% 0.19/0.40  # Unit Clause-clause subsumption calls : 3
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 1
% 0.19/0.40  # BW rewrite match successes           : 1
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 3409
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.048 s
% 0.19/0.40  # System time              : 0.005 s
% 0.19/0.40  # Total time               : 0.053 s
% 0.19/0.40  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
