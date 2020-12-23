%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:13 EST 2020

% Result     : Theorem 0.10s
% Output     : CNFRefutation 0.10s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 207 expanded)
%              Number of clauses        :   39 (  74 expanded)
%              Number of leaves         :   11 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :  241 (1007 expanded)
%              Number of equality atoms :   22 ( 124 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   36 (   3 average)
%              Maximal term depth       :    3 (   1 average)

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

fof(t82_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m2_orders_2(X3,X1,X2)
             => ! [X4] :
                  ( m2_orders_2(X4,X1,X2)
                 => ~ r1_xboole_0(X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_orders_2)).

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

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(rc1_xboole_0,axiom,(
    ? [X1] : v1_xboole_0(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

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

fof(c_0_12,plain,(
    ! [X22,X23,X24,X25,X26,X27] :
      ( ( ~ r2_hidden(X25,X24)
        | m2_orders_2(X25,X22,X23)
        | X24 != k4_orders_2(X22,X23)
        | ~ m1_orders_1(X23,k1_orders_1(u1_struct_0(X22)))
        | v2_struct_0(X22)
        | ~ v3_orders_2(X22)
        | ~ v4_orders_2(X22)
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) )
      & ( ~ m2_orders_2(X26,X22,X23)
        | r2_hidden(X26,X24)
        | X24 != k4_orders_2(X22,X23)
        | ~ m1_orders_1(X23,k1_orders_1(u1_struct_0(X22)))
        | v2_struct_0(X22)
        | ~ v3_orders_2(X22)
        | ~ v4_orders_2(X22)
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) )
      & ( ~ r2_hidden(esk4_3(X22,X23,X27),X27)
        | ~ m2_orders_2(esk4_3(X22,X23,X27),X22,X23)
        | X27 = k4_orders_2(X22,X23)
        | ~ m1_orders_1(X23,k1_orders_1(u1_struct_0(X22)))
        | v2_struct_0(X22)
        | ~ v3_orders_2(X22)
        | ~ v4_orders_2(X22)
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) )
      & ( r2_hidden(esk4_3(X22,X23,X27),X27)
        | m2_orders_2(esk4_3(X22,X23,X27),X22,X23)
        | X27 = k4_orders_2(X22,X23)
        | ~ m1_orders_1(X23,k1_orders_1(u1_struct_0(X22)))
        | v2_struct_0(X22)
        | ~ v3_orders_2(X22)
        | ~ v4_orders_2(X22)
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_orders_2])])])])])])])).

fof(c_0_13,plain,(
    ! [X32,X33,X34,X35] :
      ( v2_struct_0(X32)
      | ~ v3_orders_2(X32)
      | ~ v4_orders_2(X32)
      | ~ v5_orders_2(X32)
      | ~ l1_orders_2(X32)
      | ~ m1_orders_1(X33,k1_orders_1(u1_struct_0(X32)))
      | ~ m2_orders_2(X34,X32,X33)
      | ~ m2_orders_2(X35,X32,X33)
      | ~ r1_xboole_0(X34,X35) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t82_orders_2])])])])).

fof(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    & v3_orders_2(esk6_0)
    & v4_orders_2(esk6_0)
    & v5_orders_2(esk6_0)
    & l1_orders_2(esk6_0)
    & m1_orders_1(esk7_0,k1_orders_1(u1_struct_0(esk6_0)))
    & k3_tarski(k4_orders_2(esk6_0,esk7_0)) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

fof(c_0_15,plain,(
    ! [X29,X30] :
      ( v2_struct_0(X29)
      | ~ v3_orders_2(X29)
      | ~ v4_orders_2(X29)
      | ~ v5_orders_2(X29)
      | ~ l1_orders_2(X29)
      | ~ m1_orders_1(X30,k1_orders_1(u1_struct_0(X29)))
      | m2_orders_2(esk5_2(X29,X30),X29,X30) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[existence_m2_orders_2])])])])).

cnf(c_0_16,plain,
    ( m2_orders_2(X1,X3,X4)
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k4_orders_2(X3,X4)
    | ~ m1_orders_1(X4,k1_orders_1(u1_struct_0(X3)))
    | ~ v3_orders_2(X3)
    | ~ v4_orders_2(X3)
    | ~ v5_orders_2(X3)
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X20,X21] :
      ( ~ r2_hidden(X20,X21)
      | r1_tarski(X20,k3_tarski(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

fof(c_0_18,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_19,plain,
    ( v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ m2_orders_2(X3,X1,X2)
    | ~ m2_orders_2(X4,X1,X2)
    | ~ r1_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( m1_orders_1(esk7_0,k1_orders_1(u1_struct_0(esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( l1_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( v5_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( v4_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,negated_conjecture,
    ( v3_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,plain,
    ( v2_struct_0(X1)
    | m2_orders_2(esk5_2(X1,X2),X1,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,plain,
    ( m2_orders_2(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2)
    | ~ r2_hidden(X1,k4_orders_2(X2,X3)) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( ~ m2_orders_2(X1,esk6_0,esk7_0)
    | ~ m2_orders_2(X2,esk6_0,esk7_0)
    | ~ r1_xboole_0(X2,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( m2_orders_2(esk5_2(esk6_0,esk7_0),esk6_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( m2_orders_2(X1,esk6_0,esk7_0)
    | ~ r2_hidden(X1,k4_orders_2(esk6_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24])]),c_0_25])).

fof(c_0_33,plain,(
    ! [X17,X18] :
      ( ( r1_tarski(X17,X18)
        | X17 != X18 )
      & ( r1_tarski(X18,X17)
        | X17 != X18 )
      & ( ~ r1_tarski(X17,X18)
        | ~ r1_tarski(X18,X17)
        | X17 = X18 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_34,plain,
    ( r1_tarski(esk1_1(X1),k3_tarski(X1))
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( k3_tarski(k4_orders_2(esk6_0,esk7_0)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_36,plain,(
    ! [X19] : r1_tarski(k1_xboole_0,X19) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_37,plain,(
    ! [X9] :
      ( ~ v1_xboole_0(X9)
      | X9 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

fof(c_0_38,plain,(
    v1_xboole_0(esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_xboole_0])])).

cnf(c_0_39,negated_conjecture,
    ( ~ m2_orders_2(X1,esk6_0,esk7_0)
    | ~ r1_xboole_0(X1,esk5_2(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( m2_orders_2(esk1_1(k4_orders_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | v1_xboole_0(k4_orders_2(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_29])).

cnf(c_0_41,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(esk1_1(k4_orders_2(esk6_0,esk7_0)),k1_xboole_0)
    | v1_xboole_0(k4_orders_2(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_44,plain,(
    ! [X11,X12,X14,X15,X16] :
      ( ( r2_hidden(esk3_2(X11,X12),X11)
        | r1_xboole_0(X11,X12) )
      & ( r2_hidden(esk3_2(X11,X12),X12)
        | r1_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X16,X14)
        | ~ r2_hidden(X16,X15)
        | ~ r1_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_45,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,plain,
    ( v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( v1_xboole_0(k4_orders_2(esk6_0,esk7_0))
    | ~ r1_xboole_0(esk1_1(k4_orders_2(esk6_0,esk7_0)),esk5_2(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( esk1_1(k4_orders_2(esk6_0,esk7_0)) = k1_xboole_0
    | v1_xboole_0(k4_orders_2(esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])])).

cnf(c_0_49,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_50,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,plain,
    ( esk2_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( v1_xboole_0(k4_orders_2(esk6_0,esk7_0))
    | ~ r1_xboole_0(k1_xboole_0,esk5_2(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,plain,
    ( r1_xboole_0(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_54,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_46,c_0_51])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,X4)
    | v2_struct_0(X2)
    | ~ m2_orders_2(X1,X2,X3)
    | X4 != k4_orders_2(X2,X3)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_56,negated_conjecture,
    ( v1_xboole_0(k4_orders_2(esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])])).

cnf(c_0_57,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k4_orders_2(X1,X3))
    | ~ m2_orders_2(X2,X1,X3)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( k4_orders_2(esk6_0,esk7_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(X1,k1_xboole_0)
    | ~ m2_orders_2(X1,esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24])]),c_0_25]),c_0_58])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk5_2(esk6_0,esk7_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_31])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_60]),c_0_54])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.10/0.32  % Computer   : n003.cluster.edu
% 0.10/0.32  % Model      : x86_64 x86_64
% 0.10/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.32  % Memory     : 8042.1875MB
% 0.10/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.32  % CPULimit   : 60
% 0.10/0.32  % WCLimit    : 600
% 0.10/0.32  % DateTime   : Tue Dec  1 15:39:57 EST 2020
% 0.10/0.32  % CPUTime    : 
% 0.10/0.33  # Version: 2.5pre002
% 0.10/0.33  # No SInE strategy applied
% 0.10/0.33  # Trying AutoSched0 for 299 seconds
% 0.10/0.36  # AutoSched0-Mode selected heuristic G_E___008_C18_F1_PI_SE_CS_SP_CO_S4S
% 0.10/0.36  # and selection function SelectNewComplexAHPNS.
% 0.10/0.36  #
% 0.10/0.36  # Preprocessing time       : 0.029 s
% 0.10/0.36  
% 0.10/0.36  # Proof found!
% 0.10/0.36  # SZS status Theorem
% 0.10/0.36  # SZS output start CNFRefutation
% 0.10/0.36  fof(t87_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>k3_tarski(k4_orders_2(X1,X2))!=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_orders_2)).
% 0.10/0.36  fof(d17_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(X3=k4_orders_2(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>m2_orders_2(X4,X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_orders_2)).
% 0.10/0.36  fof(t82_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(m2_orders_2(X3,X1,X2)=>![X4]:(m2_orders_2(X4,X1,X2)=>~(r1_xboole_0(X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_orders_2)).
% 0.10/0.36  fof(existence_m2_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))))=>?[X3]:m2_orders_2(X3,X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m2_orders_2)).
% 0.10/0.36  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 0.10/0.36  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.10/0.36  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.10/0.36  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.10/0.36  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.10/0.36  fof(rc1_xboole_0, axiom, ?[X1]:v1_xboole_0(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 0.10/0.36  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.10/0.36  fof(c_0_11, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>k3_tarski(k4_orders_2(X1,X2))!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t87_orders_2])).
% 0.10/0.36  fof(c_0_12, plain, ![X22, X23, X24, X25, X26, X27]:(((~r2_hidden(X25,X24)|m2_orders_2(X25,X22,X23)|X24!=k4_orders_2(X22,X23)|~m1_orders_1(X23,k1_orders_1(u1_struct_0(X22)))|(v2_struct_0(X22)|~v3_orders_2(X22)|~v4_orders_2(X22)|~v5_orders_2(X22)|~l1_orders_2(X22)))&(~m2_orders_2(X26,X22,X23)|r2_hidden(X26,X24)|X24!=k4_orders_2(X22,X23)|~m1_orders_1(X23,k1_orders_1(u1_struct_0(X22)))|(v2_struct_0(X22)|~v3_orders_2(X22)|~v4_orders_2(X22)|~v5_orders_2(X22)|~l1_orders_2(X22))))&((~r2_hidden(esk4_3(X22,X23,X27),X27)|~m2_orders_2(esk4_3(X22,X23,X27),X22,X23)|X27=k4_orders_2(X22,X23)|~m1_orders_1(X23,k1_orders_1(u1_struct_0(X22)))|(v2_struct_0(X22)|~v3_orders_2(X22)|~v4_orders_2(X22)|~v5_orders_2(X22)|~l1_orders_2(X22)))&(r2_hidden(esk4_3(X22,X23,X27),X27)|m2_orders_2(esk4_3(X22,X23,X27),X22,X23)|X27=k4_orders_2(X22,X23)|~m1_orders_1(X23,k1_orders_1(u1_struct_0(X22)))|(v2_struct_0(X22)|~v3_orders_2(X22)|~v4_orders_2(X22)|~v5_orders_2(X22)|~l1_orders_2(X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_orders_2])])])])])])])).
% 0.10/0.36  fof(c_0_13, plain, ![X32, X33, X34, X35]:(v2_struct_0(X32)|~v3_orders_2(X32)|~v4_orders_2(X32)|~v5_orders_2(X32)|~l1_orders_2(X32)|(~m1_orders_1(X33,k1_orders_1(u1_struct_0(X32)))|(~m2_orders_2(X34,X32,X33)|(~m2_orders_2(X35,X32,X33)|~r1_xboole_0(X34,X35))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t82_orders_2])])])])).
% 0.10/0.36  fof(c_0_14, negated_conjecture, (((((~v2_struct_0(esk6_0)&v3_orders_2(esk6_0))&v4_orders_2(esk6_0))&v5_orders_2(esk6_0))&l1_orders_2(esk6_0))&(m1_orders_1(esk7_0,k1_orders_1(u1_struct_0(esk6_0)))&k3_tarski(k4_orders_2(esk6_0,esk7_0))=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).
% 0.10/0.36  fof(c_0_15, plain, ![X29, X30]:(v2_struct_0(X29)|~v3_orders_2(X29)|~v4_orders_2(X29)|~v5_orders_2(X29)|~l1_orders_2(X29)|~m1_orders_1(X30,k1_orders_1(u1_struct_0(X29)))|m2_orders_2(esk5_2(X29,X30),X29,X30)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[existence_m2_orders_2])])])])).
% 0.10/0.36  cnf(c_0_16, plain, (m2_orders_2(X1,X3,X4)|v2_struct_0(X3)|~r2_hidden(X1,X2)|X2!=k4_orders_2(X3,X4)|~m1_orders_1(X4,k1_orders_1(u1_struct_0(X3)))|~v3_orders_2(X3)|~v4_orders_2(X3)|~v5_orders_2(X3)|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.10/0.36  fof(c_0_17, plain, ![X20, X21]:(~r2_hidden(X20,X21)|r1_tarski(X20,k3_tarski(X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 0.10/0.36  fof(c_0_18, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.10/0.36  cnf(c_0_19, plain, (v2_struct_0(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))|~m2_orders_2(X3,X1,X2)|~m2_orders_2(X4,X1,X2)|~r1_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.10/0.36  cnf(c_0_20, negated_conjecture, (m1_orders_1(esk7_0,k1_orders_1(u1_struct_0(esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.10/0.36  cnf(c_0_21, negated_conjecture, (l1_orders_2(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.10/0.36  cnf(c_0_22, negated_conjecture, (v5_orders_2(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.10/0.36  cnf(c_0_23, negated_conjecture, (v4_orders_2(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.10/0.36  cnf(c_0_24, negated_conjecture, (v3_orders_2(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.10/0.36  cnf(c_0_25, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.10/0.36  cnf(c_0_26, plain, (v2_struct_0(X1)|m2_orders_2(esk5_2(X1,X2),X1,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.10/0.36  cnf(c_0_27, plain, (m2_orders_2(X1,X2,X3)|v2_struct_0(X2)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))|~l1_orders_2(X2)|~v5_orders_2(X2)|~v4_orders_2(X2)|~v3_orders_2(X2)|~r2_hidden(X1,k4_orders_2(X2,X3))), inference(er,[status(thm)],[c_0_16])).
% 0.10/0.36  cnf(c_0_28, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.10/0.36  cnf(c_0_29, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.10/0.36  cnf(c_0_30, negated_conjecture, (~m2_orders_2(X1,esk6_0,esk7_0)|~m2_orders_2(X2,esk6_0,esk7_0)|~r1_xboole_0(X2,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_24])]), c_0_25])).
% 0.10/0.36  cnf(c_0_31, negated_conjecture, (m2_orders_2(esk5_2(esk6_0,esk7_0),esk6_0,esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_24])]), c_0_25])).
% 0.10/0.36  cnf(c_0_32, negated_conjecture, (m2_orders_2(X1,esk6_0,esk7_0)|~r2_hidden(X1,k4_orders_2(esk6_0,esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_24])]), c_0_25])).
% 0.10/0.36  fof(c_0_33, plain, ![X17, X18]:(((r1_tarski(X17,X18)|X17!=X18)&(r1_tarski(X18,X17)|X17!=X18))&(~r1_tarski(X17,X18)|~r1_tarski(X18,X17)|X17=X18)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.10/0.36  cnf(c_0_34, plain, (r1_tarski(esk1_1(X1),k3_tarski(X1))|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.10/0.36  cnf(c_0_35, negated_conjecture, (k3_tarski(k4_orders_2(esk6_0,esk7_0))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.10/0.36  fof(c_0_36, plain, ![X19]:r1_tarski(k1_xboole_0,X19), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.10/0.36  fof(c_0_37, plain, ![X9]:(~v1_xboole_0(X9)|X9=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.10/0.36  fof(c_0_38, plain, v1_xboole_0(esk2_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_xboole_0])])).
% 0.10/0.36  cnf(c_0_39, negated_conjecture, (~m2_orders_2(X1,esk6_0,esk7_0)|~r1_xboole_0(X1,esk5_2(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.10/0.36  cnf(c_0_40, negated_conjecture, (m2_orders_2(esk1_1(k4_orders_2(esk6_0,esk7_0)),esk6_0,esk7_0)|v1_xboole_0(k4_orders_2(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_32, c_0_29])).
% 0.10/0.36  cnf(c_0_41, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.10/0.36  cnf(c_0_42, negated_conjecture, (r1_tarski(esk1_1(k4_orders_2(esk6_0,esk7_0)),k1_xboole_0)|v1_xboole_0(k4_orders_2(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.10/0.36  cnf(c_0_43, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.10/0.36  fof(c_0_44, plain, ![X11, X12, X14, X15, X16]:(((r2_hidden(esk3_2(X11,X12),X11)|r1_xboole_0(X11,X12))&(r2_hidden(esk3_2(X11,X12),X12)|r1_xboole_0(X11,X12)))&(~r2_hidden(X16,X14)|~r2_hidden(X16,X15)|~r1_xboole_0(X14,X15))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.10/0.36  cnf(c_0_45, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.10/0.36  cnf(c_0_46, plain, (v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.10/0.36  cnf(c_0_47, negated_conjecture, (v1_xboole_0(k4_orders_2(esk6_0,esk7_0))|~r1_xboole_0(esk1_1(k4_orders_2(esk6_0,esk7_0)),esk5_2(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.10/0.36  cnf(c_0_48, negated_conjecture, (esk1_1(k4_orders_2(esk6_0,esk7_0))=k1_xboole_0|v1_xboole_0(k4_orders_2(esk6_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])])).
% 0.10/0.36  cnf(c_0_49, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.10/0.36  cnf(c_0_50, plain, (r2_hidden(esk3_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.10/0.36  cnf(c_0_51, plain, (esk2_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.10/0.36  cnf(c_0_52, negated_conjecture, (v1_xboole_0(k4_orders_2(esk6_0,esk7_0))|~r1_xboole_0(k1_xboole_0,esk5_2(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.10/0.36  cnf(c_0_53, plain, (r1_xboole_0(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.10/0.36  cnf(c_0_54, plain, (v1_xboole_0(k1_xboole_0)), inference(rw,[status(thm)],[c_0_46, c_0_51])).
% 0.10/0.36  cnf(c_0_55, plain, (r2_hidden(X1,X4)|v2_struct_0(X2)|~m2_orders_2(X1,X2,X3)|X4!=k4_orders_2(X2,X3)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.10/0.36  cnf(c_0_56, negated_conjecture, (v1_xboole_0(k4_orders_2(esk6_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])])).
% 0.10/0.36  cnf(c_0_57, plain, (v2_struct_0(X1)|r2_hidden(X2,k4_orders_2(X1,X3))|~m2_orders_2(X2,X1,X3)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X1)))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)), inference(er,[status(thm)],[c_0_55])).
% 0.10/0.36  cnf(c_0_58, negated_conjecture, (k4_orders_2(esk6_0,esk7_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_45, c_0_56])).
% 0.10/0.36  cnf(c_0_59, negated_conjecture, (r2_hidden(X1,k1_xboole_0)|~m2_orders_2(X1,esk6_0,esk7_0)), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_24])]), c_0_25]), c_0_58])).
% 0.10/0.36  cnf(c_0_60, negated_conjecture, (r2_hidden(esk5_2(esk6_0,esk7_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_59, c_0_31])).
% 0.10/0.36  cnf(c_0_61, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_60]), c_0_54])]), ['proof']).
% 0.10/0.36  # SZS output end CNFRefutation
% 0.10/0.36  # Proof object total steps             : 62
% 0.10/0.36  # Proof object clause steps            : 39
% 0.10/0.36  # Proof object formula steps           : 23
% 0.10/0.36  # Proof object conjectures             : 24
% 0.10/0.36  # Proof object clause conjectures      : 21
% 0.10/0.36  # Proof object formula conjectures     : 3
% 0.10/0.36  # Proof object initial clauses used    : 19
% 0.10/0.36  # Proof object initial formulas used   : 11
% 0.10/0.36  # Proof object generating inferences   : 17
% 0.10/0.36  # Proof object simplifying inferences  : 34
% 0.10/0.36  # Training examples: 0 positive, 0 negative
% 0.10/0.36  # Parsed axioms                        : 11
% 0.10/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.10/0.36  # Initial clauses                      : 25
% 0.10/0.36  # Removed in clause preprocessing      : 0
% 0.10/0.36  # Initial clauses in saturation        : 25
% 0.10/0.36  # Processed clauses                    : 90
% 0.10/0.36  # ...of these trivial                  : 1
% 0.10/0.36  # ...subsumed                          : 16
% 0.10/0.36  # ...remaining for further processing  : 73
% 0.10/0.36  # Other redundant clauses eliminated   : 4
% 0.10/0.36  # Clauses deleted for lack of memory   : 0
% 0.10/0.36  # Backward-subsumed                    : 5
% 0.10/0.36  # Backward-rewritten                   : 20
% 0.10/0.36  # Generated clauses                    : 122
% 0.10/0.36  # ...of the previous two non-trivial   : 103
% 0.10/0.36  # Contextual simplify-reflections      : 0
% 0.10/0.36  # Paramodulations                      : 118
% 0.10/0.36  # Factorizations                       : 0
% 0.10/0.36  # Equation resolutions                 : 4
% 0.10/0.36  # Propositional unsat checks           : 0
% 0.10/0.36  #    Propositional check models        : 0
% 0.10/0.36  #    Propositional check unsatisfiable : 0
% 0.10/0.36  #    Propositional clauses             : 0
% 0.10/0.36  #    Propositional clauses after purity: 0
% 0.10/0.36  #    Propositional unsat core size     : 0
% 0.10/0.36  #    Propositional preprocessing time  : 0.000
% 0.10/0.36  #    Propositional encoding time       : 0.000
% 0.10/0.36  #    Propositional solver time         : 0.000
% 0.10/0.36  #    Success case prop preproc time    : 0.000
% 0.10/0.36  #    Success case prop encoding time   : 0.000
% 0.10/0.36  #    Success case prop solver time     : 0.000
% 0.10/0.36  # Current number of processed clauses  : 44
% 0.10/0.36  #    Positive orientable unit clauses  : 13
% 0.10/0.36  #    Positive unorientable unit clauses: 0
% 0.10/0.36  #    Negative unit clauses             : 3
% 0.10/0.36  #    Non-unit-clauses                  : 28
% 0.10/0.36  # Current number of unprocessed clauses: 36
% 0.10/0.36  # ...number of literals in the above   : 96
% 0.10/0.36  # Current number of archived formulas  : 0
% 0.10/0.36  # Current number of archived clauses   : 25
% 0.10/0.36  # Clause-clause subsumption calls (NU) : 608
% 0.10/0.36  # Rec. Clause-clause subsumption calls : 308
% 0.10/0.36  # Non-unit clause-clause subsumptions  : 19
% 0.10/0.36  # Unit Clause-clause subsumption calls : 18
% 0.10/0.36  # Rewrite failures with RHS unbound    : 0
% 0.10/0.36  # BW rewrite match attempts            : 9
% 0.10/0.36  # BW rewrite match successes           : 4
% 0.10/0.36  # Condensation attempts                : 90
% 0.10/0.36  # Condensation successes               : 4
% 0.10/0.36  # Termbank termtop insertions          : 3715
% 0.10/0.36  
% 0.10/0.36  # -------------------------------------------------
% 0.10/0.36  # User time                : 0.035 s
% 0.10/0.36  # System time              : 0.002 s
% 0.10/0.36  # Total time               : 0.037 s
% 0.10/0.36  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
