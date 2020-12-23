%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0805+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:13 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   96 (1248 expanded)
%              Number of clauses        :   61 ( 485 expanded)
%              Number of leaves         :   17 ( 303 expanded)
%              Depth                    :   19
%              Number of atoms          :  367 (5881 expanded)
%              Number of equality atoms :   38 ( 948 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t58_wellord1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ~ ( v2_wellord1(X3)
          & r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X2,k3_relat_1(X3))
          & X1 != X2
          & r4_wellord1(k2_wellord1(X3,k1_wellord1(X3,X1)),k2_wellord1(X3,k1_wellord1(X3,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_wellord1)).

fof(t57_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => ! [X2] :
            ~ ( r2_hidden(X2,k3_relat_1(X1))
              & r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_wellord1)).

fof(t29_wellord1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => k2_wellord1(k2_wellord1(X3,X2),X1) = k2_wellord1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_wellord1)).

fof(dt_k2_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k2_wellord1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(l4_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v6_relat_2(X1)
      <=> ! [X2,X3] :
            ~ ( r2_hidden(X2,k3_relat_1(X1))
              & r2_hidden(X3,k3_relat_1(X1))
              & X2 != X3
              & ~ r2_hidden(k4_tarski(X2,X3),X1)
              & ~ r2_hidden(k4_tarski(X3,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l4_wellord1)).

fof(t35_wellord1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( v2_wellord1(X3)
          & r2_hidden(X1,k1_wellord1(X3,X2)) )
       => k1_wellord1(k2_wellord1(X3,k1_wellord1(X3,X2)),X1) = k1_wellord1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_wellord1)).

fof(t32_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v2_wellord1(X2)
       => v2_wellord1(k2_wellord1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_wellord1)).

fof(d4_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
      <=> ( v1_relat_2(X1)
          & v8_relat_2(X1)
          & v4_relat_2(X1)
          & v6_relat_2(X1)
          & v1_wellord1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

fof(d9_xboole_0,axiom,(
    ! [X1,X2] :
      ( r3_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        | r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_xboole_0)).

fof(t33_wellord1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( v2_wellord1(X3)
       => r3_xboole_0(k1_wellord1(X3,X1),k1_wellord1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_wellord1)).

fof(t40_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v2_wellord1(X2)
       => k3_relat_1(k2_wellord1(X2,k1_wellord1(X2,X1))) = k1_wellord1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_wellord1)).

fof(d1_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k1_wellord1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ( X4 != X2
                & r2_hidden(k4_tarski(X4,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(t50_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r4_wellord1(X1,X2)
           => r4_wellord1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ~ ( v2_wellord1(X3)
            & r2_hidden(X1,k3_relat_1(X3))
            & r2_hidden(X2,k3_relat_1(X3))
            & X1 != X2
            & r4_wellord1(k2_wellord1(X3,k1_wellord1(X3,X1)),k2_wellord1(X3,k1_wellord1(X3,X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t58_wellord1])).

fof(c_0_18,plain,(
    ! [X47,X48] :
      ( ~ v1_relat_1(X47)
      | ~ v2_wellord1(X47)
      | ~ r2_hidden(X48,k3_relat_1(X47))
      | ~ r4_wellord1(X47,k2_wellord1(X47,k1_wellord1(X47,X48))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t57_wellord1])])])).

fof(c_0_19,plain,(
    ! [X25,X26,X27] :
      ( ~ v1_relat_1(X27)
      | ~ r1_tarski(X25,X26)
      | k2_wellord1(k2_wellord1(X27,X26),X25) = k2_wellord1(X27,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_wellord1])])).

fof(c_0_20,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X16)
      | v1_relat_1(k2_wellord1(X16,X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_wellord1])])).

fof(c_0_21,plain,(
    ! [X20,X21,X22] :
      ( ( ~ v6_relat_2(X20)
        | ~ r2_hidden(X21,k3_relat_1(X20))
        | ~ r2_hidden(X22,k3_relat_1(X20))
        | X21 = X22
        | r2_hidden(k4_tarski(X21,X22),X20)
        | r2_hidden(k4_tarski(X22,X21),X20)
        | ~ v1_relat_1(X20) )
      & ( r2_hidden(esk3_1(X20),k3_relat_1(X20))
        | v6_relat_2(X20)
        | ~ v1_relat_1(X20) )
      & ( r2_hidden(esk4_1(X20),k3_relat_1(X20))
        | v6_relat_2(X20)
        | ~ v1_relat_1(X20) )
      & ( esk3_1(X20) != esk4_1(X20)
        | v6_relat_2(X20)
        | ~ v1_relat_1(X20) )
      & ( ~ r2_hidden(k4_tarski(esk3_1(X20),esk4_1(X20)),X20)
        | v6_relat_2(X20)
        | ~ v1_relat_1(X20) )
      & ( ~ r2_hidden(k4_tarski(esk4_1(X20),esk3_1(X20)),X20)
        | v6_relat_2(X20)
        | ~ v1_relat_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l4_wellord1])])])])])])).

fof(c_0_22,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & v2_wellord1(esk7_0)
    & r2_hidden(esk5_0,k3_relat_1(esk7_0))
    & r2_hidden(esk6_0,k3_relat_1(esk7_0))
    & esk5_0 != esk6_0
    & r4_wellord1(k2_wellord1(esk7_0,k1_wellord1(esk7_0,esk5_0)),k2_wellord1(esk7_0,k1_wellord1(esk7_0,esk6_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_23,plain,
    ( ~ v1_relat_1(X1)
    | ~ v2_wellord1(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k2_wellord1(k2_wellord1(X1,X3),X2) = k2_wellord1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( v1_relat_1(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X35,X36,X37] :
      ( ~ v1_relat_1(X37)
      | ~ v2_wellord1(X37)
      | ~ r2_hidden(X35,k1_wellord1(X37,X36))
      | k1_wellord1(k2_wellord1(X37,k1_wellord1(X37,X36)),X35) = k1_wellord1(X37,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_wellord1])])).

fof(c_0_27,plain,(
    ! [X30,X31] :
      ( ~ v1_relat_1(X31)
      | ~ v2_wellord1(X31)
      | v2_wellord1(k2_wellord1(X31,X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_wellord1])])).

cnf(c_0_28,plain,
    ( X2 = X3
    | r2_hidden(k4_tarski(X2,X3),X1)
    | r2_hidden(k4_tarski(X3,X2),X1)
    | ~ v6_relat_2(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r2_hidden(X3,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk6_0,k3_relat_1(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_31,plain,(
    ! [X13] :
      ( ( v1_relat_2(X13)
        | ~ v2_wellord1(X13)
        | ~ v1_relat_1(X13) )
      & ( v8_relat_2(X13)
        | ~ v2_wellord1(X13)
        | ~ v1_relat_1(X13) )
      & ( v4_relat_2(X13)
        | ~ v2_wellord1(X13)
        | ~ v1_relat_1(X13) )
      & ( v6_relat_2(X13)
        | ~ v2_wellord1(X13)
        | ~ v1_relat_1(X13) )
      & ( v1_wellord1(X13)
        | ~ v2_wellord1(X13)
        | ~ v1_relat_1(X13) )
      & ( ~ v1_relat_2(X13)
        | ~ v8_relat_2(X13)
        | ~ v4_relat_2(X13)
        | ~ v6_relat_2(X13)
        | ~ v1_wellord1(X13)
        | v2_wellord1(X13)
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).

cnf(c_0_32,plain,
    ( ~ r4_wellord1(k2_wellord1(X1,X2),k2_wellord1(X1,k1_wellord1(k2_wellord1(X1,X2),X3)))
    | ~ r1_tarski(k1_wellord1(k2_wellord1(X1,X2),X3),X2)
    | ~ v2_wellord1(k2_wellord1(X1,X2))
    | ~ r2_hidden(X3,k3_relat_1(k2_wellord1(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_33,plain,
    ( k1_wellord1(k2_wellord1(X1,k1_wellord1(X1,X3)),X2) = k1_wellord1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v2_wellord1(X1)
    | ~ r2_hidden(X2,k1_wellord1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( v2_wellord1(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v2_wellord1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_35,plain,(
    ! [X14,X15] :
      ( ( ~ r3_xboole_0(X14,X15)
        | r1_tarski(X14,X15)
        | r1_tarski(X15,X14) )
      & ( ~ r1_tarski(X14,X15)
        | r3_xboole_0(X14,X15) )
      & ( ~ r1_tarski(X15,X14)
        | r3_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_xboole_0])])])).

fof(c_0_36,plain,(
    ! [X32,X33,X34] :
      ( ~ v1_relat_1(X34)
      | ~ v2_wellord1(X34)
      | r3_xboole_0(k1_wellord1(X34,X32),k1_wellord1(X34,X33)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_wellord1])])).

cnf(c_0_37,negated_conjecture,
    ( X1 = esk6_0
    | r2_hidden(k4_tarski(esk6_0,X1),esk7_0)
    | r2_hidden(k4_tarski(X1,esk6_0),esk7_0)
    | ~ v6_relat_2(esk7_0)
    | ~ r2_hidden(X1,k3_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

cnf(c_0_38,plain,
    ( v6_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( v2_wellord1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_40,plain,
    ( ~ r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,X2)),k2_wellord1(X1,k1_wellord1(X1,X3)))
    | ~ r1_tarski(k1_wellord1(X1,X3),k1_wellord1(X1,X2))
    | ~ v2_wellord1(X1)
    | ~ r2_hidden(X3,k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X2))))
    | ~ r2_hidden(X3,k1_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( r4_wellord1(k2_wellord1(esk7_0,k1_wellord1(esk7_0,esk5_0)),k2_wellord1(esk7_0,k1_wellord1(esk7_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_42,plain,(
    ! [X40,X41] :
      ( ~ v1_relat_1(X41)
      | ~ v2_wellord1(X41)
      | k3_relat_1(k2_wellord1(X41,k1_wellord1(X41,X40))) = k1_wellord1(X41,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t40_wellord1])])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | r1_tarski(X2,X1)
    | ~ r3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( r3_xboole_0(k1_wellord1(X1,X2),k1_wellord1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v2_wellord1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_45,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11] :
      ( ( X8 != X6
        | ~ r2_hidden(X8,X7)
        | X7 != k1_wellord1(X5,X6)
        | ~ v1_relat_1(X5) )
      & ( r2_hidden(k4_tarski(X8,X6),X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k1_wellord1(X5,X6)
        | ~ v1_relat_1(X5) )
      & ( X9 = X6
        | ~ r2_hidden(k4_tarski(X9,X6),X5)
        | r2_hidden(X9,X7)
        | X7 != k1_wellord1(X5,X6)
        | ~ v1_relat_1(X5) )
      & ( ~ r2_hidden(esk1_3(X5,X10,X11),X11)
        | esk1_3(X5,X10,X11) = X10
        | ~ r2_hidden(k4_tarski(esk1_3(X5,X10,X11),X10),X5)
        | X11 = k1_wellord1(X5,X10)
        | ~ v1_relat_1(X5) )
      & ( esk1_3(X5,X10,X11) != X10
        | r2_hidden(esk1_3(X5,X10,X11),X11)
        | X11 = k1_wellord1(X5,X10)
        | ~ v1_relat_1(X5) )
      & ( r2_hidden(k4_tarski(esk1_3(X5,X10,X11),X10),X5)
        | r2_hidden(esk1_3(X5,X10,X11),X11)
        | X11 = k1_wellord1(X5,X10)
        | ~ v1_relat_1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).

cnf(c_0_46,negated_conjecture,
    ( X1 = esk6_0
    | r2_hidden(k4_tarski(X1,esk6_0),esk7_0)
    | r2_hidden(k4_tarski(esk6_0,X1),esk7_0)
    | ~ r2_hidden(X1,k3_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_30])])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk5_0,k3_relat_1(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_48,negated_conjecture,
    ( esk5_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_49,plain,(
    ! [X42,X43,X44] :
      ( ~ r2_hidden(X42,X43)
      | ~ m1_subset_1(X43,k1_zfmisc_1(X44))
      | m1_subset_1(X42,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_50,plain,(
    ! [X38,X39] :
      ( ( ~ m1_subset_1(X38,k1_zfmisc_1(X39))
        | r1_tarski(X38,X39) )
      & ( ~ r1_tarski(X38,X39)
        | m1_subset_1(X38,k1_zfmisc_1(X39)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_51,negated_conjecture,
    ( ~ r1_tarski(k1_wellord1(esk7_0,esk6_0),k1_wellord1(esk7_0,esk5_0))
    | ~ r2_hidden(esk6_0,k3_relat_1(k2_wellord1(esk7_0,k1_wellord1(esk7_0,esk5_0))))
    | ~ r2_hidden(esk6_0,k1_wellord1(esk7_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_39]),c_0_30])])).

cnf(c_0_52,plain,
    ( k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X2))) = k1_wellord1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v2_wellord1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,plain,
    ( r1_tarski(k1_wellord1(X1,X2),k1_wellord1(X1,X3))
    | r1_tarski(k1_wellord1(X1,X3),k1_wellord1(X1,X2))
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

fof(c_0_54,plain,(
    ! [X49,X50,X51] :
      ( ~ r2_hidden(X49,X50)
      | ~ m1_subset_1(X50,k1_zfmisc_1(X51))
      | ~ v1_xboole_0(X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_55,plain,
    ( X1 = X2
    | r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk5_0),esk7_0)
    | r2_hidden(k4_tarski(esk5_0,esk6_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])).

cnf(c_0_57,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_58,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_59,negated_conjecture,
    ( ~ r1_tarski(k1_wellord1(esk7_0,esk6_0),k1_wellord1(esk7_0,esk5_0))
    | ~ r2_hidden(esk6_0,k1_wellord1(esk7_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_39]),c_0_30])])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(k1_wellord1(esk7_0,X1),k1_wellord1(esk7_0,X2))
    | r1_tarski(k1_wellord1(esk7_0,X2),k1_wellord1(esk7_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_39]),c_0_30])])).

cnf(c_0_61,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_0,esk6_0),esk7_0)
    | r2_hidden(esk6_0,X1)
    | X1 != k1_wellord1(esk7_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_30])]),c_0_48])).

fof(c_0_63,plain,(
    ! [X28,X29] :
      ( ~ m1_subset_1(X28,X29)
      | v1_xboole_0(X29)
      | r2_hidden(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_64,plain,
    ( m1_subset_1(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(k1_wellord1(esk7_0,esk5_0),k1_wellord1(esk7_0,esk6_0))
    | ~ r2_hidden(esk6_0,k1_wellord1(esk7_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_66,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r1_tarski(X2,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_61,c_0_58])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk6_0,k1_wellord1(esk7_0,esk5_0))
    | r2_hidden(k4_tarski(esk5_0,esk6_0),esk7_0) ),
    inference(er,[status(thm)],[c_0_62])).

fof(c_0_68,plain,(
    ! [X45,X46] :
      ( ~ v1_relat_1(X45)
      | ~ v1_relat_1(X46)
      | ~ r4_wellord1(X45,X46)
      | r4_wellord1(X46,X45) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_wellord1])])])).

cnf(c_0_69,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(X1,k1_wellord1(esk7_0,esk6_0))
    | ~ r2_hidden(esk6_0,k1_wellord1(esk7_0,esk5_0))
    | ~ r2_hidden(X1,k1_wellord1(esk7_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( ~ v1_xboole_0(k1_wellord1(esk7_0,esk6_0))
    | ~ r2_hidden(esk6_0,k1_wellord1(esk7_0,esk5_0))
    | ~ r2_hidden(X1,k1_wellord1(esk7_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_65])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk6_0,k1_wellord1(esk7_0,esk5_0))
    | r2_hidden(esk5_0,X1)
    | X1 != k1_wellord1(esk7_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_67]),c_0_30])]),c_0_48])).

cnf(c_0_73,plain,
    ( r4_wellord1(X2,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r4_wellord1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_74,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,X3)
    | X3 != k1_wellord1(X4,X2)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(X1,k1_wellord1(esk7_0,esk6_0))
    | ~ r2_hidden(esk6_0,k1_wellord1(esk7_0,esk5_0))
    | ~ r2_hidden(X1,k1_wellord1(esk7_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk5_0,k1_wellord1(esk7_0,esk6_0))
    | r2_hidden(esk6_0,k1_wellord1(esk7_0,esk5_0)) ),
    inference(er,[status(thm)],[c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( r4_wellord1(k2_wellord1(esk7_0,k1_wellord1(esk7_0,esk6_0)),k2_wellord1(esk7_0,k1_wellord1(esk7_0,esk5_0)))
    | ~ v1_relat_1(k2_wellord1(esk7_0,k1_wellord1(esk7_0,esk6_0)))
    | ~ v1_relat_1(k2_wellord1(esk7_0,k1_wellord1(esk7_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_41])).

cnf(c_0_78,plain,
    ( X1 != k1_wellord1(X2,X3)
    | ~ r2_hidden(X3,X1)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_74])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(esk5_0,k1_wellord1(esk7_0,esk6_0))
    | r2_hidden(X1,k1_wellord1(esk7_0,esk6_0))
    | ~ r2_hidden(X1,k1_wellord1(esk7_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_80,negated_conjecture,
    ( ~ r1_tarski(k1_wellord1(esk7_0,esk5_0),k1_wellord1(esk7_0,esk6_0))
    | ~ r2_hidden(esk5_0,k3_relat_1(k2_wellord1(esk7_0,k1_wellord1(esk7_0,esk6_0))))
    | ~ r2_hidden(esk5_0,k1_wellord1(esk7_0,esk6_0))
    | ~ v1_relat_1(k2_wellord1(esk7_0,k1_wellord1(esk7_0,esk6_0)))
    | ~ v1_relat_1(k2_wellord1(esk7_0,k1_wellord1(esk7_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_77]),c_0_39]),c_0_30])])).

cnf(c_0_81,plain,
    ( ~ r2_hidden(X1,k1_wellord1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_78])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk6_0,k1_wellord1(esk7_0,esk6_0))
    | r2_hidden(esk5_0,k1_wellord1(esk7_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_76])).

cnf(c_0_83,negated_conjecture,
    ( ~ r1_tarski(k1_wellord1(esk7_0,esk5_0),k1_wellord1(esk7_0,esk6_0))
    | ~ r2_hidden(esk5_0,k1_wellord1(esk7_0,esk6_0))
    | ~ v1_relat_1(k2_wellord1(esk7_0,k1_wellord1(esk7_0,esk6_0)))
    | ~ v1_relat_1(k2_wellord1(esk7_0,k1_wellord1(esk7_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_52]),c_0_39]),c_0_30])])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(esk5_0,k1_wellord1(esk7_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_30])])).

cnf(c_0_85,negated_conjecture,
    ( m1_subset_1(X1,k1_wellord1(esk7_0,X2))
    | r1_tarski(k1_wellord1(esk7_0,X2),k1_wellord1(esk7_0,X3))
    | ~ r2_hidden(X1,k1_wellord1(esk7_0,X3)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_60])).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(k1_wellord1(esk7_0,X1),k1_wellord1(esk7_0,X2))
    | ~ v1_xboole_0(k1_wellord1(esk7_0,X1))
    | ~ r2_hidden(X3,k1_wellord1(esk7_0,X2)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_60])).

cnf(c_0_87,negated_conjecture,
    ( ~ r1_tarski(k1_wellord1(esk7_0,esk5_0),k1_wellord1(esk7_0,esk6_0))
    | ~ v1_relat_1(k2_wellord1(esk7_0,k1_wellord1(esk7_0,esk6_0)))
    | ~ v1_relat_1(k2_wellord1(esk7_0,k1_wellord1(esk7_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_84])])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_wellord1(esk7_0,X1))
    | r1_tarski(k1_wellord1(esk7_0,X1),k1_wellord1(esk7_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_84])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(k1_wellord1(esk7_0,X1),k1_wellord1(esk7_0,esk6_0))
    | ~ v1_xboole_0(k1_wellord1(esk7_0,X1)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_84])).

cnf(c_0_90,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_wellord1(esk7_0,esk5_0))
    | ~ v1_relat_1(k2_wellord1(esk7_0,k1_wellord1(esk7_0,esk6_0)))
    | ~ v1_relat_1(k2_wellord1(esk7_0,k1_wellord1(esk7_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_91,negated_conjecture,
    ( ~ v1_xboole_0(k1_wellord1(esk7_0,esk5_0))
    | ~ v1_relat_1(k2_wellord1(esk7_0,k1_wellord1(esk7_0,esk6_0)))
    | ~ v1_relat_1(k2_wellord1(esk7_0,k1_wellord1(esk7_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_87,c_0_89])).

cnf(c_0_92,negated_conjecture,
    ( r2_hidden(esk5_0,k1_wellord1(esk7_0,esk5_0))
    | ~ v1_relat_1(k2_wellord1(esk7_0,k1_wellord1(esk7_0,esk6_0)))
    | ~ v1_relat_1(k2_wellord1(esk7_0,k1_wellord1(esk7_0,esk5_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_90]),c_0_91])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(esk5_0,k1_wellord1(esk7_0,esk5_0))
    | ~ v1_relat_1(k2_wellord1(esk7_0,k1_wellord1(esk7_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_25]),c_0_30])])).

cnf(c_0_94,negated_conjecture,
    ( r2_hidden(esk5_0,k1_wellord1(esk7_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_25]),c_0_30])])).

cnf(c_0_95,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_94]),c_0_30])]),
    [proof]).

%------------------------------------------------------------------------------
