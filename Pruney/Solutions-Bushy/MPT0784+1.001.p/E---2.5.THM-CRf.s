%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0784+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:11 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 436 expanded)
%              Number of clauses        :   56 ( 187 expanded)
%              Number of leaves         :   11 ( 101 expanded)
%              Depth                    :   21
%              Number of atoms          :  291 (1644 expanded)
%              Number of equality atoms :   37 ( 166 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t33_wellord1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( v2_wellord1(X3)
       => r3_xboole_0(k1_wellord1(X3,X1),k1_wellord1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_wellord1)).

fof(d4_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
      <=> ( v1_relat_2(X1)
          & v8_relat_2(X1)
          & v4_relat_2(X1)
          & v6_relat_2(X1)
          & v1_wellord1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord1)).

fof(t2_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k3_relat_1(X2))
        | k1_wellord1(X2,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_wellord1)).

fof(d9_xboole_0,axiom,(
    ! [X1,X2] :
      ( r3_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        | r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l4_wellord1)).

fof(d1_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k1_wellord1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ( X4 != X2
                & r2_hidden(k4_tarski(X4,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(l2_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v8_relat_2(X1)
      <=> ! [X2,X3,X4] :
            ( ( r2_hidden(k4_tarski(X2,X3),X1)
              & r2_hidden(k4_tarski(X3,X4),X1) )
           => r2_hidden(k4_tarski(X2,X4),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l2_wellord1)).

fof(reflexivity_r3_xboole_0,axiom,(
    ! [X1,X2] : r3_xboole_0(X1,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_xboole_0)).

fof(l3_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_2(X1)
      <=> ! [X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X1)
              & r2_hidden(k4_tarski(X3,X2),X1) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_wellord1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( v2_wellord1(X3)
         => r3_xboole_0(k1_wellord1(X3,X1),k1_wellord1(X3,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t33_wellord1])).

fof(c_0_12,plain,(
    ! [X19] :
      ( ( v1_relat_2(X19)
        | ~ v2_wellord1(X19)
        | ~ v1_relat_1(X19) )
      & ( v8_relat_2(X19)
        | ~ v2_wellord1(X19)
        | ~ v1_relat_1(X19) )
      & ( v4_relat_2(X19)
        | ~ v2_wellord1(X19)
        | ~ v1_relat_1(X19) )
      & ( v6_relat_2(X19)
        | ~ v2_wellord1(X19)
        | ~ v1_relat_1(X19) )
      & ( v1_wellord1(X19)
        | ~ v2_wellord1(X19)
        | ~ v1_relat_1(X19) )
      & ( ~ v1_relat_2(X19)
        | ~ v8_relat_2(X19)
        | ~ v4_relat_2(X19)
        | ~ v6_relat_2(X19)
        | ~ v1_wellord1(X19)
        | v2_wellord1(X19)
        | ~ v1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).

fof(c_0_13,negated_conjecture,
    ( v1_relat_1(esk12_0)
    & v2_wellord1(esk12_0)
    & ~ r3_xboole_0(k1_wellord1(esk12_0,esk10_0),k1_wellord1(esk12_0,esk11_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_14,plain,(
    ! [X40,X41] :
      ( ~ v1_relat_1(X41)
      | r2_hidden(X40,k3_relat_1(X41))
      | k1_wellord1(X41,X40) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_wellord1])])).

fof(c_0_15,plain,(
    ! [X20,X21] :
      ( ( ~ r3_xboole_0(X20,X21)
        | r1_tarski(X20,X21)
        | r1_tarski(X21,X20) )
      & ( ~ r1_tarski(X20,X21)
        | r3_xboole_0(X20,X21) )
      & ( ~ r1_tarski(X21,X20)
        | r3_xboole_0(X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_xboole_0])])])).

fof(c_0_16,plain,(
    ! [X42] : r1_tarski(k1_xboole_0,X42) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_17,plain,(
    ! [X34,X35,X36] :
      ( ( ~ v6_relat_2(X34)
        | ~ r2_hidden(X35,k3_relat_1(X34))
        | ~ r2_hidden(X36,k3_relat_1(X34))
        | X35 = X36
        | r2_hidden(k4_tarski(X35,X36),X34)
        | r2_hidden(k4_tarski(X36,X35),X34)
        | ~ v1_relat_1(X34) )
      & ( r2_hidden(esk8_1(X34),k3_relat_1(X34))
        | v6_relat_2(X34)
        | ~ v1_relat_1(X34) )
      & ( r2_hidden(esk9_1(X34),k3_relat_1(X34))
        | v6_relat_2(X34)
        | ~ v1_relat_1(X34) )
      & ( esk8_1(X34) != esk9_1(X34)
        | v6_relat_2(X34)
        | ~ v1_relat_1(X34) )
      & ( ~ r2_hidden(k4_tarski(esk8_1(X34),esk9_1(X34)),X34)
        | v6_relat_2(X34)
        | ~ v1_relat_1(X34) )
      & ( ~ r2_hidden(k4_tarski(esk9_1(X34),esk8_1(X34)),X34)
        | v6_relat_2(X34)
        | ~ v1_relat_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l4_wellord1])])])])])])).

cnf(c_0_18,plain,
    ( v6_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( v2_wellord1(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( r2_hidden(X2,k3_relat_1(X1))
    | k1_wellord1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( r3_xboole_0(X2,X1)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( X2 = X3
    | r2_hidden(k4_tarski(X2,X3),X1)
    | r2_hidden(k4_tarski(X3,X2),X1)
    | ~ v6_relat_2(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r2_hidden(X3,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( v6_relat_2(esk12_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

cnf(c_0_26,negated_conjecture,
    ( ~ r3_xboole_0(k1_wellord1(esk12_0,esk10_0),k1_wellord1(esk12_0,esk11_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,negated_conjecture,
    ( k1_wellord1(esk12_0,X1) = k1_xboole_0
    | r2_hidden(X1,k3_relat_1(esk12_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_19])).

cnf(c_0_28,plain,
    ( r3_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( r3_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_30,negated_conjecture,
    ( X1 = X2
    | r2_hidden(k4_tarski(X1,X2),esk12_0)
    | r2_hidden(k4_tarski(X2,X1),esk12_0)
    | ~ r2_hidden(X2,k3_relat_1(esk12_0))
    | ~ r2_hidden(X1,k3_relat_1(esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_19]),c_0_25])])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk11_0,k3_relat_1(esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

cnf(c_0_32,plain,
    ( r3_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_23])).

fof(c_0_33,plain,(
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

fof(c_0_34,plain,(
    ! [X13,X14,X15,X16,X17] :
      ( ( ~ r1_tarski(X13,X14)
        | ~ r2_hidden(X15,X13)
        | r2_hidden(X15,X14) )
      & ( r2_hidden(esk2_2(X16,X17),X16)
        | r1_tarski(X16,X17) )
      & ( ~ r2_hidden(esk2_2(X16,X17),X17)
        | r1_tarski(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_35,plain,(
    ! [X22,X23,X24,X25] :
      ( ( ~ v8_relat_2(X22)
        | ~ r2_hidden(k4_tarski(X23,X24),X22)
        | ~ r2_hidden(k4_tarski(X24,X25),X22)
        | r2_hidden(k4_tarski(X23,X25),X22)
        | ~ v1_relat_1(X22) )
      & ( r2_hidden(k4_tarski(esk3_1(X22),esk4_1(X22)),X22)
        | v8_relat_2(X22)
        | ~ v1_relat_1(X22) )
      & ( r2_hidden(k4_tarski(esk4_1(X22),esk5_1(X22)),X22)
        | v8_relat_2(X22)
        | ~ v1_relat_1(X22) )
      & ( ~ r2_hidden(k4_tarski(esk3_1(X22),esk5_1(X22)),X22)
        | v8_relat_2(X22)
        | ~ v1_relat_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l2_wellord1])])])])])).

cnf(c_0_36,plain,
    ( v8_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_37,negated_conjecture,
    ( X1 = esk11_0
    | r2_hidden(k4_tarski(esk11_0,X1),esk12_0)
    | r2_hidden(k4_tarski(X1,esk11_0),esk12_0)
    | ~ r2_hidden(X1,k3_relat_1(esk12_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk10_0,k3_relat_1(esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_32])])).

fof(c_0_39,plain,(
    ! [X39] : r3_xboole_0(X39,X39) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_xboole_0])])).

cnf(c_0_40,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( r2_hidden(k4_tarski(X2,X4),X1)
    | ~ v8_relat_2(X1)
    | ~ r2_hidden(k4_tarski(X2,X3),X1)
    | ~ r2_hidden(k4_tarski(X3,X4),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( v8_relat_2(esk12_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_19]),c_0_20])])).

cnf(c_0_44,negated_conjecture,
    ( esk11_0 = esk10_0
    | r2_hidden(k4_tarski(esk10_0,esk11_0),esk12_0)
    | r2_hidden(k4_tarski(esk11_0,esk10_0),esk12_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,plain,
    ( r3_xboole_0(X1,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,k1_wellord1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( r3_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X2,X1),X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_41])).

cnf(c_0_48,plain,
    ( X1 = X2
    | r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),esk12_0)
    | ~ r2_hidden(k4_tarski(X3,X2),esk12_0)
    | ~ r2_hidden(k4_tarski(X1,X3),esk12_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_19]),c_0_43])])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(k4_tarski(esk11_0,esk10_0),esk12_0)
    | r2_hidden(k4_tarski(esk10_0,esk11_0),esk12_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_44]),c_0_45])])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),esk12_0)
    | ~ r2_hidden(X1,k1_wellord1(esk12_0,X2)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_19])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk2_2(k1_wellord1(esk12_0,esk11_0),k1_wellord1(esk12_0,esk10_0)),k1_wellord1(esk12_0,esk11_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_47])).

cnf(c_0_53,plain,
    ( X1 = X2
    | r2_hidden(X1,k1_wellord1(X3,X2))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(k4_tarski(esk10_0,esk11_0),esk12_0)
    | r2_hidden(k4_tarski(X1,esk10_0),esk12_0)
    | ~ r2_hidden(k4_tarski(X1,esk11_0),esk12_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_2(k1_wellord1(esk12_0,esk11_0),k1_wellord1(esk12_0,esk10_0)),esk11_0),esk12_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( X1 = X2
    | r2_hidden(X1,k1_wellord1(esk12_0,X2))
    | ~ r2_hidden(k4_tarski(X1,X2),esk12_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_19])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_2(k1_wellord1(esk12_0,esk11_0),k1_wellord1(esk12_0,esk10_0)),esk10_0),esk12_0)
    | r2_hidden(k4_tarski(esk10_0,esk11_0),esk12_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( esk2_2(k1_wellord1(esk12_0,esk11_0),k1_wellord1(esk12_0,esk10_0)) = esk10_0
    | r2_hidden(esk2_2(k1_wellord1(esk12_0,esk11_0),k1_wellord1(esk12_0,esk10_0)),k1_wellord1(esk12_0,esk10_0))
    | r2_hidden(k4_tarski(esk10_0,esk11_0),esk12_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk2_2(k1_wellord1(esk12_0,esk11_0),k1_wellord1(esk12_0,esk10_0)),k1_wellord1(esk12_0,esk10_0))
    | r2_hidden(k4_tarski(esk10_0,esk11_0),esk12_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(k1_wellord1(esk12_0,esk11_0),k1_wellord1(esk12_0,esk10_0))
    | r2_hidden(k4_tarski(esk10_0,esk11_0),esk12_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_62,plain,
    ( r3_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_41])).

fof(c_0_63,plain,(
    ! [X29,X30,X31] :
      ( ( ~ v4_relat_2(X29)
        | ~ r2_hidden(k4_tarski(X30,X31),X29)
        | ~ r2_hidden(k4_tarski(X31,X30),X29)
        | X30 = X31
        | ~ v1_relat_1(X29) )
      & ( r2_hidden(k4_tarski(esk6_1(X29),esk7_1(X29)),X29)
        | v4_relat_2(X29)
        | ~ v1_relat_1(X29) )
      & ( r2_hidden(k4_tarski(esk7_1(X29),esk6_1(X29)),X29)
        | v4_relat_2(X29)
        | ~ v1_relat_1(X29) )
      & ( esk6_1(X29) != esk7_1(X29)
        | v4_relat_2(X29)
        | ~ v1_relat_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_wellord1])])])])])).

cnf(c_0_64,plain,
    ( v4_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(k4_tarski(esk10_0,esk11_0),esk12_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_61]),c_0_26])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk2_2(k1_wellord1(esk12_0,esk10_0),k1_wellord1(esk12_0,esk11_0)),k1_wellord1(esk12_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_62])).

cnf(c_0_67,plain,
    ( X2 = X3
    | ~ v4_relat_2(X1)
    | ~ r2_hidden(k4_tarski(X2,X3),X1)
    | ~ r2_hidden(k4_tarski(X3,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( v4_relat_2(esk12_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_19]),c_0_20])])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk11_0),esk12_0)
    | ~ r2_hidden(k4_tarski(X1,esk10_0),esk12_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_65])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_2(k1_wellord1(esk12_0,esk10_0),k1_wellord1(esk12_0,esk11_0)),esk10_0),esk12_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X2,X1),esk12_0)
    | ~ r2_hidden(k4_tarski(X1,X2),esk12_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_19]),c_0_68])])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_2(k1_wellord1(esk12_0,esk10_0),k1_wellord1(esk12_0,esk11_0)),esk11_0),esk12_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_73,negated_conjecture,
    ( esk2_2(k1_wellord1(esk12_0,esk10_0),k1_wellord1(esk12_0,esk11_0)) = esk10_0
    | ~ r2_hidden(k4_tarski(esk10_0,esk2_2(k1_wellord1(esk12_0,esk10_0),k1_wellord1(esk12_0,esk11_0))),esk12_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( esk2_2(k1_wellord1(esk12_0,esk10_0),k1_wellord1(esk12_0,esk11_0)) = esk11_0
    | r2_hidden(esk2_2(k1_wellord1(esk12_0,esk10_0),k1_wellord1(esk12_0,esk11_0)),k1_wellord1(esk12_0,esk11_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_72])).

cnf(c_0_75,negated_conjecture,
    ( esk11_0 = esk10_0
    | r2_hidden(esk2_2(k1_wellord1(esk12_0,esk10_0),k1_wellord1(esk12_0,esk11_0)),k1_wellord1(esk12_0,esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_65])])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk2_2(k1_wellord1(esk12_0,esk10_0),k1_wellord1(esk12_0,esk11_0)),k1_wellord1(esk12_0,esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_75]),c_0_45])])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(k1_wellord1(esk12_0,esk10_0),k1_wellord1(esk12_0,esk11_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_76])).

cnf(c_0_78,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_77]),c_0_26]),
    [proof]).

%------------------------------------------------------------------------------
