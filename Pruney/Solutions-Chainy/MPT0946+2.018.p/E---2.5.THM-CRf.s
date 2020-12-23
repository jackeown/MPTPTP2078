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
% DateTime   : Thu Dec  3 11:00:44 EST 2020

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   68 (1395 expanded)
%              Number of clauses        :   41 ( 567 expanded)
%              Number of leaves         :   13 ( 355 expanded)
%              Depth                    :   15
%              Number of atoms          :  258 (5203 expanded)
%              Number of equality atoms :   52 (1265 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   33 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t11_wellord2,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord2)).

fof(t50_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ~ ( ~ r2_xboole_0(X1,X2)
              & X1 != X2
              & ~ r2_xboole_0(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_ordinal1)).

fof(d1_wellord2,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( X2 = k1_wellord2(X1)
      <=> ( k3_relat_1(X2) = X1
          & ! [X3,X4] :
              ( ( r2_hidden(X3,X1)
                & r2_hidden(X4,X1) )
             => ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> r1_tarski(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

fof(dt_k1_wellord2,axiom,(
    ! [X1] : v1_relat_1(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(t57_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => ! [X2] :
            ~ ( r2_hidden(X2,k3_relat_1(X1))
              & r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_wellord1)).

fof(t10_wellord2,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,X2)
           => X1 = k1_wellord1(k1_wellord2(X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord2)).

fof(t7_wellord2,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v2_wellord1(k1_wellord2(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_wellord2)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(t8_wellord2,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_wellord1(k1_wellord2(X2),X1) = k1_wellord2(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).

fof(t50_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r4_wellord1(X1,X2)
           => r4_wellord1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).

fof(t24_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ~ ( ~ r2_hidden(X1,X2)
              & X1 != X2
              & ~ r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(t19_wellord1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k3_relat_1(k2_wellord1(X3,X2)))
       => ( r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_wellord1)).

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

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ( r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))
             => X1 = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t11_wellord2])).

fof(c_0_14,plain,(
    ! [X9,X10] :
      ( ~ v3_ordinal1(X9)
      | ~ v3_ordinal1(X10)
      | r2_xboole_0(X9,X10)
      | X9 = X10
      | r2_xboole_0(X10,X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t50_ordinal1])])])])).

fof(c_0_15,negated_conjecture,
    ( v3_ordinal1(esk4_0)
    & v3_ordinal1(esk5_0)
    & r4_wellord1(k1_wellord2(esk4_0),k1_wellord2(esk5_0))
    & esk4_0 != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_16,plain,(
    ! [X26,X27,X28,X29] :
      ( ( k3_relat_1(X27) = X26
        | X27 != k1_wellord2(X26)
        | ~ v1_relat_1(X27) )
      & ( ~ r2_hidden(k4_tarski(X28,X29),X27)
        | r1_tarski(X28,X29)
        | ~ r2_hidden(X28,X26)
        | ~ r2_hidden(X29,X26)
        | X27 != k1_wellord2(X26)
        | ~ v1_relat_1(X27) )
      & ( ~ r1_tarski(X28,X29)
        | r2_hidden(k4_tarski(X28,X29),X27)
        | ~ r2_hidden(X28,X26)
        | ~ r2_hidden(X29,X26)
        | X27 != k1_wellord2(X26)
        | ~ v1_relat_1(X27) )
      & ( r2_hidden(esk2_2(X26,X27),X26)
        | k3_relat_1(X27) != X26
        | X27 = k1_wellord2(X26)
        | ~ v1_relat_1(X27) )
      & ( r2_hidden(esk3_2(X26,X27),X26)
        | k3_relat_1(X27) != X26
        | X27 = k1_wellord2(X26)
        | ~ v1_relat_1(X27) )
      & ( ~ r2_hidden(k4_tarski(esk2_2(X26,X27),esk3_2(X26,X27)),X27)
        | ~ r1_tarski(esk2_2(X26,X27),esk3_2(X26,X27))
        | k3_relat_1(X27) != X26
        | X27 = k1_wellord2(X26)
        | ~ v1_relat_1(X27) )
      & ( r2_hidden(k4_tarski(esk2_2(X26,X27),esk3_2(X26,X27)),X27)
        | r1_tarski(esk2_2(X26,X27),esk3_2(X26,X27))
        | k3_relat_1(X27) != X26
        | X27 = k1_wellord2(X26)
        | ~ v1_relat_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).

fof(c_0_17,plain,(
    ! [X32] : v1_relat_1(k1_wellord2(X32)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

cnf(c_0_18,plain,
    ( r2_xboole_0(X1,X2)
    | X1 = X2
    | r2_xboole_0(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( v3_ordinal1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X24)
      | ~ v2_wellord1(X24)
      | ~ r2_hidden(X25,k3_relat_1(X24))
      | ~ r4_wellord1(X24,k2_wellord1(X24,k1_wellord1(X24,X25))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t57_wellord1])])])).

fof(c_0_21,plain,(
    ! [X33,X34] :
      ( ~ v3_ordinal1(X33)
      | ~ v3_ordinal1(X34)
      | ~ r2_hidden(X33,X34)
      | X33 = k1_wellord1(k1_wellord2(X34),X33) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_wellord2])])])).

cnf(c_0_22,plain,
    ( k3_relat_1(X1) = X2
    | X1 != k1_wellord2(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X35] :
      ( ~ v3_ordinal1(X35)
      | v2_wellord1(k1_wellord2(X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_wellord2])])).

fof(c_0_25,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | ~ r2_xboole_0(X5,X6) )
      & ( X5 != X6
        | ~ r2_xboole_0(X5,X6) )
      & ( ~ r1_tarski(X5,X6)
        | X5 = X6
        | r2_xboole_0(X5,X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_26,negated_conjecture,
    ( X1 = esk5_0
    | r2_xboole_0(esk5_0,X1)
    | r2_xboole_0(X1,esk5_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( v3_ordinal1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( esk4_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,plain,
    ( ~ v1_relat_1(X1)
    | ~ v2_wellord1(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( X1 = k1_wellord1(k1_wellord2(X2),X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k3_relat_1(k1_wellord2(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_22]),c_0_23])])).

cnf(c_0_32,plain,
    ( v2_wellord1(k1_wellord2(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_33,plain,(
    ! [X36,X37] :
      ( ~ r1_tarski(X36,X37)
      | k2_wellord1(k1_wellord2(X37),X36) = k1_wellord2(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_wellord2])])).

fof(c_0_34,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X22)
      | ~ v1_relat_1(X23)
      | ~ r4_wellord1(X22,X23)
      | r4_wellord1(X23,X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_wellord1])])])).

fof(c_0_35,plain,(
    ! [X7,X8] :
      ( ~ v3_ordinal1(X7)
      | ~ v3_ordinal1(X8)
      | r2_hidden(X7,X8)
      | X7 = X8
      | r2_hidden(X8,X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).

fof(c_0_36,plain,(
    ! [X19,X20,X21] :
      ( ( r2_hidden(X19,k3_relat_1(X21))
        | ~ r2_hidden(X19,k3_relat_1(k2_wellord1(X21,X20)))
        | ~ v1_relat_1(X21) )
      & ( r2_hidden(X19,X20)
        | ~ r2_hidden(X19,k3_relat_1(k2_wellord1(X21,X20)))
        | ~ v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_wellord1])])])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,negated_conjecture,
    ( r2_xboole_0(esk4_0,esk5_0)
    | r2_xboole_0(esk5_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_39,plain,
    ( ~ r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),X2))
    | ~ r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_23])]),c_0_31])]),c_0_32])).

cnf(c_0_40,plain,
    ( k2_wellord1(k1_wellord2(X2),X1) = k1_wellord2(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( r4_wellord1(X2,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r4_wellord1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk4_0),k1_wellord2(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_44,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17] :
      ( ( X14 != X12
        | ~ r2_hidden(X14,X13)
        | X13 != k1_wellord1(X11,X12)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(k4_tarski(X14,X12),X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k1_wellord1(X11,X12)
        | ~ v1_relat_1(X11) )
      & ( X15 = X12
        | ~ r2_hidden(k4_tarski(X15,X12),X11)
        | r2_hidden(X15,X13)
        | X13 != k1_wellord1(X11,X12)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(esk1_3(X11,X16,X17),X17)
        | esk1_3(X11,X16,X17) = X16
        | ~ r2_hidden(k4_tarski(esk1_3(X11,X16,X17),X16),X11)
        | X17 = k1_wellord1(X11,X16)
        | ~ v1_relat_1(X11) )
      & ( esk1_3(X11,X16,X17) != X16
        | r2_hidden(esk1_3(X11,X16,X17),X17)
        | X17 = k1_wellord1(X11,X16)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(k4_tarski(esk1_3(X11,X16,X17),X16),X11)
        | r2_hidden(esk1_3(X11,X16,X17),X17)
        | X17 = k1_wellord1(X11,X16)
        | ~ v1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(X1,k3_relat_1(k2_wellord1(X2,X3)))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0)
    | r2_xboole_0(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_47,plain,
    ( ~ r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))
    | ~ r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk5_0),k1_wellord2(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_23]),c_0_23])])).

cnf(c_0_49,negated_conjecture,
    ( X1 = esk5_0
    | r2_hidden(esk5_0,X1)
    | r2_hidden(X1,esk5_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_19])).

cnf(c_0_50,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,X3)
    | X3 != k1_wellord1(X4,X2)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_40]),c_0_23])]),c_0_31]),c_0_31])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0)
    | r1_tarski(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( ~ r2_hidden(esk4_0,esk5_0)
    | ~ r1_tarski(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_19]),c_0_27])])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0)
    | r2_hidden(esk5_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_27]),c_0_28])).

cnf(c_0_55,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_wellord1(X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_50])])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | r1_tarski(esk5_0,esk4_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0)
    | ~ r1_tarski(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_58,plain,
    ( ~ r2_hidden(X1,X1)
    | ~ r2_hidden(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_30]),c_0_23])])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk5_0,esk5_0)
    | r1_tarski(esk5_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0)
    | ~ r2_hidden(esk5_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_19])])).

cnf(c_0_61,negated_conjecture,
    ( ~ r2_hidden(esk5_0,esk4_0)
    | ~ r1_tarski(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_42]),c_0_27]),c_0_19])])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_59]),c_0_19])])).

cnf(c_0_63,negated_conjecture,
    ( ~ r2_hidden(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62])])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[c_0_54,c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( ~ r2_hidden(esk4_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_64]),c_0_27]),c_0_65])])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_64]),c_0_27]),c_0_65])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.33  % Computer   : n003.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 14:01:57 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 0.11/0.37  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.11/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.11/0.37  #
% 0.11/0.37  # Preprocessing time       : 0.028 s
% 0.11/0.37  
% 0.11/0.37  # Proof found!
% 0.11/0.37  # SZS status Theorem
% 0.11/0.37  # SZS output start CNFRefutation
% 0.11/0.37  fof(t11_wellord2, conjecture, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))=>X1=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_wellord2)).
% 0.11/0.37  fof(t50_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>~(((~(r2_xboole_0(X1,X2))&X1!=X2)&~(r2_xboole_0(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_ordinal1)).
% 0.11/0.37  fof(d1_wellord2, axiom, ![X1, X2]:(v1_relat_1(X2)=>(X2=k1_wellord2(X1)<=>(k3_relat_1(X2)=X1&![X3, X4]:((r2_hidden(X3,X1)&r2_hidden(X4,X1))=>(r2_hidden(k4_tarski(X3,X4),X2)<=>r1_tarski(X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord2)).
% 0.11/0.37  fof(dt_k1_wellord2, axiom, ![X1]:v1_relat_1(k1_wellord2(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 0.11/0.37  fof(t57_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v2_wellord1(X1)=>![X2]:~((r2_hidden(X2,k3_relat_1(X1))&r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_wellord1)).
% 0.11/0.37  fof(t10_wellord2, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)=>X1=k1_wellord1(k1_wellord2(X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_wellord2)).
% 0.11/0.37  fof(t7_wellord2, axiom, ![X1]:(v3_ordinal1(X1)=>v2_wellord1(k1_wellord2(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_wellord2)).
% 0.11/0.37  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.11/0.37  fof(t8_wellord2, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_wellord1(k1_wellord2(X2),X1)=k1_wellord2(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_wellord2)).
% 0.11/0.37  fof(t50_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r4_wellord1(X1,X2)=>r4_wellord1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_wellord1)).
% 0.11/0.37  fof(t24_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>~(((~(r2_hidden(X1,X2))&X1!=X2)&~(r2_hidden(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 0.11/0.37  fof(t19_wellord1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k3_relat_1(k2_wellord1(X3,X2)))=>(r2_hidden(X1,k3_relat_1(X3))&r2_hidden(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_wellord1)).
% 0.11/0.37  fof(d1_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k1_wellord1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4!=X2&r2_hidden(k4_tarski(X4,X2),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord1)).
% 0.11/0.37  fof(c_0_13, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))=>X1=X2)))), inference(assume_negation,[status(cth)],[t11_wellord2])).
% 0.11/0.37  fof(c_0_14, plain, ![X9, X10]:(~v3_ordinal1(X9)|(~v3_ordinal1(X10)|(r2_xboole_0(X9,X10)|X9=X10|r2_xboole_0(X10,X9)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t50_ordinal1])])])])).
% 0.11/0.37  fof(c_0_15, negated_conjecture, (v3_ordinal1(esk4_0)&(v3_ordinal1(esk5_0)&(r4_wellord1(k1_wellord2(esk4_0),k1_wellord2(esk5_0))&esk4_0!=esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.11/0.37  fof(c_0_16, plain, ![X26, X27, X28, X29]:(((k3_relat_1(X27)=X26|X27!=k1_wellord2(X26)|~v1_relat_1(X27))&((~r2_hidden(k4_tarski(X28,X29),X27)|r1_tarski(X28,X29)|(~r2_hidden(X28,X26)|~r2_hidden(X29,X26))|X27!=k1_wellord2(X26)|~v1_relat_1(X27))&(~r1_tarski(X28,X29)|r2_hidden(k4_tarski(X28,X29),X27)|(~r2_hidden(X28,X26)|~r2_hidden(X29,X26))|X27!=k1_wellord2(X26)|~v1_relat_1(X27))))&(((r2_hidden(esk2_2(X26,X27),X26)|k3_relat_1(X27)!=X26|X27=k1_wellord2(X26)|~v1_relat_1(X27))&(r2_hidden(esk3_2(X26,X27),X26)|k3_relat_1(X27)!=X26|X27=k1_wellord2(X26)|~v1_relat_1(X27)))&((~r2_hidden(k4_tarski(esk2_2(X26,X27),esk3_2(X26,X27)),X27)|~r1_tarski(esk2_2(X26,X27),esk3_2(X26,X27))|k3_relat_1(X27)!=X26|X27=k1_wellord2(X26)|~v1_relat_1(X27))&(r2_hidden(k4_tarski(esk2_2(X26,X27),esk3_2(X26,X27)),X27)|r1_tarski(esk2_2(X26,X27),esk3_2(X26,X27))|k3_relat_1(X27)!=X26|X27=k1_wellord2(X26)|~v1_relat_1(X27))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).
% 0.11/0.37  fof(c_0_17, plain, ![X32]:v1_relat_1(k1_wellord2(X32)), inference(variable_rename,[status(thm)],[dt_k1_wellord2])).
% 0.11/0.37  cnf(c_0_18, plain, (r2_xboole_0(X1,X2)|X1=X2|r2_xboole_0(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.11/0.37  cnf(c_0_19, negated_conjecture, (v3_ordinal1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.11/0.37  fof(c_0_20, plain, ![X24, X25]:(~v1_relat_1(X24)|(~v2_wellord1(X24)|(~r2_hidden(X25,k3_relat_1(X24))|~r4_wellord1(X24,k2_wellord1(X24,k1_wellord1(X24,X25)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t57_wellord1])])])).
% 0.11/0.37  fof(c_0_21, plain, ![X33, X34]:(~v3_ordinal1(X33)|(~v3_ordinal1(X34)|(~r2_hidden(X33,X34)|X33=k1_wellord1(k1_wellord2(X34),X33)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_wellord2])])])).
% 0.11/0.37  cnf(c_0_22, plain, (k3_relat_1(X1)=X2|X1!=k1_wellord2(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.11/0.37  cnf(c_0_23, plain, (v1_relat_1(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.11/0.37  fof(c_0_24, plain, ![X35]:(~v3_ordinal1(X35)|v2_wellord1(k1_wellord2(X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_wellord2])])).
% 0.11/0.37  fof(c_0_25, plain, ![X5, X6]:(((r1_tarski(X5,X6)|~r2_xboole_0(X5,X6))&(X5!=X6|~r2_xboole_0(X5,X6)))&(~r1_tarski(X5,X6)|X5=X6|r2_xboole_0(X5,X6))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.11/0.37  cnf(c_0_26, negated_conjecture, (X1=esk5_0|r2_xboole_0(esk5_0,X1)|r2_xboole_0(X1,esk5_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.11/0.37  cnf(c_0_27, negated_conjecture, (v3_ordinal1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.11/0.37  cnf(c_0_28, negated_conjecture, (esk4_0!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.11/0.37  cnf(c_0_29, plain, (~v1_relat_1(X1)|~v2_wellord1(X1)|~r2_hidden(X2,k3_relat_1(X1))|~r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.11/0.37  cnf(c_0_30, plain, (X1=k1_wellord1(k1_wellord2(X2),X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.11/0.37  cnf(c_0_31, plain, (k3_relat_1(k1_wellord2(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_22]), c_0_23])])).
% 0.11/0.37  cnf(c_0_32, plain, (v2_wellord1(k1_wellord2(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.11/0.37  fof(c_0_33, plain, ![X36, X37]:(~r1_tarski(X36,X37)|k2_wellord1(k1_wellord2(X37),X36)=k1_wellord2(X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_wellord2])])).
% 0.11/0.37  fof(c_0_34, plain, ![X22, X23]:(~v1_relat_1(X22)|(~v1_relat_1(X23)|(~r4_wellord1(X22,X23)|r4_wellord1(X23,X22)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_wellord1])])])).
% 0.11/0.37  fof(c_0_35, plain, ![X7, X8]:(~v3_ordinal1(X7)|(~v3_ordinal1(X8)|(r2_hidden(X7,X8)|X7=X8|r2_hidden(X8,X7)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).
% 0.11/0.37  fof(c_0_36, plain, ![X19, X20, X21]:((r2_hidden(X19,k3_relat_1(X21))|~r2_hidden(X19,k3_relat_1(k2_wellord1(X21,X20)))|~v1_relat_1(X21))&(r2_hidden(X19,X20)|~r2_hidden(X19,k3_relat_1(k2_wellord1(X21,X20)))|~v1_relat_1(X21))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_wellord1])])])).
% 0.11/0.37  cnf(c_0_37, plain, (r1_tarski(X1,X2)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.11/0.37  cnf(c_0_38, negated_conjecture, (r2_xboole_0(esk4_0,esk5_0)|r2_xboole_0(esk5_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 0.11/0.37  cnf(c_0_39, plain, (~r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),X2))|~r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_23])]), c_0_31])]), c_0_32])).
% 0.11/0.37  cnf(c_0_40, plain, (k2_wellord1(k1_wellord2(X2),X1)=k1_wellord2(X1)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.11/0.37  cnf(c_0_41, plain, (r4_wellord1(X2,X1)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r4_wellord1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.11/0.37  cnf(c_0_42, negated_conjecture, (r4_wellord1(k1_wellord2(esk4_0),k1_wellord2(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.11/0.37  cnf(c_0_43, plain, (r2_hidden(X1,X2)|X1=X2|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.11/0.37  fof(c_0_44, plain, ![X11, X12, X13, X14, X15, X16, X17]:((((X14!=X12|~r2_hidden(X14,X13)|X13!=k1_wellord1(X11,X12)|~v1_relat_1(X11))&(r2_hidden(k4_tarski(X14,X12),X11)|~r2_hidden(X14,X13)|X13!=k1_wellord1(X11,X12)|~v1_relat_1(X11)))&(X15=X12|~r2_hidden(k4_tarski(X15,X12),X11)|r2_hidden(X15,X13)|X13!=k1_wellord1(X11,X12)|~v1_relat_1(X11)))&((~r2_hidden(esk1_3(X11,X16,X17),X17)|(esk1_3(X11,X16,X17)=X16|~r2_hidden(k4_tarski(esk1_3(X11,X16,X17),X16),X11))|X17=k1_wellord1(X11,X16)|~v1_relat_1(X11))&((esk1_3(X11,X16,X17)!=X16|r2_hidden(esk1_3(X11,X16,X17),X17)|X17=k1_wellord1(X11,X16)|~v1_relat_1(X11))&(r2_hidden(k4_tarski(esk1_3(X11,X16,X17),X16),X11)|r2_hidden(esk1_3(X11,X16,X17),X17)|X17=k1_wellord1(X11,X16)|~v1_relat_1(X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).
% 0.11/0.37  cnf(c_0_45, plain, (r2_hidden(X1,k3_relat_1(X2))|~r2_hidden(X1,k3_relat_1(k2_wellord1(X2,X3)))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.11/0.37  cnf(c_0_46, negated_conjecture, (r1_tarski(esk4_0,esk5_0)|r2_xboole_0(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.11/0.37  cnf(c_0_47, plain, (~r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))|~r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.11/0.37  cnf(c_0_48, negated_conjecture, (r4_wellord1(k1_wellord2(esk5_0),k1_wellord2(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_23]), c_0_23])])).
% 0.11/0.37  cnf(c_0_49, negated_conjecture, (X1=esk5_0|r2_hidden(esk5_0,X1)|r2_hidden(X1,esk5_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_43, c_0_19])).
% 0.11/0.37  cnf(c_0_50, plain, (X1!=X2|~r2_hidden(X1,X3)|X3!=k1_wellord1(X4,X2)|~v1_relat_1(X4)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.11/0.37  cnf(c_0_51, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_tarski(X3,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_40]), c_0_23])]), c_0_31]), c_0_31])).
% 0.11/0.37  cnf(c_0_52, negated_conjecture, (r1_tarski(esk4_0,esk5_0)|r1_tarski(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_37, c_0_46])).
% 0.11/0.37  cnf(c_0_53, negated_conjecture, (~r2_hidden(esk4_0,esk5_0)|~r1_tarski(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_19]), c_0_27])])).
% 0.11/0.37  cnf(c_0_54, negated_conjecture, (r2_hidden(esk4_0,esk5_0)|r2_hidden(esk5_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_27]), c_0_28])).
% 0.11/0.37  cnf(c_0_55, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k1_wellord1(X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_50])])).
% 0.11/0.37  cnf(c_0_56, negated_conjecture, (r2_hidden(X1,esk5_0)|r1_tarski(esk5_0,esk4_0)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.11/0.37  cnf(c_0_57, negated_conjecture, (r2_hidden(esk5_0,esk4_0)|~r1_tarski(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.11/0.37  cnf(c_0_58, plain, (~r2_hidden(X1,X1)|~r2_hidden(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_30]), c_0_23])])).
% 0.11/0.37  cnf(c_0_59, negated_conjecture, (r2_hidden(esk5_0,esk5_0)|r1_tarski(esk5_0,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_52])).
% 0.11/0.37  cnf(c_0_60, negated_conjecture, (r1_tarski(esk5_0,esk4_0)|~r2_hidden(esk5_0,X1)|~v3_ordinal1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_19])])).
% 0.11/0.37  cnf(c_0_61, negated_conjecture, (~r2_hidden(esk5_0,esk4_0)|~r1_tarski(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_42]), c_0_27]), c_0_19])])).
% 0.11/0.37  cnf(c_0_62, negated_conjecture, (r1_tarski(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_59]), c_0_19])])).
% 0.11/0.37  cnf(c_0_63, negated_conjecture, (~r2_hidden(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62])])).
% 0.11/0.37  cnf(c_0_64, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_51, c_0_62])).
% 0.11/0.37  cnf(c_0_65, negated_conjecture, (r2_hidden(esk4_0,esk5_0)), inference(sr,[status(thm)],[c_0_54, c_0_63])).
% 0.11/0.37  cnf(c_0_66, negated_conjecture, (~r2_hidden(esk4_0,X1)|~v3_ordinal1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_64]), c_0_27]), c_0_65])])).
% 0.11/0.37  cnf(c_0_67, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_64]), c_0_27]), c_0_65])]), ['proof']).
% 0.11/0.37  # SZS output end CNFRefutation
% 0.11/0.37  # Proof object total steps             : 68
% 0.11/0.37  # Proof object clause steps            : 41
% 0.11/0.37  # Proof object formula steps           : 27
% 0.11/0.37  # Proof object conjectures             : 26
% 0.11/0.37  # Proof object clause conjectures      : 23
% 0.11/0.37  # Proof object formula conjectures     : 3
% 0.11/0.37  # Proof object initial clauses used    : 16
% 0.11/0.37  # Proof object initial formulas used   : 13
% 0.11/0.37  # Proof object generating inferences   : 21
% 0.11/0.37  # Proof object simplifying inferences  : 41
% 0.11/0.37  # Training examples: 0 positive, 0 negative
% 0.11/0.37  # Parsed axioms                        : 13
% 0.11/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.11/0.37  # Initial clauses                      : 30
% 0.11/0.37  # Removed in clause preprocessing      : 0
% 0.11/0.37  # Initial clauses in saturation        : 30
% 0.11/0.37  # Processed clauses                    : 76
% 0.11/0.37  # ...of these trivial                  : 1
% 0.11/0.37  # ...subsumed                          : 5
% 0.11/0.37  # ...remaining for further processing  : 70
% 0.11/0.37  # Other redundant clauses eliminated   : 12
% 0.11/0.37  # Clauses deleted for lack of memory   : 0
% 0.11/0.37  # Backward-subsumed                    : 0
% 0.11/0.37  # Backward-rewritten                   : 8
% 0.11/0.37  # Generated clauses                    : 74
% 0.11/0.37  # ...of the previous two non-trivial   : 69
% 0.11/0.37  # Contextual simplify-reflections      : 2
% 0.11/0.37  # Paramodulations                      : 61
% 0.11/0.37  # Factorizations                       : 0
% 0.11/0.37  # Equation resolutions                 : 12
% 0.11/0.37  # Propositional unsat checks           : 0
% 0.11/0.37  #    Propositional check models        : 0
% 0.11/0.37  #    Propositional check unsatisfiable : 0
% 0.11/0.37  #    Propositional clauses             : 0
% 0.11/0.37  #    Propositional clauses after purity: 0
% 0.11/0.37  #    Propositional unsat core size     : 0
% 0.11/0.37  #    Propositional preprocessing time  : 0.000
% 0.11/0.37  #    Propositional encoding time       : 0.000
% 0.11/0.37  #    Propositional solver time         : 0.000
% 0.11/0.37  #    Success case prop preproc time    : 0.000
% 0.11/0.37  #    Success case prop encoding time   : 0.000
% 0.11/0.37  #    Success case prop solver time     : 0.000
% 0.11/0.37  # Current number of processed clauses  : 49
% 0.11/0.37  #    Positive orientable unit clauses  : 9
% 0.11/0.37  #    Positive unorientable unit clauses: 0
% 0.11/0.37  #    Negative unit clauses             : 5
% 0.11/0.37  #    Non-unit-clauses                  : 35
% 0.11/0.37  # Current number of unprocessed clauses: 22
% 0.11/0.37  # ...number of literals in the above   : 98
% 0.11/0.37  # Current number of archived formulas  : 0
% 0.11/0.37  # Current number of archived clauses   : 10
% 0.11/0.37  # Clause-clause subsumption calls (NU) : 277
% 0.11/0.37  # Rec. Clause-clause subsumption calls : 103
% 0.11/0.37  # Non-unit clause-clause subsumptions  : 5
% 0.11/0.37  # Unit Clause-clause subsumption calls : 105
% 0.11/0.37  # Rewrite failures with RHS unbound    : 0
% 0.11/0.37  # BW rewrite match attempts            : 3
% 0.11/0.37  # BW rewrite match successes           : 3
% 0.11/0.37  # Condensation attempts                : 0
% 0.11/0.37  # Condensation successes               : 0
% 0.11/0.37  # Termbank termtop insertions          : 3463
% 0.11/0.37  
% 0.11/0.37  # -------------------------------------------------
% 0.11/0.37  # User time                : 0.032 s
% 0.11/0.37  # System time              : 0.003 s
% 0.11/0.37  # Total time               : 0.035 s
% 0.11/0.37  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
