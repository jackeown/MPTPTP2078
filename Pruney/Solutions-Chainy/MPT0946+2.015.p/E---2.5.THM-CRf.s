%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:44 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 659 expanded)
%              Number of clauses        :   55 ( 278 expanded)
%              Number of leaves         :   14 ( 165 expanded)
%              Depth                    :   15
%              Number of atoms          :  268 (2404 expanded)
%              Number of equality atoms :   63 ( 614 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   33 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t29_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v3_ordinal1(k1_ordinal1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(t11_wellord2,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord2)).

fof(t13_ordinal1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,k1_ordinal1(X2))
    <=> ( r2_hidden(X1,X2)
        | X1 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

fof(t10_wellord2,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,X2)
           => X1 = k1_wellord1(k1_wellord2(X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord2)).

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

fof(t24_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ~ ( ~ r2_hidden(X1,X2)
              & X1 != X2
              & ~ r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(t30_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X2,k3_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

fof(t7_wellord2,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v2_wellord1(k1_wellord2(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_wellord2)).

fof(t57_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => ! [X2] :
            ~ ( r2_hidden(X2,k3_relat_1(X1))
              & r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_wellord1)).

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

fof(c_0_14,plain,(
    ! [X13] :
      ( ~ v3_ordinal1(X13)
      | v3_ordinal1(k1_ordinal1(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).

fof(c_0_15,plain,(
    ! [X8] : k1_ordinal1(X8) = k2_xboole_0(X8,k1_tarski(X8)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ( r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))
             => X1 = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t11_wellord2])).

cnf(c_0_17,plain,
    ( v3_ordinal1(k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,negated_conjecture,
    ( v3_ordinal1(esk4_0)
    & v3_ordinal1(esk5_0)
    & r4_wellord1(k1_wellord2(esk4_0),k1_wellord2(esk5_0))
    & esk4_0 != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_20,plain,(
    ! [X9,X10] :
      ( ( ~ r2_hidden(X9,k1_ordinal1(X10))
        | r2_hidden(X9,X10)
        | X9 = X10 )
      & ( ~ r2_hidden(X9,X10)
        | r2_hidden(X9,k1_ordinal1(X10)) )
      & ( X9 != X10
        | r2_hidden(X9,k1_ordinal1(X10)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).

fof(c_0_21,plain,(
    ! [X33,X34] :
      ( ~ v3_ordinal1(X33)
      | ~ v3_ordinal1(X34)
      | ~ r2_hidden(X33,X34)
      | X33 = k1_wellord1(k1_wellord2(X34),X33) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_wellord2])])])).

cnf(c_0_22,plain,
    ( v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X1) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( v3_ordinal1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,k1_ordinal1(X2))
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_25,plain,(
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

fof(c_0_26,plain,(
    ! [X32] : v1_relat_1(k1_wellord2(X32)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_27,plain,(
    ! [X14,X15,X16,X17,X18,X19,X20] :
      ( ( X17 != X15
        | ~ r2_hidden(X17,X16)
        | X16 != k1_wellord1(X14,X15)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(k4_tarski(X17,X15),X14)
        | ~ r2_hidden(X17,X16)
        | X16 != k1_wellord1(X14,X15)
        | ~ v1_relat_1(X14) )
      & ( X18 = X15
        | ~ r2_hidden(k4_tarski(X18,X15),X14)
        | r2_hidden(X18,X16)
        | X16 != k1_wellord1(X14,X15)
        | ~ v1_relat_1(X14) )
      & ( ~ r2_hidden(esk1_3(X14,X19,X20),X20)
        | esk1_3(X14,X19,X20) = X19
        | ~ r2_hidden(k4_tarski(esk1_3(X14,X19,X20),X19),X14)
        | X20 = k1_wellord1(X14,X19)
        | ~ v1_relat_1(X14) )
      & ( esk1_3(X14,X19,X20) != X19
        | r2_hidden(esk1_3(X14,X19,X20),X20)
        | X20 = k1_wellord1(X14,X19)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(k4_tarski(esk1_3(X14,X19,X20),X19),X14)
        | r2_hidden(esk1_3(X14,X19,X20),X20)
        | X20 = k1_wellord1(X14,X19)
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).

cnf(c_0_28,plain,
    ( X1 = k1_wellord1(k1_wellord2(X2),X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( v3_ordinal1(k2_xboole_0(esk5_0,k1_tarski(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))
    | X1 != X2 ),
    inference(rw,[status(thm)],[c_0_24,c_0_18])).

fof(c_0_31,plain,(
    ! [X11,X12] :
      ( ~ v3_ordinal1(X11)
      | ~ v3_ordinal1(X12)
      | r2_hidden(X11,X12)
      | X11 = X12
      | r2_hidden(X12,X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).

fof(c_0_32,plain,(
    ! [X5,X6,X7] :
      ( ( r2_hidden(X5,k3_relat_1(X7))
        | ~ r2_hidden(k4_tarski(X5,X6),X7)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(X6,k3_relat_1(X7))
        | ~ r2_hidden(k4_tarski(X5,X6),X7)
        | ~ v1_relat_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_relat_1])])])).

cnf(c_0_33,plain,
    ( k3_relat_1(X1) = X2
    | X1 != k1_wellord2(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( k1_wellord1(k1_wellord2(k2_xboole_0(esk5_0,k1_tarski(esk5_0))),X1) = X1
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,k2_xboole_0(esk5_0,k1_tarski(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | ~ r2_hidden(X2,X4)
    | X3 != k1_wellord2(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( k3_relat_1(k1_wellord2(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_33]),c_0_34])])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,k1_wellord1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( k1_wellord1(k1_wellord2(k2_xboole_0(esk5_0,k1_tarski(esk5_0))),esk5_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_23])])).

cnf(c_0_45,negated_conjecture,
    ( X1 = esk5_0
    | r2_hidden(X1,esk5_0)
    | r2_hidden(esk5_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_23])).

cnf(c_0_46,negated_conjecture,
    ( v3_ordinal1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_47,negated_conjecture,
    ( esk4_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_48,plain,(
    ! [X35] :
      ( ~ v3_ordinal1(X35)
      | v2_wellord1(k1_wellord2(X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_wellord2])])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),k1_wellord2(X3))
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_39]),c_0_34])])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k1_wellord2(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_34])])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k1_wellord2(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_41]),c_0_34])])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk5_0),k1_wellord2(k2_xboole_0(esk5_0,k1_tarski(esk5_0))))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_34])])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0)
    | r2_hidden(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( v3_ordinal1(k2_xboole_0(esk4_0,k1_tarski(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_46])).

fof(c_0_55,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X24)
      | ~ v2_wellord1(X24)
      | ~ r2_hidden(X25,k3_relat_1(X24))
      | ~ r4_wellord1(X24,k2_wellord1(X24,k1_wellord1(X24,X25))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t57_wellord1])])])).

cnf(c_0_56,negated_conjecture,
    ( k1_wellord1(k1_wellord2(esk5_0),X1) = X1
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_23])).

cnf(c_0_57,plain,
    ( v2_wellord1(k1_wellord2(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_58,plain,(
    ! [X36,X37] :
      ( ~ r1_tarski(X36,X37)
      | k2_wellord1(k1_wellord2(X37),X36) = k1_wellord2(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_wellord2])])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),k1_wellord2(X3)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_0,esk5_0),k1_wellord2(k2_xboole_0(esk5_0,k1_tarski(esk5_0))))
    | r2_hidden(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

fof(c_0_61,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X22)
      | ~ v1_relat_1(X23)
      | ~ r4_wellord1(X22,X23)
      | r4_wellord1(X23,X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_wellord1])])])).

cnf(c_0_62,negated_conjecture,
    ( k1_wellord1(k1_wellord2(k2_xboole_0(esk4_0,k1_tarski(esk4_0))),X1) = X1
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,k2_xboole_0(esk4_0,k1_tarski(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_54])).

cnf(c_0_63,plain,
    ( ~ v1_relat_1(X1)
    | ~ v2_wellord1(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_64,negated_conjecture,
    ( k1_wellord1(k1_wellord2(esk5_0),esk4_0) = esk4_0
    | r2_hidden(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_53]),c_0_46])])).

cnf(c_0_65,negated_conjecture,
    ( v2_wellord1(k1_wellord2(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_23])).

cnf(c_0_66,plain,
    ( k2_wellord1(k1_wellord2(X2),X1) = k1_wellord2(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0)
    | r2_hidden(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_68,plain,
    ( r4_wellord1(X2,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r4_wellord1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk4_0),k1_wellord2(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_70,negated_conjecture,
    ( k1_wellord1(k1_wellord2(k2_xboole_0(esk4_0,k1_tarski(esk4_0))),esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_37]),c_0_46])])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0)
    | ~ r4_wellord1(k1_wellord2(esk5_0),k2_wellord1(k1_wellord2(esk5_0),esk4_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65]),c_0_41]),c_0_34])]),c_0_53])).

cnf(c_0_72,negated_conjecture,
    ( k2_wellord1(k1_wellord2(esk5_0),esk4_0) = k1_wellord2(esk4_0)
    | r2_hidden(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_73,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk5_0),k1_wellord2(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_34]),c_0_34])])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk4_0),k1_wellord2(k2_xboole_0(esk4_0,k1_tarski(esk4_0))))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_70]),c_0_34])])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73])])).

cnf(c_0_76,negated_conjecture,
    ( k1_wellord1(k1_wellord2(esk4_0),X1) = X1
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_46])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_0,esk4_0),k1_wellord2(k2_xboole_0(esk4_0,k1_tarski(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_78,negated_conjecture,
    ( k1_wellord1(k1_wellord2(esk4_0),esk5_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_75]),c_0_23])])).

cnf(c_0_79,negated_conjecture,
    ( v2_wellord1(k1_wellord2(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_46])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_77])).

cnf(c_0_81,negated_conjecture,
    ( ~ r4_wellord1(k1_wellord2(esk4_0),k2_wellord1(k1_wellord2(esk4_0),esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_78]),c_0_79]),c_0_41]),c_0_75]),c_0_34])])).

cnf(c_0_82,negated_conjecture,
    ( k2_wellord1(k1_wellord2(esk4_0),esk5_0) = k1_wellord2(esk5_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_80])).

cnf(c_0_83,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_82]),c_0_69])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:23:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S049N
% 0.20/0.38  # and selection function PSelectComplexPreferEQ.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.029 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t29_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k1_ordinal1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 0.20/0.38  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 0.20/0.38  fof(t11_wellord2, conjecture, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))=>X1=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_wellord2)).
% 0.20/0.38  fof(t13_ordinal1, axiom, ![X1, X2]:(r2_hidden(X1,k1_ordinal1(X2))<=>(r2_hidden(X1,X2)|X1=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 0.20/0.38  fof(t10_wellord2, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)=>X1=k1_wellord1(k1_wellord2(X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_wellord2)).
% 0.20/0.38  fof(d1_wellord2, axiom, ![X1, X2]:(v1_relat_1(X2)=>(X2=k1_wellord2(X1)<=>(k3_relat_1(X2)=X1&![X3, X4]:((r2_hidden(X3,X1)&r2_hidden(X4,X1))=>(r2_hidden(k4_tarski(X3,X4),X2)<=>r1_tarski(X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord2)).
% 0.20/0.38  fof(dt_k1_wellord2, axiom, ![X1]:v1_relat_1(k1_wellord2(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 0.20/0.38  fof(d1_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k1_wellord1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4!=X2&r2_hidden(k4_tarski(X4,X2),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord1)).
% 0.20/0.38  fof(t24_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>~(((~(r2_hidden(X1,X2))&X1!=X2)&~(r2_hidden(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 0.20/0.38  fof(t30_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k3_relat_1(X3))&r2_hidden(X2,k3_relat_1(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relat_1)).
% 0.20/0.38  fof(t7_wellord2, axiom, ![X1]:(v3_ordinal1(X1)=>v2_wellord1(k1_wellord2(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_wellord2)).
% 0.20/0.38  fof(t57_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v2_wellord1(X1)=>![X2]:~((r2_hidden(X2,k3_relat_1(X1))&r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_wellord1)).
% 0.20/0.38  fof(t8_wellord2, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_wellord1(k1_wellord2(X2),X1)=k1_wellord2(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_wellord2)).
% 0.20/0.38  fof(t50_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r4_wellord1(X1,X2)=>r4_wellord1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_wellord1)).
% 0.20/0.38  fof(c_0_14, plain, ![X13]:(~v3_ordinal1(X13)|v3_ordinal1(k1_ordinal1(X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).
% 0.20/0.38  fof(c_0_15, plain, ![X8]:k1_ordinal1(X8)=k2_xboole_0(X8,k1_tarski(X8)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 0.20/0.38  fof(c_0_16, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))=>X1=X2)))), inference(assume_negation,[status(cth)],[t11_wellord2])).
% 0.20/0.38  cnf(c_0_17, plain, (v3_ordinal1(k1_ordinal1(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  cnf(c_0_18, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  fof(c_0_19, negated_conjecture, (v3_ordinal1(esk4_0)&(v3_ordinal1(esk5_0)&(r4_wellord1(k1_wellord2(esk4_0),k1_wellord2(esk5_0))&esk4_0!=esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.20/0.38  fof(c_0_20, plain, ![X9, X10]:((~r2_hidden(X9,k1_ordinal1(X10))|(r2_hidden(X9,X10)|X9=X10))&((~r2_hidden(X9,X10)|r2_hidden(X9,k1_ordinal1(X10)))&(X9!=X10|r2_hidden(X9,k1_ordinal1(X10))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).
% 0.20/0.38  fof(c_0_21, plain, ![X33, X34]:(~v3_ordinal1(X33)|(~v3_ordinal1(X34)|(~r2_hidden(X33,X34)|X33=k1_wellord1(k1_wellord2(X34),X33)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_wellord2])])])).
% 0.20/0.38  cnf(c_0_22, plain, (v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))|~v3_ordinal1(X1)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.38  cnf(c_0_23, negated_conjecture, (v3_ordinal1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  cnf(c_0_24, plain, (r2_hidden(X1,k1_ordinal1(X2))|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.38  fof(c_0_25, plain, ![X26, X27, X28, X29]:(((k3_relat_1(X27)=X26|X27!=k1_wellord2(X26)|~v1_relat_1(X27))&((~r2_hidden(k4_tarski(X28,X29),X27)|r1_tarski(X28,X29)|(~r2_hidden(X28,X26)|~r2_hidden(X29,X26))|X27!=k1_wellord2(X26)|~v1_relat_1(X27))&(~r1_tarski(X28,X29)|r2_hidden(k4_tarski(X28,X29),X27)|(~r2_hidden(X28,X26)|~r2_hidden(X29,X26))|X27!=k1_wellord2(X26)|~v1_relat_1(X27))))&(((r2_hidden(esk2_2(X26,X27),X26)|k3_relat_1(X27)!=X26|X27=k1_wellord2(X26)|~v1_relat_1(X27))&(r2_hidden(esk3_2(X26,X27),X26)|k3_relat_1(X27)!=X26|X27=k1_wellord2(X26)|~v1_relat_1(X27)))&((~r2_hidden(k4_tarski(esk2_2(X26,X27),esk3_2(X26,X27)),X27)|~r1_tarski(esk2_2(X26,X27),esk3_2(X26,X27))|k3_relat_1(X27)!=X26|X27=k1_wellord2(X26)|~v1_relat_1(X27))&(r2_hidden(k4_tarski(esk2_2(X26,X27),esk3_2(X26,X27)),X27)|r1_tarski(esk2_2(X26,X27),esk3_2(X26,X27))|k3_relat_1(X27)!=X26|X27=k1_wellord2(X26)|~v1_relat_1(X27))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).
% 0.20/0.38  fof(c_0_26, plain, ![X32]:v1_relat_1(k1_wellord2(X32)), inference(variable_rename,[status(thm)],[dt_k1_wellord2])).
% 0.20/0.38  fof(c_0_27, plain, ![X14, X15, X16, X17, X18, X19, X20]:((((X17!=X15|~r2_hidden(X17,X16)|X16!=k1_wellord1(X14,X15)|~v1_relat_1(X14))&(r2_hidden(k4_tarski(X17,X15),X14)|~r2_hidden(X17,X16)|X16!=k1_wellord1(X14,X15)|~v1_relat_1(X14)))&(X18=X15|~r2_hidden(k4_tarski(X18,X15),X14)|r2_hidden(X18,X16)|X16!=k1_wellord1(X14,X15)|~v1_relat_1(X14)))&((~r2_hidden(esk1_3(X14,X19,X20),X20)|(esk1_3(X14,X19,X20)=X19|~r2_hidden(k4_tarski(esk1_3(X14,X19,X20),X19),X14))|X20=k1_wellord1(X14,X19)|~v1_relat_1(X14))&((esk1_3(X14,X19,X20)!=X19|r2_hidden(esk1_3(X14,X19,X20),X20)|X20=k1_wellord1(X14,X19)|~v1_relat_1(X14))&(r2_hidden(k4_tarski(esk1_3(X14,X19,X20),X19),X14)|r2_hidden(esk1_3(X14,X19,X20),X20)|X20=k1_wellord1(X14,X19)|~v1_relat_1(X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).
% 0.20/0.38  cnf(c_0_28, plain, (X1=k1_wellord1(k1_wellord2(X2),X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.38  cnf(c_0_29, negated_conjecture, (v3_ordinal1(k2_xboole_0(esk5_0,k1_tarski(esk5_0)))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.38  cnf(c_0_30, plain, (r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))|X1!=X2), inference(rw,[status(thm)],[c_0_24, c_0_18])).
% 0.20/0.38  fof(c_0_31, plain, ![X11, X12]:(~v3_ordinal1(X11)|(~v3_ordinal1(X12)|(r2_hidden(X11,X12)|X11=X12|r2_hidden(X12,X11)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).
% 0.20/0.38  fof(c_0_32, plain, ![X5, X6, X7]:((r2_hidden(X5,k3_relat_1(X7))|~r2_hidden(k4_tarski(X5,X6),X7)|~v1_relat_1(X7))&(r2_hidden(X6,k3_relat_1(X7))|~r2_hidden(k4_tarski(X5,X6),X7)|~v1_relat_1(X7))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_relat_1])])])).
% 0.20/0.38  cnf(c_0_33, plain, (k3_relat_1(X1)=X2|X1!=k1_wellord2(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.38  cnf(c_0_34, plain, (v1_relat_1(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.38  cnf(c_0_35, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,X4)|X4!=k1_wellord1(X3,X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.38  cnf(c_0_36, negated_conjecture, (k1_wellord1(k1_wellord2(k2_xboole_0(esk5_0,k1_tarski(esk5_0))),X1)=X1|~v3_ordinal1(X1)|~r2_hidden(X1,k2_xboole_0(esk5_0,k1_tarski(esk5_0)))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.38  cnf(c_0_37, plain, (r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1)))), inference(er,[status(thm)],[c_0_30])).
% 0.20/0.38  cnf(c_0_38, plain, (r2_hidden(X1,X2)|X1=X2|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.38  cnf(c_0_39, plain, (r1_tarski(X1,X2)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,X4)|~r2_hidden(X2,X4)|X3!=k1_wellord2(X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.38  cnf(c_0_40, plain, (r2_hidden(X1,k3_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.38  cnf(c_0_41, plain, (k3_relat_1(k1_wellord2(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_33]), c_0_34])])).
% 0.20/0.38  cnf(c_0_42, plain, (r2_hidden(X1,k3_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.38  cnf(c_0_43, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,k1_wellord1(X3,X2))|~v1_relat_1(X3)), inference(er,[status(thm)],[c_0_35])).
% 0.20/0.38  cnf(c_0_44, negated_conjecture, (k1_wellord1(k1_wellord2(k2_xboole_0(esk5_0,k1_tarski(esk5_0))),esk5_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_23])])).
% 0.20/0.38  cnf(c_0_45, negated_conjecture, (X1=esk5_0|r2_hidden(X1,esk5_0)|r2_hidden(esk5_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_38, c_0_23])).
% 0.20/0.38  cnf(c_0_46, negated_conjecture, (v3_ordinal1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  cnf(c_0_47, negated_conjecture, (esk4_0!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  fof(c_0_48, plain, ![X35]:(~v3_ordinal1(X35)|v2_wellord1(k1_wellord2(X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_wellord2])])).
% 0.20/0.38  cnf(c_0_49, plain, (r1_tarski(X1,X2)|~r2_hidden(k4_tarski(X1,X2),k1_wellord2(X3))|~r2_hidden(X2,X3)|~r2_hidden(X1,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_39]), c_0_34])])).
% 0.20/0.38  cnf(c_0_50, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k1_wellord2(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_34])])).
% 0.20/0.38  cnf(c_0_51, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k1_wellord2(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_41]), c_0_34])])).
% 0.20/0.38  cnf(c_0_52, negated_conjecture, (r2_hidden(k4_tarski(X1,esk5_0),k1_wellord2(k2_xboole_0(esk5_0,k1_tarski(esk5_0))))|~r2_hidden(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_34])])).
% 0.20/0.38  cnf(c_0_53, negated_conjecture, (r2_hidden(esk5_0,esk4_0)|r2_hidden(esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])).
% 0.20/0.38  cnf(c_0_54, negated_conjecture, (v3_ordinal1(k2_xboole_0(esk4_0,k1_tarski(esk4_0)))), inference(spm,[status(thm)],[c_0_22, c_0_46])).
% 0.20/0.38  fof(c_0_55, plain, ![X24, X25]:(~v1_relat_1(X24)|(~v2_wellord1(X24)|(~r2_hidden(X25,k3_relat_1(X24))|~r4_wellord1(X24,k2_wellord1(X24,k1_wellord1(X24,X25)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t57_wellord1])])])).
% 0.20/0.38  cnf(c_0_56, negated_conjecture, (k1_wellord1(k1_wellord2(esk5_0),X1)=X1|~v3_ordinal1(X1)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_28, c_0_23])).
% 0.20/0.38  cnf(c_0_57, plain, (v2_wellord1(k1_wellord2(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.38  fof(c_0_58, plain, ![X36, X37]:(~r1_tarski(X36,X37)|k2_wellord1(k1_wellord2(X37),X36)=k1_wellord2(X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_wellord2])])).
% 0.20/0.38  cnf(c_0_59, plain, (r1_tarski(X1,X2)|~r2_hidden(k4_tarski(X1,X2),k1_wellord2(X3))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_49, c_0_50]), c_0_51])).
% 0.20/0.38  cnf(c_0_60, negated_conjecture, (r2_hidden(k4_tarski(esk4_0,esk5_0),k1_wellord2(k2_xboole_0(esk5_0,k1_tarski(esk5_0))))|r2_hidden(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.38  fof(c_0_61, plain, ![X22, X23]:(~v1_relat_1(X22)|(~v1_relat_1(X23)|(~r4_wellord1(X22,X23)|r4_wellord1(X23,X22)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_wellord1])])])).
% 0.20/0.38  cnf(c_0_62, negated_conjecture, (k1_wellord1(k1_wellord2(k2_xboole_0(esk4_0,k1_tarski(esk4_0))),X1)=X1|~v3_ordinal1(X1)|~r2_hidden(X1,k2_xboole_0(esk4_0,k1_tarski(esk4_0)))), inference(spm,[status(thm)],[c_0_28, c_0_54])).
% 0.20/0.38  cnf(c_0_63, plain, (~v1_relat_1(X1)|~v2_wellord1(X1)|~r2_hidden(X2,k3_relat_1(X1))|~r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.38  cnf(c_0_64, negated_conjecture, (k1_wellord1(k1_wellord2(esk5_0),esk4_0)=esk4_0|r2_hidden(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_53]), c_0_46])])).
% 0.20/0.38  cnf(c_0_65, negated_conjecture, (v2_wellord1(k1_wellord2(esk5_0))), inference(spm,[status(thm)],[c_0_57, c_0_23])).
% 0.20/0.38  cnf(c_0_66, plain, (k2_wellord1(k1_wellord2(X2),X1)=k1_wellord2(X1)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.38  cnf(c_0_67, negated_conjecture, (r1_tarski(esk4_0,esk5_0)|r2_hidden(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.20/0.38  cnf(c_0_68, plain, (r4_wellord1(X2,X1)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r4_wellord1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.20/0.38  cnf(c_0_69, negated_conjecture, (r4_wellord1(k1_wellord2(esk4_0),k1_wellord2(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  cnf(c_0_70, negated_conjecture, (k1_wellord1(k1_wellord2(k2_xboole_0(esk4_0,k1_tarski(esk4_0))),esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_37]), c_0_46])])).
% 0.20/0.38  cnf(c_0_71, negated_conjecture, (r2_hidden(esk5_0,esk4_0)|~r4_wellord1(k1_wellord2(esk5_0),k2_wellord1(k1_wellord2(esk5_0),esk4_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65]), c_0_41]), c_0_34])]), c_0_53])).
% 0.20/0.38  cnf(c_0_72, negated_conjecture, (k2_wellord1(k1_wellord2(esk5_0),esk4_0)=k1_wellord2(esk4_0)|r2_hidden(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.20/0.38  cnf(c_0_73, negated_conjecture, (r4_wellord1(k1_wellord2(esk5_0),k1_wellord2(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_34]), c_0_34])])).
% 0.20/0.38  cnf(c_0_74, negated_conjecture, (r2_hidden(k4_tarski(X1,esk4_0),k1_wellord2(k2_xboole_0(esk4_0,k1_tarski(esk4_0))))|~r2_hidden(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_70]), c_0_34])])).
% 0.20/0.38  cnf(c_0_75, negated_conjecture, (r2_hidden(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73])])).
% 0.20/0.38  cnf(c_0_76, negated_conjecture, (k1_wellord1(k1_wellord2(esk4_0),X1)=X1|~v3_ordinal1(X1)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_28, c_0_46])).
% 0.20/0.38  cnf(c_0_77, negated_conjecture, (r2_hidden(k4_tarski(esk5_0,esk4_0),k1_wellord2(k2_xboole_0(esk4_0,k1_tarski(esk4_0))))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.20/0.38  cnf(c_0_78, negated_conjecture, (k1_wellord1(k1_wellord2(esk4_0),esk5_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_75]), c_0_23])])).
% 0.20/0.38  cnf(c_0_79, negated_conjecture, (v2_wellord1(k1_wellord2(esk4_0))), inference(spm,[status(thm)],[c_0_57, c_0_46])).
% 0.20/0.38  cnf(c_0_80, negated_conjecture, (r1_tarski(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_59, c_0_77])).
% 0.20/0.38  cnf(c_0_81, negated_conjecture, (~r4_wellord1(k1_wellord2(esk4_0),k2_wellord1(k1_wellord2(esk4_0),esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_78]), c_0_79]), c_0_41]), c_0_75]), c_0_34])])).
% 0.20/0.38  cnf(c_0_82, negated_conjecture, (k2_wellord1(k1_wellord2(esk4_0),esk5_0)=k1_wellord2(esk5_0)), inference(spm,[status(thm)],[c_0_66, c_0_80])).
% 0.20/0.38  cnf(c_0_83, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_82]), c_0_69])]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 84
% 0.20/0.38  # Proof object clause steps            : 55
% 0.20/0.38  # Proof object formula steps           : 29
% 0.20/0.38  # Proof object conjectures             : 34
% 0.20/0.38  # Proof object clause conjectures      : 31
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 19
% 0.20/0.38  # Proof object initial formulas used   : 14
% 0.20/0.38  # Proof object generating inferences   : 28
% 0.20/0.38  # Proof object simplifying inferences  : 47
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 14
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 31
% 0.20/0.38  # Removed in clause preprocessing      : 1
% 0.20/0.38  # Initial clauses in saturation        : 30
% 0.20/0.38  # Processed clauses                    : 150
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 11
% 0.20/0.38  # ...remaining for further processing  : 139
% 0.20/0.38  # Other redundant clauses eliminated   : 12
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 7
% 0.20/0.38  # Backward-rewritten                   : 11
% 0.20/0.38  # Generated clauses                    : 152
% 0.20/0.38  # ...of the previous two non-trivial   : 124
% 0.20/0.38  # Contextual simplify-reflections      : 4
% 0.20/0.38  # Paramodulations                      : 131
% 0.20/0.38  # Factorizations                       : 10
% 0.20/0.38  # Equation resolutions                 : 12
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 80
% 0.20/0.38  #    Positive orientable unit clauses  : 33
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 6
% 0.20/0.38  #    Non-unit-clauses                  : 41
% 0.20/0.38  # Current number of unprocessed clauses: 28
% 0.20/0.38  # ...number of literals in the above   : 75
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 49
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 718
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 468
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 13
% 0.20/0.38  # Unit Clause-clause subsumption calls : 215
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 27
% 0.20/0.38  # BW rewrite match successes           : 3
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 7842
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.042 s
% 0.20/0.38  # System time              : 0.001 s
% 0.20/0.38  # Total time               : 0.043 s
% 0.20/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
