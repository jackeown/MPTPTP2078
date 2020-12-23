%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:24 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 231 expanded)
%              Number of clauses        :   43 ( 107 expanded)
%              Number of leaves         :   11 (  57 expanded)
%              Depth                    :   15
%              Number of atoms          :  171 ( 913 expanded)
%              Number of equality atoms :   30 ( 203 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t31_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(d6_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(c_0_11,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k4_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k4_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_12,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_13,plain,(
    ! [X26] : k4_xboole_0(X26,k1_xboole_0) = X26 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_14,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_17,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk2_3(X1,X2,k1_xboole_0),X1)
    | ~ r2_hidden(esk2_3(X1,X2,k1_xboole_0),X3) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_19,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_20,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk2_3(X1,X2,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_17])).

fof(c_0_22,plain,(
    ! [X25] : r1_tarski(k1_xboole_0,X25) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_23,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0
    | r2_hidden(esk2_3(X1,X1,k1_xboole_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_26,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(X1,X2)
             => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_relat_1])).

fof(c_0_27,plain,(
    ! [X27,X28,X29] :
      ( ~ r1_tarski(k4_xboole_0(X27,X28),X29)
      | r1_tarski(X27,k2_xboole_0(X28,X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0
    | r2_hidden(esk2_3(X1,X1,k1_xboole_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

fof(c_0_29,plain,(
    ! [X50] :
      ( ~ v1_relat_1(X50)
      | k3_relat_1(X50) = k2_xboole_0(k1_relat_1(X50),k2_relat_1(X50)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

fof(c_0_30,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & v1_relat_1(esk7_0)
    & r1_tarski(esk6_0,esk7_0)
    & ~ r1_tarski(k3_relat_1(esk6_0),k3_relat_1(esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_28]),c_0_28])).

cnf(c_0_33,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_35,plain,(
    ! [X53,X54] :
      ( ( r1_tarski(k1_relat_1(X53),k1_relat_1(X54))
        | ~ r1_tarski(X53,X54)
        | ~ v1_relat_1(X54)
        | ~ v1_relat_1(X53) )
      & ( r1_tarski(k2_relat_1(X53),k2_relat_1(X54))
        | ~ r1_tarski(X53,X54)
        | ~ v1_relat_1(X54)
        | ~ v1_relat_1(X53) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

fof(c_0_36,plain,(
    ! [X30,X31,X32] :
      ( ~ r1_tarski(X30,X31)
      | ~ r1_tarski(X32,X31)
      | r1_tarski(k2_xboole_0(X30,X32),X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_25])])).

cnf(c_0_38,negated_conjecture,
    ( k2_xboole_0(k1_relat_1(esk7_0),k2_relat_1(esk7_0)) = k3_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_39,plain,(
    ! [X20,X21] :
      ( ( r1_tarski(X20,X21)
        | X20 != X21 )
      & ( r1_tarski(X21,X20)
        | X20 != X21 )
      & ( ~ r1_tarski(X20,X21)
        | ~ r1_tarski(X21,X20)
        | X20 = X21 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_40,plain,(
    ! [X22,X23,X24] :
      ( ~ r1_tarski(X22,X23)
      | r1_tarski(X22,k2_xboole_0(X24,X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

cnf(c_0_41,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk7_0),k3_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(esk7_0))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_34])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(esk7_0))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_34])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(k2_xboole_0(X1,k1_relat_1(esk7_0)),k3_relat_1(esk7_0))
    | ~ r1_tarski(X1,k3_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( k2_xboole_0(k1_relat_1(esk6_0),k2_relat_1(esk6_0)) = k3_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(X1,k3_relat_1(esk7_0))
    | ~ r1_tarski(X1,k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_38])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk6_0),k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_46])])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk6_0),k1_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_49]),c_0_46])])).

cnf(c_0_57,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k3_relat_1(esk7_0),k1_relat_1(esk7_0)),k3_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k3_relat_1(esk6_0),X1)
    | ~ r1_tarski(k2_relat_1(esk6_0),X1)
    | ~ r1_tarski(k1_relat_1(esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk6_0),k3_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(esk6_0),k3_relat_1(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk6_0),k2_xboole_0(X1,k1_relat_1(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_56])).

cnf(c_0_63,negated_conjecture,
    ( k2_xboole_0(k3_relat_1(esk7_0),k1_relat_1(esk7_0)) = k3_relat_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_37])])).

cnf(c_0_64,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk6_0),k3_relat_1(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:25:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S049N
% 0.19/0.41  # and selection function PSelectComplexPreferEQ.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.029 s
% 0.19/0.41  # Presaturation interreduction done
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.19/0.41  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.19/0.41  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.41  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.41  fof(t31_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 0.19/0.41  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 0.19/0.41  fof(d6_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 0.19/0.41  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 0.19/0.41  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 0.19/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.41  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 0.19/0.41  fof(c_0_11, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12))&(~r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k4_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k4_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))&(~r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.19/0.41  cnf(c_0_12, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.41  fof(c_0_13, plain, ![X26]:k4_xboole_0(X26,k1_xboole_0)=X26, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.19/0.41  cnf(c_0_14, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_12])).
% 0.19/0.41  cnf(c_0_15, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.41  cnf(c_0_16, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.41  cnf(c_0_17, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.41  cnf(c_0_18, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|r2_hidden(esk2_3(X1,X2,k1_xboole_0),X1)|~r2_hidden(esk2_3(X1,X2,k1_xboole_0),X3)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.41  fof(c_0_19, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.41  cnf(c_0_20, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.41  cnf(c_0_21, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|r2_hidden(esk2_3(X1,X2,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_18, c_0_17])).
% 0.19/0.41  fof(c_0_22, plain, ![X25]:r1_tarski(k1_xboole_0,X25), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.41  cnf(c_0_23, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_24, plain, (k4_xboole_0(X1,X1)=k1_xboole_0|r2_hidden(esk2_3(X1,X1,k1_xboole_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.41  cnf(c_0_25, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.41  fof(c_0_26, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2)))))), inference(assume_negation,[status(cth)],[t31_relat_1])).
% 0.19/0.41  fof(c_0_27, plain, ![X27, X28, X29]:(~r1_tarski(k4_xboole_0(X27,X28),X29)|r1_tarski(X27,k2_xboole_0(X28,X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 0.19/0.41  cnf(c_0_28, plain, (k4_xboole_0(X1,X1)=k1_xboole_0|r2_hidden(esk2_3(X1,X1,k1_xboole_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])])).
% 0.19/0.41  fof(c_0_29, plain, ![X50]:(~v1_relat_1(X50)|k3_relat_1(X50)=k2_xboole_0(k1_relat_1(X50),k2_relat_1(X50))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).
% 0.19/0.41  fof(c_0_30, negated_conjecture, (v1_relat_1(esk6_0)&(v1_relat_1(esk7_0)&(r1_tarski(esk6_0,esk7_0)&~r1_tarski(k3_relat_1(esk6_0),k3_relat_1(esk7_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).
% 0.19/0.41  cnf(c_0_31, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.41  cnf(c_0_32, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_28]), c_0_28])).
% 0.19/0.41  cnf(c_0_33, plain, (k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.41  cnf(c_0_34, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.41  fof(c_0_35, plain, ![X53, X54]:((r1_tarski(k1_relat_1(X53),k1_relat_1(X54))|~r1_tarski(X53,X54)|~v1_relat_1(X54)|~v1_relat_1(X53))&(r1_tarski(k2_relat_1(X53),k2_relat_1(X54))|~r1_tarski(X53,X54)|~v1_relat_1(X54)|~v1_relat_1(X53))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.19/0.41  fof(c_0_36, plain, ![X30, X31, X32]:(~r1_tarski(X30,X31)|~r1_tarski(X32,X31)|r1_tarski(k2_xboole_0(X30,X32),X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 0.19/0.41  cnf(c_0_37, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_25])])).
% 0.19/0.41  cnf(c_0_38, negated_conjecture, (k2_xboole_0(k1_relat_1(esk7_0),k2_relat_1(esk7_0))=k3_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.41  fof(c_0_39, plain, ![X20, X21]:(((r1_tarski(X20,X21)|X20!=X21)&(r1_tarski(X21,X20)|X20!=X21))&(~r1_tarski(X20,X21)|~r1_tarski(X21,X20)|X20=X21)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.41  fof(c_0_40, plain, ![X22, X23, X24]:(~r1_tarski(X22,X23)|r1_tarski(X22,k2_xboole_0(X24,X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 0.19/0.41  cnf(c_0_41, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.41  cnf(c_0_42, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.41  cnf(c_0_43, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.41  cnf(c_0_44, negated_conjecture, (r1_tarski(k1_relat_1(esk7_0),k3_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.41  cnf(c_0_45, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.41  cnf(c_0_46, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.41  cnf(c_0_47, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.41  cnf(c_0_48, negated_conjecture, (r1_tarski(k2_relat_1(X1),k2_relat_1(esk7_0))|~v1_relat_1(X1)|~r1_tarski(X1,esk7_0)), inference(spm,[status(thm)],[c_0_41, c_0_34])).
% 0.19/0.41  cnf(c_0_49, negated_conjecture, (r1_tarski(esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.41  cnf(c_0_50, negated_conjecture, (r1_tarski(k1_relat_1(X1),k1_relat_1(esk7_0))|~v1_relat_1(X1)|~r1_tarski(X1,esk7_0)), inference(spm,[status(thm)],[c_0_42, c_0_34])).
% 0.19/0.41  cnf(c_0_51, negated_conjecture, (r1_tarski(k2_xboole_0(X1,k1_relat_1(esk7_0)),k3_relat_1(esk7_0))|~r1_tarski(X1,k3_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.41  cnf(c_0_52, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_45])).
% 0.19/0.41  cnf(c_0_53, negated_conjecture, (k2_xboole_0(k1_relat_1(esk6_0),k2_relat_1(esk6_0))=k3_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_33, c_0_46])).
% 0.19/0.41  cnf(c_0_54, negated_conjecture, (r1_tarski(X1,k3_relat_1(esk7_0))|~r1_tarski(X1,k2_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_47, c_0_38])).
% 0.19/0.41  cnf(c_0_55, negated_conjecture, (r1_tarski(k2_relat_1(esk6_0),k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_46])])).
% 0.19/0.41  cnf(c_0_56, negated_conjecture, (r1_tarski(k1_relat_1(esk6_0),k1_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_49]), c_0_46])])).
% 0.19/0.41  cnf(c_0_57, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.41  cnf(c_0_58, negated_conjecture, (r1_tarski(k2_xboole_0(k3_relat_1(esk7_0),k1_relat_1(esk7_0)),k3_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.41  cnf(c_0_59, negated_conjecture, (r1_tarski(k3_relat_1(esk6_0),X1)|~r1_tarski(k2_relat_1(esk6_0),X1)|~r1_tarski(k1_relat_1(esk6_0),X1)), inference(spm,[status(thm)],[c_0_43, c_0_53])).
% 0.19/0.41  cnf(c_0_60, negated_conjecture, (r1_tarski(k2_relat_1(esk6_0),k3_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.19/0.41  cnf(c_0_61, negated_conjecture, (~r1_tarski(k3_relat_1(esk6_0),k3_relat_1(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.41  cnf(c_0_62, negated_conjecture, (r1_tarski(k1_relat_1(esk6_0),k2_xboole_0(X1,k1_relat_1(esk7_0)))), inference(spm,[status(thm)],[c_0_47, c_0_56])).
% 0.19/0.41  cnf(c_0_63, negated_conjecture, (k2_xboole_0(k3_relat_1(esk7_0),k1_relat_1(esk7_0))=k3_relat_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_37])])).
% 0.19/0.41  cnf(c_0_64, negated_conjecture, (~r1_tarski(k1_relat_1(esk6_0),k3_relat_1(esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])).
% 0.19/0.41  cnf(c_0_65, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 66
% 0.19/0.41  # Proof object clause steps            : 43
% 0.19/0.41  # Proof object formula steps           : 23
% 0.19/0.41  # Proof object conjectures             : 23
% 0.19/0.41  # Proof object clause conjectures      : 20
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 18
% 0.19/0.41  # Proof object initial formulas used   : 11
% 0.19/0.41  # Proof object generating inferences   : 23
% 0.19/0.41  # Proof object simplifying inferences  : 15
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 16
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 33
% 0.19/0.41  # Removed in clause preprocessing      : 1
% 0.19/0.41  # Initial clauses in saturation        : 32
% 0.19/0.41  # Processed clauses                    : 489
% 0.19/0.41  # ...of these trivial                  : 16
% 0.19/0.41  # ...subsumed                          : 138
% 0.19/0.41  # ...remaining for further processing  : 335
% 0.19/0.41  # Other redundant clauses eliminated   : 7
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 6
% 0.19/0.41  # Backward-rewritten                   : 68
% 0.19/0.41  # Generated clauses                    : 1994
% 0.19/0.41  # ...of the previous two non-trivial   : 1299
% 0.19/0.41  # Contextual simplify-reflections      : 2
% 0.19/0.41  # Paramodulations                      : 1985
% 0.19/0.41  # Factorizations                       : 2
% 0.19/0.41  # Equation resolutions                 : 7
% 0.19/0.41  # Propositional unsat checks           : 0
% 0.19/0.41  #    Propositional check models        : 0
% 0.19/0.41  #    Propositional check unsatisfiable : 0
% 0.19/0.41  #    Propositional clauses             : 0
% 0.19/0.41  #    Propositional clauses after purity: 0
% 0.19/0.41  #    Propositional unsat core size     : 0
% 0.19/0.41  #    Propositional preprocessing time  : 0.000
% 0.19/0.41  #    Propositional encoding time       : 0.000
% 0.19/0.41  #    Propositional solver time         : 0.000
% 0.19/0.41  #    Success case prop preproc time    : 0.000
% 0.19/0.41  #    Success case prop encoding time   : 0.000
% 0.19/0.41  #    Success case prop solver time     : 0.000
% 0.19/0.41  # Current number of processed clauses  : 223
% 0.19/0.41  #    Positive orientable unit clauses  : 99
% 0.19/0.41  #    Positive unorientable unit clauses: 0
% 0.19/0.41  #    Negative unit clauses             : 3
% 0.19/0.41  #    Non-unit-clauses                  : 121
% 0.19/0.41  # Current number of unprocessed clauses: 764
% 0.19/0.41  # ...number of literals in the above   : 1262
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 106
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 2018
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 1761
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 139
% 0.19/0.41  # Unit Clause-clause subsumption calls : 350
% 0.19/0.41  # Rewrite failures with RHS unbound    : 0
% 0.19/0.41  # BW rewrite match attempts            : 157
% 0.19/0.41  # BW rewrite match successes           : 40
% 0.19/0.41  # Condensation attempts                : 0
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 24033
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.061 s
% 0.19/0.41  # System time              : 0.006 s
% 0.19/0.41  # Total time               : 0.067 s
% 0.19/0.41  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
