%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0783+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:11 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   43 (  95 expanded)
%              Number of clauses        :   26 (  35 expanded)
%              Number of leaves         :    8 (  24 expanded)
%              Depth                    :   13
%              Number of atoms          :  165 ( 418 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t31_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v1_wellord1(X2)
       => v1_wellord1(k2_wellord1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_wellord1)).

fof(dt_k2_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k2_wellord1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(t23_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v6_relat_2(X2)
       => v6_relat_2(k2_wellord1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_wellord1)).

fof(t25_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_2(X2)
       => v4_relat_2(k2_wellord1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_wellord1)).

fof(t24_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v8_relat_2(X2)
       => v8_relat_2(k2_wellord1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_wellord1)).

fof(t32_wellord1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v2_wellord1(X2)
       => v2_wellord1(k2_wellord1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_wellord1)).

fof(t22_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v1_relat_2(X2)
       => v1_relat_2(k2_wellord1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_wellord1)).

fof(c_0_8,plain,(
    ! [X3] :
      ( ( v1_relat_2(X3)
        | ~ v2_wellord1(X3)
        | ~ v1_relat_1(X3) )
      & ( v8_relat_2(X3)
        | ~ v2_wellord1(X3)
        | ~ v1_relat_1(X3) )
      & ( v4_relat_2(X3)
        | ~ v2_wellord1(X3)
        | ~ v1_relat_1(X3) )
      & ( v6_relat_2(X3)
        | ~ v2_wellord1(X3)
        | ~ v1_relat_1(X3) )
      & ( v1_wellord1(X3)
        | ~ v2_wellord1(X3)
        | ~ v1_relat_1(X3) )
      & ( ~ v1_relat_2(X3)
        | ~ v8_relat_2(X3)
        | ~ v4_relat_2(X3)
        | ~ v6_relat_2(X3)
        | ~ v1_wellord1(X3)
        | v2_wellord1(X3)
        | ~ v1_relat_1(X3) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).

fof(c_0_9,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X15)
      | ~ v1_wellord1(X15)
      | v1_wellord1(k2_wellord1(X15,X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_wellord1])])).

fof(c_0_10,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X4)
      | v1_relat_1(k2_wellord1(X4,X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_wellord1])])).

cnf(c_0_11,plain,
    ( v2_wellord1(X1)
    | ~ v1_relat_2(X1)
    | ~ v8_relat_2(X1)
    | ~ v4_relat_2(X1)
    | ~ v6_relat_2(X1)
    | ~ v1_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( v1_wellord1(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_wellord1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( v1_relat_1(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X8,X9] :
      ( ~ v1_relat_1(X9)
      | ~ v6_relat_2(X9)
      | v6_relat_2(k2_wellord1(X9,X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_wellord1])])).

cnf(c_0_15,plain,
    ( v2_wellord1(k2_wellord1(X1,X2))
    | ~ v1_wellord1(X1)
    | ~ v6_relat_2(k2_wellord1(X1,X2))
    | ~ v4_relat_2(k2_wellord1(X1,X2))
    | ~ v8_relat_2(k2_wellord1(X1,X2))
    | ~ v1_relat_2(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])).

cnf(c_0_16,plain,
    ( v6_relat_2(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v6_relat_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_17,plain,(
    ! [X12,X13] :
      ( ~ v1_relat_1(X13)
      | ~ v4_relat_2(X13)
      | v4_relat_2(k2_wellord1(X13,X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_wellord1])])).

cnf(c_0_18,plain,
    ( v2_wellord1(k2_wellord1(X1,X2))
    | ~ v1_wellord1(X1)
    | ~ v6_relat_2(X1)
    | ~ v4_relat_2(k2_wellord1(X1,X2))
    | ~ v8_relat_2(k2_wellord1(X1,X2))
    | ~ v1_relat_2(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,plain,
    ( v4_relat_2(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v4_relat_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_20,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X11)
      | ~ v8_relat_2(X11)
      | v8_relat_2(k2_wellord1(X11,X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_wellord1])])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( v2_wellord1(X2)
         => v2_wellord1(k2_wellord1(X2,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t32_wellord1])).

cnf(c_0_22,plain,
    ( v2_wellord1(k2_wellord1(X1,X2))
    | ~ v1_wellord1(X1)
    | ~ v6_relat_2(X1)
    | ~ v4_relat_2(X1)
    | ~ v8_relat_2(k2_wellord1(X1,X2))
    | ~ v1_relat_2(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( v8_relat_2(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v8_relat_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_24,plain,(
    ! [X6,X7] :
      ( ~ v1_relat_1(X7)
      | ~ v1_relat_2(X7)
      | v1_relat_2(k2_wellord1(X7,X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_wellord1])])).

fof(c_0_25,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v2_wellord1(esk2_0)
    & ~ v2_wellord1(k2_wellord1(esk2_0,esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

cnf(c_0_26,plain,
    ( v2_wellord1(k2_wellord1(X1,X2))
    | ~ v1_wellord1(X1)
    | ~ v6_relat_2(X1)
    | ~ v4_relat_2(X1)
    | ~ v8_relat_2(X1)
    | ~ v1_relat_2(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,plain,
    ( v1_relat_2(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( ~ v2_wellord1(k2_wellord1(esk2_0,esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,plain,
    ( v2_wellord1(k2_wellord1(X1,X2))
    | ~ v1_wellord1(X1)
    | ~ v6_relat_2(X1)
    | ~ v4_relat_2(X1)
    | ~ v8_relat_2(X1)
    | ~ v1_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( ~ v1_wellord1(esk2_0)
    | ~ v6_relat_2(esk2_0)
    | ~ v4_relat_2(esk2_0)
    | ~ v8_relat_2(esk2_0)
    | ~ v1_relat_2(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

cnf(c_0_32,plain,
    ( v1_wellord1(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_33,negated_conjecture,
    ( v2_wellord1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( ~ v6_relat_2(esk2_0)
    | ~ v4_relat_2(esk2_0)
    | ~ v8_relat_2(esk2_0)
    | ~ v1_relat_2(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_30])])).

cnf(c_0_35,plain,
    ( v6_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_36,negated_conjecture,
    ( ~ v4_relat_2(esk2_0)
    | ~ v8_relat_2(esk2_0)
    | ~ v1_relat_2(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_33]),c_0_30])])).

cnf(c_0_37,plain,
    ( v4_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_38,negated_conjecture,
    ( ~ v8_relat_2(esk2_0)
    | ~ v1_relat_2(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_33]),c_0_30])])).

cnf(c_0_39,plain,
    ( v8_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_40,negated_conjecture,
    ( ~ v1_relat_2(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_33]),c_0_30])])).

cnf(c_0_41,plain,
    ( v1_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_33]),c_0_30])]),
    [proof]).

%------------------------------------------------------------------------------
