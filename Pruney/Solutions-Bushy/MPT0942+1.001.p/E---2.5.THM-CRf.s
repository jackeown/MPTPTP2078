%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0942+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:27 EST 2020

% Result     : Theorem 0.22s
% Output     : CNFRefutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   28 (  31 expanded)
%              Number of clauses        :   11 (  11 expanded)
%              Number of leaves         :    8 (   9 expanded)
%              Depth                    :    4
%              Number of atoms          :   71 (  77 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal clause size      :   22 (   2 average)
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

fof(t6_wellord2,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v1_wellord1(k1_wellord2(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_wellord2)).

fof(t5_wellord2,axiom,(
    ! [X1] : v4_relat_2(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_wellord2)).

fof(t3_wellord2,axiom,(
    ! [X1] : v8_relat_2(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_wellord2)).

fof(t2_wellord2,axiom,(
    ! [X1] : v1_relat_2(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_wellord2)).

fof(dt_k1_wellord2,axiom,(
    ! [X1] : v1_relat_1(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(t4_wellord2,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v6_relat_2(k1_wellord2(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_wellord2)).

fof(t7_wellord2,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v2_wellord1(k1_wellord2(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_wellord2)).

fof(c_0_8,plain,(
    ! [X2] :
      ( ( v1_relat_2(X2)
        | ~ v2_wellord1(X2)
        | ~ v1_relat_1(X2) )
      & ( v8_relat_2(X2)
        | ~ v2_wellord1(X2)
        | ~ v1_relat_1(X2) )
      & ( v4_relat_2(X2)
        | ~ v2_wellord1(X2)
        | ~ v1_relat_1(X2) )
      & ( v6_relat_2(X2)
        | ~ v2_wellord1(X2)
        | ~ v1_relat_1(X2) )
      & ( v1_wellord1(X2)
        | ~ v2_wellord1(X2)
        | ~ v1_relat_1(X2) )
      & ( ~ v1_relat_2(X2)
        | ~ v8_relat_2(X2)
        | ~ v4_relat_2(X2)
        | ~ v6_relat_2(X2)
        | ~ v1_wellord1(X2)
        | v2_wellord1(X2)
        | ~ v1_relat_1(X2) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).

fof(c_0_9,plain,(
    ! [X8] :
      ( ~ v3_ordinal1(X8)
      | v1_wellord1(k1_wellord2(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_wellord2])])).

fof(c_0_10,plain,(
    ! [X7] : v4_relat_2(k1_wellord2(X7)) ),
    inference(variable_rename,[status(thm)],[t5_wellord2])).

fof(c_0_11,plain,(
    ! [X5] : v8_relat_2(k1_wellord2(X5)) ),
    inference(variable_rename,[status(thm)],[t3_wellord2])).

fof(c_0_12,plain,(
    ! [X4] : v1_relat_2(k1_wellord2(X4)) ),
    inference(variable_rename,[status(thm)],[t2_wellord2])).

fof(c_0_13,plain,(
    ! [X3] : v1_relat_1(k1_wellord2(X3)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_14,plain,(
    ! [X6] :
      ( ~ v3_ordinal1(X6)
      | v6_relat_2(k1_wellord2(X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_wellord2])])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => v2_wellord1(k1_wellord2(X1)) ) ),
    inference(assume_negation,[status(cth)],[t7_wellord2])).

cnf(c_0_16,plain,
    ( v2_wellord1(X1)
    | ~ v1_relat_2(X1)
    | ~ v8_relat_2(X1)
    | ~ v4_relat_2(X1)
    | ~ v6_relat_2(X1)
    | ~ v1_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,plain,
    ( v1_wellord1(k1_wellord2(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( v4_relat_2(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( v8_relat_2(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( v1_relat_2(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( v6_relat_2(k1_wellord2(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_23,negated_conjecture,
    ( v3_ordinal1(esk1_0)
    & ~ v2_wellord1(k1_wellord2(esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

cnf(c_0_24,plain,
    ( v2_wellord1(k1_wellord2(X1))
    | ~ v3_ordinal1(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( v3_ordinal1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_wellord1(k1_wellord2(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),
    [proof]).

%------------------------------------------------------------------------------
