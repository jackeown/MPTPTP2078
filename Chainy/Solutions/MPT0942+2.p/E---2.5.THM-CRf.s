%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0942+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:58 EST 2020

% Result     : Theorem 1.38s
% Output     : CNFRefutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   30 (  37 expanded)
%              Number of clauses        :   13 (  14 expanded)
%              Number of leaves         :    8 (  10 expanded)
%              Depth                    :    5
%              Number of atoms          :   74 (  87 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_wellord2,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v2_wellord1(k1_wellord2(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).

fof(d4_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
      <=> ( v1_relat_2(X1)
          & v8_relat_2(X1)
          & v4_relat_2(X1)
          & v6_relat_2(X1)
          & v1_wellord1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT010+2.ax',d4_wellord1)).

fof(dt_k1_wellord2,axiom,(
    ! [X1] : v1_relat_1(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(t2_wellord2,axiom,(
    ! [X1] : v1_relat_2(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_wellord2)).

fof(t3_wellord2,axiom,(
    ! [X1] : v8_relat_2(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_wellord2)).

fof(t5_wellord2,axiom,(
    ! [X1] : v4_relat_2(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_wellord2)).

fof(t6_wellord2,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v1_wellord1(k1_wellord2(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_wellord2)).

fof(t4_wellord2,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v6_relat_2(k1_wellord2(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_wellord2)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => v2_wellord1(k1_wellord2(X1)) ) ),
    inference(assume_negation,[status(cth)],[t7_wellord2])).

fof(c_0_9,plain,(
    ! [X14] :
      ( ( v1_relat_2(X14)
        | ~ v2_wellord1(X14)
        | ~ v1_relat_1(X14) )
      & ( v8_relat_2(X14)
        | ~ v2_wellord1(X14)
        | ~ v1_relat_1(X14) )
      & ( v4_relat_2(X14)
        | ~ v2_wellord1(X14)
        | ~ v1_relat_1(X14) )
      & ( v6_relat_2(X14)
        | ~ v2_wellord1(X14)
        | ~ v1_relat_1(X14) )
      & ( v1_wellord1(X14)
        | ~ v2_wellord1(X14)
        | ~ v1_relat_1(X14) )
      & ( ~ v1_relat_2(X14)
        | ~ v8_relat_2(X14)
        | ~ v4_relat_2(X14)
        | ~ v6_relat_2(X14)
        | ~ v1_wellord1(X14)
        | v2_wellord1(X14)
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).

fof(c_0_10,plain,(
    ! [X106] : v1_relat_1(k1_wellord2(X106)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_11,plain,(
    ! [X107] : v1_relat_2(k1_wellord2(X107)) ),
    inference(variable_rename,[status(thm)],[t2_wellord2])).

fof(c_0_12,plain,(
    ! [X108] : v8_relat_2(k1_wellord2(X108)) ),
    inference(variable_rename,[status(thm)],[t3_wellord2])).

fof(c_0_13,plain,(
    ! [X110] : v4_relat_2(k1_wellord2(X110)) ),
    inference(variable_rename,[status(thm)],[t5_wellord2])).

fof(c_0_14,plain,(
    ! [X111] :
      ( ~ v3_ordinal1(X111)
      | v1_wellord1(k1_wellord2(X111)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_wellord2])])).

fof(c_0_15,negated_conjecture,
    ( v3_ordinal1(esk1_0)
    & ~ v2_wellord1(k1_wellord2(esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_16,plain,(
    ! [X109] :
      ( ~ v3_ordinal1(X109)
      | v6_relat_2(k1_wellord2(X109)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_wellord2])])).

cnf(c_0_17,plain,
    ( v2_wellord1(X1)
    | ~ v1_relat_2(X1)
    | ~ v8_relat_2(X1)
    | ~ v4_relat_2(X1)
    | ~ v6_relat_2(X1)
    | ~ v1_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( v1_relat_2(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( v8_relat_2(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( v4_relat_2(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( v1_wellord1(k1_wellord2(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( v3_ordinal1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( v6_relat_2(k1_wellord2(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( v2_wellord1(k1_wellord2(X1))
    | ~ v1_wellord1(k1_wellord2(X1))
    | ~ v6_relat_2(k1_wellord2(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20]),c_0_21])])).

cnf(c_0_26,negated_conjecture,
    ( v1_wellord1(k1_wellord2(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( v6_relat_2(k1_wellord2(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( ~ v2_wellord1(k1_wellord2(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])]),c_0_28]),
    [proof]).
%------------------------------------------------------------------------------
