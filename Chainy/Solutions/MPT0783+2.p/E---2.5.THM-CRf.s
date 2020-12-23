%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0783+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:52 EST 2020

% Result     : Theorem 1.37s
% Output     : CNFRefutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 117 expanded)
%              Number of clauses        :   28 (  42 expanded)
%              Number of leaves         :    8 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :  127 ( 430 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t32_wellord1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v2_wellord1(X2)
       => v2_wellord1(k2_wellord1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_wellord1)).

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

fof(dt_k2_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k2_wellord1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(t22_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v1_relat_2(X2)
       => v1_relat_2(k2_wellord1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_wellord1)).

fof(t31_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v1_wellord1(X2)
       => v1_wellord1(k2_wellord1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_wellord1)).

fof(t24_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v8_relat_2(X2)
       => v8_relat_2(k2_wellord1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_wellord1)).

fof(t23_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v6_relat_2(X2)
       => v6_relat_2(k2_wellord1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_wellord1)).

fof(t25_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_2(X2)
       => v4_relat_2(k2_wellord1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_wellord1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( v2_wellord1(X2)
         => v2_wellord1(k2_wellord1(X2,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t32_wellord1])).

fof(c_0_9,plain,(
    ! [X3357] :
      ( ( v1_relat_2(X3357)
        | ~ v2_wellord1(X3357)
        | ~ v1_relat_1(X3357) )
      & ( v8_relat_2(X3357)
        | ~ v2_wellord1(X3357)
        | ~ v1_relat_1(X3357) )
      & ( v4_relat_2(X3357)
        | ~ v2_wellord1(X3357)
        | ~ v1_relat_1(X3357) )
      & ( v6_relat_2(X3357)
        | ~ v2_wellord1(X3357)
        | ~ v1_relat_1(X3357) )
      & ( v1_wellord1(X3357)
        | ~ v2_wellord1(X3357)
        | ~ v1_relat_1(X3357) )
      & ( ~ v1_relat_2(X3357)
        | ~ v8_relat_2(X3357)
        | ~ v4_relat_2(X3357)
        | ~ v6_relat_2(X3357)
        | ~ v1_wellord1(X3357)
        | v2_wellord1(X3357)
        | ~ v1_relat_1(X3357) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).

fof(c_0_10,negated_conjecture,
    ( v1_relat_1(esk276_0)
    & v2_wellord1(esk276_0)
    & ~ v2_wellord1(k2_wellord1(esk276_0,esk275_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_11,plain,(
    ! [X3370,X3371] :
      ( ~ v1_relat_1(X3370)
      | v1_relat_1(k2_wellord1(X3370,X3371)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_wellord1])])).

fof(c_0_12,plain,(
    ! [X3427,X3428] :
      ( ~ v1_relat_1(X3428)
      | ~ v1_relat_2(X3428)
      | v1_relat_2(k2_wellord1(X3428,X3427)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_wellord1])])).

cnf(c_0_13,plain,
    ( v1_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk276_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( v2_wellord1(esk276_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
    ! [X3449,X3450] :
      ( ~ v1_relat_1(X3450)
      | ~ v1_wellord1(X3450)
      | v1_wellord1(k2_wellord1(X3450,X3449)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_wellord1])])).

cnf(c_0_17,plain,
    ( v1_wellord1(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_18,plain,(
    ! [X3431,X3432] :
      ( ~ v1_relat_1(X3432)
      | ~ v8_relat_2(X3432)
      | v8_relat_2(k2_wellord1(X3432,X3431)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_wellord1])])).

cnf(c_0_19,plain,
    ( v8_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_20,plain,(
    ! [X3429,X3430] :
      ( ~ v1_relat_1(X3430)
      | ~ v6_relat_2(X3430)
      | v6_relat_2(k2_wellord1(X3430,X3429)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_wellord1])])).

cnf(c_0_21,plain,
    ( v6_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_22,plain,(
    ! [X3433,X3434] :
      ( ~ v1_relat_1(X3434)
      | ~ v4_relat_2(X3434)
      | v4_relat_2(k2_wellord1(X3434,X3433)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_wellord1])])).

cnf(c_0_23,plain,
    ( v4_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,plain,
    ( v1_relat_1(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_25,plain,
    ( v1_relat_2(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_2(esk276_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])])).

cnf(c_0_27,plain,
    ( v1_wellord1(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_wellord1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( v1_wellord1(esk276_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_14]),c_0_15])])).

cnf(c_0_29,plain,
    ( v8_relat_2(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v8_relat_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( v8_relat_2(esk276_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_14]),c_0_15])])).

cnf(c_0_31,plain,
    ( v6_relat_2(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v6_relat_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,negated_conjecture,
    ( v6_relat_2(esk276_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_14]),c_0_15])])).

cnf(c_0_33,plain,
    ( v4_relat_2(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v4_relat_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( v4_relat_2(esk276_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_14]),c_0_15])])).

cnf(c_0_35,plain,
    ( v2_wellord1(X1)
    | ~ v1_relat_2(X1)
    | ~ v8_relat_2(X1)
    | ~ v4_relat_2(X1)
    | ~ v6_relat_2(X1)
    | ~ v1_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_36,negated_conjecture,
    ( v1_relat_1(k2_wellord1(esk276_0,X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_14])).

cnf(c_0_37,negated_conjecture,
    ( v1_relat_2(k2_wellord1(esk276_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_14]),c_0_26])])).

cnf(c_0_38,negated_conjecture,
    ( v1_wellord1(k2_wellord1(esk276_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_14]),c_0_28])])).

cnf(c_0_39,negated_conjecture,
    ( v8_relat_2(k2_wellord1(esk276_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_14]),c_0_30])])).

cnf(c_0_40,negated_conjecture,
    ( v6_relat_2(k2_wellord1(esk276_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_14]),c_0_32])])).

cnf(c_0_41,negated_conjecture,
    ( v4_relat_2(k2_wellord1(esk276_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_14]),c_0_34])])).

cnf(c_0_42,negated_conjecture,
    ( ~ v2_wellord1(k2_wellord1(esk276_0,esk275_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_43,negated_conjecture,
    ( v2_wellord1(k2_wellord1(esk276_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41])])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43])]),
    [proof]).
%------------------------------------------------------------------------------
