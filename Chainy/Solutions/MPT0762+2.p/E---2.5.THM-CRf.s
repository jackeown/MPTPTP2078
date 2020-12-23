%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0762+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:52 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 341 expanded)
%              Number of clauses        :   48 ( 123 expanded)
%              Number of leaves         :    8 (  85 expanded)
%              Depth                    :    8
%              Number of atoms          :  226 (1537 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t8_wellord1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( r2_wellord1(X1,k3_relat_1(X1))
      <=> v2_wellord1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord1)).

fof(d5_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r2_wellord1(X1,X2)
        <=> ( r1_relat_2(X1,X2)
            & r8_relat_2(X1,X2)
            & r4_relat_2(X1,X2)
            & r6_relat_2(X1,X2)
            & r1_wellord1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_wellord1)).

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

fof(d9_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v1_relat_2(X1)
      <=> r1_relat_2(X1,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_relat_2)).

fof(t5_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v1_wellord1(X1)
      <=> r1_wellord1(X1,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_wellord1)).

fof(d16_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v8_relat_2(X1)
      <=> r8_relat_2(X1,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_2)).

fof(d14_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v6_relat_2(X1)
      <=> r6_relat_2(X1,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_2)).

fof(d12_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_2(X1)
      <=> r4_relat_2(X1,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_relat_2)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ( r2_wellord1(X1,k3_relat_1(X1))
        <=> v2_wellord1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t8_wellord1])).

fof(c_0_9,plain,(
    ! [X3353,X3354] :
      ( ( r1_relat_2(X3353,X3354)
        | ~ r2_wellord1(X3353,X3354)
        | ~ v1_relat_1(X3353) )
      & ( r8_relat_2(X3353,X3354)
        | ~ r2_wellord1(X3353,X3354)
        | ~ v1_relat_1(X3353) )
      & ( r4_relat_2(X3353,X3354)
        | ~ r2_wellord1(X3353,X3354)
        | ~ v1_relat_1(X3353) )
      & ( r6_relat_2(X3353,X3354)
        | ~ r2_wellord1(X3353,X3354)
        | ~ v1_relat_1(X3353) )
      & ( r1_wellord1(X3353,X3354)
        | ~ r2_wellord1(X3353,X3354)
        | ~ v1_relat_1(X3353) )
      & ( ~ r1_relat_2(X3353,X3354)
        | ~ r8_relat_2(X3353,X3354)
        | ~ r4_relat_2(X3353,X3354)
        | ~ r6_relat_2(X3353,X3354)
        | ~ r1_wellord1(X3353,X3354)
        | r2_wellord1(X3353,X3354)
        | ~ v1_relat_1(X3353) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_wellord1])])])])).

fof(c_0_10,negated_conjecture,
    ( v1_relat_1(esk260_0)
    & ( ~ r2_wellord1(esk260_0,k3_relat_1(esk260_0))
      | ~ v2_wellord1(esk260_0) )
    & ( r2_wellord1(esk260_0,k3_relat_1(esk260_0))
      | v2_wellord1(esk260_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_11,plain,(
    ! [X3352] :
      ( ( v1_relat_2(X3352)
        | ~ v2_wellord1(X3352)
        | ~ v1_relat_1(X3352) )
      & ( v8_relat_2(X3352)
        | ~ v2_wellord1(X3352)
        | ~ v1_relat_1(X3352) )
      & ( v4_relat_2(X3352)
        | ~ v2_wellord1(X3352)
        | ~ v1_relat_1(X3352) )
      & ( v6_relat_2(X3352)
        | ~ v2_wellord1(X3352)
        | ~ v1_relat_1(X3352) )
      & ( v1_wellord1(X3352)
        | ~ v2_wellord1(X3352)
        | ~ v1_relat_1(X3352) )
      & ( ~ v1_relat_2(X3352)
        | ~ v8_relat_2(X3352)
        | ~ v4_relat_2(X3352)
        | ~ v6_relat_2(X3352)
        | ~ v1_wellord1(X3352)
        | v2_wellord1(X3352)
        | ~ v1_relat_1(X3352) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).

fof(c_0_12,plain,(
    ! [X3355] :
      ( ( ~ v1_relat_2(X3355)
        | r1_relat_2(X3355,k3_relat_1(X3355))
        | ~ v1_relat_1(X3355) )
      & ( ~ r1_relat_2(X3355,k3_relat_1(X3355))
        | v1_relat_2(X3355)
        | ~ v1_relat_1(X3355) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_relat_2])])])).

cnf(c_0_13,plain,
    ( r1_relat_2(X1,X2)
    | ~ r2_wellord1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( r2_wellord1(esk260_0,k3_relat_1(esk260_0))
    | v2_wellord1(esk260_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk260_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( v1_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,plain,(
    ! [X3360] :
      ( ( ~ v1_wellord1(X3360)
        | r1_wellord1(X3360,k3_relat_1(X3360))
        | ~ v1_relat_1(X3360) )
      & ( ~ r1_wellord1(X3360,k3_relat_1(X3360))
        | v1_wellord1(X3360)
        | ~ v1_relat_1(X3360) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_wellord1])])])).

cnf(c_0_18,plain,
    ( r1_wellord1(X1,X2)
    | ~ r2_wellord1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,plain,
    ( v1_wellord1(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_20,plain,(
    ! [X3331] :
      ( ( ~ v8_relat_2(X3331)
        | r8_relat_2(X3331,k3_relat_1(X3331))
        | ~ v1_relat_1(X3331) )
      & ( ~ r8_relat_2(X3331,k3_relat_1(X3331))
        | v8_relat_2(X3331)
        | ~ v1_relat_1(X3331) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_2])])])).

cnf(c_0_21,plain,
    ( r8_relat_2(X1,X2)
    | ~ r2_wellord1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,plain,
    ( v8_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_23,plain,(
    ! [X3330] :
      ( ( ~ v6_relat_2(X3330)
        | r6_relat_2(X3330,k3_relat_1(X3330))
        | ~ v1_relat_1(X3330) )
      & ( ~ r6_relat_2(X3330,k3_relat_1(X3330))
        | v6_relat_2(X3330)
        | ~ v1_relat_1(X3330) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_2])])])).

cnf(c_0_24,plain,
    ( r6_relat_2(X1,X2)
    | ~ r2_wellord1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,plain,
    ( v6_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_26,plain,(
    ! [X3329] :
      ( ( ~ v4_relat_2(X3329)
        | r4_relat_2(X3329,k3_relat_1(X3329))
        | ~ v1_relat_1(X3329) )
      & ( ~ r4_relat_2(X3329,k3_relat_1(X3329))
        | v4_relat_2(X3329)
        | ~ v1_relat_1(X3329) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_relat_2])])])).

cnf(c_0_27,plain,
    ( r4_relat_2(X1,X2)
    | ~ r2_wellord1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_28,plain,
    ( v4_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_29,plain,
    ( v1_relat_2(X1)
    | ~ r1_relat_2(X1,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_30,negated_conjecture,
    ( r1_relat_2(esk260_0,k3_relat_1(esk260_0))
    | v2_wellord1(esk260_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])])).

cnf(c_0_31,negated_conjecture,
    ( v1_relat_2(esk260_0)
    | ~ v2_wellord1(esk260_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_15])).

cnf(c_0_32,plain,
    ( v1_wellord1(X1)
    | ~ r1_wellord1(X1,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_33,negated_conjecture,
    ( v2_wellord1(esk260_0)
    | r1_wellord1(esk260_0,k3_relat_1(esk260_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_14]),c_0_15])])).

cnf(c_0_34,negated_conjecture,
    ( v1_wellord1(esk260_0)
    | ~ v2_wellord1(esk260_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_15])).

cnf(c_0_35,plain,
    ( v8_relat_2(X1)
    | ~ r8_relat_2(X1,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_36,negated_conjecture,
    ( v2_wellord1(esk260_0)
    | r8_relat_2(esk260_0,k3_relat_1(esk260_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_14]),c_0_15])])).

cnf(c_0_37,negated_conjecture,
    ( v8_relat_2(esk260_0)
    | ~ v2_wellord1(esk260_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_15])).

cnf(c_0_38,plain,
    ( v6_relat_2(X1)
    | ~ r6_relat_2(X1,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_39,negated_conjecture,
    ( v2_wellord1(esk260_0)
    | r6_relat_2(esk260_0,k3_relat_1(esk260_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_14]),c_0_15])])).

cnf(c_0_40,negated_conjecture,
    ( v6_relat_2(esk260_0)
    | ~ v2_wellord1(esk260_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_15])).

cnf(c_0_41,plain,
    ( v4_relat_2(X1)
    | ~ r4_relat_2(X1,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_42,negated_conjecture,
    ( v2_wellord1(esk260_0)
    | r4_relat_2(esk260_0,k3_relat_1(esk260_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_14]),c_0_15])])).

cnf(c_0_43,negated_conjecture,
    ( v4_relat_2(esk260_0)
    | ~ v2_wellord1(esk260_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_15])).

cnf(c_0_44,plain,
    ( v2_wellord1(X1)
    | ~ v1_relat_2(X1)
    | ~ v8_relat_2(X1)
    | ~ v4_relat_2(X1)
    | ~ v6_relat_2(X1)
    | ~ v1_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_45,negated_conjecture,
    ( v1_relat_2(esk260_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_15])]),c_0_31])).

cnf(c_0_46,negated_conjecture,
    ( v1_wellord1(esk260_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_15])]),c_0_34])).

cnf(c_0_47,negated_conjecture,
    ( v8_relat_2(esk260_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_15])]),c_0_37])).

cnf(c_0_48,negated_conjecture,
    ( v6_relat_2(esk260_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_15])]),c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( v4_relat_2(esk260_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_15])]),c_0_43])).

cnf(c_0_50,plain,
    ( r1_relat_2(X1,k3_relat_1(X1))
    | ~ v1_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_51,plain,
    ( r1_wellord1(X1,k3_relat_1(X1))
    | ~ v1_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_52,plain,
    ( r8_relat_2(X1,k3_relat_1(X1))
    | ~ v8_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_53,plain,
    ( r6_relat_2(X1,k3_relat_1(X1))
    | ~ v6_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_54,plain,
    ( r4_relat_2(X1,k3_relat_1(X1))
    | ~ v4_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_55,negated_conjecture,
    ( ~ r2_wellord1(esk260_0,k3_relat_1(esk260_0))
    | ~ v2_wellord1(esk260_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_56,negated_conjecture,
    ( v2_wellord1(esk260_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_15]),c_0_45]),c_0_46]),c_0_47]),c_0_48]),c_0_49])])).

cnf(c_0_57,plain,
    ( r2_wellord1(X1,X2)
    | ~ r1_relat_2(X1,X2)
    | ~ r8_relat_2(X1,X2)
    | ~ r4_relat_2(X1,X2)
    | ~ r6_relat_2(X1,X2)
    | ~ r1_wellord1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_58,negated_conjecture,
    ( r1_relat_2(esk260_0,k3_relat_1(esk260_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_15]),c_0_45])])).

cnf(c_0_59,negated_conjecture,
    ( r1_wellord1(esk260_0,k3_relat_1(esk260_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_15]),c_0_46])])).

cnf(c_0_60,negated_conjecture,
    ( r8_relat_2(esk260_0,k3_relat_1(esk260_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_15]),c_0_47])])).

cnf(c_0_61,negated_conjecture,
    ( r6_relat_2(esk260_0,k3_relat_1(esk260_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_15]),c_0_48])])).

cnf(c_0_62,negated_conjecture,
    ( r4_relat_2(esk260_0,k3_relat_1(esk260_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_15]),c_0_49])])).

cnf(c_0_63,negated_conjecture,
    ( ~ r2_wellord1(esk260_0,k3_relat_1(esk260_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56])])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59]),c_0_60]),c_0_61]),c_0_62]),c_0_15])]),c_0_63]),
    [proof]).
%------------------------------------------------------------------------------
