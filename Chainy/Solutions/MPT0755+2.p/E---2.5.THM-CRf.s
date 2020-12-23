%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0755+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:52 EST 2020

% Result     : Theorem 1.08s
% Output     : CNFRefutation 1.08s
% Verified   : 
% Statistics : Number of formulae       :   30 (  61 expanded)
%              Number of clauses        :   19 (  23 expanded)
%              Number of leaves         :    5 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :  108 ( 355 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_ordinal1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1)
        & v1_funct_1(X2)
        & v5_ordinal1(X2) )
     => ! [X3] :
          ( v3_ordinal1(X3)
         => ( v1_relat_1(k7_relat_1(X2,X3))
            & v5_relat_1(k7_relat_1(X2,X3),X1)
            & v1_funct_1(k7_relat_1(X2,X3))
            & v5_ordinal1(k7_relat_1(X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_ordinal1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',dt_k7_relat_1)).

fof(fc8_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k7_relat_1(X1,X2))
        & v1_funct_1(k7_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT008+2.ax',fc8_funct_1)).

fof(fc5_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v5_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( v1_relat_1(k7_relat_1(X1,X2))
        & v5_relat_1(k7_relat_1(X1,X2),k2_relat_1(X1))
        & v5_ordinal1(k7_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_ordinal1)).

fof(fc22_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v5_relat_1(X3,X2) )
     => ( v1_relat_1(k7_relat_1(X3,X1))
        & v5_relat_1(k7_relat_1(X3,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc22_relat_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v5_relat_1(X2,X1)
          & v1_funct_1(X2)
          & v5_ordinal1(X2) )
       => ! [X3] :
            ( v3_ordinal1(X3)
           => ( v1_relat_1(k7_relat_1(X2,X3))
              & v5_relat_1(k7_relat_1(X2,X3),X1)
              & v1_funct_1(k7_relat_1(X2,X3))
              & v5_ordinal1(k7_relat_1(X2,X3)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t48_ordinal1])).

fof(c_0_6,plain,(
    ! [X2227,X2228] :
      ( ~ v1_relat_1(X2227)
      | v1_relat_1(k7_relat_1(X2227,X2228)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk240_0)
    & v5_relat_1(esk240_0,esk239_0)
    & v1_funct_1(esk240_0)
    & v5_ordinal1(esk240_0)
    & v3_ordinal1(esk241_0)
    & ( ~ v1_relat_1(k7_relat_1(esk240_0,esk241_0))
      | ~ v5_relat_1(k7_relat_1(esk240_0,esk241_0),esk239_0)
      | ~ v1_funct_1(k7_relat_1(esk240_0,esk241_0))
      | ~ v5_ordinal1(k7_relat_1(esk240_0,esk241_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_8,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( v1_relat_1(esk240_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_10,plain,(
    ! [X2803,X2804] :
      ( ( v1_relat_1(k7_relat_1(X2803,X2804))
        | ~ v1_relat_1(X2803)
        | ~ v1_funct_1(X2803) )
      & ( v1_funct_1(k7_relat_1(X2803,X2804))
        | ~ v1_relat_1(X2803)
        | ~ v1_funct_1(X2803) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).

fof(c_0_11,plain,(
    ! [X3181,X3182] :
      ( ( v1_relat_1(k7_relat_1(X3181,X3182))
        | ~ v1_relat_1(X3181)
        | ~ v1_funct_1(X3181)
        | ~ v5_ordinal1(X3181)
        | ~ v3_ordinal1(X3182) )
      & ( v5_relat_1(k7_relat_1(X3181,X3182),k2_relat_1(X3181))
        | ~ v1_relat_1(X3181)
        | ~ v1_funct_1(X3181)
        | ~ v5_ordinal1(X3181)
        | ~ v3_ordinal1(X3182) )
      & ( v5_ordinal1(k7_relat_1(X3181,X3182))
        | ~ v1_relat_1(X3181)
        | ~ v1_funct_1(X3181)
        | ~ v5_ordinal1(X3181)
        | ~ v3_ordinal1(X3182) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc5_ordinal1])])])).

cnf(c_0_12,negated_conjecture,
    ( ~ v1_relat_1(k7_relat_1(esk240_0,esk241_0))
    | ~ v5_relat_1(k7_relat_1(esk240_0,esk241_0),esk239_0)
    | ~ v1_funct_1(k7_relat_1(esk240_0,esk241_0))
    | ~ v5_ordinal1(k7_relat_1(esk240_0,esk241_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk240_0,X1)) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_14,plain,
    ( v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( v1_funct_1(esk240_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,plain,
    ( v5_ordinal1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v5_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( v5_ordinal1(esk240_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,negated_conjecture,
    ( ~ v5_ordinal1(k7_relat_1(esk240_0,esk241_0))
    | ~ v1_funct_1(k7_relat_1(esk240_0,esk241_0))
    | ~ v5_relat_1(k7_relat_1(esk240_0,esk241_0),esk239_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_13])])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_1(k7_relat_1(esk240_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_9])])).

cnf(c_0_20,negated_conjecture,
    ( v5_ordinal1(k7_relat_1(esk240_0,X1))
    | ~ v3_ordinal1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_15]),c_0_17]),c_0_9])])).

cnf(c_0_21,negated_conjecture,
    ( v3_ordinal1(esk241_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_22,plain,(
    ! [X3176,X3177,X3178] :
      ( ( v1_relat_1(k7_relat_1(X3178,X3176))
        | ~ v1_relat_1(X3178)
        | ~ v5_relat_1(X3178,X3177) )
      & ( v5_relat_1(k7_relat_1(X3178,X3176),X3177)
        | ~ v1_relat_1(X3178)
        | ~ v5_relat_1(X3178,X3177) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc22_relat_1])])])).

cnf(c_0_23,negated_conjecture,
    ( ~ v5_ordinal1(k7_relat_1(esk240_0,esk241_0))
    | ~ v5_relat_1(k7_relat_1(esk240_0,esk241_0),esk239_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19])])).

cnf(c_0_24,negated_conjecture,
    ( v5_ordinal1(k7_relat_1(esk240_0,esk241_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,plain,
    ( v5_relat_1(k7_relat_1(X1,X2),X3)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( v5_relat_1(esk240_0,esk239_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_27,negated_conjecture,
    ( ~ v5_relat_1(k7_relat_1(esk240_0,esk241_0),esk239_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24])])).

cnf(c_0_28,negated_conjecture,
    ( v5_relat_1(k7_relat_1(esk240_0,X1),esk239_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_9])])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28])]),
    [proof]).
%------------------------------------------------------------------------------
