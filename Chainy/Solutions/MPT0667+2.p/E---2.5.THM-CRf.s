%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0667+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:50 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   27 (  40 expanded)
%              Number of clauses        :   14 (  15 expanded)
%              Number of leaves         :    6 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :   72 ( 121 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t84_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v2_funct_1(X2)
       => v2_funct_1(k7_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_funct_1)).

fof(fc7_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v2_funct_1(X1)
        & v1_relat_1(X2)
        & v1_funct_1(X2)
        & v2_funct_1(X2) )
     => ( v1_relat_1(k5_relat_1(X1,X2))
        & v2_funct_1(k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_funct_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(fc4_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v2_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',dt_k6_relat_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',t94_relat_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( v2_funct_1(X2)
         => v2_funct_1(k7_relat_1(X2,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t84_funct_1])).

fof(c_0_7,plain,(
    ! [X2755,X2756] :
      ( ( v1_relat_1(k5_relat_1(X2755,X2756))
        | ~ v1_relat_1(X2755)
        | ~ v1_funct_1(X2755)
        | ~ v2_funct_1(X2755)
        | ~ v1_relat_1(X2756)
        | ~ v1_funct_1(X2756)
        | ~ v2_funct_1(X2756) )
      & ( v2_funct_1(k5_relat_1(X2755,X2756))
        | ~ v1_relat_1(X2755)
        | ~ v1_funct_1(X2755)
        | ~ v2_funct_1(X2755)
        | ~ v1_relat_1(X2756)
        | ~ v1_funct_1(X2756)
        | ~ v2_funct_1(X2756) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_funct_1])])])).

fof(c_0_8,negated_conjecture,
    ( v1_relat_1(esk197_0)
    & v1_funct_1(esk197_0)
    & v2_funct_1(esk197_0)
    & ~ v2_funct_1(k7_relat_1(esk197_0,esk196_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_9,plain,
    ( v2_funct_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( v1_funct_1(esk197_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( v2_funct_1(esk197_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( v1_relat_1(esk197_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,plain,(
    ! [X2751] :
      ( v1_relat_1(k6_relat_1(X2751))
      & v1_funct_1(k6_relat_1(X2751)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_14,plain,(
    ! [X2752] :
      ( v1_relat_1(k6_relat_1(X2752))
      & v2_funct_1(k6_relat_1(X2752)) ) ),
    inference(variable_rename,[status(thm)],[fc4_funct_1])).

fof(c_0_15,plain,(
    ! [X2226] : v1_relat_1(k6_relat_1(X2226)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_16,plain,(
    ! [X2706,X2707] :
      ( ~ v1_relat_1(X2707)
      | k7_relat_1(X2707,X2706) = k5_relat_1(k6_relat_1(X2706),X2707) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

cnf(c_0_17,negated_conjecture,
    ( v2_funct_1(k5_relat_1(X1,esk197_0))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12])])).

cnf(c_0_18,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( v2_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( v2_funct_1(k5_relat_1(k6_relat_1(X1),esk197_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_23,negated_conjecture,
    ( k5_relat_1(k6_relat_1(X1),esk197_0) = k7_relat_1(esk197_0,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_12])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_funct_1(k7_relat_1(esk197_0,esk196_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,negated_conjecture,
    ( v2_funct_1(k7_relat_1(esk197_0,X1)) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25])]),
    [proof]).
%------------------------------------------------------------------------------
