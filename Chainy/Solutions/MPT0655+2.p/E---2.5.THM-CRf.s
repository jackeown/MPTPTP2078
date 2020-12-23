%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0655+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:49 EST 2020

% Result     : Theorem 1.23s
% Output     : CNFRefutation 1.23s
% Verified   : 
% Statistics : Number of formulae       :   31 (  82 expanded)
%              Number of clauses        :   18 (  28 expanded)
%              Number of leaves         :    6 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   98 ( 274 expanded)
%              Number of equality atoms :   21 (  21 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t62_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => v2_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).

fof(t37_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
        & k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',t37_relat_1)).

fof(d9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(X1) = k4_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(t53_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( ? [X2] :
            ( v1_relat_1(X2)
            & v1_funct_1(X2)
            & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X1)) )
       => v2_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).

fof(t61_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
          & k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
         => v2_funct_1(k2_funct_1(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t62_funct_1])).

fof(c_0_7,plain,(
    ! [X2614] :
      ( ( k2_relat_1(X2614) = k1_relat_1(k4_relat_1(X2614))
        | ~ v1_relat_1(X2614) )
      & ( k1_relat_1(X2614) = k2_relat_1(k4_relat_1(X2614))
        | ~ v1_relat_1(X2614) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).

fof(c_0_8,negated_conjecture,
    ( v1_relat_1(esk195_0)
    & v1_funct_1(esk195_0)
    & v2_funct_1(esk195_0)
    & ~ v2_funct_1(k2_funct_1(esk195_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_9,plain,(
    ! [X2737] :
      ( ~ v1_relat_1(X2737)
      | ~ v1_funct_1(X2737)
      | ~ v2_funct_1(X2737)
      | k2_funct_1(X2737) = k4_relat_1(X2737) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).

cnf(c_0_10,plain,
    ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( v1_relat_1(esk195_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( k2_funct_1(X1) = k4_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( v1_funct_1(esk195_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( v2_funct_1(esk195_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_15,plain,(
    ! [X2738] :
      ( ( v1_relat_1(k2_funct_1(X2738))
        | ~ v1_relat_1(X2738)
        | ~ v1_funct_1(X2738) )
      & ( v1_funct_1(k2_funct_1(X2738))
        | ~ v1_relat_1(X2738)
        | ~ v1_funct_1(X2738) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_16,plain,(
    ! [X2866,X2867] :
      ( ~ v1_relat_1(X2866)
      | ~ v1_funct_1(X2866)
      | ~ v1_relat_1(X2867)
      | ~ v1_funct_1(X2867)
      | k5_relat_1(X2866,X2867) != k6_relat_1(k1_relat_1(X2866))
      | v2_funct_1(X2866) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t53_funct_1])])])).

cnf(c_0_17,negated_conjecture,
    ( k1_relat_1(k4_relat_1(esk195_0)) = k2_relat_1(esk195_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( k4_relat_1(esk195_0) = k2_funct_1(esk195_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_11])])).

cnf(c_0_19,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X2889] :
      ( ( k5_relat_1(X2889,k2_funct_1(X2889)) = k6_relat_1(k1_relat_1(X2889))
        | ~ v2_funct_1(X2889)
        | ~ v1_relat_1(X2889)
        | ~ v1_funct_1(X2889) )
      & ( k5_relat_1(k2_funct_1(X2889),X2889) = k6_relat_1(k2_relat_1(X2889))
        | ~ v2_funct_1(X2889)
        | ~ v1_relat_1(X2889)
        | ~ v1_funct_1(X2889) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).

cnf(c_0_22,plain,
    ( v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk195_0)) = k2_relat_1(esk195_0) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk195_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_13]),c_0_11])])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk195_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_13]),c_0_11])])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_funct_1(k2_funct_1(esk195_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_27,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk195_0),X1) != k6_relat_1(k2_relat_1(esk195_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk195_0),esk195_0) = k6_relat_1(k2_relat_1(esk195_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_13]),c_0_14]),c_0_11])])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_13]),c_0_11])]),
    [proof]).
%------------------------------------------------------------------------------
