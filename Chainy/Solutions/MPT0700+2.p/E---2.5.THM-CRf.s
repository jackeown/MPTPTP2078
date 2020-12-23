%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0700+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:50 EST 2020

% Result     : Theorem 0.98s
% Output     : CNFRefutation 0.98s
% Verified   : 
% Statistics : Number of formulae       :   26 (  65 expanded)
%              Number of clauses        :   15 (  22 expanded)
%              Number of leaves         :    5 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :   84 ( 221 expanded)
%              Number of equality atoms :   12 (  42 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t155_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v2_funct_1(X2)
       => k10_relat_1(X2,X1) = k9_relat_1(k2_funct_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(t65_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(k2_funct_1(X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(fc6_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v2_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1))
        & v2_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

fof(t154_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,X1) = k10_relat_1(k2_funct_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( v2_funct_1(X2)
         => k10_relat_1(X2,X1) = k9_relat_1(k2_funct_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t155_funct_1])).

fof(c_0_6,plain,(
    ! [X2758] :
      ( ( v1_relat_1(k2_funct_1(X2758))
        | ~ v1_relat_1(X2758)
        | ~ v1_funct_1(X2758) )
      & ( v1_funct_1(k2_funct_1(X2758))
        | ~ v1_relat_1(X2758)
        | ~ v1_funct_1(X2758) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk190_0)
    & v1_funct_1(esk190_0)
    & v2_funct_1(esk190_0)
    & k10_relat_1(esk190_0,esk189_0) != k9_relat_1(k2_funct_1(esk190_0),esk189_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_8,plain,(
    ! [X3007] :
      ( ~ v1_relat_1(X3007)
      | ~ v1_funct_1(X3007)
      | ~ v2_funct_1(X3007)
      | k2_funct_1(k2_funct_1(X3007)) = X3007 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_funct_1])])).

fof(c_0_9,plain,(
    ! [X2776] :
      ( ( v1_relat_1(k2_funct_1(X2776))
        | ~ v1_relat_1(X2776)
        | ~ v1_funct_1(X2776)
        | ~ v2_funct_1(X2776) )
      & ( v1_funct_1(k2_funct_1(X2776))
        | ~ v1_relat_1(X2776)
        | ~ v1_funct_1(X2776)
        | ~ v2_funct_1(X2776) )
      & ( v2_funct_1(k2_funct_1(X2776))
        | ~ v1_relat_1(X2776)
        | ~ v1_funct_1(X2776)
        | ~ v2_funct_1(X2776) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_funct_1])])])).

fof(c_0_10,plain,(
    ! [X2900,X2901] :
      ( ~ v1_relat_1(X2901)
      | ~ v1_funct_1(X2901)
      | ~ v2_funct_1(X2901)
      | k9_relat_1(X2901,X2900) = k10_relat_1(k2_funct_1(X2901),X2900) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t154_funct_1])])).

cnf(c_0_11,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( v1_funct_1(esk190_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( v1_relat_1(esk190_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( k2_funct_1(k2_funct_1(X1)) = X1
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( v2_funct_1(esk190_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,plain,
    ( v2_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,plain,
    ( k9_relat_1(X1,X2) = k10_relat_1(k2_funct_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk190_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])])).

cnf(c_0_20,negated_conjecture,
    ( k2_funct_1(k2_funct_1(esk190_0)) = esk190_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_12]),c_0_15]),c_0_13])])).

cnf(c_0_21,negated_conjecture,
    ( v2_funct_1(k2_funct_1(esk190_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_12]),c_0_15]),c_0_13])])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk190_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_12]),c_0_13])])).

cnf(c_0_23,negated_conjecture,
    ( k10_relat_1(esk190_0,esk189_0) != k9_relat_1(k2_funct_1(esk190_0),esk189_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_24,negated_conjecture,
    ( k9_relat_1(k2_funct_1(esk190_0),X1) = k10_relat_1(esk190_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21]),c_0_22])])).

cnf(c_0_25,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24])]),
    [proof]).
%------------------------------------------------------------------------------
