%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0646+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:49 EST 2020

% Result     : Theorem 1.39s
% Output     : CNFRefutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   25 (  60 expanded)
%              Number of clauses        :   14 (  19 expanded)
%              Number of leaves         :    5 (  15 expanded)
%              Depth                    :    6
%              Number of atoms          :   77 ( 262 expanded)
%              Number of equality atoms :   13 (  44 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t53_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( ? [X2] :
            ( v1_relat_1(X2)
            & v1_funct_1(X2)
            & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X1)) )
       => v2_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',t71_relat_1)).

fof(t27_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( k1_relat_1(k5_relat_1(X2,X1)) = k1_relat_1(X2)
           => r1_tarski(k2_relat_1(X2),k1_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).

fof(fc4_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v2_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(t47_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(k5_relat_1(X2,X1))
              & r1_tarski(k2_relat_1(X2),k1_relat_1(X1)) )
           => v2_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( ? [X2] :
              ( v1_relat_1(X2)
              & v1_funct_1(X2)
              & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X1)) )
         => v2_funct_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t53_funct_1])).

fof(c_0_6,plain,(
    ! [X2662] :
      ( k1_relat_1(k6_relat_1(X2662)) = X2662
      & k2_relat_1(k6_relat_1(X2662)) = X2662 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk188_0)
    & v1_funct_1(esk188_0)
    & v1_relat_1(esk189_0)
    & v1_funct_1(esk189_0)
    & k5_relat_1(esk188_0,esk189_0) = k6_relat_1(k1_relat_1(esk188_0))
    & ~ v2_funct_1(esk188_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_8,plain,(
    ! [X2820,X2821] :
      ( ~ v1_relat_1(X2820)
      | ~ v1_funct_1(X2820)
      | ~ v1_relat_1(X2821)
      | ~ v1_funct_1(X2821)
      | k1_relat_1(k5_relat_1(X2821,X2820)) != k1_relat_1(X2821)
      | r1_tarski(k2_relat_1(X2821),k1_relat_1(X2820)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_funct_1])])])).

cnf(c_0_9,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( k5_relat_1(esk188_0,esk189_0) = k6_relat_1(k1_relat_1(esk188_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X2749] :
      ( v1_relat_1(k6_relat_1(X2749))
      & v2_funct_1(k6_relat_1(X2749)) ) ),
    inference(variable_rename,[status(thm)],[fc4_funct_1])).

fof(c_0_12,plain,(
    ! [X2846,X2847] :
      ( ~ v1_relat_1(X2846)
      | ~ v1_funct_1(X2846)
      | ~ v1_relat_1(X2847)
      | ~ v1_funct_1(X2847)
      | ~ v2_funct_1(k5_relat_1(X2847,X2846))
      | ~ r1_tarski(k2_relat_1(X2847),k1_relat_1(X2846))
      | v2_funct_1(X2847) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_funct_1])])])).

cnf(c_0_13,plain,
    ( r1_tarski(k2_relat_1(X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k1_relat_1(k5_relat_1(X2,X1)) != k1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk188_0,esk189_0)) = k1_relat_1(esk188_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( v1_funct_1(esk188_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,negated_conjecture,
    ( v1_funct_1(esk189_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,negated_conjecture,
    ( v1_relat_1(esk188_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,negated_conjecture,
    ( v1_relat_1(esk189_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,plain,
    ( v2_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( v2_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(k5_relat_1(X2,X1))
    | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk188_0),k1_relat_1(esk189_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_22,negated_conjecture,
    ( v2_funct_1(k5_relat_1(esk188_0,esk189_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_10])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_funct_1(esk188_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_24,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_23]),
    [proof]).
%------------------------------------------------------------------------------
