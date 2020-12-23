%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0709+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:50 EST 2020

% Result     : Theorem 1.04s
% Output     : CNFRefutation 1.04s
% Verified   : 
% Statistics : Number of formulae       :   21 (  37 expanded)
%              Number of clauses        :   12 (  13 expanded)
%              Number of leaves         :    4 (   9 expanded)
%              Depth                    :    6
%              Number of atoms          :   58 ( 134 expanded)
%              Number of equality atoms :    9 (  24 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t164_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ( r1_tarski(X1,k1_relat_1(X2))
          & v2_funct_1(X2) )
       => k10_relat_1(X2,k9_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

fof(t146_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',d10_xboole_0)).

fof(t152_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v2_funct_1(X2)
       => r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( ( r1_tarski(X1,k1_relat_1(X2))
            & v2_funct_1(X2) )
         => k10_relat_1(X2,k9_relat_1(X2,X1)) = X1 ) ) ),
    inference(assume_negation,[status(cth)],[t164_funct_1])).

fof(c_0_5,plain,(
    ! [X2880,X2881] :
      ( ~ v1_relat_1(X2881)
      | ~ r1_tarski(X2880,k1_relat_1(X2881))
      | r1_tarski(X2880,k10_relat_1(X2881,k9_relat_1(X2881,X2880))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).

fof(c_0_6,negated_conjecture,
    ( v1_relat_1(esk194_0)
    & v1_funct_1(esk194_0)
    & r1_tarski(esk193_0,k1_relat_1(esk194_0))
    & v2_funct_1(esk194_0)
    & k10_relat_1(esk194_0,k9_relat_1(esk194_0,esk193_0)) != esk193_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X104,X105] :
      ( ( r1_tarski(X104,X105)
        | X104 != X105 )
      & ( r1_tarski(X105,X104)
        | X104 != X105 )
      & ( ~ r1_tarski(X104,X105)
        | ~ r1_tarski(X105,X104)
        | X104 = X105 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_8,plain,
    ( r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( r1_tarski(esk193_0,k1_relat_1(esk194_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( v1_relat_1(esk194_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_11,plain,(
    ! [X2897,X2898] :
      ( ~ v1_relat_1(X2898)
      | ~ v1_funct_1(X2898)
      | ~ v2_funct_1(X2898)
      | r1_tarski(k10_relat_1(X2898,k9_relat_1(X2898,X2897)),X2897) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t152_funct_1])])).

cnf(c_0_12,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( r1_tarski(esk193_0,k10_relat_1(esk194_0,k9_relat_1(esk194_0,esk193_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10])])).

cnf(c_0_14,negated_conjecture,
    ( k10_relat_1(esk194_0,k9_relat_1(esk194_0,esk193_0)) != esk193_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,plain,
    ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( v1_funct_1(esk194_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,negated_conjecture,
    ( v2_funct_1(esk194_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(esk194_0,k9_relat_1(esk194_0,esk193_0)),esk193_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk194_0,k9_relat_1(esk194_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_10])])).

cnf(c_0_20,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19])]),
    [proof]).
%------------------------------------------------------------------------------
