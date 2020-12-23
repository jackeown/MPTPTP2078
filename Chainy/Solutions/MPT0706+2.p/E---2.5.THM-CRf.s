%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0706+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:50 EST 2020

% Result     : Theorem 1.10s
% Output     : CNFRefutation 1.10s
% Verified   : 
% Statistics : Number of formulae       :   22 (  58 expanded)
%              Number of clauses        :   15 (  21 expanded)
%              Number of leaves         :    3 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :   62 ( 247 expanded)
%              Number of equality atoms :   14 (  72 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t161_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( k10_relat_1(X3,X1) = k10_relat_1(X3,X2)
          & r1_tarski(X1,k2_relat_1(X3))
          & r1_tarski(X2,k2_relat_1(X3)) )
       => X1 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t161_funct_1)).

fof(t158_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2))
          & r1_tarski(X1,k2_relat_1(X3)) )
       => r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',d10_xboole_0)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( ( k10_relat_1(X3,X1) = k10_relat_1(X3,X2)
            & r1_tarski(X1,k2_relat_1(X3))
            & r1_tarski(X2,k2_relat_1(X3)) )
         => X1 = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t161_funct_1])).

fof(c_0_4,plain,(
    ! [X2911,X2912,X2913] :
      ( ~ v1_relat_1(X2913)
      | ~ v1_funct_1(X2913)
      | ~ r1_tarski(k10_relat_1(X2913,X2911),k10_relat_1(X2913,X2912))
      | ~ r1_tarski(X2911,k2_relat_1(X2913))
      | r1_tarski(X2911,X2912) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_funct_1])])).

fof(c_0_5,negated_conjecture,
    ( v1_relat_1(esk194_0)
    & v1_funct_1(esk194_0)
    & k10_relat_1(esk194_0,esk192_0) = k10_relat_1(esk194_0,esk193_0)
    & r1_tarski(esk192_0,k2_relat_1(esk194_0))
    & r1_tarski(esk193_0,k2_relat_1(esk194_0))
    & esk192_0 != esk193_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_6,plain,(
    ! [X104,X105] :
      ( ( r1_tarski(X104,X105)
        | X104 != X105 )
      & ( r1_tarski(X105,X104)
        | X104 != X105 )
      & ( ~ r1_tarski(X104,X105)
        | ~ r1_tarski(X105,X104)
        | X104 = X105 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_7,plain,
    ( r1_tarski(X2,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ r1_tarski(X2,k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( r1_tarski(esk193_0,k2_relat_1(esk194_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( v1_funct_1(esk194_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( v1_relat_1(esk194_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,negated_conjecture,
    ( k10_relat_1(esk194_0,esk192_0) = k10_relat_1(esk194_0,esk193_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( r1_tarski(esk193_0,X1)
    | ~ r1_tarski(k10_relat_1(esk194_0,esk192_0),k10_relat_1(esk194_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9]),c_0_10]),c_0_11])])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(esk192_0,k2_relat_1(esk194_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(esk193_0,esk192_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( esk192_0 != esk193_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(esk192_0,X1)
    | ~ r1_tarski(k10_relat_1(esk194_0,esk192_0),k10_relat_1(esk194_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_15]),c_0_9]),c_0_10])])).

cnf(c_0_20,negated_conjecture,
    ( ~ r1_tarski(esk192_0,esk193_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_11]),c_0_14])]),c_0_20]),
    [proof]).
%------------------------------------------------------------------------------
