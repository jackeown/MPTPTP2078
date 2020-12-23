%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_1__t161_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:18 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   23 (  60 expanded)
%              Number of clauses        :   16 (  23 expanded)
%              Number of leaves         :    3 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :   65 ( 253 expanded)
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
    file('/export/starexec/sandbox/benchmark/funct_1__t161_funct_1.p',t161_funct_1)).

fof(t158_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2))
          & r1_tarski(X1,k2_relat_1(X3)) )
       => r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t161_funct_1.p',t158_funct_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t161_funct_1.p',d10_xboole_0)).

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
    ! [X11,X12,X13] :
      ( ~ v1_relat_1(X13)
      | ~ v1_funct_1(X13)
      | ~ r1_tarski(k10_relat_1(X13,X11),k10_relat_1(X13,X12))
      | ~ r1_tarski(X11,k2_relat_1(X13))
      | r1_tarski(X11,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_funct_1])])).

fof(c_0_5,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & k10_relat_1(esk3_0,esk1_0) = k10_relat_1(esk3_0,esk2_0)
    & r1_tarski(esk1_0,k2_relat_1(esk3_0))
    & r1_tarski(esk2_0,k2_relat_1(esk3_0))
    & esk1_0 != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_6,plain,
    ( r1_tarski(X2,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ r1_tarski(X2,k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_9,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_10,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(k10_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X2))
    | ~ r1_tarski(X1,k2_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_7]),c_0_8])])).

cnf(c_0_11,negated_conjecture,
    ( r1_tarski(esk2_0,k2_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,negated_conjecture,
    ( k10_relat_1(esk3_0,esk1_0) = k10_relat_1(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | ~ r1_tarski(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(esk1_0,k2_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( esk1_0 != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(esk1_0,X1)
    | ~ r1_tarski(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_12]),c_0_15])]),c_0_21]),
    [proof]).
%------------------------------------------------------------------------------
