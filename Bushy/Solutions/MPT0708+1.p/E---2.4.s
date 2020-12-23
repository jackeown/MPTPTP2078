%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_1__t163_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:18 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   19 (  28 expanded)
%              Number of clauses        :   10 (  10 expanded)
%              Number of leaves         :    4 (   7 expanded)
%              Depth                    :    5
%              Number of atoms          :   55 ( 100 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t163_funct_1.p',t1_xboole_1)).

fof(t178_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t163_funct_1.p',t178_relat_1)).

fof(t146_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t163_funct_1.p',t146_funct_1)).

fof(t163_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(X1,k1_relat_1(X3))
          & r1_tarski(k9_relat_1(X3,X1),X2) )
       => r1_tarski(X1,k10_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t163_funct_1.p',t163_funct_1)).

fof(c_0_4,plain,(
    ! [X14,X15,X16] :
      ( ~ r1_tarski(X14,X15)
      | ~ r1_tarski(X15,X16)
      | r1_tarski(X14,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_5,plain,(
    ! [X11,X12,X13] :
      ( ~ v1_relat_1(X13)
      | ~ r1_tarski(X11,X12)
      | r1_tarski(k10_relat_1(X13,X11),k10_relat_1(X13,X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t178_relat_1])])).

cnf(c_0_6,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,plain,(
    ! [X9,X10] :
      ( ~ v1_relat_1(X10)
      | ~ r1_tarski(X9,k1_relat_1(X10))
      | r1_tarski(X9,k10_relat_1(X10,k9_relat_1(X10,X9))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( ( r1_tarski(X1,k1_relat_1(X3))
            & r1_tarski(k9_relat_1(X3,X1),X2) )
         => r1_tarski(X1,k10_relat_1(X3,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t163_funct_1])).

cnf(c_0_10,plain,
    ( r1_tarski(X1,k10_relat_1(X2,X3))
    | ~ r1_tarski(X1,k10_relat_1(X2,X4))
    | ~ r1_tarski(X4,X3)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_11,plain,
    ( r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & r1_tarski(esk1_0,k1_relat_1(esk3_0))
    & r1_tarski(k9_relat_1(esk3_0,esk1_0),esk2_0)
    & ~ r1_tarski(esk1_0,k10_relat_1(esk3_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,k10_relat_1(X2,X3))
    | ~ r1_tarski(k9_relat_1(X2,X1),X3)
    | ~ r1_tarski(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(esk1_0,k1_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k10_relat_1(esk3_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16])]),c_0_17]),
    [proof]).
%------------------------------------------------------------------------------
