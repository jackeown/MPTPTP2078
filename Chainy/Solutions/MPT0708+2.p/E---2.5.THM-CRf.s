%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0708+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:50 EST 2020

% Result     : Theorem 1.15s
% Output     : CNFRefutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :   21 (  34 expanded)
%              Number of clauses        :   12 (  13 expanded)
%              Number of leaves         :    4 (   8 expanded)
%              Depth                    :    7
%              Number of atoms          :   53 ( 114 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t163_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(X1,k1_relat_1(X3))
          & r1_tarski(k9_relat_1(X3,X1),X2) )
       => r1_tarski(X1,k10_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

fof(t178_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',t178_relat_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t1_xboole_1)).

fof(t146_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( ( r1_tarski(X1,k1_relat_1(X3))
            & r1_tarski(k9_relat_1(X3,X1),X2) )
         => r1_tarski(X1,k10_relat_1(X3,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t163_funct_1])).

fof(c_0_5,plain,(
    ! [X2469,X2470,X2471] :
      ( ~ v1_relat_1(X2471)
      | ~ r1_tarski(X2469,X2470)
      | r1_tarski(k10_relat_1(X2471,X2469),k10_relat_1(X2471,X2470)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t178_relat_1])])).

fof(c_0_6,negated_conjecture,
    ( v1_relat_1(esk194_0)
    & v1_funct_1(esk194_0)
    & r1_tarski(esk192_0,k1_relat_1(esk194_0))
    & r1_tarski(k9_relat_1(esk194_0,esk192_0),esk193_0)
    & ~ r1_tarski(esk192_0,k10_relat_1(esk194_0,esk193_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_7,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk194_0,esk192_0),esk193_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,plain,(
    ! [X206,X207,X208] :
      ( ~ r1_tarski(X206,X207)
      | ~ r1_tarski(X207,X208)
      | r1_tarski(X206,X208) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_10,negated_conjecture,
    ( r1_tarski(k10_relat_1(X1,k9_relat_1(esk194_0,esk192_0)),k10_relat_1(X1,esk193_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( v1_relat_1(esk194_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_12,plain,(
    ! [X2879,X2880] :
      ( ~ v1_relat_1(X2880)
      | ~ r1_tarski(X2879,k1_relat_1(X2880))
      | r1_tarski(X2879,k10_relat_1(X2880,k9_relat_1(X2880,X2879))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk194_0,k9_relat_1(esk194_0,esk192_0)),k10_relat_1(esk194_0,esk193_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,plain,
    ( r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(esk192_0,k1_relat_1(esk194_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(X1,k10_relat_1(esk194_0,esk193_0))
    | ~ r1_tarski(X1,k10_relat_1(esk194_0,k9_relat_1(esk194_0,esk192_0))) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(esk192_0,k10_relat_1(esk194_0,k9_relat_1(esk194_0,esk192_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_11])])).

cnf(c_0_19,negated_conjecture,
    ( ~ r1_tarski(esk192_0,k10_relat_1(esk194_0,esk193_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),
    [proof]).
%------------------------------------------------------------------------------
