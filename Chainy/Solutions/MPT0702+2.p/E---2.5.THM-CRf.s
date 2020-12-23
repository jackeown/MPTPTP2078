%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0702+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:50 EST 2020

% Result     : Theorem 10.02s
% Output     : CNFRefutation 10.02s
% Verified   : 
% Statistics : Number of formulae       :   38 (  96 expanded)
%              Number of clauses        :   23 (  35 expanded)
%              Number of leaves         :    7 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :  102 ( 385 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t157_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2))
          & r1_tarski(X1,k1_relat_1(X3))
          & v2_funct_1(X3) )
       => r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

fof(t156_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',t156_relat_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(t155_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v2_funct_1(X2)
       => k10_relat_1(X2,X1) = k9_relat_1(k2_funct_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

fof(t152_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v2_funct_1(X2)
       => r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

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

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( ( r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2))
            & r1_tarski(X1,k1_relat_1(X3))
            & v2_funct_1(X3) )
         => r1_tarski(X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t157_funct_1])).

fof(c_0_8,plain,(
    ! [X2417,X2418,X2419] :
      ( ~ v1_relat_1(X2419)
      | ~ r1_tarski(X2417,X2418)
      | r1_tarski(k9_relat_1(X2419,X2417),k9_relat_1(X2419,X2418)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t156_relat_1])])).

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk191_0)
    & v1_funct_1(esk191_0)
    & r1_tarski(k9_relat_1(esk191_0,esk189_0),k9_relat_1(esk191_0,esk190_0))
    & r1_tarski(esk189_0,k1_relat_1(esk191_0))
    & v2_funct_1(esk191_0)
    & ~ r1_tarski(esk189_0,esk190_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X2758] :
      ( ( v1_relat_1(k2_funct_1(X2758))
        | ~ v1_relat_1(X2758)
        | ~ v1_funct_1(X2758) )
      & ( v1_funct_1(k2_funct_1(X2758))
        | ~ v1_relat_1(X2758)
        | ~ v1_funct_1(X2758) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

cnf(c_0_11,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk191_0,esk189_0),k9_relat_1(esk191_0,esk190_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( v1_funct_1(esk191_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk191_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_16,plain,(
    ! [X2902,X2903] :
      ( ~ v1_relat_1(X2903)
      | ~ v1_funct_1(X2903)
      | ~ v2_funct_1(X2903)
      | k10_relat_1(X2903,X2902) = k9_relat_1(k2_funct_1(X2903),X2902) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t155_funct_1])])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(k9_relat_1(X1,k9_relat_1(esk191_0,esk189_0)),k9_relat_1(X1,k9_relat_1(esk191_0,esk190_0)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk191_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])])).

cnf(c_0_19,plain,
    ( k10_relat_1(X1,X2) = k9_relat_1(k2_funct_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( v2_funct_1(esk191_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_21,plain,(
    ! [X2896,X2897] :
      ( ~ v1_relat_1(X2897)
      | ~ v1_funct_1(X2897)
      | ~ v2_funct_1(X2897)
      | r1_tarski(k10_relat_1(X2897,k9_relat_1(X2897,X2896)),X2896) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t152_funct_1])])).

fof(c_0_22,plain,(
    ! [X206,X207,X208] :
      ( ~ r1_tarski(X206,X207)
      | ~ r1_tarski(X207,X208)
      | r1_tarski(X206,X208) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(k9_relat_1(k2_funct_1(esk191_0),k9_relat_1(esk191_0,esk189_0)),k9_relat_1(k2_funct_1(esk191_0),k9_relat_1(esk191_0,esk190_0))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( k9_relat_1(k2_funct_1(esk191_0),X1) = k10_relat_1(esk191_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_14]),c_0_20]),c_0_15])])).

fof(c_0_25,plain,(
    ! [X2879,X2880] :
      ( ~ v1_relat_1(X2880)
      | ~ r1_tarski(X2879,k1_relat_1(X2880))
      | r1_tarski(X2879,k10_relat_1(X2880,k9_relat_1(X2880,X2879))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).

cnf(c_0_26,plain,
    ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk191_0,k9_relat_1(esk191_0,esk189_0)),k10_relat_1(esk191_0,k9_relat_1(esk191_0,esk190_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_24])).

cnf(c_0_29,plain,
    ( r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(esk189_0,k1_relat_1(esk191_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk191_0,k9_relat_1(esk191_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_14]),c_0_20]),c_0_15])])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(X1,k10_relat_1(esk191_0,k9_relat_1(esk191_0,esk190_0)))
    | ~ r1_tarski(X1,k10_relat_1(esk191_0,k9_relat_1(esk191_0,esk189_0))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk189_0,k10_relat_1(esk191_0,k9_relat_1(esk191_0,esk189_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_15])])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k10_relat_1(esk191_0,k9_relat_1(esk191_0,X2))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(esk189_0,k10_relat_1(esk191_0,k9_relat_1(esk191_0,esk190_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( ~ r1_tarski(esk189_0,esk190_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),
    [proof]).
%------------------------------------------------------------------------------
