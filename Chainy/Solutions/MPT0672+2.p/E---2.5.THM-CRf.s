%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0672+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:50 EST 2020

% Result     : Theorem 1.06s
% Output     : CNFRefutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :   29 (  47 expanded)
%              Number of clauses        :   16 (  19 expanded)
%              Number of leaves         :    6 (  11 expanded)
%              Depth                    :    8
%              Number of atoms          :   68 ( 146 expanded)
%              Number of equality atoms :   17 (  47 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t97_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r1_tarski(X1,X2)
       => ( k8_relat_1(X2,k8_relat_1(X1,X3)) = k8_relat_1(X1,X3)
          & k8_relat_1(X1,k8_relat_1(X2,X3)) = k8_relat_1(X1,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_funct_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t1_xboole_1)).

fof(t116_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k2_relat_1(k8_relat_1(X1,X2)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',t116_relat_1)).

fof(dt_k8_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => v1_relat_1(k8_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',dt_k8_relat_1)).

fof(t125_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k8_relat_1(X1,X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',t125_relat_1)).

fof(t130_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => k8_relat_1(X1,k8_relat_1(X2,X3)) = k8_relat_1(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',t130_relat_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( r1_tarski(X1,X2)
         => ( k8_relat_1(X2,k8_relat_1(X1,X3)) = k8_relat_1(X1,X3)
            & k8_relat_1(X1,k8_relat_1(X2,X3)) = k8_relat_1(X1,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t97_funct_1])).

fof(c_0_7,plain,(
    ! [X206,X207,X208] :
      ( ~ r1_tarski(X206,X207)
      | ~ r1_tarski(X207,X208)
      | r1_tarski(X206,X208) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_8,negated_conjecture,
    ( v1_relat_1(esk200_0)
    & v1_funct_1(esk200_0)
    & r1_tarski(esk198_0,esk199_0)
    & ( k8_relat_1(esk199_0,k8_relat_1(esk198_0,esk200_0)) != k8_relat_1(esk198_0,esk200_0)
      | k8_relat_1(esk198_0,k8_relat_1(esk199_0,esk200_0)) != k8_relat_1(esk198_0,esk200_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_9,plain,(
    ! [X2323,X2324] :
      ( ~ v1_relat_1(X2324)
      | r1_tarski(k2_relat_1(k8_relat_1(X2323,X2324)),X2323) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t116_relat_1])])).

cnf(c_0_10,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( r1_tarski(esk198_0,esk199_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X2,X1)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( v1_relat_1(esk200_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_14,plain,(
    ! [X2229,X2230] :
      ( ~ v1_relat_1(X2230)
      | v1_relat_1(k8_relat_1(X2229,X2230)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).

fof(c_0_15,plain,(
    ! [X2343,X2344] :
      ( ~ v1_relat_1(X2344)
      | ~ r1_tarski(k2_relat_1(X2344),X2343)
      | k8_relat_1(X2343,X2344) = X2344 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(X1,esk199_0)
    | ~ r1_tarski(X1,esk198_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(k2_relat_1(k8_relat_1(X1,esk200_0)),X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( v1_relat_1(k8_relat_1(X2,X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X2354,X2355,X2356] :
      ( ~ v1_relat_1(X2356)
      | ~ r1_tarski(X2354,X2355)
      | k8_relat_1(X2354,k8_relat_1(X2355,X2356)) = k8_relat_1(X2354,X2356) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t130_relat_1])])).

cnf(c_0_20,plain,
    ( k8_relat_1(X2,X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(k2_relat_1(k8_relat_1(esk198_0,esk200_0)),esk199_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(k8_relat_1(X1,esk200_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_13])).

cnf(c_0_23,plain,
    ( k8_relat_1(X2,k8_relat_1(X3,X1)) = k8_relat_1(X2,X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( k8_relat_1(esk199_0,k8_relat_1(esk198_0,esk200_0)) != k8_relat_1(esk198_0,esk200_0)
    | k8_relat_1(esk198_0,k8_relat_1(esk199_0,esk200_0)) != k8_relat_1(esk198_0,esk200_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,negated_conjecture,
    ( k8_relat_1(esk199_0,k8_relat_1(esk198_0,esk200_0)) = k8_relat_1(esk198_0,esk200_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_26,negated_conjecture,
    ( k8_relat_1(esk198_0,k8_relat_1(esk199_0,X1)) = k8_relat_1(esk198_0,X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_11])).

cnf(c_0_27,negated_conjecture,
    ( k8_relat_1(esk198_0,k8_relat_1(esk199_0,esk200_0)) != k8_relat_1(esk198_0,esk200_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25])])).

cnf(c_0_28,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_13]),c_0_27]),
    [proof]).
%------------------------------------------------------------------------------
