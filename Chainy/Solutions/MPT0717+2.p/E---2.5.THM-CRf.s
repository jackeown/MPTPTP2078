%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0717+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:50 EST 2020

% Result     : Theorem 1.15s
% Output     : CNFRefutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :   21 (  41 expanded)
%              Number of clauses        :   12 (  14 expanded)
%              Number of leaves         :    4 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :   68 ( 160 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t172_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k1_relat_1(X2))
         => r2_hidden(k1_funct_1(X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',d19_relat_1)).

fof(t125_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k8_relat_1(X1,X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',t125_relat_1)).

fof(t86_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,k1_relat_1(k8_relat_1(X2,X3)))
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(k1_funct_1(X3,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_funct_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v5_relat_1(X2,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( r2_hidden(X3,k1_relat_1(X2))
           => r2_hidden(k1_funct_1(X2,X3),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t172_funct_1])).

fof(c_0_5,plain,(
    ! [X2154,X2155] :
      ( ( ~ v5_relat_1(X2155,X2154)
        | r1_tarski(k2_relat_1(X2155),X2154)
        | ~ v1_relat_1(X2155) )
      & ( ~ r1_tarski(k2_relat_1(X2155),X2154)
        | v5_relat_1(X2155,X2154)
        | ~ v1_relat_1(X2155) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

fof(c_0_6,negated_conjecture,
    ( v1_relat_1(esk200_0)
    & v5_relat_1(esk200_0,esk199_0)
    & v1_funct_1(esk200_0)
    & r2_hidden(esk201_0,k1_relat_1(esk200_0))
    & ~ r2_hidden(k1_funct_1(esk200_0,esk201_0),esk199_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X2343,X2344] :
      ( ~ v1_relat_1(X2344)
      | ~ r1_tarski(k2_relat_1(X2344),X2343)
      | k8_relat_1(X2343,X2344) = X2344 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).

cnf(c_0_8,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( v5_relat_1(esk200_0,esk199_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( v1_relat_1(esk200_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_11,plain,(
    ! [X3109,X3110,X3111] :
      ( ( r2_hidden(X3109,k1_relat_1(X3111))
        | ~ r2_hidden(X3109,k1_relat_1(k8_relat_1(X3110,X3111)))
        | ~ v1_relat_1(X3111)
        | ~ v1_funct_1(X3111) )
      & ( r2_hidden(k1_funct_1(X3111,X3109),X3110)
        | ~ r2_hidden(X3109,k1_relat_1(k8_relat_1(X3110,X3111)))
        | ~ v1_relat_1(X3111)
        | ~ v1_funct_1(X3111) )
      & ( ~ r2_hidden(X3109,k1_relat_1(X3111))
        | ~ r2_hidden(k1_funct_1(X3111,X3109),X3110)
        | r2_hidden(X3109,k1_relat_1(k8_relat_1(X3110,X3111)))
        | ~ v1_relat_1(X3111)
        | ~ v1_funct_1(X3111) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_funct_1])])])).

cnf(c_0_12,plain,
    ( k8_relat_1(X2,X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk200_0),esk199_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10])])).

cnf(c_0_14,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | ~ r2_hidden(X2,k1_relat_1(k8_relat_1(X3,X1)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( k8_relat_1(esk199_0,esk200_0) = esk200_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_10])])).

cnf(c_0_16,negated_conjecture,
    ( v1_funct_1(esk200_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk200_0,X1),esk199_0)
    | ~ r2_hidden(X1,k1_relat_1(esk200_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_10])])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk201_0,k1_relat_1(esk200_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk200_0,esk201_0),esk199_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),
    [proof]).
%------------------------------------------------------------------------------
