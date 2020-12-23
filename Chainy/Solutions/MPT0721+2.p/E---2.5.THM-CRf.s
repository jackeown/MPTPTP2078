%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0721+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:51 EST 2020

% Result     : Theorem 1.10s
% Output     : CNFRefutation 1.10s
% Verified   : 
% Statistics : Number of formulae       :   25 (  45 expanded)
%              Number of clauses        :   14 (  16 expanded)
%              Number of leaves         :    5 (  11 expanded)
%              Depth                    :    8
%              Number of atoms          :   75 ( 167 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t176_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v5_relat_1(X3,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,k1_relat_1(X3))
       => m1_subset_1(k1_funct_1(X3,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',d19_relat_1)).

fof(t125_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k8_relat_1(X1,X2) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',t125_relat_1)).

fof(t86_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,k1_relat_1(k8_relat_1(X2,X3)))
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(k1_funct_1(X3,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_funct_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT006+2.ax',t1_subset)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v5_relat_1(X3,X1)
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,k1_relat_1(X3))
         => m1_subset_1(k1_funct_1(X3,X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t176_funct_1])).

fof(c_0_6,plain,(
    ! [X2154,X2155] :
      ( ( ~ v5_relat_1(X2155,X2154)
        | r1_tarski(k2_relat_1(X2155),X2154)
        | ~ v1_relat_1(X2155) )
      & ( ~ r1_tarski(k2_relat_1(X2155),X2154)
        | v5_relat_1(X2155,X2154)
        | ~ v1_relat_1(X2155) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk204_0)
    & v5_relat_1(esk204_0,esk202_0)
    & v1_funct_1(esk204_0)
    & r2_hidden(esk203_0,k1_relat_1(esk204_0))
    & ~ m1_subset_1(k1_funct_1(esk204_0,esk203_0),esk202_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_8,plain,(
    ! [X2343,X2344] :
      ( ~ v1_relat_1(X2344)
      | ~ r1_tarski(k2_relat_1(X2344),X2343)
      | k8_relat_1(X2343,X2344) = X2344 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).

cnf(c_0_9,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( v5_relat_1(esk204_0,esk202_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( v1_relat_1(esk204_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,plain,(
    ! [X3130,X3131,X3132] :
      ( ( r2_hidden(X3130,k1_relat_1(X3132))
        | ~ r2_hidden(X3130,k1_relat_1(k8_relat_1(X3131,X3132)))
        | ~ v1_relat_1(X3132)
        | ~ v1_funct_1(X3132) )
      & ( r2_hidden(k1_funct_1(X3132,X3130),X3131)
        | ~ r2_hidden(X3130,k1_relat_1(k8_relat_1(X3131,X3132)))
        | ~ v1_relat_1(X3132)
        | ~ v1_funct_1(X3132) )
      & ( ~ r2_hidden(X3130,k1_relat_1(X3132))
        | ~ r2_hidden(k1_funct_1(X3132,X3130),X3131)
        | r2_hidden(X3130,k1_relat_1(k8_relat_1(X3131,X3132)))
        | ~ v1_relat_1(X3132)
        | ~ v1_funct_1(X3132) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_funct_1])])])).

cnf(c_0_13,plain,
    ( k8_relat_1(X2,X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk204_0),esk202_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])])).

cnf(c_0_15,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | ~ r2_hidden(X2,k1_relat_1(k8_relat_1(X3,X1)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( k8_relat_1(esk202_0,esk204_0) = esk204_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_11])])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_1(esk204_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_18,plain,(
    ! [X1979,X1980] :
      ( ~ r2_hidden(X1979,X1980)
      | m1_subset_1(X1979,X1980) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk204_0,X1),esk202_0)
    | ~ r2_hidden(X1,k1_relat_1(esk204_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_11])])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk203_0,k1_relat_1(esk204_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_21,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk204_0,esk203_0),esk202_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( ~ m1_subset_1(k1_funct_1(esk204_0,esk203_0),esk202_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_24,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),
    [proof]).
%------------------------------------------------------------------------------
