%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0582+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:48 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   18 (  34 expanded)
%              Number of clauses        :   11 (  12 expanded)
%              Number of leaves         :    3 (   8 expanded)
%              Depth                    :    6
%              Number of atoms          :   46 ( 122 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t186_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(k1_relat_1(X3),X1)
              & r1_tarski(X3,X2) )
           => r1_tarski(X3,k7_relat_1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_relat_1)).

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(t105_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( r1_tarski(X2,X3)
           => r1_tarski(k7_relat_1(X2,X1),k7_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(k1_relat_1(X3),X1)
                & r1_tarski(X3,X2) )
             => r1_tarski(X3,k7_relat_1(X2,X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t186_relat_1])).

fof(c_0_4,plain,(
    ! [X2605,X2606] :
      ( ~ v1_relat_1(X2606)
      | ~ r1_tarski(k1_relat_1(X2606),X2605)
      | k7_relat_1(X2606,X2605) = X2606 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

fof(c_0_5,negated_conjecture,
    ( v1_relat_1(esk152_0)
    & v1_relat_1(esk153_0)
    & r1_tarski(k1_relat_1(esk153_0),esk151_0)
    & r1_tarski(esk153_0,esk152_0)
    & ~ r1_tarski(esk153_0,k7_relat_1(esk152_0,esk151_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_6,plain,(
    ! [X2272,X2273,X2274] :
      ( ~ v1_relat_1(X2273)
      | ~ v1_relat_1(X2274)
      | ~ r1_tarski(X2273,X2274)
      | r1_tarski(k7_relat_1(X2273,X2272),k7_relat_1(X2274,X2272)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t105_relat_1])])])).

cnf(c_0_7,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( v1_relat_1(esk153_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r1_tarski(k7_relat_1(X1,X3),k7_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( r1_tarski(esk153_0,esk152_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,negated_conjecture,
    ( v1_relat_1(esk152_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,negated_conjecture,
    ( k7_relat_1(esk153_0,X1) = esk153_0
    | ~ r1_tarski(k1_relat_1(esk153_0),X1) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk153_0),esk151_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( r1_tarski(k7_relat_1(esk153_0,X1),k7_relat_1(esk152_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_8])])).

cnf(c_0_15,negated_conjecture,
    ( k7_relat_1(esk153_0,esk151_0) = esk153_0 ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( ~ r1_tarski(esk153_0,k7_relat_1(esk152_0,esk151_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),
    [proof]).
%------------------------------------------------------------------------------
