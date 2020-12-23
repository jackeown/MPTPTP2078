%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0595+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:48 EST 2020

% Result     : Theorem 8.81s
% Output     : CNFRefutation 8.81s
% Verified   : 
% Statistics : Number of formulae       :   14 (  34 expanded)
%              Number of clauses        :    9 (  12 expanded)
%              Number of leaves         :    2 (   8 expanded)
%              Depth                    :    6
%              Number of atoms          :   33 ( 120 expanded)
%              Number of equality atoms :   13 (  47 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    5 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t199_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( k2_relat_1(X1) = k2_relat_1(X2)
               => k2_relat_1(k5_relat_1(X1,X3)) = k2_relat_1(k5_relat_1(X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t199_relat_1)).

fof(t160_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k2_relat_1(k5_relat_1(X1,X2)) = k9_relat_1(X2,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3] :
                ( v1_relat_1(X3)
               => ( k2_relat_1(X1) = k2_relat_1(X2)
                 => k2_relat_1(k5_relat_1(X1,X3)) = k2_relat_1(k5_relat_1(X2,X3)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t199_relat_1])).

fof(c_0_3,plain,(
    ! [X2408,X2409] :
      ( ~ v1_relat_1(X2408)
      | ~ v1_relat_1(X2409)
      | k2_relat_1(k5_relat_1(X2408,X2409)) = k9_relat_1(X2409,k2_relat_1(X2408)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t160_relat_1])])])).

fof(c_0_4,negated_conjecture,
    ( v1_relat_1(esk152_0)
    & v1_relat_1(esk153_0)
    & v1_relat_1(esk154_0)
    & k2_relat_1(esk152_0) = k2_relat_1(esk153_0)
    & k2_relat_1(k5_relat_1(esk152_0,esk154_0)) != k2_relat_1(k5_relat_1(esk153_0,esk154_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])).

cnf(c_0_5,plain,
    ( k2_relat_1(k5_relat_1(X1,X2)) = k9_relat_1(X2,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,negated_conjecture,
    ( v1_relat_1(esk154_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( k9_relat_1(esk154_0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,esk154_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_5,c_0_6])).

cnf(c_0_8,negated_conjecture,
    ( v1_relat_1(esk153_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,negated_conjecture,
    ( k2_relat_1(esk152_0) = k2_relat_1(esk153_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,negated_conjecture,
    ( v1_relat_1(esk152_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,negated_conjecture,
    ( k9_relat_1(esk154_0,k2_relat_1(esk152_0)) = k2_relat_1(k5_relat_1(esk153_0,esk154_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( k2_relat_1(k5_relat_1(esk152_0,esk154_0)) != k2_relat_1(k5_relat_1(esk153_0,esk154_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_10]),c_0_11]),c_0_12]),
    [proof]).
%------------------------------------------------------------------------------
