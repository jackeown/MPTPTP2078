%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0597+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:48 EST 2020

% Result     : Theorem 0.47s
% Output     : CNFRefutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   14 (  26 expanded)
%              Number of clauses        :    9 (  10 expanded)
%              Number of leaves         :    2 (   6 expanded)
%              Depth                    :    6
%              Number of atoms          :   26 (  68 expanded)
%              Number of equality atoms :   14 (  35 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t201_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( k7_relat_1(X2,X1) = k7_relat_1(X3,X1)
           => k9_relat_1(X2,X1) = k9_relat_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t201_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( k7_relat_1(X2,X1) = k7_relat_1(X3,X1)
             => k9_relat_1(X2,X1) = k9_relat_1(X3,X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t201_relat_1])).

fof(c_0_3,plain,(
    ! [X2376,X2377] :
      ( ~ v1_relat_1(X2377)
      | k2_relat_1(k7_relat_1(X2377,X2376)) = k9_relat_1(X2377,X2376) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_4,negated_conjecture,
    ( v1_relat_1(esk154_0)
    & v1_relat_1(esk155_0)
    & k7_relat_1(esk154_0,esk153_0) = k7_relat_1(esk155_0,esk153_0)
    & k9_relat_1(esk154_0,esk153_0) != k9_relat_1(esk155_0,esk153_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])).

cnf(c_0_5,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,negated_conjecture,
    ( v1_relat_1(esk155_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk155_0,X1)) = k9_relat_1(esk155_0,X1) ),
    inference(spm,[status(thm)],[c_0_5,c_0_6])).

cnf(c_0_8,negated_conjecture,
    ( k7_relat_1(esk154_0,esk153_0) = k7_relat_1(esk155_0,esk153_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,negated_conjecture,
    ( v1_relat_1(esk154_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk154_0,esk153_0)) = k9_relat_1(esk155_0,esk153_0) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk154_0,X1)) = k9_relat_1(esk154_0,X1) ),
    inference(spm,[status(thm)],[c_0_5,c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( k9_relat_1(esk154_0,esk153_0) != k9_relat_1(esk155_0,esk153_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_10,c_0_11]),c_0_12]),
    [proof]).
%------------------------------------------------------------------------------
