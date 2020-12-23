%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0593+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:48 EST 2020

% Result     : Theorem 0.48s
% Output     : CNFRefutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   14 (  29 expanded)
%              Number of clauses        :    9 (  10 expanded)
%              Number of leaves         :    2 (   7 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 ( 109 expanded)
%              Number of equality atoms :   23 (  68 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t197_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( ( k2_relat_1(X1) = k1_xboole_0
              & k2_relat_1(X2) = k1_xboole_0 )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t197_relat_1)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( ( k2_relat_1(X1) = k1_xboole_0
                & k2_relat_1(X2) = k1_xboole_0 )
             => X1 = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t197_relat_1])).

fof(c_0_3,plain,(
    ! [X2578] :
      ( ( k1_relat_1(X2578) != k1_xboole_0
        | X2578 = k1_xboole_0
        | ~ v1_relat_1(X2578) )
      & ( k2_relat_1(X2578) != k1_xboole_0
        | X2578 = k1_xboole_0
        | ~ v1_relat_1(X2578) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

fof(c_0_4,negated_conjecture,
    ( v1_relat_1(esk152_0)
    & v1_relat_1(esk153_0)
    & k2_relat_1(esk152_0) = k1_xboole_0
    & k2_relat_1(esk153_0) = k1_xboole_0
    & esk152_0 != esk153_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])).

cnf(c_0_5,plain,
    ( X1 = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,negated_conjecture,
    ( v1_relat_1(esk153_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( k2_relat_1(esk153_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( esk152_0 != esk153_0 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,negated_conjecture,
    ( esk153_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_6]),c_0_7])])).

cnf(c_0_10,negated_conjecture,
    ( v1_relat_1(esk152_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,negated_conjecture,
    ( k2_relat_1(esk152_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_12,negated_conjecture,
    ( esk152_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_10]),c_0_11])]),c_0_12]),
    [proof]).
%------------------------------------------------------------------------------
