%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0581+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:51 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   14 (  29 expanded)
%              Number of clauses        :    9 (  10 expanded)
%              Number of leaves         :    2 (   7 expanded)
%              Depth                    :    6
%              Number of atoms          :   29 (  95 expanded)
%              Number of equality atoms :   17 (  56 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    5 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t185_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3,X4] :
              ( ( k7_relat_1(X1,X3) = k7_relat_1(X2,X3)
                & k7_relat_1(X1,X4) = k7_relat_1(X2,X4) )
             => k7_relat_1(X1,k2_xboole_0(X3,X4)) = k7_relat_1(X2,k2_xboole_0(X3,X4)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_relat_1)).

fof(t107_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k7_relat_1(X3,X1),k7_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_relat_1)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3,X4] :
                ( ( k7_relat_1(X1,X3) = k7_relat_1(X2,X3)
                  & k7_relat_1(X1,X4) = k7_relat_1(X2,X4) )
               => k7_relat_1(X1,k2_xboole_0(X3,X4)) = k7_relat_1(X2,k2_xboole_0(X3,X4)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t185_relat_1])).

fof(c_0_3,plain,(
    ! [X5,X6,X7] :
      ( ~ v1_relat_1(X7)
      | k7_relat_1(X7,k2_xboole_0(X5,X6)) = k2_xboole_0(k7_relat_1(X7,X5),k7_relat_1(X7,X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t107_relat_1])])).

fof(c_0_4,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & k7_relat_1(esk1_0,esk3_0) = k7_relat_1(esk2_0,esk3_0)
    & k7_relat_1(esk1_0,esk4_0) = k7_relat_1(esk2_0,esk4_0)
    & k7_relat_1(esk1_0,k2_xboole_0(esk3_0,esk4_0)) != k7_relat_1(esk2_0,k2_xboole_0(esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])).

cnf(c_0_5,plain,
    ( k7_relat_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k7_relat_1(X1,X2),k7_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,negated_conjecture,
    ( k7_relat_1(esk1_0,esk4_0) = k7_relat_1(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( k2_xboole_0(k7_relat_1(esk1_0,X1),k7_relat_1(esk2_0,esk4_0)) = k7_relat_1(esk1_0,k2_xboole_0(X1,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_6]),c_0_7])])).

cnf(c_0_9,negated_conjecture,
    ( k7_relat_1(esk1_0,esk3_0) = k7_relat_1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,negated_conjecture,
    ( k2_xboole_0(k7_relat_1(esk2_0,esk3_0),k7_relat_1(esk2_0,esk4_0)) = k7_relat_1(esk1_0,k2_xboole_0(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_11,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_12,negated_conjecture,
    ( k7_relat_1(esk1_0,k2_xboole_0(esk3_0,esk4_0)) != k7_relat_1(esk2_0,k2_xboole_0(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_10]),c_0_11])]),c_0_12]),
    [proof]).

%------------------------------------------------------------------------------
