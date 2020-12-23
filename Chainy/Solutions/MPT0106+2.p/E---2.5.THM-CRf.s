%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0106+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:37 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   21 (  53 expanded)
%              Number of clauses        :   10 (  22 expanded)
%              Number of leaves         :    5 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   21 (  53 expanded)
%              Number of equality atoms :   20 (  52 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t99_xboole_1,conjecture,(
    ! [X1,X2,X3] : k4_xboole_0(k5_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X2,k2_xboole_0(X1,X3))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t42_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d6_xboole_0)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] : k4_xboole_0(k5_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X2,k2_xboole_0(X1,X3))) ),
    inference(assume_negation,[status(cth)],[t99_xboole_1])).

fof(c_0_6,negated_conjecture,(
    k4_xboole_0(k5_xboole_0(esk16_0,esk17_0),esk18_0) != k2_xboole_0(k4_xboole_0(esk16_0,k2_xboole_0(esk17_0,esk18_0)),k4_xboole_0(esk17_0,k2_xboole_0(esk16_0,esk18_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_7,plain,(
    ! [X371,X372] : k2_xboole_0(X371,X372) = k5_xboole_0(X371,k4_xboole_0(X372,X371)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_8,plain,(
    ! [X208,X209,X210] : k4_xboole_0(k4_xboole_0(X208,X209),X210) = k4_xboole_0(X208,k2_xboole_0(X209,X210)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_9,plain,(
    ! [X211,X212,X213] : k4_xboole_0(k2_xboole_0(X211,X212),X213) = k2_xboole_0(k4_xboole_0(X211,X213),k4_xboole_0(X212,X213)) ),
    inference(variable_rename,[status(thm)],[t42_xboole_1])).

fof(c_0_10,plain,(
    ! [X52,X53] : k5_xboole_0(X52,X53) = k2_xboole_0(k4_xboole_0(X52,X53),k4_xboole_0(X53,X52)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

cnf(c_0_11,negated_conjecture,
    ( k4_xboole_0(k5_xboole_0(esk16_0,esk17_0),esk18_0) != k2_xboole_0(k4_xboole_0(esk16_0,k2_xboole_0(esk17_0,esk18_0)),k4_xboole_0(esk17_0,k2_xboole_0(esk16_0,esk18_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( k4_xboole_0(k5_xboole_0(esk16_0,esk17_0),esk18_0) != k5_xboole_0(k4_xboole_0(esk16_0,k5_xboole_0(esk17_0,k4_xboole_0(esk18_0,esk17_0))),k4_xboole_0(k4_xboole_0(esk17_0,k5_xboole_0(esk16_0,k4_xboole_0(esk18_0,esk16_0))),k4_xboole_0(esk16_0,k5_xboole_0(esk17_0,k4_xboole_0(esk18_0,esk17_0))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11,c_0_12]),c_0_12]),c_0_12])).

cnf(c_0_17,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2))) ),
    inference(rw,[status(thm)],[c_0_13,c_0_12])).

cnf(c_0_18,plain,
    ( k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X3) = k5_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_12]),c_0_12])).

cnf(c_0_19,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_15,c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_17]),c_0_17]),c_0_18]),c_0_19])]),
    [proof]).
%------------------------------------------------------------------------------
