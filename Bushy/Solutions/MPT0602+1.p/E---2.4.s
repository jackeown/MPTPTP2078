%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relat_1__t206_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:58 EDT 2019

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   10 (  12 expanded)
%              Number of clauses        :    5 (   5 expanded)
%              Number of leaves         :    2 (   3 expanded)
%              Depth                    :    5
%              Number of atoms          :   16 (  20 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t206_relat_1,conjecture,(
    ! [X1,X2] :
      ( v4_relat_1(k1_xboole_0,X1)
      & v5_relat_1(k1_xboole_0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t206_relat_1.p',t206_relat_1)).

fof(l222_relat_1,axiom,(
    ! [X1,X2] :
      ( v4_relat_1(k1_xboole_0,X1)
      & v5_relat_1(k1_xboole_0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t206_relat_1.p',l222_relat_1)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v4_relat_1(k1_xboole_0,X1)
        & v5_relat_1(k1_xboole_0,X2) ) ),
    inference(assume_negation,[status(cth)],[t206_relat_1])).

fof(c_0_3,negated_conjecture,
    ( ~ v4_relat_1(k1_xboole_0,esk1_0)
    | ~ v5_relat_1(k1_xboole_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])).

fof(c_0_4,plain,(
    ! [X18,X19] :
      ( v4_relat_1(k1_xboole_0,X18)
      & v5_relat_1(k1_xboole_0,X19) ) ),
    inference(variable_rename,[status(thm)],[l222_relat_1])).

cnf(c_0_5,negated_conjecture,
    ( ~ v4_relat_1(k1_xboole_0,esk1_0)
    | ~ v5_relat_1(k1_xboole_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,plain,
    ( v4_relat_1(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( ~ v5_relat_1(k1_xboole_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_5,c_0_6])])).

cnf(c_0_8,plain,
    ( v5_relat_1(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_7,c_0_8])]),
    [proof]).
%------------------------------------------------------------------------------
