%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0473+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:46 EST 2020

% Result     : Theorem 0.44s
% Output     : CNFRefutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   17 (  51 expanded)
%              Number of clauses        :   11 (  20 expanded)
%              Number of leaves         :    3 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :   42 ( 156 expanded)
%              Number of equality atoms :   32 ( 114 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t65_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k1_relat_1(X1) = k1_xboole_0
      <=> k2_relat_1(X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ( k1_relat_1(X1) = k1_xboole_0
        <=> k2_relat_1(X1) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t65_relat_1])).

fof(c_0_4,plain,(
    ! [X2270] :
      ( ( k1_relat_1(X2270) != k1_xboole_0
        | X2270 = k1_xboole_0
        | ~ v1_relat_1(X2270) )
      & ( k2_relat_1(X2270) != k1_xboole_0
        | X2270 = k1_xboole_0
        | ~ v1_relat_1(X2270) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

fof(c_0_5,negated_conjecture,
    ( v1_relat_1(esk140_0)
    & ( k1_relat_1(esk140_0) != k1_xboole_0
      | k2_relat_1(esk140_0) != k1_xboole_0 )
    & ( k1_relat_1(esk140_0) = k1_xboole_0
      | k2_relat_1(esk140_0) = k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_6,plain,
    ( X1 = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( v1_relat_1(esk140_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( X1 = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,negated_conjecture,
    ( esk140_0 = k1_xboole_0
    | k2_relat_1(esk140_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( k1_relat_1(esk140_0) = k1_xboole_0
    | k2_relat_1(esk140_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,negated_conjecture,
    ( esk140_0 = k1_xboole_0
    | k1_relat_1(esk140_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_8,c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( k1_relat_1(esk140_0) != k1_xboole_0
    | k2_relat_1(esk140_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,negated_conjecture,
    ( esk140_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])).

cnf(c_0_14,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_15,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_16,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_13]),c_0_15])]),
    [proof]).
%------------------------------------------------------------------------------
