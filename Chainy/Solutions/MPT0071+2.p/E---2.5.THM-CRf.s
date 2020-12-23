%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0071+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:34 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   19 (  34 expanded)
%              Number of clauses        :   12 (  14 expanded)
%              Number of leaves         :    3 (   8 expanded)
%              Depth                    :    8
%              Number of atoms          :   39 (  90 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t64_xboole_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4)
        & r1_xboole_0(X2,X4) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',symmetry_r1_xboole_0)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(X1,X2)
          & r1_tarski(X3,X4)
          & r1_xboole_0(X2,X4) )
       => r1_xboole_0(X1,X3) ) ),
    inference(assume_negation,[status(cth)],[t64_xboole_1])).

fof(c_0_4,plain,(
    ! [X265,X266,X267] :
      ( ~ r1_tarski(X265,X266)
      | ~ r1_xboole_0(X266,X267)
      | r1_xboole_0(X265,X267) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

fof(c_0_5,negated_conjecture,
    ( r1_tarski(esk16_0,esk17_0)
    & r1_tarski(esk18_0,esk19_0)
    & r1_xboole_0(esk17_0,esk19_0)
    & ~ r1_xboole_0(esk16_0,esk18_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_6,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( r1_tarski(esk16_0,esk17_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,plain,(
    ! [X64,X65] :
      ( ~ r1_xboole_0(X64,X65)
      | r1_xboole_0(X65,X64) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_9,negated_conjecture,
    ( r1_xboole_0(esk16_0,X1)
    | ~ r1_xboole_0(esk17_0,X1) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( r1_xboole_0(esk17_0,esk19_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,negated_conjecture,
    ( r1_tarski(esk18_0,esk19_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( r1_xboole_0(esk16_0,esk19_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( r1_xboole_0(esk18_0,X1)
    | ~ r1_xboole_0(esk19_0,X1) ),
    inference(spm,[status(thm)],[c_0_6,c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( r1_xboole_0(esk19_0,esk16_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( r1_xboole_0(esk18_0,esk16_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_17,negated_conjecture,
    ( ~ r1_xboole_0(esk16_0,esk18_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_18,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_16]),c_0_17]),
    [proof]).
%------------------------------------------------------------------------------
