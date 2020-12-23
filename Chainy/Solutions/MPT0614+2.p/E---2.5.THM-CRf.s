%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0614+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:48 EST 2020

% Result     : Theorem 0.77s
% Output     : CNFRefutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   18 (  33 expanded)
%              Number of clauses        :   11 (  12 expanded)
%              Number of leaves         :    3 (   8 expanded)
%              Depth                    :    5
%              Number of atoms          :   45 ( 103 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t218_relat_1,conjecture,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v5_relat_1(X3,X1) )
         => v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t218_relat_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t1_xboole_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_tarski(X1,X2)
       => ! [X3] :
            ( ( v1_relat_1(X3)
              & v5_relat_1(X3,X1) )
           => v5_relat_1(X3,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t218_relat_1])).

fof(c_0_4,negated_conjecture,
    ( r1_tarski(esk155_0,esk156_0)
    & v1_relat_1(esk157_0)
    & v5_relat_1(esk157_0,esk155_0)
    & ~ v5_relat_1(esk157_0,esk156_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_5,plain,(
    ! [X2154,X2155] :
      ( ( ~ v5_relat_1(X2155,X2154)
        | r1_tarski(k2_relat_1(X2155),X2154)
        | ~ v1_relat_1(X2155) )
      & ( ~ r1_tarski(k2_relat_1(X2155),X2154)
        | v5_relat_1(X2155,X2154)
        | ~ v1_relat_1(X2155) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

fof(c_0_6,plain,(
    ! [X206,X207,X208] :
      ( ~ r1_tarski(X206,X207)
      | ~ r1_tarski(X207,X208)
      | r1_tarski(X206,X208) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_7,negated_conjecture,
    ( ~ v5_relat_1(esk157_0,esk156_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( v5_relat_1(X1,X2)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( v1_relat_1(esk157_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( r1_tarski(esk155_0,esk156_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_12,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,negated_conjecture,
    ( v5_relat_1(esk157_0,esk155_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_14,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk157_0),esk156_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9])])).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(X1,esk156_0)
    | ~ r1_tarski(X1,esk155_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk157_0),esk155_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_9])])).

cnf(c_0_17,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])]),
    [proof]).
%------------------------------------------------------------------------------
