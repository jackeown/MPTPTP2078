%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0598+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:48 EST 2020

% Result     : Theorem 0.75s
% Output     : CNFRefutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   16 (  25 expanded)
%              Number of clauses        :    9 (   9 expanded)
%              Number of leaves         :    3 (   6 expanded)
%              Depth                    :    6
%              Number of atoms          :   45 (  81 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t202_relat_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1) )
     => ! [X3] :
          ( r2_hidden(X3,k2_relat_1(X2))
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t202_relat_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d3_tarski)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v5_relat_1(X2,X1) )
       => ! [X3] :
            ( r2_hidden(X3,k2_relat_1(X2))
           => r2_hidden(X3,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t202_relat_1])).

fof(c_0_4,plain,(
    ! [X2143,X2144] :
      ( ( ~ v5_relat_1(X2144,X2143)
        | r1_tarski(k2_relat_1(X2144),X2143)
        | ~ v1_relat_1(X2144) )
      & ( ~ r1_tarski(k2_relat_1(X2144),X2143)
        | v5_relat_1(X2144,X2143)
        | ~ v1_relat_1(X2144) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

fof(c_0_5,negated_conjecture,
    ( v1_relat_1(esk154_0)
    & v5_relat_1(esk154_0,esk153_0)
    & r2_hidden(esk155_0,k2_relat_1(esk154_0))
    & ~ r2_hidden(esk155_0,esk153_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_6,plain,(
    ! [X27,X28,X29,X30,X31] :
      ( ( ~ r1_tarski(X27,X28)
        | ~ r2_hidden(X29,X27)
        | r2_hidden(X29,X28) )
      & ( r2_hidden(esk2_2(X30,X31),X30)
        | r1_tarski(X30,X31) )
      & ( ~ r2_hidden(esk2_2(X30,X31),X31)
        | r1_tarski(X30,X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_7,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( v5_relat_1(esk154_0,esk153_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( v1_relat_1(esk154_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk154_0),esk153_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9])])).

cnf(c_0_12,negated_conjecture,
    ( r2_hidden(X1,esk153_0)
    | ~ r2_hidden(X1,k2_relat_1(esk154_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk155_0,k2_relat_1(esk154_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( ~ r2_hidden(esk155_0,esk153_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),
    [proof]).
%------------------------------------------------------------------------------
