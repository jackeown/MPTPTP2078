%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0437+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:45 EST 2020

% Result     : Theorem 0.44s
% Output     : CNFRefutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   16 (  23 expanded)
%              Number of clauses        :    9 (  10 expanded)
%              Number of leaves         :    3 (   5 expanded)
%              Depth                    :    6
%              Number of atoms          :   58 (  83 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(t20_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(X2,k2_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(c_0_3,plain,(
    ! [X2102,X2103,X2104,X2106,X2107,X2108,X2109,X2111] :
      ( ( ~ r2_hidden(X2104,X2103)
        | r2_hidden(k4_tarski(esk119_3(X2102,X2103,X2104),X2104),X2102)
        | X2103 != k2_relat_1(X2102) )
      & ( ~ r2_hidden(k4_tarski(X2107,X2106),X2102)
        | r2_hidden(X2106,X2103)
        | X2103 != k2_relat_1(X2102) )
      & ( ~ r2_hidden(esk120_2(X2108,X2109),X2109)
        | ~ r2_hidden(k4_tarski(X2111,esk120_2(X2108,X2109)),X2108)
        | X2109 = k2_relat_1(X2108) )
      & ( r2_hidden(esk120_2(X2108,X2109),X2109)
        | r2_hidden(k4_tarski(esk121_2(X2108,X2109),esk120_2(X2108,X2109)),X2108)
        | X2109 = k2_relat_1(X2108) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r2_hidden(k4_tarski(X1,X2),X3)
         => ( r2_hidden(X1,k1_relat_1(X3))
            & r2_hidden(X2,k2_relat_1(X3)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t20_relat_1])).

cnf(c_0_5,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

fof(c_0_6,negated_conjecture,
    ( v1_relat_1(esk126_0)
    & r2_hidden(k4_tarski(esk124_0,esk125_0),esk126_0)
    & ( ~ r2_hidden(esk124_0,k1_relat_1(esk126_0))
      | ~ r2_hidden(esk125_0,k2_relat_1(esk126_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X2091,X2092,X2093,X2095,X2096,X2097,X2098,X2100] :
      ( ( ~ r2_hidden(X2093,X2092)
        | r2_hidden(k4_tarski(X2093,esk116_3(X2091,X2092,X2093)),X2091)
        | X2092 != k1_relat_1(X2091) )
      & ( ~ r2_hidden(k4_tarski(X2095,X2096),X2091)
        | r2_hidden(X2095,X2092)
        | X2092 != k1_relat_1(X2091) )
      & ( ~ r2_hidden(esk117_2(X2097,X2098),X2098)
        | ~ r2_hidden(k4_tarski(esk117_2(X2097,X2098),X2100),X2097)
        | X2098 = k1_relat_1(X2097) )
      & ( r2_hidden(esk117_2(X2097,X2098),X2098)
        | r2_hidden(k4_tarski(esk117_2(X2097,X2098),esk118_2(X2097,X2098)),X2097)
        | X2098 = k1_relat_1(X2097) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_8,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( r2_hidden(k4_tarski(esk124_0,esk125_0),esk126_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( ~ r2_hidden(esk124_0,k1_relat_1(esk126_0))
    | ~ r2_hidden(esk125_0,k2_relat_1(esk126_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( r2_hidden(esk125_0,k2_relat_1(esk126_0)) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( ~ r2_hidden(esk124_0,k1_relat_1(esk126_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_11,c_0_12])])).

cnf(c_0_15,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_9]),c_0_14]),
    [proof]).
%------------------------------------------------------------------------------
