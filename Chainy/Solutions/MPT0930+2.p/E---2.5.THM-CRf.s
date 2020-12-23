%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0930+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:58 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   22 (  47 expanded)
%              Number of clauses        :   13 (  20 expanded)
%              Number of leaves         :    4 (  11 expanded)
%              Depth                    :    9
%              Number of atoms          :   53 ( 133 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t91_mcart_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => ( r2_hidden(k1_mcart_1(X2),k1_relat_1(X1))
            & r2_hidden(k2_mcart_1(X2),k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_mcart_1)).

fof(t21_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',t21_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d3_tarski)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( r2_hidden(X2,X1)
           => ( r2_hidden(k1_mcart_1(X2),k1_relat_1(X1))
              & r2_hidden(k2_mcart_1(X2),k2_relat_1(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t91_mcart_1])).

fof(c_0_5,plain,(
    ! [X583] :
      ( ~ v1_relat_1(X583)
      | r1_tarski(X583,k2_zfmisc_1(k1_relat_1(X583),k2_relat_1(X583))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).

fof(c_0_6,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & r2_hidden(esk2_0,esk1_0)
    & ( ~ r2_hidden(k1_mcart_1(esk2_0),k1_relat_1(esk1_0))
      | ~ r2_hidden(k2_mcart_1(esk2_0),k2_relat_1(esk1_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X21,X22,X23,X24,X25] :
      ( ( ~ r1_tarski(X21,X22)
        | ~ r2_hidden(X23,X21)
        | r2_hidden(X23,X22) )
      & ( r2_hidden(esk4_2(X24,X25),X24)
        | r1_tarski(X24,X25) )
      & ( ~ r2_hidden(esk4_2(X24,X25),X25)
        | r1_tarski(X24,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_8,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

fof(c_0_12,plain,(
    ! [X753,X754,X755] :
      ( ( r2_hidden(k1_mcart_1(X753),X754)
        | ~ r2_hidden(X753,k2_zfmisc_1(X754,X755)) )
      & ( r2_hidden(k2_mcart_1(X753),X755)
        | ~ r2_hidden(X753,k2_zfmisc_1(X754,X755)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))
    | ~ r2_hidden(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( ~ r2_hidden(k1_mcart_1(esk2_0),k1_relat_1(esk1_0))
    | ~ r2_hidden(k2_mcart_1(esk2_0),k2_relat_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk2_0),k1_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( ~ r2_hidden(k2_mcart_1(esk2_0),k2_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18])])).

cnf(c_0_21,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_16]),c_0_20]),
    [proof]).
%------------------------------------------------------------------------------
