%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0907+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:57 EST 2020

% Result     : Theorem 1.28s
% Output     : CNFRefutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :   25 (  43 expanded)
%              Number of clauses        :   14 (  18 expanded)
%              Number of leaves         :    5 (  11 expanded)
%              Depth                    :    6
%              Number of atoms          :   47 (  90 expanded)
%              Number of equality atoms :   33 (  60 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t67_mcart_1,conjecture,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( X1 != k1_mcart_1(X1)
        & X1 != k2_mcart_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_mcart_1)).

fof(t20_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ( X1 != k1_mcart_1(X1)
        & X1 != k2_mcart_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(t23_mcart_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,X2)
       => X1 = k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',fc6_relat_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
       => ( X1 != k1_mcart_1(X1)
          & X1 != k2_mcart_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t67_mcart_1])).

fof(c_0_6,plain,(
    ! [X63,X64,X65] :
      ( ( X63 != k1_mcart_1(X63)
        | X63 != k4_tarski(X64,X65) )
      & ( X63 != k2_mcart_1(X63)
        | X63 != k4_tarski(X64,X65) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_mcart_1])])])])).

fof(c_0_7,plain,(
    ! [X86,X87] :
      ( k1_mcart_1(k4_tarski(X86,X87)) = X86
      & k2_mcart_1(k4_tarski(X86,X87)) = X87 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

fof(c_0_8,plain,(
    ! [X66,X67] :
      ( ~ v1_relat_1(X67)
      | ~ r2_hidden(X66,X67)
      | X66 = k4_tarski(k1_mcart_1(X66),k2_mcart_1(X66)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_mcart_1])])).

fof(c_0_9,negated_conjecture,
    ( r2_hidden(esk1_0,k2_zfmisc_1(esk2_0,esk3_0))
    & ( esk1_0 = k1_mcart_1(esk1_0)
      | esk1_0 = k2_mcart_1(esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_10,plain,(
    ! [X703,X704] : v1_relat_1(k2_zfmisc_1(X703,X704)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_11,plain,
    ( X1 != k1_mcart_1(X1)
    | X1 != k4_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( X2 = k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk1_0,k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( X1 != k2_mcart_1(X1)
    | X1 != k4_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,plain,
    ( k4_tarski(X1,X2) != X1 ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_11]),c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk1_0),k2_mcart_1(esk1_0)) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])])).

cnf(c_0_20,plain,
    ( k4_tarski(X1,X2) != X2 ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_16]),c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( esk1_0 = k1_mcart_1(esk1_0)
    | esk1_0 = k2_mcart_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,negated_conjecture,
    ( k1_mcart_1(esk1_0) != esk1_0 ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( k2_mcart_1(esk1_0) != esk1_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[c_0_21,c_0_22]),c_0_23]),
    [proof]).
%------------------------------------------------------------------------------
