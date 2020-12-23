%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1091+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:01 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   35 ( 187 expanded)
%              Number of clauses        :   22 (  84 expanded)
%              Number of leaves         :    6 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :   88 ( 578 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :   11 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t25_finset_1,conjecture,(
    ! [X1] :
      ( ( v1_finset_1(X1)
        & ! [X2] :
            ( r2_hidden(X2,X1)
           => v1_finset_1(X2) ) )
    <=> v1_finset_1(k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_finset_1)).

fof(t13_finset_1,axiom,(
    ! [X1,X2] :
      ( ( r1_tarski(X1,X2)
        & v1_finset_1(X2) )
     => v1_finset_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_finset_1)).

fof(t100_zfmisc_1,axiom,(
    ! [X1] : r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT004+2.ax',t100_zfmisc_1)).

fof(fc17_finset_1,axiom,(
    ! [X1] :
      ( v1_finset_1(X1)
     => v1_finset_1(k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc17_finset_1)).

fof(l22_finset_1,axiom,(
    ! [X1] :
      ( ( v1_finset_1(X1)
        & ! [X2] :
            ( r2_hidden(X2,X1)
           => v1_finset_1(X2) ) )
     => v1_finset_1(k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_finset_1)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT004+2.ax',l49_zfmisc_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_finset_1(X1)
          & ! [X2] :
              ( r2_hidden(X2,X1)
             => v1_finset_1(X2) ) )
      <=> v1_finset_1(k3_tarski(X1)) ) ),
    inference(assume_negation,[status(cth)],[t25_finset_1])).

fof(c_0_7,plain,(
    ! [X46,X47] :
      ( ~ r1_tarski(X46,X47)
      | ~ v1_finset_1(X47)
      | v1_finset_1(X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_finset_1])])).

fof(c_0_8,plain,(
    ! [X83] : r1_tarski(X83,k1_zfmisc_1(k3_tarski(X83))) ),
    inference(variable_rename,[status(thm)],[t100_zfmisc_1])).

fof(c_0_9,plain,(
    ! [X39] :
      ( ~ v1_finset_1(X39)
      | v1_finset_1(k1_zfmisc_1(X39)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc17_finset_1])])).

fof(c_0_10,negated_conjecture,(
    ! [X23] :
      ( ( r2_hidden(esk2_0,esk1_0)
        | ~ v1_finset_1(esk1_0)
        | ~ v1_finset_1(k3_tarski(esk1_0)) )
      & ( ~ v1_finset_1(esk2_0)
        | ~ v1_finset_1(esk1_0)
        | ~ v1_finset_1(k3_tarski(esk1_0)) )
      & ( v1_finset_1(esk1_0)
        | v1_finset_1(k3_tarski(esk1_0)) )
      & ( ~ r2_hidden(X23,esk1_0)
        | v1_finset_1(X23)
        | v1_finset_1(k3_tarski(esk1_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])])).

cnf(c_0_11,plain,
    ( v1_finset_1(X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_finset_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( v1_finset_1(k1_zfmisc_1(X1))
    | ~ v1_finset_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( v1_finset_1(esk1_0)
    | v1_finset_1(k3_tarski(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X43] :
      ( ( r2_hidden(esk4_1(X43),X43)
        | ~ v1_finset_1(X43)
        | v1_finset_1(k3_tarski(X43)) )
      & ( ~ v1_finset_1(esk4_1(X43))
        | ~ v1_finset_1(X43)
        | v1_finset_1(k3_tarski(X43)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_finset_1])])])])).

cnf(c_0_16,plain,
    ( v1_finset_1(X1)
    | ~ v1_finset_1(k1_zfmisc_1(k3_tarski(X1))) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( v1_finset_1(k1_zfmisc_1(k3_tarski(esk1_0)))
    | v1_finset_1(esk1_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( r2_hidden(esk4_1(X1),X1)
    | v1_finset_1(k3_tarski(X1))
    | ~ v1_finset_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( v1_finset_1(esk1_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_20,plain,
    ( v1_finset_1(k3_tarski(X1))
    | ~ v1_finset_1(esk4_1(X1))
    | ~ v1_finset_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk2_0,esk1_0)
    | ~ v1_finset_1(esk1_0)
    | ~ v1_finset_1(k3_tarski(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( v1_finset_1(X1)
    | v1_finset_1(k3_tarski(esk1_0))
    | ~ r2_hidden(X1,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,negated_conjecture,
    ( v1_finset_1(k3_tarski(esk1_0))
    | r2_hidden(esk4_1(esk1_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( v1_finset_1(k3_tarski(esk1_0))
    | ~ v1_finset_1(esk4_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_19])).

fof(c_0_25,plain,(
    ! [X71,X72] :
      ( ~ r2_hidden(X71,X72)
      | r1_tarski(X71,k3_tarski(X72)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk2_0,esk1_0)
    | ~ v1_finset_1(k3_tarski(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_19])])).

cnf(c_0_27,negated_conjecture,
    ( v1_finset_1(k3_tarski(esk1_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( ~ v1_finset_1(esk2_0)
    | ~ v1_finset_1(esk1_0)
    | ~ v1_finset_1(k3_tarski(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27])])).

cnf(c_0_31,negated_conjecture,
    ( ~ v1_finset_1(k3_tarski(esk1_0))
    | ~ v1_finset_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_19])])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(esk2_0,k3_tarski(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( ~ v1_finset_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_27])])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_32]),c_0_27])]),c_0_33]),
    [proof]).
%------------------------------------------------------------------------------
