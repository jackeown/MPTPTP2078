%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0960+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:28 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   29 (  59 expanded)
%              Number of clauses        :   16 (  26 expanded)
%              Number of leaves         :    6 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :  114 ( 219 expanded)
%              Number of equality atoms :   17 (  34 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   33 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_tarski(X1,X2)
        <=> ! [X3,X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
             => r2_hidden(k4_tarski(X3,X4),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(dt_k1_wellord2,axiom,(
    ! [X1] : v1_relat_1(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(d1_wellord2,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( X2 = k1_wellord2(X1)
      <=> ( k3_relat_1(X2) = X1
          & ! [X3,X4] :
              ( ( r2_hidden(X3,X1)
                & r2_hidden(X4,X1) )
             => ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> r1_tarski(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

fof(t106_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(t30_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X2,k3_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

fof(t33_wellord2,conjecture,(
    ! [X1] : r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_wellord2)).

fof(c_0_6,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( ~ r1_tarski(X11,X12)
        | ~ r2_hidden(k4_tarski(X13,X14),X11)
        | r2_hidden(k4_tarski(X13,X14),X12)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(k4_tarski(esk3_2(X11,X15),esk4_2(X11,X15)),X11)
        | r1_tarski(X11,X15)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(k4_tarski(esk3_2(X11,X15),esk4_2(X11,X15)),X15)
        | r1_tarski(X11,X15)
        | ~ v1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).

fof(c_0_7,plain,(
    ! [X18] : v1_relat_1(k1_wellord2(X18)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_8,plain,(
    ! [X5,X6,X7,X8] :
      ( ( k3_relat_1(X6) = X5
        | X6 != k1_wellord2(X5)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(k4_tarski(X7,X8),X6)
        | r1_tarski(X7,X8)
        | ~ r2_hidden(X7,X5)
        | ~ r2_hidden(X8,X5)
        | X6 != k1_wellord2(X5)
        | ~ v1_relat_1(X6) )
      & ( ~ r1_tarski(X7,X8)
        | r2_hidden(k4_tarski(X7,X8),X6)
        | ~ r2_hidden(X7,X5)
        | ~ r2_hidden(X8,X5)
        | X6 != k1_wellord2(X5)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(esk1_2(X5,X6),X5)
        | k3_relat_1(X6) != X5
        | X6 = k1_wellord2(X5)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(esk2_2(X5,X6),X5)
        | k3_relat_1(X6) != X5
        | X6 = k1_wellord2(X5)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)
        | ~ r1_tarski(esk1_2(X5,X6),esk2_2(X5,X6))
        | k3_relat_1(X6) != X5
        | X6 = k1_wellord2(X5)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)
        | r1_tarski(esk1_2(X5,X6),esk2_2(X5,X6))
        | k3_relat_1(X6) != X5
        | X6 = k1_wellord2(X5)
        | ~ v1_relat_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).

fof(c_0_9,plain,(
    ! [X19,X20,X21,X22] :
      ( ( r2_hidden(X19,X21)
        | ~ r2_hidden(k4_tarski(X19,X20),k2_zfmisc_1(X21,X22)) )
      & ( r2_hidden(X20,X22)
        | ~ r2_hidden(k4_tarski(X19,X20),k2_zfmisc_1(X21,X22)) )
      & ( ~ r2_hidden(X19,X21)
        | ~ r2_hidden(X20,X22)
        | r2_hidden(k4_tarski(X19,X20),k2_zfmisc_1(X21,X22)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).

fof(c_0_10,plain,(
    ! [X23,X24,X25] :
      ( ( r2_hidden(X23,k3_relat_1(X25))
        | ~ r2_hidden(k4_tarski(X23,X24),X25)
        | ~ v1_relat_1(X25) )
      & ( r2_hidden(X24,k3_relat_1(X25))
        | ~ r2_hidden(k4_tarski(X23,X24),X25)
        | ~ v1_relat_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_relat_1])])])).

cnf(c_0_11,plain,
    ( r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( k3_relat_1(X1) = X2
    | X1 != k1_wellord2(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( r1_tarski(k1_wellord2(X1),X2)
    | r2_hidden(k4_tarski(esk3_2(k1_wellord2(X1),X2),esk4_2(k1_wellord2(X1),X2)),k1_wellord2(X1)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_18,plain,
    ( k3_relat_1(k1_wellord2(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_13]),c_0_12])])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1] : r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,X1)) ),
    inference(assume_negation,[status(cth)],[t33_wellord2])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ r2_hidden(esk4_2(X1,k2_zfmisc_1(X2,X3)),X3)
    | ~ r2_hidden(esk3_2(X1,k2_zfmisc_1(X2,X3)),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,plain,
    ( r1_tarski(k1_wellord2(X1),X2)
    | r2_hidden(esk4_2(k1_wellord2(X1),X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_12])])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_23,negated_conjecture,(
    ~ r1_tarski(k1_wellord2(esk5_0),k2_zfmisc_1(esk5_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

cnf(c_0_24,plain,
    ( r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X2,X1))
    | ~ r2_hidden(esk3_2(k1_wellord2(X1),k2_zfmisc_1(X2,X1)),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_12])])).

cnf(c_0_25,plain,
    ( r1_tarski(k1_wellord2(X1),X2)
    | r2_hidden(esk3_2(k1_wellord2(X1),X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_17]),c_0_18]),c_0_12])])).

cnf(c_0_26,negated_conjecture,
    ( ~ r1_tarski(k1_wellord2(esk5_0),k2_zfmisc_1(esk5_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,plain,
    ( r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27])]),
    [proof]).

%------------------------------------------------------------------------------
