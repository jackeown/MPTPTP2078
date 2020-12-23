%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : zfmisc_1__t151_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:02 EDT 2019

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   18 (  32 expanded)
%              Number of clauses        :   11 (  14 expanded)
%              Number of leaves         :    3 (   8 expanded)
%              Depth                    :    9
%              Number of atoms          :   46 (  89 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t151_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( ! [X3,X4] :
          ( ( r2_hidden(X3,X1)
            & r2_hidden(X4,X2) )
         => r1_xboole_0(X3,X4) )
     => r1_xboole_0(k3_tarski(X1),k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t151_zfmisc_1.p',t151_zfmisc_1)).

fof(t98_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_xboole_0(X3,X2) )
     => r1_xboole_0(k3_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t151_zfmisc_1.p',t98_zfmisc_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t151_zfmisc_1.p',symmetry_r1_xboole_0)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ! [X3,X4] :
            ( ( r2_hidden(X3,X1)
              & r2_hidden(X4,X2) )
           => r1_xboole_0(X3,X4) )
       => r1_xboole_0(k3_tarski(X1),k3_tarski(X2)) ) ),
    inference(assume_negation,[status(cth)],[t151_zfmisc_1])).

fof(c_0_4,negated_conjecture,(
    ! [X7,X8] :
      ( ( ~ r2_hidden(X7,esk1_0)
        | ~ r2_hidden(X8,esk2_0)
        | r1_xboole_0(X7,X8) )
      & ~ r1_xboole_0(k3_tarski(esk1_0),k3_tarski(esk2_0)) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])).

fof(c_0_5,plain,(
    ! [X18,X19] :
      ( ( r2_hidden(esk3_2(X18,X19),X18)
        | r1_xboole_0(k3_tarski(X18),X19) )
      & ( ~ r1_xboole_0(esk3_2(X18,X19),X19)
        | r1_xboole_0(k3_tarski(X18),X19) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_zfmisc_1])])])])).

fof(c_0_6,plain,(
    ! [X11,X12] :
      ( ~ r1_xboole_0(X11,X12)
      | r1_xboole_0(X12,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_7,negated_conjecture,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(X1,esk1_0)
    | ~ r2_hidden(X2,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r1_xboole_0(k3_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( r1_xboole_0(X1,esk3_2(esk2_0,X2))
    | r1_xboole_0(k3_tarski(esk2_0),X2)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,plain,
    ( r1_xboole_0(k3_tarski(X1),X2)
    | ~ r1_xboole_0(esk3_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,negated_conjecture,
    ( r1_xboole_0(esk3_2(esk2_0,X1),X2)
    | r1_xboole_0(k3_tarski(esk2_0),X1)
    | ~ r2_hidden(X2,esk1_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( r1_xboole_0(k3_tarski(esk2_0),X1)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_14,negated_conjecture,
    ( r1_xboole_0(X1,k3_tarski(esk2_0))
    | ~ r2_hidden(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_13])).

cnf(c_0_15,negated_conjecture,
    ( r1_xboole_0(k3_tarski(X1),k3_tarski(esk2_0))
    | ~ r2_hidden(esk3_2(X1,k3_tarski(esk2_0)),esk1_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_14])).

cnf(c_0_16,negated_conjecture,
    ( ~ r1_xboole_0(k3_tarski(esk1_0),k3_tarski(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_17,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_8]),c_0_16]),
    [proof]).
%------------------------------------------------------------------------------
