%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0688+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:02 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   16 (  24 expanded)
%              Number of clauses        :    9 (   9 expanded)
%              Number of leaves         :    3 (   6 expanded)
%              Depth                    :    6
%              Number of atoms          :   47 (  81 expanded)
%              Number of equality atoms :    8 (  14 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t143_funct_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( ! [X3] :
            ~ ( r2_hidden(X3,X1)
              & k10_relat_1(X2,k1_tarski(X3)) = k1_xboole_0 )
       => r1_tarski(X1,k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_funct_1)).

fof(t142_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k2_relat_1(X2))
      <=> k10_relat_1(X2,k1_tarski(X1)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & k10_relat_1(X2,k1_tarski(X3)) = k1_xboole_0 )
         => r1_tarski(X1,k2_relat_1(X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t143_funct_1])).

fof(c_0_4,negated_conjecture,(
    ! [X14] :
      ( v1_relat_1(esk3_0)
      & ( ~ r2_hidden(X14,esk2_0)
        | k10_relat_1(esk3_0,k1_tarski(X14)) != k1_xboole_0 )
      & ~ r1_tarski(esk2_0,k2_relat_1(esk3_0)) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])).

fof(c_0_5,plain,(
    ! [X10,X11] :
      ( ( ~ r2_hidden(X10,k2_relat_1(X11))
        | k10_relat_1(X11,k1_tarski(X10)) != k1_xboole_0
        | ~ v1_relat_1(X11) )
      & ( k10_relat_1(X11,k1_tarski(X10)) = k1_xboole_0
        | r2_hidden(X10,k2_relat_1(X11))
        | ~ v1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t142_funct_1])])])).

fof(c_0_6,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_7,negated_conjecture,
    ( ~ r2_hidden(X1,esk2_0)
    | k10_relat_1(esk3_0,k1_tarski(X1)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( k10_relat_1(X1,k1_tarski(X2)) = k1_xboole_0
    | r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(X1,k2_relat_1(esk3_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9])])).

cnf(c_0_12,negated_conjecture,
    ( r1_tarski(X1,k2_relat_1(esk3_0))
    | ~ r2_hidden(esk1_2(X1,k2_relat_1(esk3_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_13,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( ~ r1_tarski(esk2_0,k2_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_15,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),
    [proof]).

%------------------------------------------------------------------------------
