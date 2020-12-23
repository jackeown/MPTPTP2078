%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0624+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:56 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   22 (  48 expanded)
%              Number of clauses        :   15 (  19 expanded)
%              Number of leaves         :    3 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :   95 ( 234 expanded)
%              Number of equality atoms :   19 (  37 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t19_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( r2_hidden(X3,X1)
              & ! [X4] :
                  ~ ( r2_hidden(X4,k1_relat_1(X2))
                    & X3 = k1_funct_1(X2,X4) ) )
       => r1_tarski(X1,k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_funct_1)).

fof(d5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( X2 = k2_relat_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                  & X3 = k1_funct_1(X1,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & ! [X4] :
                    ~ ( r2_hidden(X4,k1_relat_1(X2))
                      & X3 = k1_funct_1(X2,X4) ) )
         => r1_tarski(X1,k2_relat_1(X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t19_funct_1])).

fof(c_0_4,plain,(
    ! [X11,X12,X13,X15,X16,X17,X19] :
      ( ( r2_hidden(esk2_3(X11,X12,X13),k1_relat_1(X11))
        | ~ r2_hidden(X13,X12)
        | X12 != k2_relat_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( X13 = k1_funct_1(X11,esk2_3(X11,X12,X13))
        | ~ r2_hidden(X13,X12)
        | X12 != k2_relat_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( ~ r2_hidden(X16,k1_relat_1(X11))
        | X15 != k1_funct_1(X11,X16)
        | r2_hidden(X15,X12)
        | X12 != k2_relat_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( ~ r2_hidden(esk3_2(X11,X17),X17)
        | ~ r2_hidden(X19,k1_relat_1(X11))
        | esk3_2(X11,X17) != k1_funct_1(X11,X19)
        | X17 = k2_relat_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( r2_hidden(esk4_2(X11,X17),k1_relat_1(X11))
        | r2_hidden(esk3_2(X11,X17),X17)
        | X17 = k2_relat_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( esk3_2(X11,X17) = k1_funct_1(X11,esk4_2(X11,X17))
        | r2_hidden(esk3_2(X11,X17),X17)
        | X17 = k2_relat_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_5,negated_conjecture,(
    ! [X23] :
      ( v1_relat_1(esk6_0)
      & v1_funct_1(esk6_0)
      & ( r2_hidden(esk7_1(X23),k1_relat_1(esk6_0))
        | ~ r2_hidden(X23,esk5_0) )
      & ( X23 = k1_funct_1(esk6_0,esk7_1(X23))
        | ~ r2_hidden(X23,esk5_0) )
      & ~ r1_tarski(esk5_0,k2_relat_1(esk6_0)) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])])).

fof(c_0_6,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_7,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( ~ r1_tarski(esk5_0,k2_relat_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_7])])).

cnf(c_0_11,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk7_1(X1),k1_relat_1(esk6_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k2_relat_1(esk6_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( X1 = k1_funct_1(esk6_0,esk7_1(X1))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk6_0,X1),k2_relat_1(esk6_0))
    | ~ r2_hidden(X1,k1_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk7_1(esk1_2(esk5_0,k2_relat_1(esk6_0))),k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( k1_funct_1(esk6_0,esk7_1(esk1_2(esk5_0,k2_relat_1(esk6_0)))) = esk1_2(esk5_0,k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_14])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k2_relat_1(esk6_0)),k2_relat_1(esk6_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_8]),
    [proof]).

%------------------------------------------------------------------------------
