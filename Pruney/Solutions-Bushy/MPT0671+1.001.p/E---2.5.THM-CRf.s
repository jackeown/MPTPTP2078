%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0671+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:00 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   23 (  35 expanded)
%              Number of clauses        :   12 (  13 expanded)
%              Number of leaves         :    5 (   9 expanded)
%              Depth                    :    6
%              Number of atoms          :  148 ( 186 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal formula depth    :   24 (   5 average)
%              Maximal clause size      :   79 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t89_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k1_relat_1(k8_relat_1(X1,X2)),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_funct_1)).

fof(t85_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( X2 = k8_relat_1(X1,X3)
          <=> ( ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X2))
                <=> ( r2_hidden(X4,k1_relat_1(X3))
                    & r2_hidden(k1_funct_1(X3,X4),X1) ) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X2))
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_1)).

fof(dt_k8_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => v1_relat_1(k8_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(fc9_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v1_relat_1(k8_relat_1(X1,X2))
        & v1_funct_1(k8_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_funct_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => r1_tarski(k1_relat_1(k8_relat_1(X1,X2)),k1_relat_1(X2)) ) ),
    inference(assume_negation,[status(cth)],[t89_funct_1])).

fof(c_0_6,plain,(
    ! [X15,X16,X17,X18,X19,X20] :
      ( ( r2_hidden(X18,k1_relat_1(X17))
        | ~ r2_hidden(X18,k1_relat_1(X16))
        | X16 != k8_relat_1(X15,X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( r2_hidden(k1_funct_1(X17,X18),X15)
        | ~ r2_hidden(X18,k1_relat_1(X16))
        | X16 != k8_relat_1(X15,X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( ~ r2_hidden(X19,k1_relat_1(X17))
        | ~ r2_hidden(k1_funct_1(X17,X19),X15)
        | r2_hidden(X19,k1_relat_1(X16))
        | X16 != k8_relat_1(X15,X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( ~ r2_hidden(X20,k1_relat_1(X16))
        | k1_funct_1(X16,X20) = k1_funct_1(X17,X20)
        | X16 != k8_relat_1(X15,X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( r2_hidden(esk3_3(X15,X16,X17),k1_relat_1(X16))
        | ~ r2_hidden(esk2_3(X15,X16,X17),k1_relat_1(X16))
        | ~ r2_hidden(esk2_3(X15,X16,X17),k1_relat_1(X17))
        | ~ r2_hidden(k1_funct_1(X17,esk2_3(X15,X16,X17)),X15)
        | X16 = k8_relat_1(X15,X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( k1_funct_1(X16,esk3_3(X15,X16,X17)) != k1_funct_1(X17,esk3_3(X15,X16,X17))
        | ~ r2_hidden(esk2_3(X15,X16,X17),k1_relat_1(X16))
        | ~ r2_hidden(esk2_3(X15,X16,X17),k1_relat_1(X17))
        | ~ r2_hidden(k1_funct_1(X17,esk2_3(X15,X16,X17)),X15)
        | X16 = k8_relat_1(X15,X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( r2_hidden(esk3_3(X15,X16,X17),k1_relat_1(X16))
        | r2_hidden(esk2_3(X15,X16,X17),k1_relat_1(X17))
        | r2_hidden(esk2_3(X15,X16,X17),k1_relat_1(X16))
        | X16 = k8_relat_1(X15,X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( k1_funct_1(X16,esk3_3(X15,X16,X17)) != k1_funct_1(X17,esk3_3(X15,X16,X17))
        | r2_hidden(esk2_3(X15,X16,X17),k1_relat_1(X17))
        | r2_hidden(esk2_3(X15,X16,X17),k1_relat_1(X16))
        | X16 = k8_relat_1(X15,X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( r2_hidden(esk3_3(X15,X16,X17),k1_relat_1(X16))
        | r2_hidden(k1_funct_1(X17,esk2_3(X15,X16,X17)),X15)
        | r2_hidden(esk2_3(X15,X16,X17),k1_relat_1(X16))
        | X16 = k8_relat_1(X15,X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( k1_funct_1(X16,esk3_3(X15,X16,X17)) != k1_funct_1(X17,esk3_3(X15,X16,X17))
        | r2_hidden(k1_funct_1(X17,esk2_3(X15,X16,X17)),X15)
        | r2_hidden(esk2_3(X15,X16,X17),k1_relat_1(X16))
        | X16 = k8_relat_1(X15,X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_funct_1])])])])])])).

fof(c_0_7,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X12)
      | v1_relat_1(k8_relat_1(X11,X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).

fof(c_0_8,plain,(
    ! [X13,X14] :
      ( ( v1_relat_1(k8_relat_1(X13,X14))
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( v1_funct_1(k8_relat_1(X13,X14))
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_funct_1])])])).

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & v1_funct_1(esk5_0)
    & ~ r1_tarski(k1_relat_1(k8_relat_1(esk4_0,esk5_0)),k1_relat_1(esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_10,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | X3 != k8_relat_1(X4,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( v1_relat_1(k8_relat_1(X2,X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( v1_funct_1(k8_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(k8_relat_1(esk4_0,esk5_0)),k1_relat_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(k8_relat_1(X3,X2))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_11]),c_0_12]),c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk1_2(k1_relat_1(k8_relat_1(esk4_0,esk5_0)),k1_relat_1(esk5_0)),k1_relat_1(k8_relat_1(esk4_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk1_2(k1_relat_1(k8_relat_1(esk4_0,esk5_0)),k1_relat_1(esk5_0)),k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19])])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_14]),
    [proof]).

%------------------------------------------------------------------------------
