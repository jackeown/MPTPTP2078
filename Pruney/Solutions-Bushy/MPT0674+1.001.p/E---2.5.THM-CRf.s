%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0674+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   33 (  80 expanded)
%              Number of clauses        :   24 (  35 expanded)
%              Number of leaves         :    4 (  18 expanded)
%              Depth                    :   11
%              Number of atoms          :  143 ( 420 expanded)
%              Number of equality atoms :   62 ( 162 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   44 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t117_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => k11_relat_1(X2,X1) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(d12_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( X3 = k9_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(X5,k1_relat_1(X1))
                  & r2_hidden(X5,X2)
                  & X4 = k1_funct_1(X1,X5) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

fof(d16_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( r2_hidden(X1,k1_relat_1(X2))
         => k11_relat_1(X2,X1) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t117_funct_1])).

fof(c_0_5,plain,(
    ! [X20,X21,X22,X23,X24,X25] :
      ( ( ~ r2_hidden(X22,X21)
        | X22 = X20
        | X21 != k1_tarski(X20) )
      & ( X23 != X20
        | r2_hidden(X23,X21)
        | X21 != k1_tarski(X20) )
      & ( ~ r2_hidden(esk4_2(X24,X25),X25)
        | esk4_2(X24,X25) != X24
        | X25 = k1_tarski(X24) )
      & ( r2_hidden(esk4_2(X24,X25),X25)
        | esk4_2(X24,X25) = X24
        | X25 = k1_tarski(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_6,plain,(
    ! [X6,X7,X8,X9,X11,X12,X13,X14,X16] :
      ( ( r2_hidden(esk1_4(X6,X7,X8,X9),k1_relat_1(X6))
        | ~ r2_hidden(X9,X8)
        | X8 != k9_relat_1(X6,X7)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( r2_hidden(esk1_4(X6,X7,X8,X9),X7)
        | ~ r2_hidden(X9,X8)
        | X8 != k9_relat_1(X6,X7)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( X9 = k1_funct_1(X6,esk1_4(X6,X7,X8,X9))
        | ~ r2_hidden(X9,X8)
        | X8 != k9_relat_1(X6,X7)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( ~ r2_hidden(X12,k1_relat_1(X6))
        | ~ r2_hidden(X12,X7)
        | X11 != k1_funct_1(X6,X12)
        | r2_hidden(X11,X8)
        | X8 != k9_relat_1(X6,X7)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( ~ r2_hidden(esk2_3(X6,X13,X14),X14)
        | ~ r2_hidden(X16,k1_relat_1(X6))
        | ~ r2_hidden(X16,X13)
        | esk2_3(X6,X13,X14) != k1_funct_1(X6,X16)
        | X14 = k9_relat_1(X6,X13)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( r2_hidden(esk3_3(X6,X13,X14),k1_relat_1(X6))
        | r2_hidden(esk2_3(X6,X13,X14),X14)
        | X14 = k9_relat_1(X6,X13)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( r2_hidden(esk3_3(X6,X13,X14),X13)
        | r2_hidden(esk2_3(X6,X13,X14),X14)
        | X14 = k9_relat_1(X6,X13)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( esk2_3(X6,X13,X14) = k1_funct_1(X6,esk3_3(X6,X13,X14))
        | r2_hidden(esk2_3(X6,X13,X14),X14)
        | X14 = k9_relat_1(X6,X13)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & v1_funct_1(esk6_0)
    & r2_hidden(esk5_0,k1_relat_1(esk6_0))
    & k11_relat_1(esk6_0,esk5_0) != k1_tarski(k1_funct_1(esk6_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_8,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( esk2_3(X1,X2,X3) = k1_funct_1(X1,esk3_3(X1,X2,X3))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( X1 = k9_relat_1(esk6_0,X2)
    | r2_hidden(esk3_3(esk6_0,X2,X1),X2)
    | r2_hidden(esk2_3(esk6_0,X2,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])])).

cnf(c_0_15,negated_conjecture,
    ( k1_funct_1(esk6_0,esk3_3(esk6_0,X1,X2)) = esk2_3(esk6_0,X1,X2)
    | X2 = k9_relat_1(esk6_0,X1)
    | r2_hidden(esk2_3(esk6_0,X1,X2),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_10]),c_0_11])])).

cnf(c_0_16,negated_conjecture,
    ( esk2_3(esk6_0,X1,k1_tarski(X2)) = X2
    | k1_tarski(X2) = k9_relat_1(esk6_0,X1)
    | r2_hidden(esk3_3(esk6_0,X1,k1_tarski(X2)),X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( k1_funct_1(esk6_0,esk3_3(esk6_0,X1,k1_tarski(X2))) = esk2_3(esk6_0,X1,k1_tarski(X2))
    | esk2_3(esk6_0,X1,k1_tarski(X2)) = X2
    | k1_tarski(X2) = k9_relat_1(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( esk2_3(esk6_0,k1_tarski(X1),k1_tarski(X2)) = X2
    | esk3_3(esk6_0,k1_tarski(X1),k1_tarski(X2)) = X1
    | k1_tarski(X2) = k9_relat_1(esk6_0,k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( esk2_3(esk6_0,k1_tarski(X1),k1_tarski(X2)) = k1_funct_1(esk6_0,X1)
    | esk2_3(esk6_0,k1_tarski(X1),k1_tarski(X2)) = X2
    | k1_tarski(X2) = k9_relat_1(esk6_0,k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_21,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X18)
      | k11_relat_1(X18,X19) = k9_relat_1(X18,k1_tarski(X19)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).

cnf(c_0_22,plain,
    ( X3 = k9_relat_1(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(X4,k1_relat_1(X1))
    | ~ r2_hidden(X4,X2)
    | esk2_3(X1,X2,X3) != k1_funct_1(X1,X4)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_23,negated_conjecture,
    ( esk2_3(esk6_0,k1_tarski(X1),k1_tarski(k1_funct_1(esk6_0,X1))) = k1_funct_1(esk6_0,X1)
    | k1_tarski(k1_funct_1(esk6_0,X1)) = k9_relat_1(esk6_0,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_19])])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_20])])).

cnf(c_0_25,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( k1_tarski(k1_funct_1(esk6_0,X1)) = k9_relat_1(esk6_0,k1_tarski(X1))
    | k1_funct_1(esk6_0,X1) != k1_funct_1(esk6_0,X2)
    | ~ r2_hidden(X2,k1_relat_1(esk6_0))
    | ~ r2_hidden(X2,k1_tarski(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_10]),c_0_11])])).

cnf(c_0_27,negated_conjecture,
    ( k11_relat_1(esk6_0,esk5_0) != k1_tarski(k1_funct_1(esk6_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_28,negated_conjecture,
    ( k11_relat_1(esk6_0,X1) = k9_relat_1(esk6_0,k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_11])).

cnf(c_0_29,negated_conjecture,
    ( k1_tarski(k1_funct_1(esk6_0,X1)) = k9_relat_1(esk6_0,k1_tarski(X1))
    | ~ r2_hidden(X1,k1_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_26]),c_0_24])])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk5_0,k1_relat_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_31,negated_conjecture,
    ( k1_tarski(k1_funct_1(esk6_0,esk5_0)) != k9_relat_1(esk6_0,k1_tarski(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),
    [proof]).

%------------------------------------------------------------------------------
