%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0676+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:01 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 192 expanded)
%              Number of clauses        :   34 (  75 expanded)
%              Number of leaves         :    6 (  47 expanded)
%              Depth                    :   11
%              Number of atoms          :  271 ( 941 expanded)
%              Number of equality atoms :   45 ( 118 expanded)
%              Maximal formula depth    :   24 (   5 average)
%              Maximal clause size      :   79 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t120_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => r1_tarski(k9_relat_1(k8_relat_1(X1,X3),X2),k9_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_funct_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(fc9_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v1_relat_1(k8_relat_1(X1,X2))
        & v1_funct_1(k8_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_funct_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_1)).

fof(dt_k8_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => v1_relat_1(k8_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => r1_tarski(k9_relat_1(k8_relat_1(X1,X3),X2),k9_relat_1(X3,X2)) ) ),
    inference(assume_negation,[status(cth)],[t120_funct_1])).

fof(c_0_7,plain,(
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

fof(c_0_8,negated_conjecture,
    ( v1_relat_1(esk9_0)
    & v1_funct_1(esk9_0)
    & ~ r1_tarski(k9_relat_1(k8_relat_1(esk7_0,esk9_0),esk8_0),k9_relat_1(esk9_0,esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_9,plain,(
    ! [X18,X19,X20,X21,X22] :
      ( ( ~ r1_tarski(X18,X19)
        | ~ r2_hidden(X20,X18)
        | r2_hidden(X20,X19) )
      & ( r2_hidden(esk4_2(X21,X22),X21)
        | r1_tarski(X21,X22) )
      & ( ~ r2_hidden(esk4_2(X21,X22),X22)
        | r1_tarski(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_10,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),k1_relat_1(X1))
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(k8_relat_1(esk7_0,esk9_0),esk8_0),k9_relat_1(esk9_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( X1 = k1_funct_1(X2,esk1_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k9_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( r2_hidden(esk1_4(X1,X2,k9_relat_1(X1,X2),X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,k9_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk4_2(k9_relat_1(k8_relat_1(esk7_0,esk9_0),esk8_0),k9_relat_1(esk9_0,esk8_0)),k9_relat_1(k8_relat_1(esk7_0,esk9_0),esk8_0)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

fof(c_0_16,plain,(
    ! [X26,X27] :
      ( ( v1_relat_1(k8_relat_1(X26,X27))
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( v1_funct_1(k8_relat_1(X26,X27))
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_funct_1])])])).

cnf(c_0_17,plain,
    ( k1_funct_1(X1,esk1_4(X1,X2,k9_relat_1(X1,X2),X3)) = X3
    | ~ r2_hidden(X3,k9_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X28,X29,X30,X31,X32,X33] :
      ( ( r2_hidden(X31,k1_relat_1(X30))
        | ~ r2_hidden(X31,k1_relat_1(X29))
        | X29 != k8_relat_1(X28,X30)
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( r2_hidden(k1_funct_1(X30,X31),X28)
        | ~ r2_hidden(X31,k1_relat_1(X29))
        | X29 != k8_relat_1(X28,X30)
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( ~ r2_hidden(X32,k1_relat_1(X30))
        | ~ r2_hidden(k1_funct_1(X30,X32),X28)
        | r2_hidden(X32,k1_relat_1(X29))
        | X29 != k8_relat_1(X28,X30)
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( ~ r2_hidden(X33,k1_relat_1(X29))
        | k1_funct_1(X29,X33) = k1_funct_1(X30,X33)
        | X29 != k8_relat_1(X28,X30)
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( r2_hidden(esk6_3(X28,X29,X30),k1_relat_1(X29))
        | ~ r2_hidden(esk5_3(X28,X29,X30),k1_relat_1(X29))
        | ~ r2_hidden(esk5_3(X28,X29,X30),k1_relat_1(X30))
        | ~ r2_hidden(k1_funct_1(X30,esk5_3(X28,X29,X30)),X28)
        | X29 = k8_relat_1(X28,X30)
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( k1_funct_1(X29,esk6_3(X28,X29,X30)) != k1_funct_1(X30,esk6_3(X28,X29,X30))
        | ~ r2_hidden(esk5_3(X28,X29,X30),k1_relat_1(X29))
        | ~ r2_hidden(esk5_3(X28,X29,X30),k1_relat_1(X30))
        | ~ r2_hidden(k1_funct_1(X30,esk5_3(X28,X29,X30)),X28)
        | X29 = k8_relat_1(X28,X30)
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( r2_hidden(esk6_3(X28,X29,X30),k1_relat_1(X29))
        | r2_hidden(esk5_3(X28,X29,X30),k1_relat_1(X30))
        | r2_hidden(esk5_3(X28,X29,X30),k1_relat_1(X29))
        | X29 = k8_relat_1(X28,X30)
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( k1_funct_1(X29,esk6_3(X28,X29,X30)) != k1_funct_1(X30,esk6_3(X28,X29,X30))
        | r2_hidden(esk5_3(X28,X29,X30),k1_relat_1(X30))
        | r2_hidden(esk5_3(X28,X29,X30),k1_relat_1(X29))
        | X29 = k8_relat_1(X28,X30)
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( r2_hidden(esk6_3(X28,X29,X30),k1_relat_1(X29))
        | r2_hidden(k1_funct_1(X30,esk5_3(X28,X29,X30)),X28)
        | r2_hidden(esk5_3(X28,X29,X30),k1_relat_1(X29))
        | X29 = k8_relat_1(X28,X30)
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( k1_funct_1(X29,esk6_3(X28,X29,X30)) != k1_funct_1(X30,esk6_3(X28,X29,X30))
        | r2_hidden(k1_funct_1(X30,esk5_3(X28,X29,X30)),X28)
        | r2_hidden(esk5_3(X28,X29,X30),k1_relat_1(X29))
        | X29 = k8_relat_1(X28,X30)
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_funct_1])])])])])])).

fof(c_0_19,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X25)
      | v1_relat_1(k8_relat_1(X24,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk1_4(k8_relat_1(esk7_0,esk9_0),esk8_0,k9_relat_1(k8_relat_1(esk7_0,esk9_0),esk8_0),esk4_2(k9_relat_1(k8_relat_1(esk7_0,esk9_0),esk8_0),k9_relat_1(esk9_0,esk8_0))),k1_relat_1(k8_relat_1(esk7_0,esk9_0)))
    | ~ v1_funct_1(k8_relat_1(esk7_0,esk9_0))
    | ~ v1_relat_1(k8_relat_1(esk7_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,plain,
    ( v1_funct_1(k8_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,negated_conjecture,
    ( k1_funct_1(k8_relat_1(esk7_0,esk9_0),esk1_4(k8_relat_1(esk7_0,esk9_0),esk8_0,k9_relat_1(k8_relat_1(esk7_0,esk9_0),esk8_0),esk4_2(k9_relat_1(k8_relat_1(esk7_0,esk9_0),esk8_0),k9_relat_1(esk9_0,esk8_0)))) = esk4_2(k9_relat_1(k8_relat_1(esk7_0,esk9_0),esk8_0),k9_relat_1(esk9_0,esk8_0))
    | ~ v1_funct_1(k8_relat_1(esk7_0,esk9_0))
    | ~ v1_relat_1(k8_relat_1(esk7_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_15])).

cnf(c_0_25,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | X3 != k8_relat_1(X4,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( v1_relat_1(k8_relat_1(X2,X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk1_4(k8_relat_1(esk7_0,esk9_0),esk8_0,k9_relat_1(k8_relat_1(esk7_0,esk9_0),esk8_0),esk4_2(k9_relat_1(k8_relat_1(esk7_0,esk9_0),esk8_0),k9_relat_1(esk9_0,esk8_0))),k1_relat_1(k8_relat_1(esk7_0,esk9_0)))
    | ~ v1_relat_1(k8_relat_1(esk7_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])])).

cnf(c_0_29,plain,
    ( k1_funct_1(X2,X1) = k1_funct_1(X3,X1)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X2 != k8_relat_1(X4,X3)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( k1_funct_1(k8_relat_1(esk7_0,esk9_0),esk1_4(k8_relat_1(esk7_0,esk9_0),esk8_0,k9_relat_1(k8_relat_1(esk7_0,esk9_0),esk8_0),esk4_2(k9_relat_1(k8_relat_1(esk7_0,esk9_0),esk8_0),k9_relat_1(esk9_0,esk8_0)))) = esk4_2(k9_relat_1(k8_relat_1(esk7_0,esk9_0),esk8_0),k9_relat_1(esk9_0,esk8_0))
    | ~ v1_relat_1(k8_relat_1(esk7_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_21]),c_0_22]),c_0_23])])).

cnf(c_0_31,plain,
    ( r2_hidden(esk1_4(X1,X2,k9_relat_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k9_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( r2_hidden(X4,X5)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,X3)
    | X4 != k1_funct_1(X2,X1)
    | X5 != k9_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,k1_relat_1(k8_relat_1(X3,X2)))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_26]),c_0_27]),c_0_21])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk1_4(k8_relat_1(esk7_0,esk9_0),esk8_0,k9_relat_1(k8_relat_1(esk7_0,esk9_0),esk8_0),esk4_2(k9_relat_1(k8_relat_1(esk7_0,esk9_0),esk8_0),k9_relat_1(esk9_0,esk8_0))),k1_relat_1(k8_relat_1(esk7_0,esk9_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_27]),c_0_23])])).

cnf(c_0_35,plain,
    ( k1_funct_1(k8_relat_1(X1,X2),X3) = k1_funct_1(X2,X3)
    | ~ r2_hidden(X3,k1_relat_1(k8_relat_1(X1,X2)))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_29]),c_0_27]),c_0_21])).

cnf(c_0_36,negated_conjecture,
    ( k1_funct_1(k8_relat_1(esk7_0,esk9_0),esk1_4(k8_relat_1(esk7_0,esk9_0),esk8_0,k9_relat_1(k8_relat_1(esk7_0,esk9_0),esk8_0),esk4_2(k9_relat_1(k8_relat_1(esk7_0,esk9_0),esk8_0),k9_relat_1(esk9_0,esk8_0)))) = esk4_2(k9_relat_1(k8_relat_1(esk7_0,esk9_0),esk8_0),k9_relat_1(esk9_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_27]),c_0_23])])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk1_4(k8_relat_1(esk7_0,esk9_0),esk8_0,k9_relat_1(k8_relat_1(esk7_0,esk9_0),esk8_0),esk4_2(k9_relat_1(k8_relat_1(esk7_0,esk9_0),esk8_0),k9_relat_1(esk9_0,esk8_0))),esk8_0)
    | ~ v1_funct_1(k8_relat_1(esk7_0,esk9_0))
    | ~ v1_relat_1(k8_relat_1(esk7_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_15])).

cnf(c_0_38,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k9_relat_1(X1,X3))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_32])])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk1_4(k8_relat_1(esk7_0,esk9_0),esk8_0,k9_relat_1(k8_relat_1(esk7_0,esk9_0),esk8_0),esk4_2(k9_relat_1(k8_relat_1(esk7_0,esk9_0),esk8_0),k9_relat_1(esk9_0,esk8_0))),k1_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_22]),c_0_23])])).

cnf(c_0_40,negated_conjecture,
    ( k1_funct_1(esk9_0,esk1_4(k8_relat_1(esk7_0,esk9_0),esk8_0,k9_relat_1(k8_relat_1(esk7_0,esk9_0),esk8_0),esk4_2(k9_relat_1(k8_relat_1(esk7_0,esk9_0),esk8_0),k9_relat_1(esk9_0,esk8_0)))) = esk4_2(k9_relat_1(k8_relat_1(esk7_0,esk9_0),esk8_0),k9_relat_1(esk9_0,esk8_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_34]),c_0_22]),c_0_23])]),c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk1_4(k8_relat_1(esk7_0,esk9_0),esk8_0,k9_relat_1(k8_relat_1(esk7_0,esk9_0),esk8_0),esk4_2(k9_relat_1(k8_relat_1(esk7_0,esk9_0),esk8_0),k9_relat_1(esk9_0,esk8_0))),esk8_0)
    | ~ v1_relat_1(k8_relat_1(esk7_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_21]),c_0_22]),c_0_23])])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk4_2(k9_relat_1(k8_relat_1(esk7_0,esk9_0),esk8_0),k9_relat_1(esk9_0,esk8_0)),k9_relat_1(esk9_0,X1))
    | ~ r2_hidden(esk1_4(k8_relat_1(esk7_0,esk9_0),esk8_0,k9_relat_1(k8_relat_1(esk7_0,esk9_0),esk8_0),esk4_2(k9_relat_1(k8_relat_1(esk7_0,esk9_0),esk8_0),k9_relat_1(esk9_0,esk8_0))),X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_22]),c_0_23])]),c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk1_4(k8_relat_1(esk7_0,esk9_0),esk8_0,k9_relat_1(k8_relat_1(esk7_0,esk9_0),esk8_0),esk4_2(k9_relat_1(k8_relat_1(esk7_0,esk9_0),esk8_0),k9_relat_1(esk9_0,esk8_0))),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_27]),c_0_23])])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk4_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk4_2(k9_relat_1(k8_relat_1(esk7_0,esk9_0),esk8_0),k9_relat_1(esk9_0,esk8_0)),k9_relat_1(esk9_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_11]),
    [proof]).

%------------------------------------------------------------------------------
