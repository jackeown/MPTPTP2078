%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1032+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:36 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 247 expanded)
%              Number of clauses        :   30 ( 117 expanded)
%              Number of leaves         :    4 (  56 expanded)
%              Depth                    :   15
%              Number of atoms          :  181 (1391 expanded)
%              Number of equality atoms :   54 ( 454 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t141_funct_2,conjecture,(
    ! [X1,X2] : r1_tarski(k1_funct_2(X1,X2),k4_partfun1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t141_funct_2)).

fof(d2_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k1_funct_2(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5] :
              ( v1_relat_1(X5)
              & v1_funct_1(X5)
              & X4 = X5
              & k1_relat_1(X5) = X1
              & r1_tarski(k2_relat_1(X5),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d5_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_partfun1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5] :
              ( v1_relat_1(X5)
              & v1_funct_1(X5)
              & X4 = X5
              & r1_tarski(k1_relat_1(X5),X1)
              & r1_tarski(k2_relat_1(X5),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_partfun1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2] : r1_tarski(k1_funct_2(X1,X2),k4_partfun1(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t141_funct_2])).

fof(c_0_5,plain,(
    ! [X6,X7,X8,X9,X11,X12,X13,X14,X15,X17] :
      ( ( v1_relat_1(esk1_4(X6,X7,X8,X9))
        | ~ r2_hidden(X9,X8)
        | X8 != k1_funct_2(X6,X7) )
      & ( v1_funct_1(esk1_4(X6,X7,X8,X9))
        | ~ r2_hidden(X9,X8)
        | X8 != k1_funct_2(X6,X7) )
      & ( X9 = esk1_4(X6,X7,X8,X9)
        | ~ r2_hidden(X9,X8)
        | X8 != k1_funct_2(X6,X7) )
      & ( k1_relat_1(esk1_4(X6,X7,X8,X9)) = X6
        | ~ r2_hidden(X9,X8)
        | X8 != k1_funct_2(X6,X7) )
      & ( r1_tarski(k2_relat_1(esk1_4(X6,X7,X8,X9)),X7)
        | ~ r2_hidden(X9,X8)
        | X8 != k1_funct_2(X6,X7) )
      & ( ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12)
        | X11 != X12
        | k1_relat_1(X12) != X6
        | ~ r1_tarski(k2_relat_1(X12),X7)
        | r2_hidden(X11,X8)
        | X8 != k1_funct_2(X6,X7) )
      & ( ~ r2_hidden(esk2_3(X13,X14,X15),X15)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17)
        | esk2_3(X13,X14,X15) != X17
        | k1_relat_1(X17) != X13
        | ~ r1_tarski(k2_relat_1(X17),X14)
        | X15 = k1_funct_2(X13,X14) )
      & ( v1_relat_1(esk3_3(X13,X14,X15))
        | r2_hidden(esk2_3(X13,X14,X15),X15)
        | X15 = k1_funct_2(X13,X14) )
      & ( v1_funct_1(esk3_3(X13,X14,X15))
        | r2_hidden(esk2_3(X13,X14,X15),X15)
        | X15 = k1_funct_2(X13,X14) )
      & ( esk2_3(X13,X14,X15) = esk3_3(X13,X14,X15)
        | r2_hidden(esk2_3(X13,X14,X15),X15)
        | X15 = k1_funct_2(X13,X14) )
      & ( k1_relat_1(esk3_3(X13,X14,X15)) = X13
        | r2_hidden(esk2_3(X13,X14,X15),X15)
        | X15 = k1_funct_2(X13,X14) )
      & ( r1_tarski(k2_relat_1(esk3_3(X13,X14,X15)),X14)
        | r2_hidden(esk2_3(X13,X14,X15),X15)
        | X15 = k1_funct_2(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).

fof(c_0_6,negated_conjecture,(
    ~ r1_tarski(k1_funct_2(esk8_0,esk9_0),k4_partfun1(esk8_0,esk9_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X19,X20,X21,X22,X23] :
      ( ( ~ r1_tarski(X19,X20)
        | ~ r2_hidden(X21,X19)
        | r2_hidden(X21,X20) )
      & ( r2_hidden(esk4_2(X22,X23),X22)
        | r1_tarski(X22,X23) )
      & ( ~ r2_hidden(esk4_2(X22,X23),X23)
        | r1_tarski(X22,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_8,plain,
    ( X1 = esk1_4(X2,X3,X4,X1)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_funct_2(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( ~ r1_tarski(k1_funct_2(esk8_0,esk9_0),k4_partfun1(esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X25,X26,X27,X28,X30,X31,X32,X33,X34,X36] :
      ( ( v1_relat_1(esk5_4(X25,X26,X27,X28))
        | ~ r2_hidden(X28,X27)
        | X27 != k4_partfun1(X25,X26) )
      & ( v1_funct_1(esk5_4(X25,X26,X27,X28))
        | ~ r2_hidden(X28,X27)
        | X27 != k4_partfun1(X25,X26) )
      & ( X28 = esk5_4(X25,X26,X27,X28)
        | ~ r2_hidden(X28,X27)
        | X27 != k4_partfun1(X25,X26) )
      & ( r1_tarski(k1_relat_1(esk5_4(X25,X26,X27,X28)),X25)
        | ~ r2_hidden(X28,X27)
        | X27 != k4_partfun1(X25,X26) )
      & ( r1_tarski(k2_relat_1(esk5_4(X25,X26,X27,X28)),X26)
        | ~ r2_hidden(X28,X27)
        | X27 != k4_partfun1(X25,X26) )
      & ( ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31)
        | X30 != X31
        | ~ r1_tarski(k1_relat_1(X31),X25)
        | ~ r1_tarski(k2_relat_1(X31),X26)
        | r2_hidden(X30,X27)
        | X27 != k4_partfun1(X25,X26) )
      & ( ~ r2_hidden(esk6_3(X32,X33,X34),X34)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36)
        | esk6_3(X32,X33,X34) != X36
        | ~ r1_tarski(k1_relat_1(X36),X32)
        | ~ r1_tarski(k2_relat_1(X36),X33)
        | X34 = k4_partfun1(X32,X33) )
      & ( v1_relat_1(esk7_3(X32,X33,X34))
        | r2_hidden(esk6_3(X32,X33,X34),X34)
        | X34 = k4_partfun1(X32,X33) )
      & ( v1_funct_1(esk7_3(X32,X33,X34))
        | r2_hidden(esk6_3(X32,X33,X34),X34)
        | X34 = k4_partfun1(X32,X33) )
      & ( esk6_3(X32,X33,X34) = esk7_3(X32,X33,X34)
        | r2_hidden(esk6_3(X32,X33,X34),X34)
        | X34 = k4_partfun1(X32,X33) )
      & ( r1_tarski(k1_relat_1(esk7_3(X32,X33,X34)),X32)
        | r2_hidden(esk6_3(X32,X33,X34),X34)
        | X34 = k4_partfun1(X32,X33) )
      & ( r1_tarski(k2_relat_1(esk7_3(X32,X33,X34)),X33)
        | r2_hidden(esk6_3(X32,X33,X34),X34)
        | X34 = k4_partfun1(X32,X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_partfun1])])])])])])).

cnf(c_0_12,plain,
    ( k1_relat_1(esk1_4(X1,X2,X3,X4)) = X1
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,plain,
    ( esk1_4(X1,X2,k1_funct_2(X1,X2),X3) = X3
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk4_2(k1_funct_2(esk8_0,esk9_0),k4_partfun1(esk8_0,esk9_0)),k1_funct_2(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_15,plain,
    ( v1_relat_1(esk1_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,plain,
    ( r2_hidden(X2,X5)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | X2 != X1
    | ~ r1_tarski(k1_relat_1(X1),X3)
    | ~ r1_tarski(k2_relat_1(X1),X4)
    | X5 != k4_partfun1(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k1_relat_1(esk1_4(X1,X2,k1_funct_2(X1,X2),X3)) = X1
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( esk1_4(esk8_0,esk9_0,k1_funct_2(esk8_0,esk9_0),esk4_2(k1_funct_2(esk8_0,esk9_0),k4_partfun1(esk8_0,esk9_0))) = esk4_2(k1_funct_2(esk8_0,esk9_0),k4_partfun1(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( v1_relat_1(esk1_4(X1,X2,k1_funct_2(X1,X2),X3))
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( v1_funct_1(esk1_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,k4_partfun1(X2,X3))
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_16])])).

cnf(c_0_22,negated_conjecture,
    ( k1_relat_1(esk4_2(k1_funct_2(esk8_0,esk9_0),k4_partfun1(esk8_0,esk9_0))) = esk8_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_14]),c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( v1_relat_1(esk4_2(k1_funct_2(esk8_0,esk9_0),k4_partfun1(esk8_0,esk9_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_14]),c_0_18])).

cnf(c_0_24,plain,
    ( v1_funct_1(esk1_4(X1,X2,k1_funct_2(X1,X2),X3))
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk4_2(k1_funct_2(esk8_0,esk9_0),k4_partfun1(esk8_0,esk9_0)),k4_partfun1(X1,X2))
    | ~ r1_tarski(k2_relat_1(esk4_2(k1_funct_2(esk8_0,esk9_0),k4_partfun1(esk8_0,esk9_0))),X2)
    | ~ r1_tarski(esk8_0,X1)
    | ~ v1_funct_1(esk4_2(k1_funct_2(esk8_0,esk9_0),k4_partfun1(esk8_0,esk9_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_1(esk4_2(k1_funct_2(esk8_0,esk9_0),k4_partfun1(esk8_0,esk9_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_14]),c_0_18])).

cnf(c_0_27,plain,
    ( r1_tarski(k2_relat_1(esk1_4(X1,X2,X3,X4)),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk4_2(k1_funct_2(esk8_0,esk9_0),k4_partfun1(esk8_0,esk9_0)),k4_partfun1(X1,X2))
    | ~ r1_tarski(k2_relat_1(esk4_2(k1_funct_2(esk8_0,esk9_0),k4_partfun1(esk8_0,esk9_0))),X2)
    | ~ r1_tarski(esk8_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26])])).

cnf(c_0_29,plain,
    ( r1_tarski(k2_relat_1(esk1_4(X1,X2,k1_funct_2(X1,X2),X3)),X2)
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk4_2(k1_funct_2(esk8_0,esk9_0),k4_partfun1(esk8_0,esk9_0)),k4_partfun1(X1,X2))
    | r2_hidden(esk4_2(esk8_0,X1),esk8_0)
    | ~ r1_tarski(k2_relat_1(esk4_2(k1_funct_2(esk8_0,esk9_0),k4_partfun1(esk8_0,esk9_0))),X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_10])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk4_2(k1_funct_2(esk8_0,esk9_0),k4_partfun1(esk8_0,esk9_0))),esk9_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_14]),c_0_18])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk4_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk4_2(k1_funct_2(esk8_0,esk9_0),k4_partfun1(esk8_0,esk9_0)),k4_partfun1(X1,esk9_0))
    | r2_hidden(esk4_2(esk8_0,X1),esk8_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk4_2(esk8_0,esk8_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_9])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(esk8_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_34])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk4_2(k1_funct_2(esk8_0,esk9_0),k4_partfun1(esk8_0,esk9_0)),k4_partfun1(esk8_0,X1))
    | ~ r1_tarski(k2_relat_1(esk4_2(k1_funct_2(esk8_0,esk9_0),k4_partfun1(esk8_0,esk9_0))),X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_35])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk4_2(k1_funct_2(esk8_0,esk9_0),k4_partfun1(esk8_0,esk9_0)),k4_partfun1(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_37]),c_0_9]),
    [proof]).

%------------------------------------------------------------------------------
