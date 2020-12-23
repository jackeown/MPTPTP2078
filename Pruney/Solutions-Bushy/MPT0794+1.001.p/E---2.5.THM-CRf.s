%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0794+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:12 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   32 ( 157 expanded)
%              Number of clauses        :   25 (  49 expanded)
%              Number of leaves         :    3 (  38 expanded)
%              Depth                    :    7
%              Number of atoms          :  236 (1505 expanded)
%              Number of equality atoms :   35 ( 269 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal clause size      :   90 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t45_wellord1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( ( v1_relat_1(X3)
                & v1_funct_1(X3) )
             => ( r3_wellord1(X1,X2,X3)
               => ! [X4,X5] :
                    ( r2_hidden(k4_tarski(X4,X5),X1)
                   => ( X4 = X5
                      | ( r2_hidden(k4_tarski(k1_funct_1(X3,X4),k1_funct_1(X3,X5)),X2)
                        & k1_funct_1(X3,X4) != k1_funct_1(X3,X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_wellord1)).

fof(d7_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( ( v1_relat_1(X3)
                & v1_funct_1(X3) )
             => ( r3_wellord1(X1,X2,X3)
              <=> ( k1_relat_1(X3) = k3_relat_1(X1)
                  & k2_relat_1(X3) = k3_relat_1(X2)
                  & v2_funct_1(X3)
                  & ! [X4,X5] :
                      ( r2_hidden(k4_tarski(X4,X5),X1)
                    <=> ( r2_hidden(X4,k3_relat_1(X1))
                        & r2_hidden(X5,k3_relat_1(X1))
                        & r2_hidden(k4_tarski(k1_funct_1(X3,X4),k1_funct_1(X3,X5)),X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_wellord1)).

fof(d8_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( r2_hidden(X2,k1_relat_1(X1))
              & r2_hidden(X3,k1_relat_1(X1))
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3] :
                ( ( v1_relat_1(X3)
                  & v1_funct_1(X3) )
               => ( r3_wellord1(X1,X2,X3)
                 => ! [X4,X5] :
                      ( r2_hidden(k4_tarski(X4,X5),X1)
                     => ( X4 = X5
                        | ( r2_hidden(k4_tarski(k1_funct_1(X3,X4),k1_funct_1(X3,X5)),X2)
                          & k1_funct_1(X3,X4) != k1_funct_1(X3,X5) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t45_wellord1])).

fof(c_0_4,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12] :
      ( ( k1_relat_1(X8) = k3_relat_1(X6)
        | ~ r3_wellord1(X6,X7,X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v1_relat_1(X7)
        | ~ v1_relat_1(X6) )
      & ( k2_relat_1(X8) = k3_relat_1(X7)
        | ~ r3_wellord1(X6,X7,X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v1_relat_1(X7)
        | ~ v1_relat_1(X6) )
      & ( v2_funct_1(X8)
        | ~ r3_wellord1(X6,X7,X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v1_relat_1(X7)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(X9,k3_relat_1(X6))
        | ~ r2_hidden(k4_tarski(X9,X10),X6)
        | ~ r3_wellord1(X6,X7,X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v1_relat_1(X7)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(X10,k3_relat_1(X6))
        | ~ r2_hidden(k4_tarski(X9,X10),X6)
        | ~ r3_wellord1(X6,X7,X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v1_relat_1(X7)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(k4_tarski(k1_funct_1(X8,X9),k1_funct_1(X8,X10)),X7)
        | ~ r2_hidden(k4_tarski(X9,X10),X6)
        | ~ r3_wellord1(X6,X7,X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v1_relat_1(X7)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(X11,k3_relat_1(X6))
        | ~ r2_hidden(X12,k3_relat_1(X6))
        | ~ r2_hidden(k4_tarski(k1_funct_1(X8,X11),k1_funct_1(X8,X12)),X7)
        | r2_hidden(k4_tarski(X11,X12),X6)
        | ~ r3_wellord1(X6,X7,X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v1_relat_1(X7)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X6)
        | ~ r2_hidden(esk1_3(X6,X7,X8),k3_relat_1(X6))
        | ~ r2_hidden(esk2_3(X6,X7,X8),k3_relat_1(X6))
        | ~ r2_hidden(k4_tarski(k1_funct_1(X8,esk1_3(X6,X7,X8)),k1_funct_1(X8,esk2_3(X6,X7,X8))),X7)
        | k1_relat_1(X8) != k3_relat_1(X6)
        | k2_relat_1(X8) != k3_relat_1(X7)
        | ~ v2_funct_1(X8)
        | r3_wellord1(X6,X7,X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v1_relat_1(X7)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(esk1_3(X6,X7,X8),k3_relat_1(X6))
        | r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X6)
        | k1_relat_1(X8) != k3_relat_1(X6)
        | k2_relat_1(X8) != k3_relat_1(X7)
        | ~ v2_funct_1(X8)
        | r3_wellord1(X6,X7,X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v1_relat_1(X7)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(esk2_3(X6,X7,X8),k3_relat_1(X6))
        | r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X6)
        | k1_relat_1(X8) != k3_relat_1(X6)
        | k2_relat_1(X8) != k3_relat_1(X7)
        | ~ v2_funct_1(X8)
        | r3_wellord1(X6,X7,X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v1_relat_1(X7)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(k4_tarski(k1_funct_1(X8,esk1_3(X6,X7,X8)),k1_funct_1(X8,esk2_3(X6,X7,X8))),X7)
        | r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X6)
        | k1_relat_1(X8) != k3_relat_1(X6)
        | k2_relat_1(X8) != k3_relat_1(X7)
        | ~ v2_funct_1(X8)
        | r3_wellord1(X6,X7,X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v1_relat_1(X7)
        | ~ v1_relat_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_wellord1])])])])])])).

fof(c_0_5,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & v1_relat_1(esk6_0)
    & v1_relat_1(esk7_0)
    & v1_funct_1(esk7_0)
    & r3_wellord1(esk5_0,esk6_0,esk7_0)
    & r2_hidden(k4_tarski(esk8_0,esk9_0),esk5_0)
    & esk8_0 != esk9_0
    & ( ~ r2_hidden(k4_tarski(k1_funct_1(esk7_0,esk8_0),k1_funct_1(esk7_0,esk9_0)),esk6_0)
      | k1_funct_1(esk7_0,esk8_0) = k1_funct_1(esk7_0,esk9_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_6,plain,(
    ! [X15,X16,X17] :
      ( ( ~ v2_funct_1(X15)
        | ~ r2_hidden(X16,k1_relat_1(X15))
        | ~ r2_hidden(X17,k1_relat_1(X15))
        | k1_funct_1(X15,X16) != k1_funct_1(X15,X17)
        | X16 = X17
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( r2_hidden(esk3_1(X15),k1_relat_1(X15))
        | v2_funct_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( r2_hidden(esk4_1(X15),k1_relat_1(X15))
        | v2_funct_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( k1_funct_1(X15,esk3_1(X15)) = k1_funct_1(X15,esk4_1(X15))
        | v2_funct_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( esk3_1(X15) != esk4_1(X15)
        | v2_funct_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).

cnf(c_0_7,plain,
    ( k1_relat_1(X1) = k3_relat_1(X2)
    | ~ r3_wellord1(X2,X3,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( r3_wellord1(esk5_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,plain,
    ( v2_funct_1(X1)
    | ~ r3_wellord1(X2,X3,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(X1,X2),k1_funct_1(X1,X3)),X4)
    | ~ r2_hidden(k4_tarski(X2,X3),X5)
    | ~ r3_wellord1(X5,X4,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X5) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_0,esk9_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r3_wellord1(X2,X4,X5)
    | ~ v1_relat_1(X5)
    | ~ v1_funct_1(X5)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_17,plain,
    ( X2 = X3
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,negated_conjecture,
    ( k1_relat_1(esk7_0) = k3_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12])])).

cnf(c_0_19,negated_conjecture,
    ( v2_funct_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12])])).

cnf(c_0_20,negated_conjecture,
    ( k1_funct_1(esk7_0,esk8_0) = k1_funct_1(esk7_0,esk9_0)
    | ~ r2_hidden(k4_tarski(k1_funct_1(esk7_0,esk8_0),k1_funct_1(esk7_0,esk9_0)),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(k4_tarski(k1_funct_1(X1,esk8_0),k1_funct_1(X1,esk9_0)),X2)
    | ~ r3_wellord1(esk5_0,X2,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_11])])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk9_0,k3_relat_1(esk5_0))
    | ~ r3_wellord1(esk5_0,X1,X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_15]),c_0_11])])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r3_wellord1(X2,X4,X5)
    | ~ v1_relat_1(X5)
    | ~ v1_funct_1(X5)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_24,negated_conjecture,
    ( X1 = X2
    | k1_funct_1(esk7_0,X1) != k1_funct_1(esk7_0,X2)
    | ~ r2_hidden(X2,k3_relat_1(esk5_0))
    | ~ r2_hidden(X1,k3_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_9]),c_0_12])])).

cnf(c_0_25,negated_conjecture,
    ( k1_funct_1(esk7_0,esk9_0) = k1_funct_1(esk7_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_8]),c_0_9]),c_0_10]),c_0_12])])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk9_0,k3_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_8]),c_0_9]),c_0_12]),c_0_10])])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk8_0,k3_relat_1(esk5_0))
    | ~ r3_wellord1(esk5_0,X1,X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_15]),c_0_11])])).

cnf(c_0_28,negated_conjecture,
    ( esk9_0 = X1
    | k1_funct_1(esk7_0,esk8_0) != k1_funct_1(esk7_0,X1)
    | ~ r2_hidden(X1,k3_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk8_0,k3_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_8]),c_0_9]),c_0_12]),c_0_10])])).

cnf(c_0_30,negated_conjecture,
    ( esk8_0 != esk9_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_28]),c_0_29])]),c_0_30]),
    [proof]).

%------------------------------------------------------------------------------
