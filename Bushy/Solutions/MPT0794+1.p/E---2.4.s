%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : wellord1__t45_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:14 EDT 2019

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   33 ( 158 expanded)
%              Number of clauses        :   26 (  50 expanded)
%              Number of leaves         :    3 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :  239 (1508 expanded)
%              Number of equality atoms :   37 ( 271 expanded)
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
    file('/export/starexec/sandbox/benchmark/wellord1__t45_wellord1.p',t45_wellord1)).

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
    file('/export/starexec/sandbox/benchmark/wellord1__t45_wellord1.p',d7_wellord1)).

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
    file('/export/starexec/sandbox/benchmark/wellord1__t45_wellord1.p',d8_funct_1)).

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
    ! [X15,X16,X17,X18,X19,X20,X21] :
      ( ( k1_relat_1(X17) = k3_relat_1(X15)
        | ~ r3_wellord1(X15,X16,X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15) )
      & ( k2_relat_1(X17) = k3_relat_1(X16)
        | ~ r3_wellord1(X15,X16,X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15) )
      & ( v2_funct_1(X17)
        | ~ r3_wellord1(X15,X16,X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(X18,k3_relat_1(X15))
        | ~ r2_hidden(k4_tarski(X18,X19),X15)
        | ~ r3_wellord1(X15,X16,X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(X19,k3_relat_1(X15))
        | ~ r2_hidden(k4_tarski(X18,X19),X15)
        | ~ r3_wellord1(X15,X16,X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(k4_tarski(k1_funct_1(X17,X18),k1_funct_1(X17,X19)),X16)
        | ~ r2_hidden(k4_tarski(X18,X19),X15)
        | ~ r3_wellord1(X15,X16,X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15) )
      & ( ~ r2_hidden(X20,k3_relat_1(X15))
        | ~ r2_hidden(X21,k3_relat_1(X15))
        | ~ r2_hidden(k4_tarski(k1_funct_1(X17,X20),k1_funct_1(X17,X21)),X16)
        | r2_hidden(k4_tarski(X20,X21),X15)
        | ~ r3_wellord1(X15,X16,X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15) )
      & ( ~ r2_hidden(k4_tarski(esk6_3(X15,X16,X17),esk7_3(X15,X16,X17)),X15)
        | ~ r2_hidden(esk6_3(X15,X16,X17),k3_relat_1(X15))
        | ~ r2_hidden(esk7_3(X15,X16,X17),k3_relat_1(X15))
        | ~ r2_hidden(k4_tarski(k1_funct_1(X17,esk6_3(X15,X16,X17)),k1_funct_1(X17,esk7_3(X15,X16,X17))),X16)
        | k1_relat_1(X17) != k3_relat_1(X15)
        | k2_relat_1(X17) != k3_relat_1(X16)
        | ~ v2_funct_1(X17)
        | r3_wellord1(X15,X16,X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(esk6_3(X15,X16,X17),k3_relat_1(X15))
        | r2_hidden(k4_tarski(esk6_3(X15,X16,X17),esk7_3(X15,X16,X17)),X15)
        | k1_relat_1(X17) != k3_relat_1(X15)
        | k2_relat_1(X17) != k3_relat_1(X16)
        | ~ v2_funct_1(X17)
        | r3_wellord1(X15,X16,X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(esk7_3(X15,X16,X17),k3_relat_1(X15))
        | r2_hidden(k4_tarski(esk6_3(X15,X16,X17),esk7_3(X15,X16,X17)),X15)
        | k1_relat_1(X17) != k3_relat_1(X15)
        | k2_relat_1(X17) != k3_relat_1(X16)
        | ~ v2_funct_1(X17)
        | r3_wellord1(X15,X16,X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(k4_tarski(k1_funct_1(X17,esk6_3(X15,X16,X17)),k1_funct_1(X17,esk7_3(X15,X16,X17))),X16)
        | r2_hidden(k4_tarski(esk6_3(X15,X16,X17),esk7_3(X15,X16,X17)),X15)
        | k1_relat_1(X17) != k3_relat_1(X15)
        | k2_relat_1(X17) != k3_relat_1(X16)
        | ~ v2_funct_1(X17)
        | r3_wellord1(X15,X16,X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_wellord1])])])])])])).

fof(c_0_5,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & r3_wellord1(esk1_0,esk2_0,esk3_0)
    & r2_hidden(k4_tarski(esk4_0,esk5_0),esk1_0)
    & esk4_0 != esk5_0
    & ( ~ r2_hidden(k4_tarski(k1_funct_1(esk3_0,esk4_0),k1_funct_1(esk3_0,esk5_0)),esk2_0)
      | k1_funct_1(esk3_0,esk4_0) = k1_funct_1(esk3_0,esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_6,plain,(
    ! [X24,X25,X26] :
      ( ( ~ v2_funct_1(X24)
        | ~ r2_hidden(X25,k1_relat_1(X24))
        | ~ r2_hidden(X26,k1_relat_1(X24))
        | k1_funct_1(X24,X25) != k1_funct_1(X24,X26)
        | X25 = X26
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) )
      & ( r2_hidden(esk8_1(X24),k1_relat_1(X24))
        | v2_funct_1(X24)
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) )
      & ( r2_hidden(esk9_1(X24),k1_relat_1(X24))
        | v2_funct_1(X24)
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) )
      & ( k1_funct_1(X24,esk8_1(X24)) = k1_funct_1(X24,esk9_1(X24))
        | v2_funct_1(X24)
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) )
      & ( esk8_1(X24) != esk9_1(X24)
        | v2_funct_1(X24)
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) ) ) ),
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
    ( r3_wellord1(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
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
    ( r2_hidden(k4_tarski(esk4_0,esk5_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,plain,
    ( X2 = X3
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,negated_conjecture,
    ( k1_relat_1(esk3_0) = k3_relat_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12])])).

cnf(c_0_18,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12])])).

cnf(c_0_19,negated_conjecture,
    ( k1_funct_1(esk3_0,esk4_0) = k1_funct_1(esk3_0,esk5_0)
    | ~ r2_hidden(k4_tarski(k1_funct_1(esk3_0,esk4_0),k1_funct_1(esk3_0,esk5_0)),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(k4_tarski(k1_funct_1(X1,esk4_0),k1_funct_1(X1,esk5_0)),X2)
    | ~ r3_wellord1(esk1_0,X2,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_11])])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r3_wellord1(X2,X4,X5)
    | ~ v1_relat_1(X5)
    | ~ v1_funct_1(X5)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_22,negated_conjecture,
    ( X1 = X2
    | k1_funct_1(esk3_0,X1) != k1_funct_1(esk3_0,X2)
    | ~ r2_hidden(X2,k3_relat_1(esk1_0))
    | ~ r2_hidden(X1,k3_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_9]),c_0_12])])).

cnf(c_0_23,negated_conjecture,
    ( k1_funct_1(esk3_0,esk5_0) = k1_funct_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_8]),c_0_9]),c_0_10]),c_0_12])])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk5_0,k3_relat_1(esk1_0))
    | ~ r3_wellord1(esk1_0,X1,X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_15]),c_0_11])])).

cnf(c_0_25,negated_conjecture,
    ( X1 = esk5_0
    | k1_funct_1(esk3_0,X1) != k1_funct_1(esk3_0,esk4_0)
    | ~ r2_hidden(esk5_0,k3_relat_1(esk1_0))
    | ~ r2_hidden(X1,k3_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk5_0,k3_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_8]),c_0_9]),c_0_12]),c_0_10])])).

cnf(c_0_27,negated_conjecture,
    ( X1 = esk5_0
    | k1_funct_1(esk3_0,X1) != k1_funct_1(esk3_0,esk4_0)
    | ~ r2_hidden(X1,k3_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26])])).

cnf(c_0_28,negated_conjecture,
    ( esk4_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r3_wellord1(X2,X4,X5)
    | ~ v1_relat_1(X5)
    | ~ v1_funct_1(X5)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_30,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k3_relat_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_27]),c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( ~ r3_wellord1(esk1_0,X1,X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_15]),c_0_11])]),c_0_30])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_8]),c_0_9]),c_0_12]),c_0_10])]),
    [proof]).
%------------------------------------------------------------------------------
