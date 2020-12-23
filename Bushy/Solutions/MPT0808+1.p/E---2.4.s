%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : wellord1__t61_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:15 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   26 (  69 expanded)
%              Number of clauses        :   17 (  22 expanded)
%              Number of leaves         :    4 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :  131 ( 482 expanded)
%              Number of equality atoms :    3 (   5 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t61_wellord1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( ( v1_relat_1(X3)
                & v1_funct_1(X3) )
             => ( ( v2_wellord1(X1)
                  & r3_wellord1(X1,X2,X3) )
               => ! [X4] :
                    ~ ( r2_hidden(X4,k3_relat_1(X1))
                      & ! [X5] :
                          ~ ( r2_hidden(X5,k3_relat_1(X2))
                            & r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,X4)),k2_wellord1(X2,k1_wellord1(X2,X5))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t61_wellord1.p',t61_wellord1)).

fof(t60_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( ( v1_relat_1(X3)
                & v1_funct_1(X3) )
             => ( r3_wellord1(X1,X2,X3)
               => ! [X4] :
                    ~ ( r2_hidden(X4,k3_relat_1(X1))
                      & ! [X5] :
                          ~ ( r2_hidden(X5,k3_relat_1(X2))
                            & k9_relat_1(X3,k1_wellord1(X1,X4)) = k1_wellord1(X2,X5) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t61_wellord1.p',t60_wellord1)).

fof(t59_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ! [X4] :
              ( ( v1_relat_1(X4)
                & v1_funct_1(X4) )
             => ( ( v2_wellord1(X2)
                  & r1_tarski(X1,k3_relat_1(X2))
                  & r3_wellord1(X2,X3,X4) )
               => ( r3_wellord1(k2_wellord1(X2,X1),k2_wellord1(X3,k9_relat_1(X4,X1)),k7_relat_1(X4,X1))
                  & r4_wellord1(k2_wellord1(X2,X1),k2_wellord1(X3,k9_relat_1(X4,X1))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t61_wellord1.p',t59_wellord1)).

fof(t13_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_wellord1(X2,X1),k3_relat_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t61_wellord1.p',t13_wellord1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3] :
                ( ( v1_relat_1(X3)
                  & v1_funct_1(X3) )
               => ( ( v2_wellord1(X1)
                    & r3_wellord1(X1,X2,X3) )
                 => ! [X4] :
                      ~ ( r2_hidden(X4,k3_relat_1(X1))
                        & ! [X5] :
                            ~ ( r2_hidden(X5,k3_relat_1(X2))
                              & r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,X4)),k2_wellord1(X2,k1_wellord1(X2,X5))) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t61_wellord1])).

fof(c_0_5,negated_conjecture,(
    ! [X10] :
      ( v1_relat_1(esk1_0)
      & v1_relat_1(esk2_0)
      & v1_relat_1(esk3_0)
      & v1_funct_1(esk3_0)
      & v2_wellord1(esk1_0)
      & r3_wellord1(esk1_0,esk2_0,esk3_0)
      & r2_hidden(esk4_0,k3_relat_1(esk1_0))
      & ( ~ r2_hidden(X10,k3_relat_1(esk2_0))
        | ~ r4_wellord1(k2_wellord1(esk1_0,k1_wellord1(esk1_0,esk4_0)),k2_wellord1(esk2_0,k1_wellord1(esk2_0,X10))) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

fof(c_0_6,plain,(
    ! [X48,X49,X50,X51] :
      ( ( r2_hidden(esk6_4(X48,X49,X50,X51),k3_relat_1(X49))
        | ~ r2_hidden(X51,k3_relat_1(X48))
        | ~ r3_wellord1(X48,X49,X50)
        | ~ v1_relat_1(X50)
        | ~ v1_funct_1(X50)
        | ~ v1_relat_1(X49)
        | ~ v1_relat_1(X48) )
      & ( k9_relat_1(X50,k1_wellord1(X48,X51)) = k1_wellord1(X49,esk6_4(X48,X49,X50,X51))
        | ~ r2_hidden(X51,k3_relat_1(X48))
        | ~ r3_wellord1(X48,X49,X50)
        | ~ v1_relat_1(X50)
        | ~ v1_funct_1(X50)
        | ~ v1_relat_1(X49)
        | ~ v1_relat_1(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_wellord1])])])])])).

cnf(c_0_7,negated_conjecture,
    ( ~ r2_hidden(X1,k3_relat_1(esk2_0))
    | ~ r4_wellord1(k2_wellord1(esk1_0,k1_wellord1(esk1_0,esk4_0)),k2_wellord1(esk2_0,k1_wellord1(esk2_0,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( k9_relat_1(X1,k1_wellord1(X2,X3)) = k1_wellord1(X4,esk6_4(X2,X4,X1,X3))
    | ~ r2_hidden(X3,k3_relat_1(X2))
    | ~ r3_wellord1(X2,X4,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_10,plain,(
    ! [X41,X42,X43,X44] :
      ( ( r3_wellord1(k2_wellord1(X42,X41),k2_wellord1(X43,k9_relat_1(X44,X41)),k7_relat_1(X44,X41))
        | ~ v2_wellord1(X42)
        | ~ r1_tarski(X41,k3_relat_1(X42))
        | ~ r3_wellord1(X42,X43,X44)
        | ~ v1_relat_1(X44)
        | ~ v1_funct_1(X44)
        | ~ v1_relat_1(X43)
        | ~ v1_relat_1(X42) )
      & ( r4_wellord1(k2_wellord1(X42,X41),k2_wellord1(X43,k9_relat_1(X44,X41)))
        | ~ v2_wellord1(X42)
        | ~ r1_tarski(X41,k3_relat_1(X42))
        | ~ r3_wellord1(X42,X43,X44)
        | ~ v1_relat_1(X44)
        | ~ v1_funct_1(X44)
        | ~ v1_relat_1(X43)
        | ~ v1_relat_1(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_wellord1])])])])).

cnf(c_0_11,negated_conjecture,
    ( ~ r4_wellord1(k2_wellord1(esk1_0,k1_wellord1(esk1_0,esk4_0)),k2_wellord1(esk2_0,k9_relat_1(X1,k1_wellord1(X2,X3))))
    | ~ r2_hidden(esk6_4(X2,esk2_0,X1,X3),k3_relat_1(esk2_0))
    | ~ r2_hidden(X3,k3_relat_1(X2))
    | ~ r3_wellord1(X2,esk2_0,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9])])).

cnf(c_0_12,plain,
    ( r4_wellord1(k2_wellord1(X1,X2),k2_wellord1(X3,k9_relat_1(X4,X2)))
    | ~ v2_wellord1(X1)
    | ~ r1_tarski(X2,k3_relat_1(X1))
    | ~ r3_wellord1(X1,X3,X4)
    | ~ v1_relat_1(X4)
    | ~ v1_funct_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk4_0,k3_relat_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( v2_wellord1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_16,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X29)
      | r1_tarski(k1_wellord1(X29,X28),k3_relat_1(X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_wellord1])])).

cnf(c_0_17,negated_conjecture,
    ( ~ r1_tarski(k1_wellord1(esk1_0,esk4_0),k3_relat_1(esk1_0))
    | ~ r2_hidden(esk6_4(esk1_0,esk2_0,X1,esk4_0),k3_relat_1(esk2_0))
    | ~ r3_wellord1(esk1_0,esk2_0,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_14]),c_0_15]),c_0_9])])).

cnf(c_0_18,plain,
    ( r1_tarski(k1_wellord1(X1,X2),k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( ~ r2_hidden(esk6_4(esk1_0,esk2_0,X1,esk4_0),k3_relat_1(esk2_0))
    | ~ r3_wellord1(esk1_0,esk2_0,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_14])])).

cnf(c_0_20,plain,
    ( r2_hidden(esk6_4(X1,X2,X3,X4),k3_relat_1(X2))
    | ~ r2_hidden(X4,k3_relat_1(X1))
    | ~ r3_wellord1(X1,X2,X3)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_21,negated_conjecture,
    ( ~ r3_wellord1(esk1_0,esk2_0,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_13]),c_0_9]),c_0_14])])).

cnf(c_0_22,negated_conjecture,
    ( r3_wellord1(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_25,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24])]),
    [proof]).
%------------------------------------------------------------------------------
