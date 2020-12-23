%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0808+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:13 EST 2020

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_wellord1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_wellord1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_wellord1)).

fof(t13_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_wellord1(X2,X1),k3_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_wellord1)).

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
    ! [X21] :
      ( v1_relat_1(esk2_0)
      & v1_relat_1(esk3_0)
      & v1_relat_1(esk4_0)
      & v1_funct_1(esk4_0)
      & v2_wellord1(esk2_0)
      & r3_wellord1(esk2_0,esk3_0,esk4_0)
      & r2_hidden(esk5_0,k3_relat_1(esk2_0))
      & ( ~ r2_hidden(X21,k3_relat_1(esk3_0))
        | ~ r4_wellord1(k2_wellord1(esk2_0,k1_wellord1(esk2_0,esk5_0)),k2_wellord1(esk3_0,k1_wellord1(esk3_0,X21))) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

fof(c_0_6,plain,(
    ! [X12,X13,X14,X15] :
      ( ( r2_hidden(esk1_4(X12,X13,X14,X15),k3_relat_1(X13))
        | ~ r2_hidden(X15,k3_relat_1(X12))
        | ~ r3_wellord1(X12,X13,X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14)
        | ~ v1_relat_1(X13)
        | ~ v1_relat_1(X12) )
      & ( k9_relat_1(X14,k1_wellord1(X12,X15)) = k1_wellord1(X13,esk1_4(X12,X13,X14,X15))
        | ~ r2_hidden(X15,k3_relat_1(X12))
        | ~ r3_wellord1(X12,X13,X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14)
        | ~ v1_relat_1(X13)
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_wellord1])])])])])).

cnf(c_0_7,negated_conjecture,
    ( ~ r2_hidden(X1,k3_relat_1(esk3_0))
    | ~ r4_wellord1(k2_wellord1(esk2_0,k1_wellord1(esk2_0,esk5_0)),k2_wellord1(esk3_0,k1_wellord1(esk3_0,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( k9_relat_1(X1,k1_wellord1(X2,X3)) = k1_wellord1(X4,esk1_4(X2,X4,X1,X3))
    | ~ r2_hidden(X3,k3_relat_1(X2))
    | ~ r3_wellord1(X2,X4,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_10,plain,(
    ! [X8,X9,X10,X11] :
      ( ( r3_wellord1(k2_wellord1(X9,X8),k2_wellord1(X10,k9_relat_1(X11,X8)),k7_relat_1(X11,X8))
        | ~ v2_wellord1(X9)
        | ~ r1_tarski(X8,k3_relat_1(X9))
        | ~ r3_wellord1(X9,X10,X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11)
        | ~ v1_relat_1(X10)
        | ~ v1_relat_1(X9) )
      & ( r4_wellord1(k2_wellord1(X9,X8),k2_wellord1(X10,k9_relat_1(X11,X8)))
        | ~ v2_wellord1(X9)
        | ~ r1_tarski(X8,k3_relat_1(X9))
        | ~ r3_wellord1(X9,X10,X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11)
        | ~ v1_relat_1(X10)
        | ~ v1_relat_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_wellord1])])])])).

cnf(c_0_11,negated_conjecture,
    ( ~ r2_hidden(esk1_4(X1,esk3_0,X2,X3),k3_relat_1(esk3_0))
    | ~ r2_hidden(X3,k3_relat_1(X1))
    | ~ r4_wellord1(k2_wellord1(esk2_0,k1_wellord1(esk2_0,esk5_0)),k2_wellord1(esk3_0,k9_relat_1(X2,k1_wellord1(X1,X3))))
    | ~ r3_wellord1(X1,esk3_0,X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
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
    ( r2_hidden(esk5_0,k3_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( v2_wellord1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,negated_conjecture,
    ( ~ r2_hidden(esk1_4(esk2_0,esk3_0,X1,esk5_0),k3_relat_1(esk3_0))
    | ~ r3_wellord1(esk2_0,esk3_0,X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(k1_wellord1(esk2_0,esk5_0),k3_relat_1(esk2_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_14]),c_0_15]),c_0_9])])).

cnf(c_0_17,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),k3_relat_1(X2))
    | ~ r2_hidden(X4,k3_relat_1(X1))
    | ~ r3_wellord1(X1,X2,X3)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_18,plain,(
    ! [X6,X7] :
      ( ~ v1_relat_1(X7)
      | r1_tarski(k1_wellord1(X7,X6),k3_relat_1(X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_wellord1])])).

cnf(c_0_19,negated_conjecture,
    ( ~ r3_wellord1(esk2_0,esk3_0,X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(k1_wellord1(esk2_0,esk5_0),k3_relat_1(esk2_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_13]),c_0_9]),c_0_14])])).

cnf(c_0_20,plain,
    ( r1_tarski(k1_wellord1(X1,X2),k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( ~ r3_wellord1(esk2_0,esk3_0,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_14])])).

cnf(c_0_22,negated_conjecture,
    ( r3_wellord1(esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_25,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24])]),
    [proof]).

%------------------------------------------------------------------------------
