%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0710+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:04 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   61 (1693 expanded)
%              Number of clauses        :   46 ( 664 expanded)
%              Number of leaves         :    7 ( 405 expanded)
%              Depth                    :   18
%              Number of atoms          :  184 (9398 expanded)
%              Number of equality atoms :   76 (2749 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t165_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ! [X3] :
              ( ( r1_tarski(X3,k1_relat_1(X1))
                & r1_tarski(X3,k1_relat_1(X2)) )
             => ( k7_relat_1(X1,X3) = k7_relat_1(X2,X3)
              <=> ! [X4] :
                    ( r2_hidden(X4,X3)
                   => k1_funct_1(X1,X4) = k1_funct_1(X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t165_funct_1)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(fc8_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k7_relat_1(X1,X2))
        & v1_funct_1(k7_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

fof(t9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( k1_relat_1(X1) = k1_relat_1(X2)
              & ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

fof(t72_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,X2)
       => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_funct_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ! [X3] :
                ( ( r1_tarski(X3,k1_relat_1(X1))
                  & r1_tarski(X3,k1_relat_1(X2)) )
               => ( k7_relat_1(X1,X3) = k7_relat_1(X2,X3)
                <=> ! [X4] :
                      ( r2_hidden(X4,X3)
                     => k1_funct_1(X1,X4) = k1_funct_1(X2,X4) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t165_funct_1])).

fof(c_0_8,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X15)
      | k1_relat_1(k7_relat_1(X15,X14)) = k3_xboole_0(k1_relat_1(X15),X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

fof(c_0_9,negated_conjecture,(
    ! [X23] :
      ( v1_relat_1(esk2_0)
      & v1_funct_1(esk2_0)
      & v1_relat_1(esk3_0)
      & v1_funct_1(esk3_0)
      & r1_tarski(esk4_0,k1_relat_1(esk2_0))
      & r1_tarski(esk4_0,k1_relat_1(esk3_0))
      & ( r2_hidden(esk5_0,esk4_0)
        | k7_relat_1(esk2_0,esk4_0) != k7_relat_1(esk3_0,esk4_0) )
      & ( k1_funct_1(esk2_0,esk5_0) != k1_funct_1(esk3_0,esk5_0)
        | k7_relat_1(esk2_0,esk4_0) != k7_relat_1(esk3_0,esk4_0) )
      & ( k7_relat_1(esk2_0,esk4_0) = k7_relat_1(esk3_0,esk4_0)
        | ~ r2_hidden(X23,esk4_0)
        | k1_funct_1(esk2_0,X23) = k1_funct_1(esk3_0,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])])).

fof(c_0_10,plain,(
    ! [X9,X10] :
      ( ~ r1_tarski(X9,X10)
      | k3_xboole_0(X9,X10) = X9 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_11,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_12,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(esk4_0,k1_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( k3_xboole_0(k1_relat_1(esk3_0),X1) = k1_relat_1(k7_relat_1(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_18,plain,(
    ! [X7,X8] :
      ( ( v1_relat_1(k7_relat_1(X7,X8))
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) )
      & ( v1_funct_1(k7_relat_1(X7,X8))
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_20,plain,(
    ! [X16,X17] :
      ( ( r2_hidden(esk1_2(X16,X17),k1_relat_1(X16))
        | k1_relat_1(X16) != k1_relat_1(X17)
        | X16 = X17
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( k1_funct_1(X16,esk1_2(X16,X17)) != k1_funct_1(X17,esk1_2(X16,X17))
        | k1_relat_1(X16) != k1_relat_1(X17)
        | X16 = X17
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_1])])])])])).

cnf(c_0_21,negated_conjecture,
    ( k3_xboole_0(esk4_0,k1_relat_1(esk3_0)) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( k3_xboole_0(X1,k1_relat_1(esk3_0)) = k1_relat_1(k7_relat_1(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(esk4_0,k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,negated_conjecture,
    ( k3_xboole_0(k1_relat_1(esk2_0),X1) = k1_relat_1(k7_relat_1(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_19])).

cnf(c_0_27,plain,
    ( r2_hidden(esk1_2(X1,X2),k1_relat_1(X1))
    | X1 = X2
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk3_0,esk4_0)) = esk4_0 ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk3_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_13])])).

cnf(c_0_30,negated_conjecture,
    ( k3_xboole_0(esk4_0,k1_relat_1(esk2_0)) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_14,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( k3_xboole_0(X1,k1_relat_1(esk2_0)) = k1_relat_1(k7_relat_1(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_33,negated_conjecture,
    ( X1 = k7_relat_1(esk3_0,esk4_0)
    | r2_hidden(esk1_2(X1,k7_relat_1(esk3_0,esk4_0)),k1_relat_1(X1))
    | k1_relat_1(X1) != esk4_0
    | ~ v1_funct_1(k7_relat_1(esk3_0,esk4_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])).

cnf(c_0_34,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,esk4_0)) = esk4_0 ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk2_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_32]),c_0_19])])).

cnf(c_0_36,plain,
    ( X1 = X2
    | k1_funct_1(X1,esk1_2(X1,X2)) != k1_funct_1(X2,esk1_2(X1,X2))
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_37,negated_conjecture,
    ( k7_relat_1(esk2_0,esk4_0) = k7_relat_1(esk3_0,esk4_0)
    | r2_hidden(esk1_2(k7_relat_1(esk2_0,esk4_0),k7_relat_1(esk3_0,esk4_0)),esk4_0)
    | ~ v1_funct_1(k7_relat_1(esk3_0,esk4_0))
    | ~ v1_funct_1(k7_relat_1(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

cnf(c_0_38,plain,
    ( v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_39,negated_conjecture,
    ( X1 = k7_relat_1(esk3_0,esk4_0)
    | k1_funct_1(X1,esk1_2(X1,k7_relat_1(esk3_0,esk4_0))) != k1_funct_1(k7_relat_1(esk3_0,esk4_0),esk1_2(X1,k7_relat_1(esk3_0,esk4_0)))
    | k1_relat_1(X1) != esk4_0
    | ~ v1_funct_1(k7_relat_1(esk3_0,esk4_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_28]),c_0_29])])).

fof(c_0_40,plain,(
    ! [X11,X12,X13] :
      ( ~ v1_relat_1(X13)
      | ~ v1_funct_1(X13)
      | ~ r2_hidden(X11,X12)
      | k1_funct_1(k7_relat_1(X13,X12),X11) = k1_funct_1(X13,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t72_funct_1])])).

cnf(c_0_41,negated_conjecture,
    ( k7_relat_1(esk2_0,esk4_0) = k7_relat_1(esk3_0,esk4_0)
    | r2_hidden(esk1_2(k7_relat_1(esk2_0,esk4_0),k7_relat_1(esk3_0,esk4_0)),esk4_0)
    | ~ v1_funct_1(k7_relat_1(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_24]),c_0_13])])).

cnf(c_0_42,negated_conjecture,
    ( X1 = k7_relat_1(esk3_0,esk4_0)
    | k1_funct_1(X1,esk1_2(X1,k7_relat_1(esk3_0,esk4_0))) != k1_funct_1(k7_relat_1(esk3_0,esk4_0),esk1_2(X1,k7_relat_1(esk3_0,esk4_0)))
    | k1_relat_1(X1) != esk4_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_38]),c_0_24]),c_0_13])])).

cnf(c_0_43,plain,
    ( k1_funct_1(k7_relat_1(X1,X3),X2) = k1_funct_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( k7_relat_1(esk2_0,esk4_0) = k7_relat_1(esk3_0,esk4_0)
    | r2_hidden(esk1_2(k7_relat_1(esk2_0,esk4_0),k7_relat_1(esk3_0,esk4_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_38]),c_0_32]),c_0_19])])).

cnf(c_0_45,negated_conjecture,
    ( k7_relat_1(esk2_0,esk4_0) = k7_relat_1(esk3_0,esk4_0)
    | k1_funct_1(k7_relat_1(esk2_0,esk4_0),esk1_2(k7_relat_1(esk2_0,esk4_0),k7_relat_1(esk3_0,esk4_0))) != k1_funct_1(k7_relat_1(esk3_0,esk4_0),esk1_2(k7_relat_1(esk2_0,esk4_0),k7_relat_1(esk3_0,esk4_0)))
    | ~ v1_funct_1(k7_relat_1(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_34]),c_0_35])])).

cnf(c_0_46,negated_conjecture,
    ( k1_funct_1(k7_relat_1(X1,esk4_0),esk1_2(k7_relat_1(esk2_0,esk4_0),k7_relat_1(esk3_0,esk4_0))) = k1_funct_1(X1,esk1_2(k7_relat_1(esk2_0,esk4_0),k7_relat_1(esk3_0,esk4_0)))
    | k7_relat_1(esk2_0,esk4_0) = k7_relat_1(esk3_0,esk4_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( k7_relat_1(esk2_0,esk4_0) = k7_relat_1(esk3_0,esk4_0)
    | k1_funct_1(k7_relat_1(esk2_0,esk4_0),esk1_2(k7_relat_1(esk2_0,esk4_0),k7_relat_1(esk3_0,esk4_0))) != k1_funct_1(k7_relat_1(esk3_0,esk4_0),esk1_2(k7_relat_1(esk2_0,esk4_0),k7_relat_1(esk3_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_38]),c_0_32]),c_0_19])])).

cnf(c_0_48,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk2_0,esk4_0),esk1_2(k7_relat_1(esk2_0,esk4_0),k7_relat_1(esk3_0,esk4_0))) = k1_funct_1(esk2_0,esk1_2(k7_relat_1(esk2_0,esk4_0),k7_relat_1(esk3_0,esk4_0)))
    | k7_relat_1(esk2_0,esk4_0) = k7_relat_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_32]),c_0_19])])).

cnf(c_0_49,negated_conjecture,
    ( k7_relat_1(esk2_0,esk4_0) = k7_relat_1(esk3_0,esk4_0)
    | k1_funct_1(esk2_0,X1) = k1_funct_1(esk3_0,X1)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_50,negated_conjecture,
    ( k7_relat_1(esk2_0,esk4_0) = k7_relat_1(esk3_0,esk4_0)
    | k1_funct_1(k7_relat_1(esk3_0,esk4_0),esk1_2(k7_relat_1(esk2_0,esk4_0),k7_relat_1(esk3_0,esk4_0))) != k1_funct_1(esk2_0,esk1_2(k7_relat_1(esk2_0,esk4_0),k7_relat_1(esk3_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk3_0,esk4_0),esk1_2(k7_relat_1(esk2_0,esk4_0),k7_relat_1(esk3_0,esk4_0))) = k1_funct_1(esk3_0,esk1_2(k7_relat_1(esk2_0,esk4_0),k7_relat_1(esk3_0,esk4_0)))
    | k7_relat_1(esk2_0,esk4_0) = k7_relat_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_24]),c_0_13])])).

cnf(c_0_52,negated_conjecture,
    ( k1_funct_1(esk2_0,esk1_2(k7_relat_1(esk2_0,esk4_0),k7_relat_1(esk3_0,esk4_0))) = k1_funct_1(esk3_0,esk1_2(k7_relat_1(esk2_0,esk4_0),k7_relat_1(esk3_0,esk4_0)))
    | k7_relat_1(esk2_0,esk4_0) = k7_relat_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0)
    | k7_relat_1(esk2_0,esk4_0) != k7_relat_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_54,negated_conjecture,
    ( k7_relat_1(esk2_0,esk4_0) = k7_relat_1(esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54])])).

cnf(c_0_56,negated_conjecture,
    ( k1_funct_1(k7_relat_1(X1,esk4_0),esk5_0) = k1_funct_1(X1,esk5_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_55])).

cnf(c_0_57,negated_conjecture,
    ( k1_funct_1(esk2_0,esk5_0) != k1_funct_1(esk3_0,esk5_0)
    | k7_relat_1(esk2_0,esk4_0) != k7_relat_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_58,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk3_0,esk4_0),esk5_0) = k1_funct_1(esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_24]),c_0_13])])).

cnf(c_0_59,negated_conjecture,
    ( k1_funct_1(esk2_0,esk5_0) != k1_funct_1(esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_54])])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_32]),c_0_54]),c_0_19])]),c_0_58]),c_0_59]),
    [proof]).

%------------------------------------------------------------------------------
