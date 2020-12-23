%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:36 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 679 expanded)
%              Number of clauses        :   43 ( 277 expanded)
%              Number of leaves         :   11 ( 174 expanded)
%              Depth                    :   12
%              Number of atoms          :  193 (2261 expanded)
%              Number of equality atoms :   68 ( 992 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   25 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(t166_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ! [X3] :
              ( ( k1_relat_1(X1) = k1_relat_1(X2)
                & ! [X4] :
                    ( r2_hidden(X4,X3)
                   => k1_funct_1(X1,X4) = k1_funct_1(X2,X4) ) )
             => k7_relat_1(X1,X3) = k7_relat_1(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_funct_1)).

fof(s3_funct_1__e9_44_1__funct_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( v1_relat_1(X2)
      & v1_funct_1(X2)
      & k1_relat_1(X2) = X1
      & ! [X3] :
          ( r2_hidden(X3,X1)
         => k1_funct_1(X2,X3) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e9_44_1__funct_1)).

fof(t91_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => k1_relat_1(k7_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(t89_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).

fof(t189_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k7_relat_1(X1,k1_relat_1(X2)) = k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,k1_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_relat_1)).

fof(t165_funct_1,axiom,(
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

fof(t86_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X1,k1_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

fof(c_0_11,plain,(
    ! [X9,X10] : k1_setfam_1(k2_tarski(X9,X10)) = k3_xboole_0(X9,X10) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_12,plain,(
    ! [X7,X8] : k1_enumset1(X7,X7,X8) = k2_tarski(X7,X8) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_14,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X19)
      | k1_relat_1(k7_relat_1(X19,X18)) = k3_xboole_0(k1_relat_1(X19),X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ! [X3] :
                ( ( k1_relat_1(X1) = k1_relat_1(X2)
                  & ! [X4] :
                      ( r2_hidden(X4,X3)
                     => k1_funct_1(X1,X4) = k1_funct_1(X2,X4) ) )
               => k7_relat_1(X1,X3) = k7_relat_1(X2,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t166_funct_1])).

cnf(c_0_18,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X22,X24] :
      ( v1_relat_1(esk1_1(X22))
      & v1_funct_1(esk1_1(X22))
      & k1_relat_1(esk1_1(X22)) = X22
      & ( ~ r2_hidden(X24,X22)
        | k1_funct_1(esk1_1(X22),X24) = k1_xboole_0 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e9_44_1__funct_1])])])])).

fof(c_0_22,negated_conjecture,(
    ! [X33] :
      ( v1_relat_1(esk3_0)
      & v1_funct_1(esk3_0)
      & v1_relat_1(esk4_0)
      & v1_funct_1(esk4_0)
      & k1_relat_1(esk3_0) = k1_relat_1(esk4_0)
      & ( ~ r2_hidden(X33,esk5_0)
        | k1_funct_1(esk3_0,X33) = k1_funct_1(esk4_0,X33) )
      & k7_relat_1(esk3_0,esk5_0) != k7_relat_1(esk4_0,esk5_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])])).

fof(c_0_23,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X21)
      | ~ r1_tarski(X20,k1_relat_1(X21))
      | k1_relat_1(k7_relat_1(X21,X20)) = X20 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).

cnf(c_0_24,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k1_setfam_1(k1_enumset1(X2,X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_19])).

cnf(c_0_25,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_20,c_0_19])).

cnf(c_0_26,plain,
    ( k1_relat_1(esk1_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( v1_relat_1(esk1_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( k1_relat_1(esk3_0) = k1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_31,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X17)
      | r1_tarski(k1_relat_1(k7_relat_1(X17,X16)),k1_relat_1(X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t89_relat_1])])).

cnf(c_0_32,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,k1_relat_1(X2))) = k1_relat_1(k7_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k1_relat_1(k7_relat_1(esk1_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

cnf(c_0_34,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(esk3_0),k1_relat_1(esk3_0),X1)) = k1_relat_1(k7_relat_1(esk4_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_28]),c_0_29])])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk4_0,X1)) = X1
    | ~ r1_tarski(X1,k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_28]),c_0_29])])).

cnf(c_0_37,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_38,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X11)
      | ~ v1_relat_1(X12)
      | k7_relat_1(X11,k1_relat_1(X12)) = k7_relat_1(X11,k1_relat_1(k7_relat_1(X12,k1_relat_1(X11)))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t189_relat_1])])])).

cnf(c_0_39,plain,
    ( k1_relat_1(k7_relat_1(esk1_1(X1),k1_relat_1(X2))) = k1_relat_1(k7_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk4_0,X1)) = k1_relat_1(k7_relat_1(esk3_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_34]),c_0_35])])).

fof(c_0_41,plain,(
    ! [X25,X26,X27,X28] :
      ( ( k7_relat_1(X25,X27) != k7_relat_1(X26,X27)
        | ~ r2_hidden(X28,X27)
        | k1_funct_1(X25,X28) = k1_funct_1(X26,X28)
        | ~ r1_tarski(X27,k1_relat_1(X25))
        | ~ r1_tarski(X27,k1_relat_1(X26))
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( r2_hidden(esk2_3(X25,X26,X27),X27)
        | k7_relat_1(X25,X27) = k7_relat_1(X26,X27)
        | ~ r1_tarski(X27,k1_relat_1(X25))
        | ~ r1_tarski(X27,k1_relat_1(X26))
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( k1_funct_1(X25,esk2_3(X25,X26,X27)) != k1_funct_1(X26,esk2_3(X25,X26,X27))
        | k7_relat_1(X25,X27) = k7_relat_1(X26,X27)
        | ~ r1_tarski(X27,k1_relat_1(X25))
        | ~ r1_tarski(X27,k1_relat_1(X26))
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t165_funct_1])])])])])).

cnf(c_0_42,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk4_0,k1_relat_1(k7_relat_1(esk3_0,X1)))) = k1_relat_1(k7_relat_1(esk3_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_35])])).

cnf(c_0_43,plain,
    ( k7_relat_1(X1,k1_relat_1(X2)) = k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,k1_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk1_1(X1),k1_relat_1(esk3_0))) = k1_relat_1(k7_relat_1(esk3_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_28]),c_0_40]),c_0_29])])).

cnf(c_0_45,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(esk3_0),k1_relat_1(esk3_0),X1)) = k1_relat_1(k7_relat_1(esk3_0,X1)) ),
    inference(rw,[status(thm)],[c_0_34,c_0_40])).

cnf(c_0_46,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | k7_relat_1(X1,X3) = k7_relat_1(X2,X3)
    | ~ r1_tarski(X3,k1_relat_1(X1))
    | ~ r1_tarski(X3,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk3_0,X1)),k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_42]),c_0_28]),c_0_29])])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_49,negated_conjecture,
    ( k7_relat_1(esk3_0,k1_relat_1(k7_relat_1(esk3_0,X1))) = k7_relat_1(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_26]),c_0_27]),c_0_35])])).

cnf(c_0_50,negated_conjecture,
    ( k7_relat_1(esk4_0,k1_relat_1(k7_relat_1(X1,k1_relat_1(esk3_0)))) = k7_relat_1(esk4_0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_28]),c_0_29])])).

cnf(c_0_51,plain,
    ( k1_relat_1(k7_relat_1(esk1_1(X1),X2)) = k1_relat_1(k7_relat_1(esk1_1(X2),X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_33]),c_0_33])).

cnf(c_0_52,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk1_1(k1_relat_1(esk3_0)),X1)) = k1_relat_1(k7_relat_1(esk3_0,X1)) ),
    inference(rw,[status(thm)],[c_0_45,c_0_33])).

cnf(c_0_53,plain,
    ( k7_relat_1(X1,X3) = k7_relat_1(X2,X3)
    | k1_funct_1(X1,esk2_3(X1,X2,X3)) != k1_funct_1(X2,esk2_3(X1,X2,X3))
    | ~ r1_tarski(X3,k1_relat_1(X1))
    | ~ r1_tarski(X3,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_54,negated_conjecture,
    ( k1_funct_1(esk3_0,X1) = k1_funct_1(esk4_0,X1)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_55,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_56,plain,(
    ! [X13,X14,X15] :
      ( ( r2_hidden(X13,X14)
        | ~ r2_hidden(X13,k1_relat_1(k7_relat_1(X15,X14)))
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(X13,k1_relat_1(X15))
        | ~ r2_hidden(X13,k1_relat_1(k7_relat_1(X15,X14)))
        | ~ v1_relat_1(X15) )
      & ( ~ r2_hidden(X13,X14)
        | ~ r2_hidden(X13,k1_relat_1(X15))
        | r2_hidden(X13,k1_relat_1(k7_relat_1(X15,X14)))
        | ~ v1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).

cnf(c_0_57,negated_conjecture,
    ( k7_relat_1(X1,k1_relat_1(k7_relat_1(esk3_0,X2))) = k7_relat_1(esk3_0,X2)
    | r2_hidden(esk2_3(X1,esk3_0,k1_relat_1(k7_relat_1(esk3_0,X2))),k1_relat_1(k7_relat_1(esk3_0,X2)))
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(esk3_0,X2)),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_35])]),c_0_49])).

cnf(c_0_58,negated_conjecture,
    ( k7_relat_1(esk4_0,k1_relat_1(k7_relat_1(esk3_0,X1))) = k7_relat_1(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_26]),c_0_27])])).

cnf(c_0_59,negated_conjecture,
    ( k7_relat_1(esk4_0,X1) = k7_relat_1(X2,X1)
    | k1_funct_1(esk3_0,esk2_3(esk4_0,X2,X1)) != k1_funct_1(X2,esk2_3(esk4_0,X2,X1))
    | ~ v1_funct_1(X2)
    | ~ r1_tarski(X1,k1_relat_1(esk3_0))
    | ~ r1_tarski(X1,k1_relat_1(X2))
    | ~ r2_hidden(esk2_3(esk4_0,X2,X1),esk5_0)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),c_0_28]),c_0_29])])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( k7_relat_1(esk4_0,X1) = k7_relat_1(esk3_0,X1)
    | r2_hidden(esk2_3(esk4_0,esk3_0,k1_relat_1(k7_relat_1(esk3_0,X1))),k1_relat_1(k7_relat_1(esk3_0,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_28]),c_0_58]),c_0_55]),c_0_47]),c_0_29])])).

cnf(c_0_62,negated_conjecture,
    ( k7_relat_1(esk4_0,X1) = k7_relat_1(esk3_0,X1)
    | ~ r1_tarski(X1,k1_relat_1(esk3_0))
    | ~ r2_hidden(esk2_3(esk4_0,esk3_0,X1),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_59]),c_0_48]),c_0_35])])).

cnf(c_0_63,negated_conjecture,
    ( k7_relat_1(esk4_0,X1) = k7_relat_1(esk3_0,X1)
    | r2_hidden(esk2_3(esk4_0,esk3_0,k1_relat_1(k7_relat_1(esk3_0,X1))),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_35])])).

cnf(c_0_64,negated_conjecture,
    ( k7_relat_1(esk3_0,esk5_0) != k7_relat_1(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_58]),c_0_49]),c_0_47])]),c_0_64]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n014.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 15:10:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 2.27/2.49  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 2.27/2.49  # and selection function SelectComplexExceptUniqMaxHorn.
% 2.27/2.49  #
% 2.27/2.49  # Preprocessing time       : 0.045 s
% 2.27/2.49  # Presaturation interreduction done
% 2.27/2.49  
% 2.27/2.49  # Proof found!
% 2.27/2.49  # SZS status Theorem
% 2.27/2.49  # SZS output start CNFRefutation
% 2.27/2.49  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.27/2.49  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.27/2.49  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.27/2.49  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 2.27/2.49  fof(t166_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((k1_relat_1(X1)=k1_relat_1(X2)&![X4]:(r2_hidden(X4,X3)=>k1_funct_1(X1,X4)=k1_funct_1(X2,X4)))=>k7_relat_1(X1,X3)=k7_relat_1(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_funct_1)).
% 2.27/2.49  fof(s3_funct_1__e9_44_1__funct_1, axiom, ![X1]:?[X2]:(((v1_relat_1(X2)&v1_funct_1(X2))&k1_relat_1(X2)=X1)&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e9_44_1__funct_1)).
% 2.27/2.49  fof(t91_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>k1_relat_1(k7_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 2.27/2.49  fof(t89_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),k1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_relat_1)).
% 2.27/2.49  fof(t189_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k7_relat_1(X1,k1_relat_1(X2))=k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,k1_relat_1(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t189_relat_1)).
% 2.27/2.49  fof(t165_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((r1_tarski(X3,k1_relat_1(X1))&r1_tarski(X3,k1_relat_1(X2)))=>(k7_relat_1(X1,X3)=k7_relat_1(X2,X3)<=>![X4]:(r2_hidden(X4,X3)=>k1_funct_1(X1,X4)=k1_funct_1(X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t165_funct_1)).
% 2.27/2.49  fof(t86_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))<=>(r2_hidden(X1,X2)&r2_hidden(X1,k1_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 2.27/2.49  fof(c_0_11, plain, ![X9, X10]:k1_setfam_1(k2_tarski(X9,X10))=k3_xboole_0(X9,X10), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 2.27/2.49  fof(c_0_12, plain, ![X7, X8]:k1_enumset1(X7,X7,X8)=k2_tarski(X7,X8), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 2.27/2.49  fof(c_0_13, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 2.27/2.49  cnf(c_0_14, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.27/2.49  cnf(c_0_15, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 2.27/2.49  fof(c_0_16, plain, ![X18, X19]:(~v1_relat_1(X19)|k1_relat_1(k7_relat_1(X19,X18))=k3_xboole_0(k1_relat_1(X19),X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 2.27/2.49  fof(c_0_17, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((k1_relat_1(X1)=k1_relat_1(X2)&![X4]:(r2_hidden(X4,X3)=>k1_funct_1(X1,X4)=k1_funct_1(X2,X4)))=>k7_relat_1(X1,X3)=k7_relat_1(X2,X3))))), inference(assume_negation,[status(cth)],[t166_funct_1])).
% 2.27/2.49  cnf(c_0_18, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.27/2.49  cnf(c_0_19, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 2.27/2.49  cnf(c_0_20, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.27/2.49  fof(c_0_21, plain, ![X22, X24]:(((v1_relat_1(esk1_1(X22))&v1_funct_1(esk1_1(X22)))&k1_relat_1(esk1_1(X22))=X22)&(~r2_hidden(X24,X22)|k1_funct_1(esk1_1(X22),X24)=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e9_44_1__funct_1])])])])).
% 2.27/2.49  fof(c_0_22, negated_conjecture, ![X33]:((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&((k1_relat_1(esk3_0)=k1_relat_1(esk4_0)&(~r2_hidden(X33,esk5_0)|k1_funct_1(esk3_0,X33)=k1_funct_1(esk4_0,X33)))&k7_relat_1(esk3_0,esk5_0)!=k7_relat_1(esk4_0,esk5_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])])).
% 2.27/2.49  fof(c_0_23, plain, ![X20, X21]:(~v1_relat_1(X21)|(~r1_tarski(X20,k1_relat_1(X21))|k1_relat_1(k7_relat_1(X21,X20))=X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).
% 2.27/2.49  cnf(c_0_24, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k1_setfam_1(k1_enumset1(X2,X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_19])).
% 2.27/2.49  cnf(c_0_25, plain, (k1_relat_1(k7_relat_1(X1,X2))=k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_20, c_0_19])).
% 2.27/2.49  cnf(c_0_26, plain, (k1_relat_1(esk1_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 2.27/2.49  cnf(c_0_27, plain, (v1_relat_1(esk1_1(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 2.27/2.49  cnf(c_0_28, negated_conjecture, (k1_relat_1(esk3_0)=k1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.27/2.49  cnf(c_0_29, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.27/2.49  cnf(c_0_30, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.27/2.49  fof(c_0_31, plain, ![X16, X17]:(~v1_relat_1(X17)|r1_tarski(k1_relat_1(k7_relat_1(X17,X16)),k1_relat_1(X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t89_relat_1])])).
% 2.27/2.49  cnf(c_0_32, plain, (k1_setfam_1(k1_enumset1(X1,X1,k1_relat_1(X2)))=k1_relat_1(k7_relat_1(X2,X1))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 2.27/2.49  cnf(c_0_33, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k1_relat_1(k7_relat_1(esk1_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])])).
% 2.27/2.49  cnf(c_0_34, negated_conjecture, (k1_setfam_1(k1_enumset1(k1_relat_1(esk3_0),k1_relat_1(esk3_0),X1))=k1_relat_1(k7_relat_1(esk4_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_28]), c_0_29])])).
% 2.27/2.49  cnf(c_0_35, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.27/2.49  cnf(c_0_36, negated_conjecture, (k1_relat_1(k7_relat_1(esk4_0,X1))=X1|~r1_tarski(X1,k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_28]), c_0_29])])).
% 2.27/2.49  cnf(c_0_37, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 2.27/2.49  fof(c_0_38, plain, ![X11, X12]:(~v1_relat_1(X11)|(~v1_relat_1(X12)|k7_relat_1(X11,k1_relat_1(X12))=k7_relat_1(X11,k1_relat_1(k7_relat_1(X12,k1_relat_1(X11)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t189_relat_1])])])).
% 2.27/2.49  cnf(c_0_39, plain, (k1_relat_1(k7_relat_1(esk1_1(X1),k1_relat_1(X2)))=k1_relat_1(k7_relat_1(X2,X1))|~v1_relat_1(X2)), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 2.27/2.49  cnf(c_0_40, negated_conjecture, (k1_relat_1(k7_relat_1(esk4_0,X1))=k1_relat_1(k7_relat_1(esk3_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_34]), c_0_35])])).
% 2.27/2.49  fof(c_0_41, plain, ![X25, X26, X27, X28]:((k7_relat_1(X25,X27)!=k7_relat_1(X26,X27)|(~r2_hidden(X28,X27)|k1_funct_1(X25,X28)=k1_funct_1(X26,X28))|(~r1_tarski(X27,k1_relat_1(X25))|~r1_tarski(X27,k1_relat_1(X26)))|(~v1_relat_1(X26)|~v1_funct_1(X26))|(~v1_relat_1(X25)|~v1_funct_1(X25)))&((r2_hidden(esk2_3(X25,X26,X27),X27)|k7_relat_1(X25,X27)=k7_relat_1(X26,X27)|(~r1_tarski(X27,k1_relat_1(X25))|~r1_tarski(X27,k1_relat_1(X26)))|(~v1_relat_1(X26)|~v1_funct_1(X26))|(~v1_relat_1(X25)|~v1_funct_1(X25)))&(k1_funct_1(X25,esk2_3(X25,X26,X27))!=k1_funct_1(X26,esk2_3(X25,X26,X27))|k7_relat_1(X25,X27)=k7_relat_1(X26,X27)|(~r1_tarski(X27,k1_relat_1(X25))|~r1_tarski(X27,k1_relat_1(X26)))|(~v1_relat_1(X26)|~v1_funct_1(X26))|(~v1_relat_1(X25)|~v1_funct_1(X25))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t165_funct_1])])])])])).
% 2.27/2.49  cnf(c_0_42, negated_conjecture, (k1_relat_1(k7_relat_1(esk4_0,k1_relat_1(k7_relat_1(esk3_0,X1))))=k1_relat_1(k7_relat_1(esk3_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_35])])).
% 2.27/2.49  cnf(c_0_43, plain, (k7_relat_1(X1,k1_relat_1(X2))=k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,k1_relat_1(X1))))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 2.27/2.49  cnf(c_0_44, negated_conjecture, (k1_relat_1(k7_relat_1(esk1_1(X1),k1_relat_1(esk3_0)))=k1_relat_1(k7_relat_1(esk3_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_28]), c_0_40]), c_0_29])])).
% 2.27/2.49  cnf(c_0_45, negated_conjecture, (k1_setfam_1(k1_enumset1(k1_relat_1(esk3_0),k1_relat_1(esk3_0),X1))=k1_relat_1(k7_relat_1(esk3_0,X1))), inference(rw,[status(thm)],[c_0_34, c_0_40])).
% 2.27/2.49  cnf(c_0_46, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|k7_relat_1(X1,X3)=k7_relat_1(X2,X3)|~r1_tarski(X3,k1_relat_1(X1))|~r1_tarski(X3,k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 2.27/2.49  cnf(c_0_47, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(esk3_0,X1)),k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_42]), c_0_28]), c_0_29])])).
% 2.27/2.49  cnf(c_0_48, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.27/2.49  cnf(c_0_49, negated_conjecture, (k7_relat_1(esk3_0,k1_relat_1(k7_relat_1(esk3_0,X1)))=k7_relat_1(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_26]), c_0_27]), c_0_35])])).
% 2.27/2.49  cnf(c_0_50, negated_conjecture, (k7_relat_1(esk4_0,k1_relat_1(k7_relat_1(X1,k1_relat_1(esk3_0))))=k7_relat_1(esk4_0,k1_relat_1(X1))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_28]), c_0_29])])).
% 2.27/2.49  cnf(c_0_51, plain, (k1_relat_1(k7_relat_1(esk1_1(X1),X2))=k1_relat_1(k7_relat_1(esk1_1(X2),X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_33]), c_0_33])).
% 2.27/2.49  cnf(c_0_52, negated_conjecture, (k1_relat_1(k7_relat_1(esk1_1(k1_relat_1(esk3_0)),X1))=k1_relat_1(k7_relat_1(esk3_0,X1))), inference(rw,[status(thm)],[c_0_45, c_0_33])).
% 2.27/2.49  cnf(c_0_53, plain, (k7_relat_1(X1,X3)=k7_relat_1(X2,X3)|k1_funct_1(X1,esk2_3(X1,X2,X3))!=k1_funct_1(X2,esk2_3(X1,X2,X3))|~r1_tarski(X3,k1_relat_1(X1))|~r1_tarski(X3,k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 2.27/2.49  cnf(c_0_54, negated_conjecture, (k1_funct_1(esk3_0,X1)=k1_funct_1(esk4_0,X1)|~r2_hidden(X1,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.27/2.49  cnf(c_0_55, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.27/2.49  fof(c_0_56, plain, ![X13, X14, X15]:(((r2_hidden(X13,X14)|~r2_hidden(X13,k1_relat_1(k7_relat_1(X15,X14)))|~v1_relat_1(X15))&(r2_hidden(X13,k1_relat_1(X15))|~r2_hidden(X13,k1_relat_1(k7_relat_1(X15,X14)))|~v1_relat_1(X15)))&(~r2_hidden(X13,X14)|~r2_hidden(X13,k1_relat_1(X15))|r2_hidden(X13,k1_relat_1(k7_relat_1(X15,X14)))|~v1_relat_1(X15))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).
% 2.27/2.49  cnf(c_0_57, negated_conjecture, (k7_relat_1(X1,k1_relat_1(k7_relat_1(esk3_0,X2)))=k7_relat_1(esk3_0,X2)|r2_hidden(esk2_3(X1,esk3_0,k1_relat_1(k7_relat_1(esk3_0,X2))),k1_relat_1(k7_relat_1(esk3_0,X2)))|~v1_funct_1(X1)|~r1_tarski(k1_relat_1(k7_relat_1(esk3_0,X2)),k1_relat_1(X1))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_35])]), c_0_49])).
% 2.27/2.49  cnf(c_0_58, negated_conjecture, (k7_relat_1(esk4_0,k1_relat_1(k7_relat_1(esk3_0,X1)))=k7_relat_1(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52]), c_0_26]), c_0_27])])).
% 2.27/2.49  cnf(c_0_59, negated_conjecture, (k7_relat_1(esk4_0,X1)=k7_relat_1(X2,X1)|k1_funct_1(esk3_0,esk2_3(esk4_0,X2,X1))!=k1_funct_1(X2,esk2_3(esk4_0,X2,X1))|~v1_funct_1(X2)|~r1_tarski(X1,k1_relat_1(esk3_0))|~r1_tarski(X1,k1_relat_1(X2))|~r2_hidden(esk2_3(esk4_0,X2,X1),esk5_0)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55]), c_0_28]), c_0_29])])).
% 2.27/2.49  cnf(c_0_60, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 2.27/2.49  cnf(c_0_61, negated_conjecture, (k7_relat_1(esk4_0,X1)=k7_relat_1(esk3_0,X1)|r2_hidden(esk2_3(esk4_0,esk3_0,k1_relat_1(k7_relat_1(esk3_0,X1))),k1_relat_1(k7_relat_1(esk3_0,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_28]), c_0_58]), c_0_55]), c_0_47]), c_0_29])])).
% 2.27/2.49  cnf(c_0_62, negated_conjecture, (k7_relat_1(esk4_0,X1)=k7_relat_1(esk3_0,X1)|~r1_tarski(X1,k1_relat_1(esk3_0))|~r2_hidden(esk2_3(esk4_0,esk3_0,X1),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_59]), c_0_48]), c_0_35])])).
% 2.27/2.49  cnf(c_0_63, negated_conjecture, (k7_relat_1(esk4_0,X1)=k7_relat_1(esk3_0,X1)|r2_hidden(esk2_3(esk4_0,esk3_0,k1_relat_1(k7_relat_1(esk3_0,X1))),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_35])])).
% 2.27/2.49  cnf(c_0_64, negated_conjecture, (k7_relat_1(esk3_0,esk5_0)!=k7_relat_1(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.27/2.49  cnf(c_0_65, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_58]), c_0_49]), c_0_47])]), c_0_64]), ['proof']).
% 2.27/2.49  # SZS output end CNFRefutation
% 2.27/2.49  # Proof object total steps             : 66
% 2.27/2.49  # Proof object clause steps            : 43
% 2.27/2.49  # Proof object formula steps           : 23
% 2.27/2.49  # Proof object conjectures             : 27
% 2.27/2.49  # Proof object clause conjectures      : 24
% 2.27/2.49  # Proof object formula conjectures     : 3
% 2.27/2.49  # Proof object initial clauses used    : 19
% 2.27/2.49  # Proof object initial formulas used   : 11
% 2.27/2.49  # Proof object generating inferences   : 17
% 2.27/2.49  # Proof object simplifying inferences  : 58
% 2.27/2.49  # Training examples: 0 positive, 0 negative
% 2.27/2.49  # Parsed axioms                        : 11
% 2.27/2.49  # Removed by relevancy pruning/SinE    : 0
% 2.27/2.49  # Initial clauses                      : 24
% 2.27/2.49  # Removed in clause preprocessing      : 2
% 2.27/2.49  # Initial clauses in saturation        : 22
% 2.27/2.49  # Processed clauses                    : 7014
% 2.27/2.49  # ...of these trivial                  : 47
% 2.27/2.49  # ...subsumed                          : 6038
% 2.27/2.49  # ...remaining for further processing  : 929
% 2.27/2.49  # Other redundant clauses eliminated   : 0
% 2.27/2.49  # Clauses deleted for lack of memory   : 0
% 2.27/2.49  # Backward-subsumed                    : 35
% 2.27/2.49  # Backward-rewritten                   : 22
% 2.27/2.49  # Generated clauses                    : 163067
% 2.27/2.49  # ...of the previous two non-trivial   : 156676
% 2.27/2.49  # Contextual simplify-reflections      : 2
% 2.27/2.49  # Paramodulations                      : 163064
% 2.27/2.49  # Factorizations                       : 0
% 2.27/2.49  # Equation resolutions                 : 3
% 2.27/2.49  # Propositional unsat checks           : 0
% 2.27/2.49  #    Propositional check models        : 0
% 2.27/2.49  #    Propositional check unsatisfiable : 0
% 2.27/2.49  #    Propositional clauses             : 0
% 2.27/2.49  #    Propositional clauses after purity: 0
% 2.27/2.49  #    Propositional unsat core size     : 0
% 2.27/2.49  #    Propositional preprocessing time  : 0.000
% 2.27/2.49  #    Propositional encoding time       : 0.000
% 2.27/2.49  #    Propositional solver time         : 0.000
% 2.27/2.49  #    Success case prop preproc time    : 0.000
% 2.27/2.49  #    Success case prop encoding time   : 0.000
% 2.27/2.49  #    Success case prop solver time     : 0.000
% 2.27/2.49  # Current number of processed clauses  : 850
% 2.27/2.49  #    Positive orientable unit clauses  : 26
% 2.27/2.49  #    Positive unorientable unit clauses: 1
% 2.27/2.49  #    Negative unit clauses             : 1
% 2.27/2.49  #    Non-unit-clauses                  : 822
% 2.27/2.49  # Current number of unprocessed clauses: 149452
% 2.27/2.49  # ...number of literals in the above   : 876472
% 2.27/2.49  # Current number of archived formulas  : 0
% 2.27/2.49  # Current number of archived clauses   : 81
% 2.27/2.49  # Clause-clause subsumption calls (NU) : 389322
% 2.27/2.49  # Rec. Clause-clause subsumption calls : 185387
% 2.27/2.49  # Non-unit clause-clause subsumptions  : 6069
% 2.27/2.49  # Unit Clause-clause subsumption calls : 1156
% 2.27/2.49  # Rewrite failures with RHS unbound    : 0
% 2.27/2.49  # BW rewrite match attempts            : 153
% 2.27/2.49  # BW rewrite match successes           : 32
% 2.27/2.49  # Condensation attempts                : 0
% 2.27/2.49  # Condensation successes               : 0
% 2.27/2.49  # Termbank termtop insertions          : 7581719
% 2.27/2.50  
% 2.27/2.50  # -------------------------------------------------
% 2.27/2.50  # User time                : 2.085 s
% 2.27/2.50  # System time              : 0.079 s
% 2.27/2.50  # Total time               : 2.164 s
% 2.27/2.50  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
