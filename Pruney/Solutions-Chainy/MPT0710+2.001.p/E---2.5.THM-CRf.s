%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:35 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 686 expanded)
%              Number of clauses        :   36 ( 253 expanded)
%              Number of leaves         :    7 ( 170 expanded)
%              Depth                    :   12
%              Number of atoms          :  187 (4077 expanded)
%              Number of equality atoms :   65 (1203 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t68_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( ( k1_relat_1(X2) = k3_xboole_0(k1_relat_1(X3),X1)
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X2))
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) )
           => X2 = k7_relat_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_funct_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t165_funct_1)).

fof(t91_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => k1_relat_1(k7_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(fc8_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k7_relat_1(X1,X2))
        & v1_funct_1(k7_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

fof(t72_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,X2)
       => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_funct_1)).

fof(c_0_7,plain,(
    ! [X13,X14,X15] :
      ( ( r2_hidden(esk1_3(X13,X14,X15),k1_relat_1(X14))
        | k1_relat_1(X14) != k3_xboole_0(k1_relat_1(X15),X13)
        | X14 = k7_relat_1(X15,X13)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( k1_funct_1(X14,esk1_3(X13,X14,X15)) != k1_funct_1(X15,esk1_3(X13,X14,X15))
        | k1_relat_1(X14) != k3_xboole_0(k1_relat_1(X15),X13)
        | X14 = k7_relat_1(X15,X13)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t68_funct_1])])])])])).

fof(c_0_8,plain,(
    ! [X5,X6] : k1_setfam_1(k2_tarski(X5,X6)) = k3_xboole_0(X5,X6) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_9,plain,(
    ! [X7,X8] :
      ( ~ v1_relat_1(X8)
      | k1_relat_1(k7_relat_1(X8,X7)) = k3_xboole_0(k1_relat_1(X8),X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

fof(c_0_10,negated_conjecture,(
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

cnf(c_0_11,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),k1_relat_1(X2))
    | X2 = k7_relat_1(X3,X1)
    | k1_relat_1(X2) != k3_xboole_0(k1_relat_1(X3),X1)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X9,X10] :
      ( ~ v1_relat_1(X10)
      | ~ r1_tarski(X9,k1_relat_1(X10))
      | k1_relat_1(k7_relat_1(X10,X9)) = X9 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).

fof(c_0_15,negated_conjecture,(
    ! [X24] :
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
        | ~ r2_hidden(X24,esk4_0)
        | k1_funct_1(esk2_0,X24) = k1_funct_1(esk3_0,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])])).

cnf(c_0_16,plain,
    ( X2 = k7_relat_1(X3,X1)
    | r2_hidden(esk1_3(X1,X2,X3),k1_relat_1(X2))
    | k1_relat_1(X2) != k1_setfam_1(k2_tarski(k1_relat_1(X3),X1))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_13,c_0_12])).

cnf(c_0_18,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(esk4_0,k1_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X11,X12] :
      ( ( v1_relat_1(k7_relat_1(X11,X12))
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( v1_funct_1(k7_relat_1(X11,X12))
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).

cnf(c_0_22,plain,
    ( X1 = k7_relat_1(X2,X3)
    | r2_hidden(esk1_3(X3,X1,X2),k1_relat_1(X1))
    | k1_relat_1(X1) != k1_relat_1(k7_relat_1(X2,X3))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk3_0,esk4_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(esk4_0,k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,plain,
    ( X1 = k7_relat_1(X3,X2)
    | k1_funct_1(X1,esk1_3(X2,X1,X3)) != k1_funct_1(X3,esk1_3(X2,X1,X3))
    | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X3),X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_30,negated_conjecture,
    ( X1 = k7_relat_1(esk3_0,esk4_0)
    | r2_hidden(esk1_3(esk4_0,X1,esk3_0),k1_relat_1(X1))
    | k1_relat_1(X1) != esk4_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_20])])).

cnf(c_0_31,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,esk4_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_25]),c_0_26])])).

cnf(c_0_32,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk2_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_26])])).

cnf(c_0_33,plain,
    ( X1 = k7_relat_1(X3,X2)
    | k1_relat_1(X1) != k1_setfam_1(k2_tarski(k1_relat_1(X3),X2))
    | k1_funct_1(X1,esk1_3(X2,X1,X3)) != k1_funct_1(X3,esk1_3(X2,X1,X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[c_0_29,c_0_12])).

fof(c_0_34,plain,(
    ! [X17,X18,X19] :
      ( ~ v1_relat_1(X19)
      | ~ v1_funct_1(X19)
      | ~ r2_hidden(X17,X18)
      | k1_funct_1(k7_relat_1(X19,X18),X17) = k1_funct_1(X19,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t72_funct_1])])).

cnf(c_0_35,negated_conjecture,
    ( k7_relat_1(esk2_0,esk4_0) = k7_relat_1(esk3_0,esk4_0)
    | r2_hidden(esk1_3(esk4_0,k7_relat_1(esk2_0,esk4_0),esk3_0),esk4_0)
    | ~ v1_funct_1(k7_relat_1(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])])).

cnf(c_0_36,plain,
    ( v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_37,plain,
    ( X1 = k7_relat_1(X2,X3)
    | k1_funct_1(X1,esk1_3(X3,X1,X2)) != k1_funct_1(X2,esk1_3(X3,X1,X2))
    | k1_relat_1(X1) != k1_relat_1(k7_relat_1(X2,X3))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_17])).

cnf(c_0_38,plain,
    ( k1_funct_1(k7_relat_1(X1,X3),X2) = k1_funct_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( k7_relat_1(esk2_0,esk4_0) = k7_relat_1(esk3_0,esk4_0)
    | k1_funct_1(esk2_0,X1) = k1_funct_1(esk3_0,X1)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_40,negated_conjecture,
    ( k7_relat_1(esk2_0,esk4_0) = k7_relat_1(esk3_0,esk4_0)
    | r2_hidden(esk1_3(esk4_0,k7_relat_1(esk2_0,esk4_0),esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_28]),c_0_26])])).

cnf(c_0_41,plain,
    ( k7_relat_1(X1,X2) = k7_relat_1(X3,X4)
    | k1_funct_1(X1,esk1_3(X4,k7_relat_1(X1,X2),X3)) != k1_funct_1(X3,esk1_3(X4,k7_relat_1(X1,X2),X3))
    | k1_relat_1(k7_relat_1(X1,X2)) != k1_relat_1(k7_relat_1(X3,X4))
    | ~ r2_hidden(esk1_3(X4,k7_relat_1(X1,X2),X3),X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_27]),c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( k1_funct_1(esk2_0,esk1_3(esk4_0,k7_relat_1(esk2_0,esk4_0),esk3_0)) = k1_funct_1(esk3_0,esk1_3(esk4_0,k7_relat_1(esk2_0,esk4_0),esk3_0))
    | k7_relat_1(esk2_0,esk4_0) = k7_relat_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( k7_relat_1(esk2_0,esk4_0) = k7_relat_1(esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_40]),c_0_31]),c_0_23]),c_0_24]),c_0_28]),c_0_20]),c_0_26])]),c_0_42])).

cnf(c_0_44,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk3_0,esk4_0),X1) = k1_funct_1(esk2_0,X1)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_43]),c_0_28]),c_0_26])])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0)
    | k7_relat_1(esk2_0,esk4_0) != k7_relat_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_46,negated_conjecture,
    ( k1_funct_1(esk2_0,esk5_0) != k1_funct_1(esk3_0,esk5_0)
    | k7_relat_1(esk2_0,esk4_0) != k7_relat_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_47,negated_conjecture,
    ( k1_funct_1(esk2_0,X1) = k1_funct_1(esk3_0,X1)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_44]),c_0_24]),c_0_20])])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_43])])).

cnf(c_0_49,negated_conjecture,
    ( k1_funct_1(esk2_0,esk5_0) != k1_funct_1(esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_43])])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:16:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t68_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X2)=k3_xboole_0(k1_relat_1(X3),X1)&![X4]:(r2_hidden(X4,k1_relat_1(X2))=>k1_funct_1(X2,X4)=k1_funct_1(X3,X4)))=>X2=k7_relat_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_funct_1)).
% 0.13/0.38  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.13/0.38  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 0.13/0.38  fof(t165_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((r1_tarski(X3,k1_relat_1(X1))&r1_tarski(X3,k1_relat_1(X2)))=>(k7_relat_1(X1,X3)=k7_relat_1(X2,X3)<=>![X4]:(r2_hidden(X4,X3)=>k1_funct_1(X1,X4)=k1_funct_1(X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t165_funct_1)).
% 0.13/0.38  fof(t91_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>k1_relat_1(k7_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 0.13/0.38  fof(fc8_funct_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k7_relat_1(X1,X2))&v1_funct_1(k7_relat_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_funct_1)).
% 0.13/0.38  fof(t72_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,X2)=>k1_funct_1(k7_relat_1(X3,X2),X1)=k1_funct_1(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_funct_1)).
% 0.13/0.38  fof(c_0_7, plain, ![X13, X14, X15]:((r2_hidden(esk1_3(X13,X14,X15),k1_relat_1(X14))|k1_relat_1(X14)!=k3_xboole_0(k1_relat_1(X15),X13)|X14=k7_relat_1(X15,X13)|(~v1_relat_1(X15)|~v1_funct_1(X15))|(~v1_relat_1(X14)|~v1_funct_1(X14)))&(k1_funct_1(X14,esk1_3(X13,X14,X15))!=k1_funct_1(X15,esk1_3(X13,X14,X15))|k1_relat_1(X14)!=k3_xboole_0(k1_relat_1(X15),X13)|X14=k7_relat_1(X15,X13)|(~v1_relat_1(X15)|~v1_funct_1(X15))|(~v1_relat_1(X14)|~v1_funct_1(X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t68_funct_1])])])])])).
% 0.13/0.38  fof(c_0_8, plain, ![X5, X6]:k1_setfam_1(k2_tarski(X5,X6))=k3_xboole_0(X5,X6), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.13/0.38  fof(c_0_9, plain, ![X7, X8]:(~v1_relat_1(X8)|k1_relat_1(k7_relat_1(X8,X7))=k3_xboole_0(k1_relat_1(X8),X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 0.13/0.38  fof(c_0_10, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((r1_tarski(X3,k1_relat_1(X1))&r1_tarski(X3,k1_relat_1(X2)))=>(k7_relat_1(X1,X3)=k7_relat_1(X2,X3)<=>![X4]:(r2_hidden(X4,X3)=>k1_funct_1(X1,X4)=k1_funct_1(X2,X4))))))), inference(assume_negation,[status(cth)],[t165_funct_1])).
% 0.13/0.38  cnf(c_0_11, plain, (r2_hidden(esk1_3(X1,X2,X3),k1_relat_1(X2))|X2=k7_relat_1(X3,X1)|k1_relat_1(X2)!=k3_xboole_0(k1_relat_1(X3),X1)|~v1_relat_1(X3)|~v1_funct_1(X3)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_12, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_13, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  fof(c_0_14, plain, ![X9, X10]:(~v1_relat_1(X10)|(~r1_tarski(X9,k1_relat_1(X10))|k1_relat_1(k7_relat_1(X10,X9))=X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).
% 0.13/0.38  fof(c_0_15, negated_conjecture, ![X24]:((v1_relat_1(esk2_0)&v1_funct_1(esk2_0))&((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&((r1_tarski(esk4_0,k1_relat_1(esk2_0))&r1_tarski(esk4_0,k1_relat_1(esk3_0)))&(((r2_hidden(esk5_0,esk4_0)|k7_relat_1(esk2_0,esk4_0)!=k7_relat_1(esk3_0,esk4_0))&(k1_funct_1(esk2_0,esk5_0)!=k1_funct_1(esk3_0,esk5_0)|k7_relat_1(esk2_0,esk4_0)!=k7_relat_1(esk3_0,esk4_0)))&(k7_relat_1(esk2_0,esk4_0)=k7_relat_1(esk3_0,esk4_0)|(~r2_hidden(X24,esk4_0)|k1_funct_1(esk2_0,X24)=k1_funct_1(esk3_0,X24))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])])).
% 0.13/0.38  cnf(c_0_16, plain, (X2=k7_relat_1(X3,X1)|r2_hidden(esk1_3(X1,X2,X3),k1_relat_1(X2))|k1_relat_1(X2)!=k1_setfam_1(k2_tarski(k1_relat_1(X3),X1))|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_funct_1(X3)|~v1_funct_1(X2)), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 0.13/0.38  cnf(c_0_17, plain, (k1_relat_1(k7_relat_1(X1,X2))=k1_setfam_1(k2_tarski(k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_13, c_0_12])).
% 0.13/0.38  cnf(c_0_18, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_19, negated_conjecture, (r1_tarski(esk4_0,k1_relat_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_20, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  fof(c_0_21, plain, ![X11, X12]:((v1_relat_1(k7_relat_1(X11,X12))|(~v1_relat_1(X11)|~v1_funct_1(X11)))&(v1_funct_1(k7_relat_1(X11,X12))|(~v1_relat_1(X11)|~v1_funct_1(X11)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).
% 0.13/0.38  cnf(c_0_22, plain, (X1=k7_relat_1(X2,X3)|r2_hidden(esk1_3(X3,X1,X2),k1_relat_1(X1))|k1_relat_1(X1)!=k1_relat_1(k7_relat_1(X2,X3))|~v1_funct_1(X2)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (k1_relat_1(k7_relat_1(esk3_0,esk4_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])])).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (r1_tarski(esk4_0,k1_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_27, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_29, plain, (X1=k7_relat_1(X3,X2)|k1_funct_1(X1,esk1_3(X2,X1,X3))!=k1_funct_1(X3,esk1_3(X2,X1,X3))|k1_relat_1(X1)!=k3_xboole_0(k1_relat_1(X3),X2)|~v1_relat_1(X3)|~v1_funct_1(X3)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (X1=k7_relat_1(esk3_0,esk4_0)|r2_hidden(esk1_3(esk4_0,X1,esk3_0),k1_relat_1(X1))|k1_relat_1(X1)!=esk4_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_20])])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,esk4_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_25]), c_0_26])])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (v1_relat_1(k7_relat_1(esk2_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_26])])).
% 0.13/0.38  cnf(c_0_33, plain, (X1=k7_relat_1(X3,X2)|k1_relat_1(X1)!=k1_setfam_1(k2_tarski(k1_relat_1(X3),X2))|k1_funct_1(X1,esk1_3(X2,X1,X3))!=k1_funct_1(X3,esk1_3(X2,X1,X3))|~v1_relat_1(X3)|~v1_relat_1(X1)|~v1_funct_1(X3)|~v1_funct_1(X1)), inference(rw,[status(thm)],[c_0_29, c_0_12])).
% 0.13/0.38  fof(c_0_34, plain, ![X17, X18, X19]:(~v1_relat_1(X19)|~v1_funct_1(X19)|(~r2_hidden(X17,X18)|k1_funct_1(k7_relat_1(X19,X18),X17)=k1_funct_1(X19,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t72_funct_1])])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (k7_relat_1(esk2_0,esk4_0)=k7_relat_1(esk3_0,esk4_0)|r2_hidden(esk1_3(esk4_0,k7_relat_1(esk2_0,esk4_0),esk3_0),esk4_0)|~v1_funct_1(k7_relat_1(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])])).
% 0.13/0.38  cnf(c_0_36, plain, (v1_funct_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_37, plain, (X1=k7_relat_1(X2,X3)|k1_funct_1(X1,esk1_3(X3,X1,X2))!=k1_funct_1(X2,esk1_3(X3,X1,X2))|k1_relat_1(X1)!=k1_relat_1(k7_relat_1(X2,X3))|~v1_funct_1(X2)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_33, c_0_17])).
% 0.13/0.38  cnf(c_0_38, plain, (k1_funct_1(k7_relat_1(X1,X3),X2)=k1_funct_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, (k7_relat_1(esk2_0,esk4_0)=k7_relat_1(esk3_0,esk4_0)|k1_funct_1(esk2_0,X1)=k1_funct_1(esk3_0,X1)|~r2_hidden(X1,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (k7_relat_1(esk2_0,esk4_0)=k7_relat_1(esk3_0,esk4_0)|r2_hidden(esk1_3(esk4_0,k7_relat_1(esk2_0,esk4_0),esk3_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_28]), c_0_26])])).
% 0.13/0.38  cnf(c_0_41, plain, (k7_relat_1(X1,X2)=k7_relat_1(X3,X4)|k1_funct_1(X1,esk1_3(X4,k7_relat_1(X1,X2),X3))!=k1_funct_1(X3,esk1_3(X4,k7_relat_1(X1,X2),X3))|k1_relat_1(k7_relat_1(X1,X2))!=k1_relat_1(k7_relat_1(X3,X4))|~r2_hidden(esk1_3(X4,k7_relat_1(X1,X2),X3),X2)|~v1_funct_1(X3)|~v1_funct_1(X1)|~v1_relat_1(X3)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_27]), c_0_36])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (k1_funct_1(esk2_0,esk1_3(esk4_0,k7_relat_1(esk2_0,esk4_0),esk3_0))=k1_funct_1(esk3_0,esk1_3(esk4_0,k7_relat_1(esk2_0,esk4_0),esk3_0))|k7_relat_1(esk2_0,esk4_0)=k7_relat_1(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.13/0.38  cnf(c_0_43, negated_conjecture, (k7_relat_1(esk2_0,esk4_0)=k7_relat_1(esk3_0,esk4_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_40]), c_0_31]), c_0_23]), c_0_24]), c_0_28]), c_0_20]), c_0_26])]), c_0_42])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (k1_funct_1(k7_relat_1(esk3_0,esk4_0),X1)=k1_funct_1(esk2_0,X1)|~r2_hidden(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_43]), c_0_28]), c_0_26])])).
% 0.13/0.38  cnf(c_0_45, negated_conjecture, (r2_hidden(esk5_0,esk4_0)|k7_relat_1(esk2_0,esk4_0)!=k7_relat_1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (k1_funct_1(esk2_0,esk5_0)!=k1_funct_1(esk3_0,esk5_0)|k7_relat_1(esk2_0,esk4_0)!=k7_relat_1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, (k1_funct_1(esk2_0,X1)=k1_funct_1(esk3_0,X1)|~r2_hidden(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_44]), c_0_24]), c_0_20])])).
% 0.13/0.38  cnf(c_0_48, negated_conjecture, (r2_hidden(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_43])])).
% 0.13/0.38  cnf(c_0_49, negated_conjecture, (k1_funct_1(esk2_0,esk5_0)!=k1_funct_1(esk3_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_43])])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 51
% 0.13/0.38  # Proof object clause steps            : 36
% 0.13/0.38  # Proof object formula steps           : 15
% 0.13/0.38  # Proof object conjectures             : 25
% 0.13/0.38  # Proof object clause conjectures      : 22
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 17
% 0.13/0.38  # Proof object initial formulas used   : 7
% 0.13/0.38  # Proof object generating inferences   : 14
% 0.13/0.38  # Proof object simplifying inferences  : 38
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 7
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 17
% 0.13/0.38  # Removed in clause preprocessing      : 1
% 0.13/0.38  # Initial clauses in saturation        : 16
% 0.13/0.38  # Processed clauses                    : 108
% 0.13/0.38  # ...of these trivial                  : 1
% 0.13/0.38  # ...subsumed                          : 7
% 0.13/0.38  # ...remaining for further processing  : 100
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 14
% 0.13/0.38  # Backward-rewritten                   : 32
% 0.13/0.38  # Generated clauses                    : 108
% 0.13/0.38  # ...of the previous two non-trivial   : 125
% 0.13/0.38  # Contextual simplify-reflections      : 6
% 0.13/0.38  # Paramodulations                      : 101
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 7
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 38
% 0.13/0.38  #    Positive orientable unit clauses  : 14
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 1
% 0.13/0.38  #    Non-unit-clauses                  : 23
% 0.13/0.38  # Current number of unprocessed clauses: 49
% 0.13/0.38  # ...number of literals in the above   : 297
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 63
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 1251
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 173
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 27
% 0.13/0.38  # Unit Clause-clause subsumption calls : 21
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 5
% 0.13/0.38  # BW rewrite match successes           : 3
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 6619
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.036 s
% 0.13/0.38  # System time              : 0.004 s
% 0.13/0.38  # Total time               : 0.040 s
% 0.13/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
