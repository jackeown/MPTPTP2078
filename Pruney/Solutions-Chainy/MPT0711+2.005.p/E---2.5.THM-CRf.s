%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:36 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 831 expanded)
%              Number of clauses        :   45 ( 345 expanded)
%              Number of leaves         :   10 ( 208 expanded)
%              Depth                    :   14
%              Number of atoms          :  198 (2808 expanded)
%              Number of equality atoms :   64 (1203 expanded)
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

fof(t100_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(k7_relat_1(X3,X1),X2) = k7_relat_1(X3,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

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

fof(t98_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(t86_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X1,k1_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

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

fof(c_0_10,plain,(
    ! [X13,X14] : k1_setfam_1(k2_tarski(X13,X14)) = k3_xboole_0(X13,X14) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_11,plain,(
    ! [X11,X12] : k1_enumset1(X11,X11,X12) = k2_tarski(X11,X12) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_12,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X22)
      | k1_relat_1(k7_relat_1(X22,X21)) = k3_xboole_0(k1_relat_1(X22),X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

cnf(c_0_13,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,negated_conjecture,(
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

cnf(c_0_16,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_18,negated_conjecture,(
    ! [X35] :
      ( v1_relat_1(esk4_0)
      & v1_funct_1(esk4_0)
      & v1_relat_1(esk5_0)
      & v1_funct_1(esk5_0)
      & k1_relat_1(esk4_0) = k1_relat_1(esk5_0)
      & ( ~ r2_hidden(X35,esk6_0)
        | k1_funct_1(esk4_0,X35) = k1_funct_1(esk5_0,X35) )
      & k7_relat_1(esk4_0,esk6_0) != k7_relat_1(esk5_0,esk6_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])])).

cnf(c_0_19,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( k1_relat_1(esk4_0) = k1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X15,X16,X17] :
      ( ~ v1_relat_1(X17)
      | k7_relat_1(k7_relat_1(X17,X15),X16) = k7_relat_1(X17,k3_xboole_0(X15,X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).

fof(c_0_23,plain,(
    ! [X24,X26] :
      ( v1_relat_1(esk2_1(X24))
      & v1_funct_1(esk2_1(X24))
      & k1_relat_1(esk2_1(X24)) = X24
      & ( ~ r2_hidden(X26,X24)
        | k1_funct_1(esk2_1(X24),X26) = k1_xboole_0 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e9_44_1__funct_1])])])])).

cnf(c_0_24,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),X1)) = k1_relat_1(k7_relat_1(esk5_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_26,plain,(
    ! [X23] :
      ( ~ v1_relat_1(X23)
      | k7_relat_1(X23,k1_relat_1(X23)) = X23 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).

fof(c_0_27,plain,(
    ! [X18,X19,X20] :
      ( ( r2_hidden(X18,X19)
        | ~ r2_hidden(X18,k1_relat_1(k7_relat_1(X20,X19)))
        | ~ v1_relat_1(X20) )
      & ( r2_hidden(X18,k1_relat_1(X20))
        | ~ r2_hidden(X18,k1_relat_1(k7_relat_1(X20,X19)))
        | ~ v1_relat_1(X20) )
      & ( ~ r2_hidden(X18,X19)
        | ~ r2_hidden(X18,k1_relat_1(X20))
        | r2_hidden(X18,k1_relat_1(k7_relat_1(X20,X19)))
        | ~ v1_relat_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).

cnf(c_0_28,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k1_relat_1(esk2_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( v1_relat_1(esk2_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk5_0,X1)) = k1_relat_1(k7_relat_1(esk4_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_24]),c_0_25])])).

cnf(c_0_32,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X3)))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_34,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_35,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_28,c_0_17])).

cnf(c_0_36,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k1_relat_1(k7_relat_1(esk2_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_29]),c_0_30])])).

cnf(c_0_37,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),X1)) = k1_relat_1(k7_relat_1(esk4_0,X1)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])]),c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk4_0,k1_relat_1(esk4_0))) = k1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_20]),c_0_20]),c_0_21])])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(esk4_0))
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(esk4_0,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_31]),c_0_20]),c_0_21])])).

cnf(c_0_40,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,plain,
    ( k7_relat_1(X1,k1_relat_1(k7_relat_1(esk2_1(X2),X3))) = k7_relat_1(k7_relat_1(X1,X2),X3)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_1(k1_relat_1(esk4_0)),X1)) = k1_relat_1(k7_relat_1(esk4_0,X1)) ),
    inference(rw,[status(thm)],[c_0_37,c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk4_0,k1_relat_1(esk4_0)),k1_relat_1(esk4_0)) = k7_relat_1(esk4_0,k1_relat_1(esk4_0))
    | ~ v1_relat_1(k7_relat_1(esk4_0,k1_relat_1(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_38])).

fof(c_0_44,plain,(
    ! [X27,X28,X29,X30] :
      ( ( k7_relat_1(X27,X29) != k7_relat_1(X28,X29)
        | ~ r2_hidden(X30,X29)
        | k1_funct_1(X27,X30) = k1_funct_1(X28,X30)
        | ~ r1_tarski(X29,k1_relat_1(X27))
        | ~ r1_tarski(X29,k1_relat_1(X28))
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( r2_hidden(esk3_3(X27,X28,X29),X29)
        | k7_relat_1(X27,X29) = k7_relat_1(X28,X29)
        | ~ r1_tarski(X29,k1_relat_1(X27))
        | ~ r1_tarski(X29,k1_relat_1(X28))
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( k1_funct_1(X27,esk3_3(X27,X28,X29)) != k1_funct_1(X28,esk3_3(X27,X28,X29))
        | k7_relat_1(X27,X29) = k7_relat_1(X28,X29)
        | ~ r1_tarski(X29,k1_relat_1(X27))
        | ~ r1_tarski(X29,k1_relat_1(X28))
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t165_funct_1])])])])])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk1_2(k1_relat_1(k7_relat_1(esk4_0,X1)),X2),k1_relat_1(esk4_0))
    | r1_tarski(k1_relat_1(k7_relat_1(esk4_0,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( k7_relat_1(k7_relat_1(X1,k1_relat_1(esk4_0)),X2) = k7_relat_1(X1,k1_relat_1(k7_relat_1(esk4_0,X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( k7_relat_1(esk4_0,k1_relat_1(esk4_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_32]),c_0_25])])).

cnf(c_0_49,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X3)
    | k7_relat_1(X1,X3) = k7_relat_1(X2,X3)
    | ~ r1_tarski(X3,k1_relat_1(X1))
    | ~ r1_tarski(X3,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk4_0,X1)),k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( k7_relat_1(esk4_0,k1_relat_1(k7_relat_1(esk4_0,X1))) = k7_relat_1(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_25])])).

cnf(c_0_52,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_53,negated_conjecture,
    ( k7_relat_1(esk5_0,k1_relat_1(esk4_0)) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_20]),c_0_21])])).

cnf(c_0_54,plain,
    ( k7_relat_1(X1,X3) = k7_relat_1(X2,X3)
    | k1_funct_1(X1,esk3_3(X1,X2,X3)) != k1_funct_1(X2,esk3_3(X1,X2,X3))
    | ~ r1_tarski(X3,k1_relat_1(X1))
    | ~ r1_tarski(X3,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_55,negated_conjecture,
    ( k1_funct_1(esk4_0,X1) = k1_funct_1(esk5_0,X1)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_56,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_57,negated_conjecture,
    ( k7_relat_1(X1,k1_relat_1(k7_relat_1(esk4_0,X2))) = k7_relat_1(esk4_0,X2)
    | r2_hidden(esk3_3(X1,esk4_0,k1_relat_1(k7_relat_1(esk4_0,X2))),k1_relat_1(k7_relat_1(esk4_0,X2)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(esk4_0,X2)),k1_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_52]),c_0_25])])).

cnf(c_0_58,negated_conjecture,
    ( k7_relat_1(esk5_0,k1_relat_1(k7_relat_1(esk4_0,X1))) = k7_relat_1(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_53]),c_0_21])])).

cnf(c_0_59,negated_conjecture,
    ( k7_relat_1(esk5_0,X1) = k7_relat_1(X2,X1)
    | k1_funct_1(esk4_0,esk3_3(esk5_0,X2,X1)) != k1_funct_1(X2,esk3_3(esk5_0,X2,X1))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(esk3_3(esk5_0,X2,X1),esk6_0)
    | ~ r1_tarski(X1,k1_relat_1(esk4_0))
    | ~ r1_tarski(X1,k1_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_21]),c_0_20])])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_61,negated_conjecture,
    ( k7_relat_1(esk5_0,X1) = k7_relat_1(esk4_0,X1)
    | r2_hidden(esk3_3(esk5_0,esk4_0,k1_relat_1(k7_relat_1(esk4_0,X1))),k1_relat_1(k7_relat_1(esk4_0,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_20]),c_0_58]),c_0_56]),c_0_21]),c_0_50])])).

cnf(c_0_62,negated_conjecture,
    ( k7_relat_1(esk5_0,X1) = k7_relat_1(esk4_0,X1)
    | ~ r2_hidden(esk3_3(esk5_0,esk4_0,X1),esk6_0)
    | ~ r1_tarski(X1,k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_59]),c_0_52]),c_0_25])])).

cnf(c_0_63,negated_conjecture,
    ( k7_relat_1(esk5_0,X1) = k7_relat_1(esk4_0,X1)
    | r2_hidden(esk3_3(esk5_0,esk4_0,k1_relat_1(k7_relat_1(esk4_0,X1))),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_25])])).

cnf(c_0_64,negated_conjecture,
    ( k7_relat_1(esk4_0,esk6_0) != k7_relat_1(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_58]),c_0_51]),c_0_50])]),c_0_64]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:01:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 1.67/1.89  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 1.67/1.89  # and selection function SelectComplexExceptUniqMaxHorn.
% 1.67/1.89  #
% 1.67/1.89  # Preprocessing time       : 0.028 s
% 1.67/1.89  # Presaturation interreduction done
% 1.67/1.89  
% 1.67/1.89  # Proof found!
% 1.67/1.89  # SZS status Theorem
% 1.67/1.89  # SZS output start CNFRefutation
% 1.67/1.89  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.67/1.89  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.67/1.89  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 1.67/1.89  fof(t166_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((k1_relat_1(X1)=k1_relat_1(X2)&![X4]:(r2_hidden(X4,X3)=>k1_funct_1(X1,X4)=k1_funct_1(X2,X4)))=>k7_relat_1(X1,X3)=k7_relat_1(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_funct_1)).
% 1.67/1.89  fof(t100_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k7_relat_1(X3,k3_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 1.67/1.89  fof(s3_funct_1__e9_44_1__funct_1, axiom, ![X1]:?[X2]:(((v1_relat_1(X2)&v1_funct_1(X2))&k1_relat_1(X2)=X1)&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e9_44_1__funct_1)).
% 1.67/1.89  fof(t98_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 1.67/1.89  fof(t86_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))<=>(r2_hidden(X1,X2)&r2_hidden(X1,k1_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 1.67/1.89  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.67/1.89  fof(t165_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((r1_tarski(X3,k1_relat_1(X1))&r1_tarski(X3,k1_relat_1(X2)))=>(k7_relat_1(X1,X3)=k7_relat_1(X2,X3)<=>![X4]:(r2_hidden(X4,X3)=>k1_funct_1(X1,X4)=k1_funct_1(X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t165_funct_1)).
% 1.67/1.89  fof(c_0_10, plain, ![X13, X14]:k1_setfam_1(k2_tarski(X13,X14))=k3_xboole_0(X13,X14), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 1.67/1.89  fof(c_0_11, plain, ![X11, X12]:k1_enumset1(X11,X11,X12)=k2_tarski(X11,X12), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 1.67/1.89  fof(c_0_12, plain, ![X21, X22]:(~v1_relat_1(X22)|k1_relat_1(k7_relat_1(X22,X21))=k3_xboole_0(k1_relat_1(X22),X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 1.67/1.89  cnf(c_0_13, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.67/1.89  cnf(c_0_14, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.67/1.89  fof(c_0_15, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((k1_relat_1(X1)=k1_relat_1(X2)&![X4]:(r2_hidden(X4,X3)=>k1_funct_1(X1,X4)=k1_funct_1(X2,X4)))=>k7_relat_1(X1,X3)=k7_relat_1(X2,X3))))), inference(assume_negation,[status(cth)],[t166_funct_1])).
% 1.67/1.89  cnf(c_0_16, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.67/1.89  cnf(c_0_17, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 1.67/1.89  fof(c_0_18, negated_conjecture, ![X35]:((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&((v1_relat_1(esk5_0)&v1_funct_1(esk5_0))&((k1_relat_1(esk4_0)=k1_relat_1(esk5_0)&(~r2_hidden(X35,esk6_0)|k1_funct_1(esk4_0,X35)=k1_funct_1(esk5_0,X35)))&k7_relat_1(esk4_0,esk6_0)!=k7_relat_1(esk5_0,esk6_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])])).
% 1.67/1.89  cnf(c_0_19, plain, (k1_relat_1(k7_relat_1(X1,X2))=k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 1.67/1.89  cnf(c_0_20, negated_conjecture, (k1_relat_1(esk4_0)=k1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.67/1.89  cnf(c_0_21, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.67/1.89  fof(c_0_22, plain, ![X15, X16, X17]:(~v1_relat_1(X17)|k7_relat_1(k7_relat_1(X17,X15),X16)=k7_relat_1(X17,k3_xboole_0(X15,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).
% 1.67/1.89  fof(c_0_23, plain, ![X24, X26]:(((v1_relat_1(esk2_1(X24))&v1_funct_1(esk2_1(X24)))&k1_relat_1(esk2_1(X24))=X24)&(~r2_hidden(X26,X24)|k1_funct_1(esk2_1(X24),X26)=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e9_44_1__funct_1])])])])).
% 1.67/1.89  cnf(c_0_24, negated_conjecture, (k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),X1))=k1_relat_1(k7_relat_1(esk5_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])).
% 1.67/1.89  cnf(c_0_25, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.67/1.89  fof(c_0_26, plain, ![X23]:(~v1_relat_1(X23)|k7_relat_1(X23,k1_relat_1(X23))=X23), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).
% 1.67/1.89  fof(c_0_27, plain, ![X18, X19, X20]:(((r2_hidden(X18,X19)|~r2_hidden(X18,k1_relat_1(k7_relat_1(X20,X19)))|~v1_relat_1(X20))&(r2_hidden(X18,k1_relat_1(X20))|~r2_hidden(X18,k1_relat_1(k7_relat_1(X20,X19)))|~v1_relat_1(X20)))&(~r2_hidden(X18,X19)|~r2_hidden(X18,k1_relat_1(X20))|r2_hidden(X18,k1_relat_1(k7_relat_1(X20,X19)))|~v1_relat_1(X20))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).
% 1.67/1.89  cnf(c_0_28, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.67/1.89  cnf(c_0_29, plain, (k1_relat_1(esk2_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.67/1.89  cnf(c_0_30, plain, (v1_relat_1(esk2_1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.67/1.89  cnf(c_0_31, negated_conjecture, (k1_relat_1(k7_relat_1(esk5_0,X1))=k1_relat_1(k7_relat_1(esk4_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_24]), c_0_25])])).
% 1.67/1.89  cnf(c_0_32, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.67/1.89  cnf(c_0_33, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X3)))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.67/1.89  fof(c_0_34, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 1.67/1.89  cnf(c_0_35, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_28, c_0_17])).
% 1.67/1.89  cnf(c_0_36, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k1_relat_1(k7_relat_1(esk2_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_29]), c_0_30])])).
% 1.67/1.89  cnf(c_0_37, negated_conjecture, (k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),X1))=k1_relat_1(k7_relat_1(esk4_0,X1))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])]), c_0_31])).
% 1.67/1.89  cnf(c_0_38, negated_conjecture, (k1_relat_1(k7_relat_1(esk4_0,k1_relat_1(esk4_0)))=k1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_20]), c_0_20]), c_0_21])])).
% 1.67/1.89  cnf(c_0_39, negated_conjecture, (r2_hidden(X1,k1_relat_1(esk4_0))|~r2_hidden(X1,k1_relat_1(k7_relat_1(esk4_0,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_31]), c_0_20]), c_0_21])])).
% 1.67/1.89  cnf(c_0_40, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.67/1.89  cnf(c_0_41, plain, (k7_relat_1(X1,k1_relat_1(k7_relat_1(esk2_1(X2),X3)))=k7_relat_1(k7_relat_1(X1,X2),X3)|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 1.67/1.89  cnf(c_0_42, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_1(k1_relat_1(esk4_0)),X1))=k1_relat_1(k7_relat_1(esk4_0,X1))), inference(rw,[status(thm)],[c_0_37, c_0_36])).
% 1.67/1.89  cnf(c_0_43, negated_conjecture, (k7_relat_1(k7_relat_1(esk4_0,k1_relat_1(esk4_0)),k1_relat_1(esk4_0))=k7_relat_1(esk4_0,k1_relat_1(esk4_0))|~v1_relat_1(k7_relat_1(esk4_0,k1_relat_1(esk4_0)))), inference(spm,[status(thm)],[c_0_32, c_0_38])).
% 1.67/1.89  fof(c_0_44, plain, ![X27, X28, X29, X30]:((k7_relat_1(X27,X29)!=k7_relat_1(X28,X29)|(~r2_hidden(X30,X29)|k1_funct_1(X27,X30)=k1_funct_1(X28,X30))|(~r1_tarski(X29,k1_relat_1(X27))|~r1_tarski(X29,k1_relat_1(X28)))|(~v1_relat_1(X28)|~v1_funct_1(X28))|(~v1_relat_1(X27)|~v1_funct_1(X27)))&((r2_hidden(esk3_3(X27,X28,X29),X29)|k7_relat_1(X27,X29)=k7_relat_1(X28,X29)|(~r1_tarski(X29,k1_relat_1(X27))|~r1_tarski(X29,k1_relat_1(X28)))|(~v1_relat_1(X28)|~v1_funct_1(X28))|(~v1_relat_1(X27)|~v1_funct_1(X27)))&(k1_funct_1(X27,esk3_3(X27,X28,X29))!=k1_funct_1(X28,esk3_3(X27,X28,X29))|k7_relat_1(X27,X29)=k7_relat_1(X28,X29)|(~r1_tarski(X29,k1_relat_1(X27))|~r1_tarski(X29,k1_relat_1(X28)))|(~v1_relat_1(X28)|~v1_funct_1(X28))|(~v1_relat_1(X27)|~v1_funct_1(X27))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t165_funct_1])])])])])).
% 1.67/1.89  cnf(c_0_45, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.67/1.89  cnf(c_0_46, negated_conjecture, (r2_hidden(esk1_2(k1_relat_1(k7_relat_1(esk4_0,X1)),X2),k1_relat_1(esk4_0))|r1_tarski(k1_relat_1(k7_relat_1(esk4_0,X1)),X2)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 1.67/1.89  cnf(c_0_47, negated_conjecture, (k7_relat_1(k7_relat_1(X1,k1_relat_1(esk4_0)),X2)=k7_relat_1(X1,k1_relat_1(k7_relat_1(esk4_0,X2)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 1.67/1.89  cnf(c_0_48, negated_conjecture, (k7_relat_1(esk4_0,k1_relat_1(esk4_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_32]), c_0_25])])).
% 1.67/1.89  cnf(c_0_49, plain, (r2_hidden(esk3_3(X1,X2,X3),X3)|k7_relat_1(X1,X3)=k7_relat_1(X2,X3)|~r1_tarski(X3,k1_relat_1(X1))|~r1_tarski(X3,k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 1.67/1.89  cnf(c_0_50, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(esk4_0,X1)),k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 1.67/1.89  cnf(c_0_51, negated_conjecture, (k7_relat_1(esk4_0,k1_relat_1(k7_relat_1(esk4_0,X1)))=k7_relat_1(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_25])])).
% 1.67/1.89  cnf(c_0_52, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.67/1.89  cnf(c_0_53, negated_conjecture, (k7_relat_1(esk5_0,k1_relat_1(esk4_0))=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_20]), c_0_21])])).
% 1.67/1.89  cnf(c_0_54, plain, (k7_relat_1(X1,X3)=k7_relat_1(X2,X3)|k1_funct_1(X1,esk3_3(X1,X2,X3))!=k1_funct_1(X2,esk3_3(X1,X2,X3))|~r1_tarski(X3,k1_relat_1(X1))|~r1_tarski(X3,k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 1.67/1.89  cnf(c_0_55, negated_conjecture, (k1_funct_1(esk4_0,X1)=k1_funct_1(esk5_0,X1)|~r2_hidden(X1,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.67/1.89  cnf(c_0_56, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.67/1.89  cnf(c_0_57, negated_conjecture, (k7_relat_1(X1,k1_relat_1(k7_relat_1(esk4_0,X2)))=k7_relat_1(esk4_0,X2)|r2_hidden(esk3_3(X1,esk4_0,k1_relat_1(k7_relat_1(esk4_0,X2))),k1_relat_1(k7_relat_1(esk4_0,X2)))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(k7_relat_1(esk4_0,X2)),k1_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), c_0_52]), c_0_25])])).
% 1.67/1.89  cnf(c_0_58, negated_conjecture, (k7_relat_1(esk5_0,k1_relat_1(k7_relat_1(esk4_0,X1)))=k7_relat_1(esk5_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_53]), c_0_21])])).
% 1.67/1.89  cnf(c_0_59, negated_conjecture, (k7_relat_1(esk5_0,X1)=k7_relat_1(X2,X1)|k1_funct_1(esk4_0,esk3_3(esk5_0,X2,X1))!=k1_funct_1(X2,esk3_3(esk5_0,X2,X1))|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(esk3_3(esk5_0,X2,X1),esk6_0)|~r1_tarski(X1,k1_relat_1(esk4_0))|~r1_tarski(X1,k1_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), c_0_21]), c_0_20])])).
% 1.67/1.89  cnf(c_0_60, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.67/1.89  cnf(c_0_61, negated_conjecture, (k7_relat_1(esk5_0,X1)=k7_relat_1(esk4_0,X1)|r2_hidden(esk3_3(esk5_0,esk4_0,k1_relat_1(k7_relat_1(esk4_0,X1))),k1_relat_1(k7_relat_1(esk4_0,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_20]), c_0_58]), c_0_56]), c_0_21]), c_0_50])])).
% 1.67/1.89  cnf(c_0_62, negated_conjecture, (k7_relat_1(esk5_0,X1)=k7_relat_1(esk4_0,X1)|~r2_hidden(esk3_3(esk5_0,esk4_0,X1),esk6_0)|~r1_tarski(X1,k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_59]), c_0_52]), c_0_25])])).
% 1.67/1.89  cnf(c_0_63, negated_conjecture, (k7_relat_1(esk5_0,X1)=k7_relat_1(esk4_0,X1)|r2_hidden(esk3_3(esk5_0,esk4_0,k1_relat_1(k7_relat_1(esk4_0,X1))),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_25])])).
% 1.67/1.89  cnf(c_0_64, negated_conjecture, (k7_relat_1(esk4_0,esk6_0)!=k7_relat_1(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.67/1.89  cnf(c_0_65, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_58]), c_0_51]), c_0_50])]), c_0_64]), ['proof']).
% 1.67/1.89  # SZS output end CNFRefutation
% 1.67/1.89  # Proof object total steps             : 66
% 1.67/1.89  # Proof object clause steps            : 45
% 1.67/1.89  # Proof object formula steps           : 21
% 1.67/1.89  # Proof object conjectures             : 30
% 1.67/1.89  # Proof object clause conjectures      : 27
% 1.67/1.89  # Proof object formula conjectures     : 3
% 1.67/1.89  # Proof object initial clauses used    : 20
% 1.67/1.89  # Proof object initial formulas used   : 10
% 1.67/1.89  # Proof object generating inferences   : 20
% 1.67/1.89  # Proof object simplifying inferences  : 52
% 1.67/1.89  # Training examples: 0 positive, 0 negative
% 1.67/1.89  # Parsed axioms                        : 10
% 1.67/1.89  # Removed by relevancy pruning/SinE    : 0
% 1.67/1.89  # Initial clauses                      : 25
% 1.67/1.89  # Removed in clause preprocessing      : 2
% 1.67/1.89  # Initial clauses in saturation        : 23
% 1.67/1.89  # Processed clauses                    : 8609
% 1.67/1.89  # ...of these trivial                  : 235
% 1.67/1.89  # ...subsumed                          : 7467
% 1.67/1.89  # ...remaining for further processing  : 907
% 1.67/1.89  # Other redundant clauses eliminated   : 0
% 1.67/1.89  # Clauses deleted for lack of memory   : 0
% 1.67/1.89  # Backward-subsumed                    : 37
% 1.67/1.89  # Backward-rewritten                   : 22
% 1.67/1.89  # Generated clauses                    : 124824
% 1.67/1.89  # ...of the previous two non-trivial   : 105799
% 1.67/1.89  # Contextual simplify-reflections      : 4
% 1.67/1.89  # Paramodulations                      : 124821
% 1.67/1.89  # Factorizations                       : 0
% 1.67/1.89  # Equation resolutions                 : 3
% 1.67/1.89  # Propositional unsat checks           : 0
% 1.67/1.89  #    Propositional check models        : 0
% 1.67/1.89  #    Propositional check unsatisfiable : 0
% 1.67/1.89  #    Propositional clauses             : 0
% 1.67/1.89  #    Propositional clauses after purity: 0
% 1.67/1.89  #    Propositional unsat core size     : 0
% 1.67/1.89  #    Propositional preprocessing time  : 0.000
% 1.67/1.89  #    Propositional encoding time       : 0.000
% 1.67/1.89  #    Propositional solver time         : 0.000
% 1.67/1.89  #    Success case prop preproc time    : 0.000
% 1.67/1.89  #    Success case prop encoding time   : 0.000
% 1.67/1.89  #    Success case prop solver time     : 0.000
% 1.67/1.89  # Current number of processed clauses  : 825
% 1.67/1.89  #    Positive orientable unit clauses  : 85
% 1.67/1.89  #    Positive unorientable unit clauses: 0
% 1.67/1.89  #    Negative unit clauses             : 1
% 1.67/1.89  #    Non-unit-clauses                  : 739
% 1.67/1.89  # Current number of unprocessed clauses: 96876
% 1.67/1.89  # ...number of literals in the above   : 488389
% 1.67/1.89  # Current number of archived formulas  : 0
% 1.67/1.89  # Current number of archived clauses   : 84
% 1.67/1.89  # Clause-clause subsumption calls (NU) : 198217
% 1.67/1.89  # Rec. Clause-clause subsumption calls : 97570
% 1.67/1.89  # Non-unit clause-clause subsumptions  : 7503
% 1.67/1.89  # Unit Clause-clause subsumption calls : 528
% 1.67/1.89  # Rewrite failures with RHS unbound    : 0
% 1.67/1.89  # BW rewrite match attempts            : 1326
% 1.67/1.89  # BW rewrite match successes           : 27
% 1.67/1.89  # Condensation attempts                : 0
% 1.67/1.89  # Condensation successes               : 0
% 1.67/1.89  # Termbank termtop insertions          : 4942970
% 1.67/1.89  
% 1.67/1.89  # -------------------------------------------------
% 1.67/1.89  # User time                : 1.484 s
% 1.67/1.89  # System time              : 0.071 s
% 1.67/1.89  # Total time               : 1.555 s
% 1.67/1.89  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
