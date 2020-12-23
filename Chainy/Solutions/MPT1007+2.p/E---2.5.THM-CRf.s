%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1007+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:00 EST 2020

% Result     : Theorem 22.07s
% Output     : CNFRefutation 22.07s
% Verified   : 
% Statistics : Number of formulae       :   40 (  73 expanded)
%              Number of clauses        :   19 (  26 expanded)
%              Number of leaves         :   10 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :  146 ( 227 expanded)
%              Number of equality atoms :   89 ( 122 expanded)
%              Maximal formula depth    :   47 (   5 average)
%              Maximal clause size      :   68 (   1 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t61_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,k1_tarski(X1),X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
     => ( X2 != k1_xboole_0
       => r2_hidden(k1_funct_1(X3,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t75_enumset1)).

fof(t7_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_hidden(X3,X1)
       => ( X2 = k1_xboole_0
          | r2_hidden(k1_funct_1(X4,X3),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

fof(d6_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( X9 = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> ~ ( X10 != X1
              & X10 != X2
              & X10 != X3
              & X10 != X4
              & X10 != X5
              & X10 != X6
              & X10 != X7
              & X10 != X8 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT005+2.ax',d6_enumset1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
       => ( X2 != k1_xboole_0
         => r2_hidden(k1_funct_1(X3,X1),X2) ) ) ),
    inference(assume_negation,[status(cth)],[t61_funct_2])).

fof(c_0_11,negated_conjecture,
    ( v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,k1_tarski(esk1_0),esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk1_0),esk2_0)))
    & esk2_0 != k1_xboole_0
    & ~ r2_hidden(k1_funct_1(esk3_0,esk1_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_12,plain,(
    ! [X1162] : k2_tarski(X1162,X1162) = k1_tarski(X1162) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_13,plain,(
    ! [X2277,X2278] : k1_enumset1(X2277,X2277,X2278) = k2_tarski(X2277,X2278) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_14,plain,(
    ! [X3308,X3309,X3310] : k2_enumset1(X3308,X3308,X3309,X3310) = k1_enumset1(X3308,X3309,X3310) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_15,plain,(
    ! [X3311,X3312,X3313,X3314] : k3_enumset1(X3311,X3311,X3312,X3313,X3314) = k2_enumset1(X3311,X3312,X3313,X3314) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_16,plain,(
    ! [X3927,X3928,X3929,X3930,X3931] : k4_enumset1(X3927,X3927,X3928,X3929,X3930,X3931) = k3_enumset1(X3927,X3928,X3929,X3930,X3931) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_17,plain,(
    ! [X3978,X3979,X3980,X3981,X3982,X3983] : k5_enumset1(X3978,X3978,X3979,X3980,X3981,X3982,X3983) = k4_enumset1(X3978,X3979,X3980,X3981,X3982,X3983) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_18,plain,(
    ! [X4049,X4050,X4051,X4052,X4053,X4054,X4055] : k6_enumset1(X4049,X4049,X4050,X4051,X4052,X4053,X4054,X4055) = k5_enumset1(X4049,X4050,X4051,X4052,X4053,X4054,X4055) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_19,plain,(
    ! [X808,X809,X810,X811] :
      ( ~ v1_funct_1(X811)
      | ~ v1_funct_2(X811,X808,X809)
      | ~ m1_subset_1(X811,k1_zfmisc_1(k2_zfmisc_1(X808,X809)))
      | ~ r2_hidden(X810,X808)
      | X809 = k1_xboole_0
      | r2_hidden(k1_funct_1(X811,X810),X809) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_2(esk3_0,k1_tarski(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk1_0),esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_29,plain,(
    ! [X4103,X4104,X4105,X4106,X4107,X4108,X4109,X4110,X4111,X4112,X4113,X4114,X4115,X4116,X4117,X4118,X4119,X4120,X4121,X4122] :
      ( ( ~ r2_hidden(X4112,X4111)
        | X4112 = X4103
        | X4112 = X4104
        | X4112 = X4105
        | X4112 = X4106
        | X4112 = X4107
        | X4112 = X4108
        | X4112 = X4109
        | X4112 = X4110
        | X4111 != k6_enumset1(X4103,X4104,X4105,X4106,X4107,X4108,X4109,X4110) )
      & ( X4113 != X4103
        | r2_hidden(X4113,X4111)
        | X4111 != k6_enumset1(X4103,X4104,X4105,X4106,X4107,X4108,X4109,X4110) )
      & ( X4113 != X4104
        | r2_hidden(X4113,X4111)
        | X4111 != k6_enumset1(X4103,X4104,X4105,X4106,X4107,X4108,X4109,X4110) )
      & ( X4113 != X4105
        | r2_hidden(X4113,X4111)
        | X4111 != k6_enumset1(X4103,X4104,X4105,X4106,X4107,X4108,X4109,X4110) )
      & ( X4113 != X4106
        | r2_hidden(X4113,X4111)
        | X4111 != k6_enumset1(X4103,X4104,X4105,X4106,X4107,X4108,X4109,X4110) )
      & ( X4113 != X4107
        | r2_hidden(X4113,X4111)
        | X4111 != k6_enumset1(X4103,X4104,X4105,X4106,X4107,X4108,X4109,X4110) )
      & ( X4113 != X4108
        | r2_hidden(X4113,X4111)
        | X4111 != k6_enumset1(X4103,X4104,X4105,X4106,X4107,X4108,X4109,X4110) )
      & ( X4113 != X4109
        | r2_hidden(X4113,X4111)
        | X4111 != k6_enumset1(X4103,X4104,X4105,X4106,X4107,X4108,X4109,X4110) )
      & ( X4113 != X4110
        | r2_hidden(X4113,X4111)
        | X4111 != k6_enumset1(X4103,X4104,X4105,X4106,X4107,X4108,X4109,X4110) )
      & ( esk401_9(X4114,X4115,X4116,X4117,X4118,X4119,X4120,X4121,X4122) != X4114
        | ~ r2_hidden(esk401_9(X4114,X4115,X4116,X4117,X4118,X4119,X4120,X4121,X4122),X4122)
        | X4122 = k6_enumset1(X4114,X4115,X4116,X4117,X4118,X4119,X4120,X4121) )
      & ( esk401_9(X4114,X4115,X4116,X4117,X4118,X4119,X4120,X4121,X4122) != X4115
        | ~ r2_hidden(esk401_9(X4114,X4115,X4116,X4117,X4118,X4119,X4120,X4121,X4122),X4122)
        | X4122 = k6_enumset1(X4114,X4115,X4116,X4117,X4118,X4119,X4120,X4121) )
      & ( esk401_9(X4114,X4115,X4116,X4117,X4118,X4119,X4120,X4121,X4122) != X4116
        | ~ r2_hidden(esk401_9(X4114,X4115,X4116,X4117,X4118,X4119,X4120,X4121,X4122),X4122)
        | X4122 = k6_enumset1(X4114,X4115,X4116,X4117,X4118,X4119,X4120,X4121) )
      & ( esk401_9(X4114,X4115,X4116,X4117,X4118,X4119,X4120,X4121,X4122) != X4117
        | ~ r2_hidden(esk401_9(X4114,X4115,X4116,X4117,X4118,X4119,X4120,X4121,X4122),X4122)
        | X4122 = k6_enumset1(X4114,X4115,X4116,X4117,X4118,X4119,X4120,X4121) )
      & ( esk401_9(X4114,X4115,X4116,X4117,X4118,X4119,X4120,X4121,X4122) != X4118
        | ~ r2_hidden(esk401_9(X4114,X4115,X4116,X4117,X4118,X4119,X4120,X4121,X4122),X4122)
        | X4122 = k6_enumset1(X4114,X4115,X4116,X4117,X4118,X4119,X4120,X4121) )
      & ( esk401_9(X4114,X4115,X4116,X4117,X4118,X4119,X4120,X4121,X4122) != X4119
        | ~ r2_hidden(esk401_9(X4114,X4115,X4116,X4117,X4118,X4119,X4120,X4121,X4122),X4122)
        | X4122 = k6_enumset1(X4114,X4115,X4116,X4117,X4118,X4119,X4120,X4121) )
      & ( esk401_9(X4114,X4115,X4116,X4117,X4118,X4119,X4120,X4121,X4122) != X4120
        | ~ r2_hidden(esk401_9(X4114,X4115,X4116,X4117,X4118,X4119,X4120,X4121,X4122),X4122)
        | X4122 = k6_enumset1(X4114,X4115,X4116,X4117,X4118,X4119,X4120,X4121) )
      & ( esk401_9(X4114,X4115,X4116,X4117,X4118,X4119,X4120,X4121,X4122) != X4121
        | ~ r2_hidden(esk401_9(X4114,X4115,X4116,X4117,X4118,X4119,X4120,X4121,X4122),X4122)
        | X4122 = k6_enumset1(X4114,X4115,X4116,X4117,X4118,X4119,X4120,X4121) )
      & ( r2_hidden(esk401_9(X4114,X4115,X4116,X4117,X4118,X4119,X4120,X4121,X4122),X4122)
        | esk401_9(X4114,X4115,X4116,X4117,X4118,X4119,X4120,X4121,X4122) = X4114
        | esk401_9(X4114,X4115,X4116,X4117,X4118,X4119,X4120,X4121,X4122) = X4115
        | esk401_9(X4114,X4115,X4116,X4117,X4118,X4119,X4120,X4121,X4122) = X4116
        | esk401_9(X4114,X4115,X4116,X4117,X4118,X4119,X4120,X4121,X4122) = X4117
        | esk401_9(X4114,X4115,X4116,X4117,X4118,X4119,X4120,X4121,X4122) = X4118
        | esk401_9(X4114,X4115,X4116,X4117,X4118,X4119,X4120,X4121,X4122) = X4119
        | esk401_9(X4114,X4115,X4116,X4117,X4118,X4119,X4120,X4121,X4122) = X4120
        | esk401_9(X4114,X4115,X4116,X4117,X4118,X4119,X4120,X4121,X4122) = X4121
        | X4122 = k6_enumset1(X4114,X4115,X4116,X4117,X4118,X4119,X4120,X4121) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).

cnf(c_0_30,plain,
    ( X3 = k1_xboole_0
    | r2_hidden(k1_funct_1(X1,X4),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_2(esk3_0,k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X5,X2,X6,X7,X8,X9,X10) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk3_0,X1),esk2_0)
    | ~ r2_hidden(X1,k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X3,X1,X4,X5,X6,X7,X8)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_35])])).

cnf(c_0_38,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk3_0,esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),
    [proof]).
%------------------------------------------------------------------------------
