%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:35 EST 2020

% Result     : Theorem 10.51s
% Output     : CNFRefutation 10.51s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 669 expanded)
%              Number of clauses        :   45 ( 275 expanded)
%              Number of leaves         :   11 ( 167 expanded)
%              Depth                    :   13
%              Number of atoms          :  204 (2382 expanded)
%              Number of equality atoms :   64 ( 979 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   25 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_funct_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t189_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k7_relat_1(X1,k1_relat_1(X2)) = k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,k1_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_relat_1)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(t86_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X1,k1_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

fof(s3_funct_1__e9_44_1__funct_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( v1_relat_1(X2)
      & v1_funct_1(X2)
      & k1_relat_1(X2) = X1
      & ! [X3] :
          ( r2_hidden(X3,X1)
         => k1_funct_1(X2,X3) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e9_44_1__funct_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t192_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k7_relat_1(X2,k3_xboole_0(k1_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t165_funct_1)).

fof(c_0_11,negated_conjecture,(
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

fof(c_0_12,plain,(
    ! [X15,X16] : k1_setfam_1(k2_tarski(X15,X16)) = k3_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_13,plain,(
    ! [X13,X14] : k1_enumset1(X13,X13,X14) = k2_tarski(X13,X14) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_14,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X17)
      | ~ v1_relat_1(X18)
      | k7_relat_1(X17,k1_relat_1(X18)) = k7_relat_1(X17,k1_relat_1(k7_relat_1(X18,k1_relat_1(X17)))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t189_relat_1])])])).

fof(c_0_15,negated_conjecture,(
    ! [X37] :
      ( v1_relat_1(esk4_0)
      & v1_funct_1(esk4_0)
      & v1_relat_1(esk5_0)
      & v1_funct_1(esk5_0)
      & k1_relat_1(esk4_0) = k1_relat_1(esk5_0)
      & ( ~ r2_hidden(X37,esk6_0)
        | k1_funct_1(esk4_0,X37) = k1_funct_1(esk5_0,X37) )
      & k7_relat_1(esk4_0,esk6_0) != k7_relat_1(esk5_0,esk6_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).

fof(c_0_16,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X25)
      | k1_relat_1(k7_relat_1(X25,X24)) = k3_xboole_0(k1_relat_1(X25),X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

cnf(c_0_17,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X21,X22,X23] :
      ( ( r2_hidden(X21,X22)
        | ~ r2_hidden(X21,k1_relat_1(k7_relat_1(X23,X22)))
        | ~ v1_relat_1(X23) )
      & ( r2_hidden(X21,k1_relat_1(X23))
        | ~ r2_hidden(X21,k1_relat_1(k7_relat_1(X23,X22)))
        | ~ v1_relat_1(X23) )
      & ( ~ r2_hidden(X21,X22)
        | ~ r2_hidden(X21,k1_relat_1(X23))
        | r2_hidden(X21,k1_relat_1(k7_relat_1(X23,X22)))
        | ~ v1_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).

cnf(c_0_20,plain,
    ( k7_relat_1(X1,k1_relat_1(X2)) = k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,k1_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( k1_relat_1(esk4_0) = k1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X3)))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( k7_relat_1(esk5_0,k1_relat_1(k7_relat_1(X1,k1_relat_1(esk4_0)))) = k7_relat_1(esk5_0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

fof(c_0_27,plain,(
    ! [X26,X28] :
      ( v1_relat_1(esk2_1(X26))
      & v1_funct_1(esk2_1(X26))
      & k1_relat_1(esk2_1(X26)) = X26
      & ( ~ r2_hidden(X28,X26)
        | k1_funct_1(esk2_1(X26),X28) = k1_xboole_0 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e9_44_1__funct_1])])])])).

cnf(c_0_28,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(esk4_0))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(esk5_0,k1_relat_1(X2)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_21]),c_0_22])])).

cnf(c_0_30,plain,
    ( k1_relat_1(esk2_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_31,plain,
    ( v1_relat_1(esk2_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),X1)) = k1_relat_1(k7_relat_1(esk5_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_21]),c_0_22])])).

cnf(c_0_33,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_34,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(esk4_0))
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(esk5_0,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])])).

cnf(c_0_36,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk5_0,X1)) = k1_relat_1(k7_relat_1(esk4_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_32]),c_0_33])])).

fof(c_0_37,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_38,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X20)
      | k7_relat_1(X20,X19) = k7_relat_1(X20,k3_xboole_0(k1_relat_1(X20),X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t192_relat_1])])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(esk4_0))
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(esk4_0,X2))) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_42,plain,
    ( k7_relat_1(X1,X2) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_43,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k1_setfam_1(k1_enumset1(X2,X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_24]),c_0_24])).

cnf(c_0_44,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),X1)) = k1_relat_1(k7_relat_1(esk4_0,X1)) ),
    inference(rw,[status(thm)],[c_0_32,c_0_36])).

fof(c_0_45,plain,(
    ! [X29,X30,X31,X32] :
      ( ( k7_relat_1(X29,X31) != k7_relat_1(X30,X31)
        | ~ r2_hidden(X32,X31)
        | k1_funct_1(X29,X32) = k1_funct_1(X30,X32)
        | ~ r1_tarski(X31,k1_relat_1(X29))
        | ~ r1_tarski(X31,k1_relat_1(X30))
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( r2_hidden(esk3_3(X29,X30,X31),X31)
        | k7_relat_1(X29,X31) = k7_relat_1(X30,X31)
        | ~ r1_tarski(X31,k1_relat_1(X29))
        | ~ r1_tarski(X31,k1_relat_1(X30))
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( k1_funct_1(X29,esk3_3(X29,X30,X31)) != k1_funct_1(X30,esk3_3(X29,X30,X31))
        | k7_relat_1(X29,X31) = k7_relat_1(X30,X31)
        | ~ r1_tarski(X31,k1_relat_1(X29))
        | ~ r1_tarski(X31,k1_relat_1(X30))
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t165_funct_1])])])])])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk1_2(k1_relat_1(k7_relat_1(esk4_0,X1)),X2),k1_relat_1(esk4_0))
    | r1_tarski(k1_relat_1(k7_relat_1(esk4_0,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,plain,
    ( k7_relat_1(X1,X2) = k7_relat_1(X1,k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_42,c_0_24])).

cnf(c_0_49,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(X1,X1,k1_relat_1(esk4_0))) = k1_relat_1(k7_relat_1(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k1_relat_1(k7_relat_1(esk2_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_30]),c_0_31])])).

cnf(c_0_51,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X3)
    | k7_relat_1(X1,X3) = k7_relat_1(X2,X3)
    | ~ r1_tarski(X3,k1_relat_1(X1))
    | ~ r1_tarski(X3,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk4_0,X1)),k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( k7_relat_1(esk4_0,k1_relat_1(k7_relat_1(esk4_0,X1))) = k7_relat_1(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_44]),c_0_33])])).

cnf(c_0_54,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_55,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_1(X1),k1_relat_1(esk4_0))) = k1_relat_1(k7_relat_1(esk4_0,X1)) ),
    inference(rw,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,plain,
    ( k7_relat_1(X1,X3) = k7_relat_1(X2,X3)
    | k1_funct_1(X1,esk3_3(X1,X2,X3)) != k1_funct_1(X2,esk3_3(X1,X2,X3))
    | ~ r1_tarski(X3,k1_relat_1(X1))
    | ~ r1_tarski(X3,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_57,negated_conjecture,
    ( k1_funct_1(esk4_0,X1) = k1_funct_1(esk5_0,X1)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_58,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_59,negated_conjecture,
    ( k7_relat_1(X1,k1_relat_1(k7_relat_1(esk4_0,X2))) = k7_relat_1(esk4_0,X2)
    | r2_hidden(esk3_3(X1,esk4_0,k1_relat_1(k7_relat_1(esk4_0,X2))),k1_relat_1(k7_relat_1(esk4_0,X2)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(esk4_0,X2)),k1_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_54]),c_0_33])])).

cnf(c_0_60,negated_conjecture,
    ( k7_relat_1(esk5_0,k1_relat_1(k7_relat_1(esk4_0,X1))) = k7_relat_1(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_55]),c_0_30]),c_0_31])])).

cnf(c_0_61,negated_conjecture,
    ( k7_relat_1(esk5_0,X1) = k7_relat_1(X2,X1)
    | k1_funct_1(esk4_0,esk3_3(esk5_0,X2,X1)) != k1_funct_1(X2,esk3_3(esk5_0,X2,X1))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(esk3_3(esk5_0,X2,X1),esk6_0)
    | ~ r1_tarski(X1,k1_relat_1(esk4_0))
    | ~ r1_tarski(X1,k1_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58]),c_0_22]),c_0_21])])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_63,negated_conjecture,
    ( k7_relat_1(esk5_0,X1) = k7_relat_1(esk4_0,X1)
    | r2_hidden(esk3_3(esk5_0,esk4_0,k1_relat_1(k7_relat_1(esk4_0,X1))),k1_relat_1(k7_relat_1(esk4_0,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_21]),c_0_60]),c_0_58]),c_0_22]),c_0_52])])).

cnf(c_0_64,negated_conjecture,
    ( k7_relat_1(esk5_0,X1) = k7_relat_1(esk4_0,X1)
    | ~ r2_hidden(esk3_3(esk5_0,esk4_0,X1),esk6_0)
    | ~ r1_tarski(X1,k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_61]),c_0_54]),c_0_33])])).

cnf(c_0_65,negated_conjecture,
    ( k7_relat_1(esk5_0,X1) = k7_relat_1(esk4_0,X1)
    | r2_hidden(esk3_3(esk5_0,esk4_0,k1_relat_1(k7_relat_1(esk4_0,X1))),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_33])])).

cnf(c_0_66,negated_conjecture,
    ( k7_relat_1(esk4_0,esk6_0) != k7_relat_1(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_60]),c_0_53]),c_0_52])]),c_0_66]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:05:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 10.51/10.75  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 10.51/10.75  # and selection function SelectComplexExceptUniqMaxHorn.
% 10.51/10.75  #
% 10.51/10.75  # Preprocessing time       : 0.028 s
% 10.51/10.75  # Presaturation interreduction done
% 10.51/10.75  
% 10.51/10.75  # Proof found!
% 10.51/10.75  # SZS status Theorem
% 10.51/10.75  # SZS output start CNFRefutation
% 10.51/10.75  fof(t166_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((k1_relat_1(X1)=k1_relat_1(X2)&![X4]:(r2_hidden(X4,X3)=>k1_funct_1(X1,X4)=k1_funct_1(X2,X4)))=>k7_relat_1(X1,X3)=k7_relat_1(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_funct_1)).
% 10.51/10.75  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 10.51/10.75  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 10.51/10.75  fof(t189_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k7_relat_1(X1,k1_relat_1(X2))=k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,k1_relat_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t189_relat_1)).
% 10.51/10.75  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 10.51/10.75  fof(t86_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))<=>(r2_hidden(X1,X2)&r2_hidden(X1,k1_relat_1(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 10.51/10.75  fof(s3_funct_1__e9_44_1__funct_1, axiom, ![X1]:?[X2]:(((v1_relat_1(X2)&v1_funct_1(X2))&k1_relat_1(X2)=X1)&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e9_44_1__funct_1)).
% 10.51/10.75  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.51/10.75  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 10.51/10.75  fof(t192_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k7_relat_1(X2,k3_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_relat_1)).
% 10.51/10.75  fof(t165_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((r1_tarski(X3,k1_relat_1(X1))&r1_tarski(X3,k1_relat_1(X2)))=>(k7_relat_1(X1,X3)=k7_relat_1(X2,X3)<=>![X4]:(r2_hidden(X4,X3)=>k1_funct_1(X1,X4)=k1_funct_1(X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t165_funct_1)).
% 10.51/10.75  fof(c_0_11, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((k1_relat_1(X1)=k1_relat_1(X2)&![X4]:(r2_hidden(X4,X3)=>k1_funct_1(X1,X4)=k1_funct_1(X2,X4)))=>k7_relat_1(X1,X3)=k7_relat_1(X2,X3))))), inference(assume_negation,[status(cth)],[t166_funct_1])).
% 10.51/10.75  fof(c_0_12, plain, ![X15, X16]:k1_setfam_1(k2_tarski(X15,X16))=k3_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 10.51/10.75  fof(c_0_13, plain, ![X13, X14]:k1_enumset1(X13,X13,X14)=k2_tarski(X13,X14), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 10.51/10.75  fof(c_0_14, plain, ![X17, X18]:(~v1_relat_1(X17)|(~v1_relat_1(X18)|k7_relat_1(X17,k1_relat_1(X18))=k7_relat_1(X17,k1_relat_1(k7_relat_1(X18,k1_relat_1(X17)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t189_relat_1])])])).
% 10.51/10.75  fof(c_0_15, negated_conjecture, ![X37]:((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&((v1_relat_1(esk5_0)&v1_funct_1(esk5_0))&((k1_relat_1(esk4_0)=k1_relat_1(esk5_0)&(~r2_hidden(X37,esk6_0)|k1_funct_1(esk4_0,X37)=k1_funct_1(esk5_0,X37)))&k7_relat_1(esk4_0,esk6_0)!=k7_relat_1(esk5_0,esk6_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).
% 10.51/10.75  fof(c_0_16, plain, ![X24, X25]:(~v1_relat_1(X25)|k1_relat_1(k7_relat_1(X25,X24))=k3_xboole_0(k1_relat_1(X25),X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 10.51/10.75  cnf(c_0_17, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 10.51/10.75  cnf(c_0_18, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 10.51/10.75  fof(c_0_19, plain, ![X21, X22, X23]:(((r2_hidden(X21,X22)|~r2_hidden(X21,k1_relat_1(k7_relat_1(X23,X22)))|~v1_relat_1(X23))&(r2_hidden(X21,k1_relat_1(X23))|~r2_hidden(X21,k1_relat_1(k7_relat_1(X23,X22)))|~v1_relat_1(X23)))&(~r2_hidden(X21,X22)|~r2_hidden(X21,k1_relat_1(X23))|r2_hidden(X21,k1_relat_1(k7_relat_1(X23,X22)))|~v1_relat_1(X23))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).
% 10.51/10.75  cnf(c_0_20, plain, (k7_relat_1(X1,k1_relat_1(X2))=k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,k1_relat_1(X1))))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 10.51/10.75  cnf(c_0_21, negated_conjecture, (k1_relat_1(esk4_0)=k1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 10.51/10.75  cnf(c_0_22, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 10.51/10.75  cnf(c_0_23, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 10.51/10.75  cnf(c_0_24, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 10.51/10.75  cnf(c_0_25, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X3)))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 10.51/10.75  cnf(c_0_26, negated_conjecture, (k7_relat_1(esk5_0,k1_relat_1(k7_relat_1(X1,k1_relat_1(esk4_0))))=k7_relat_1(esk5_0,k1_relat_1(X1))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])])).
% 10.51/10.75  fof(c_0_27, plain, ![X26, X28]:(((v1_relat_1(esk2_1(X26))&v1_funct_1(esk2_1(X26)))&k1_relat_1(esk2_1(X26))=X26)&(~r2_hidden(X28,X26)|k1_funct_1(esk2_1(X26),X28)=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e9_44_1__funct_1])])])])).
% 10.51/10.75  cnf(c_0_28, plain, (k1_relat_1(k7_relat_1(X1,X2))=k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 10.51/10.75  cnf(c_0_29, negated_conjecture, (r2_hidden(X1,k1_relat_1(esk4_0))|~v1_relat_1(X2)|~r2_hidden(X1,k1_relat_1(k7_relat_1(esk5_0,k1_relat_1(X2))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_21]), c_0_22])])).
% 10.51/10.75  cnf(c_0_30, plain, (k1_relat_1(esk2_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 10.51/10.75  cnf(c_0_31, plain, (v1_relat_1(esk2_1(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 10.51/10.75  cnf(c_0_32, negated_conjecture, (k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),X1))=k1_relat_1(k7_relat_1(esk5_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_21]), c_0_22])])).
% 10.51/10.75  cnf(c_0_33, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 10.51/10.75  fof(c_0_34, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 10.51/10.75  cnf(c_0_35, negated_conjecture, (r2_hidden(X1,k1_relat_1(esk4_0))|~r2_hidden(X1,k1_relat_1(k7_relat_1(esk5_0,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])])).
% 10.51/10.75  cnf(c_0_36, negated_conjecture, (k1_relat_1(k7_relat_1(esk5_0,X1))=k1_relat_1(k7_relat_1(esk4_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_32]), c_0_33])])).
% 10.51/10.75  fof(c_0_37, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 10.51/10.75  fof(c_0_38, plain, ![X19, X20]:(~v1_relat_1(X20)|k7_relat_1(X20,X19)=k7_relat_1(X20,k3_xboole_0(k1_relat_1(X20),X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t192_relat_1])])).
% 10.51/10.75  cnf(c_0_39, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 10.51/10.75  cnf(c_0_40, negated_conjecture, (r2_hidden(X1,k1_relat_1(esk4_0))|~r2_hidden(X1,k1_relat_1(k7_relat_1(esk4_0,X2)))), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 10.51/10.75  cnf(c_0_41, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 10.51/10.75  cnf(c_0_42, plain, (k7_relat_1(X1,X2)=k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 10.51/10.75  cnf(c_0_43, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k1_setfam_1(k1_enumset1(X2,X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_24]), c_0_24])).
% 10.51/10.75  cnf(c_0_44, negated_conjecture, (k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),X1))=k1_relat_1(k7_relat_1(esk4_0,X1))), inference(rw,[status(thm)],[c_0_32, c_0_36])).
% 10.51/10.75  fof(c_0_45, plain, ![X29, X30, X31, X32]:((k7_relat_1(X29,X31)!=k7_relat_1(X30,X31)|(~r2_hidden(X32,X31)|k1_funct_1(X29,X32)=k1_funct_1(X30,X32))|(~r1_tarski(X31,k1_relat_1(X29))|~r1_tarski(X31,k1_relat_1(X30)))|(~v1_relat_1(X30)|~v1_funct_1(X30))|(~v1_relat_1(X29)|~v1_funct_1(X29)))&((r2_hidden(esk3_3(X29,X30,X31),X31)|k7_relat_1(X29,X31)=k7_relat_1(X30,X31)|(~r1_tarski(X31,k1_relat_1(X29))|~r1_tarski(X31,k1_relat_1(X30)))|(~v1_relat_1(X30)|~v1_funct_1(X30))|(~v1_relat_1(X29)|~v1_funct_1(X29)))&(k1_funct_1(X29,esk3_3(X29,X30,X31))!=k1_funct_1(X30,esk3_3(X29,X30,X31))|k7_relat_1(X29,X31)=k7_relat_1(X30,X31)|(~r1_tarski(X31,k1_relat_1(X29))|~r1_tarski(X31,k1_relat_1(X30)))|(~v1_relat_1(X30)|~v1_funct_1(X30))|(~v1_relat_1(X29)|~v1_funct_1(X29))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t165_funct_1])])])])])).
% 10.51/10.75  cnf(c_0_46, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 10.51/10.75  cnf(c_0_47, negated_conjecture, (r2_hidden(esk1_2(k1_relat_1(k7_relat_1(esk4_0,X1)),X2),k1_relat_1(esk4_0))|r1_tarski(k1_relat_1(k7_relat_1(esk4_0,X1)),X2)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 10.51/10.75  cnf(c_0_48, plain, (k7_relat_1(X1,X2)=k7_relat_1(X1,k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_42, c_0_24])).
% 10.51/10.75  cnf(c_0_49, negated_conjecture, (k1_setfam_1(k1_enumset1(X1,X1,k1_relat_1(esk4_0)))=k1_relat_1(k7_relat_1(esk4_0,X1))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 10.51/10.75  cnf(c_0_50, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k1_relat_1(k7_relat_1(esk2_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_30]), c_0_31])])).
% 10.51/10.75  cnf(c_0_51, plain, (r2_hidden(esk3_3(X1,X2,X3),X3)|k7_relat_1(X1,X3)=k7_relat_1(X2,X3)|~r1_tarski(X3,k1_relat_1(X1))|~r1_tarski(X3,k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 10.51/10.75  cnf(c_0_52, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(esk4_0,X1)),k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 10.51/10.75  cnf(c_0_53, negated_conjecture, (k7_relat_1(esk4_0,k1_relat_1(k7_relat_1(esk4_0,X1)))=k7_relat_1(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_44]), c_0_33])])).
% 10.51/10.75  cnf(c_0_54, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 10.51/10.75  cnf(c_0_55, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_1(X1),k1_relat_1(esk4_0)))=k1_relat_1(k7_relat_1(esk4_0,X1))), inference(rw,[status(thm)],[c_0_49, c_0_50])).
% 10.51/10.75  cnf(c_0_56, plain, (k7_relat_1(X1,X3)=k7_relat_1(X2,X3)|k1_funct_1(X1,esk3_3(X1,X2,X3))!=k1_funct_1(X2,esk3_3(X1,X2,X3))|~r1_tarski(X3,k1_relat_1(X1))|~r1_tarski(X3,k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 10.51/10.75  cnf(c_0_57, negated_conjecture, (k1_funct_1(esk4_0,X1)=k1_funct_1(esk5_0,X1)|~r2_hidden(X1,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 10.51/10.75  cnf(c_0_58, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 10.51/10.75  cnf(c_0_59, negated_conjecture, (k7_relat_1(X1,k1_relat_1(k7_relat_1(esk4_0,X2)))=k7_relat_1(esk4_0,X2)|r2_hidden(esk3_3(X1,esk4_0,k1_relat_1(k7_relat_1(esk4_0,X2))),k1_relat_1(k7_relat_1(esk4_0,X2)))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(k7_relat_1(esk4_0,X2)),k1_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53]), c_0_54]), c_0_33])])).
% 10.51/10.75  cnf(c_0_60, negated_conjecture, (k7_relat_1(esk5_0,k1_relat_1(k7_relat_1(esk4_0,X1)))=k7_relat_1(esk5_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_55]), c_0_30]), c_0_31])])).
% 10.51/10.75  cnf(c_0_61, negated_conjecture, (k7_relat_1(esk5_0,X1)=k7_relat_1(X2,X1)|k1_funct_1(esk4_0,esk3_3(esk5_0,X2,X1))!=k1_funct_1(X2,esk3_3(esk5_0,X2,X1))|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(esk3_3(esk5_0,X2,X1),esk6_0)|~r1_tarski(X1,k1_relat_1(esk4_0))|~r1_tarski(X1,k1_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58]), c_0_22]), c_0_21])])).
% 10.51/10.75  cnf(c_0_62, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 10.51/10.75  cnf(c_0_63, negated_conjecture, (k7_relat_1(esk5_0,X1)=k7_relat_1(esk4_0,X1)|r2_hidden(esk3_3(esk5_0,esk4_0,k1_relat_1(k7_relat_1(esk4_0,X1))),k1_relat_1(k7_relat_1(esk4_0,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_21]), c_0_60]), c_0_58]), c_0_22]), c_0_52])])).
% 10.51/10.75  cnf(c_0_64, negated_conjecture, (k7_relat_1(esk5_0,X1)=k7_relat_1(esk4_0,X1)|~r2_hidden(esk3_3(esk5_0,esk4_0,X1),esk6_0)|~r1_tarski(X1,k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_61]), c_0_54]), c_0_33])])).
% 10.51/10.75  cnf(c_0_65, negated_conjecture, (k7_relat_1(esk5_0,X1)=k7_relat_1(esk4_0,X1)|r2_hidden(esk3_3(esk5_0,esk4_0,k1_relat_1(k7_relat_1(esk4_0,X1))),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_33])])).
% 10.51/10.75  cnf(c_0_66, negated_conjecture, (k7_relat_1(esk4_0,esk6_0)!=k7_relat_1(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 10.51/10.75  cnf(c_0_67, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_60]), c_0_53]), c_0_52])]), c_0_66]), ['proof']).
% 10.51/10.75  # SZS output end CNFRefutation
% 10.51/10.75  # Proof object total steps             : 68
% 10.51/10.75  # Proof object clause steps            : 45
% 10.51/10.75  # Proof object formula steps           : 23
% 10.51/10.75  # Proof object conjectures             : 29
% 10.51/10.75  # Proof object clause conjectures      : 26
% 10.51/10.75  # Proof object formula conjectures     : 3
% 10.51/10.75  # Proof object initial clauses used    : 21
% 10.51/10.75  # Proof object initial formulas used   : 11
% 10.51/10.75  # Proof object generating inferences   : 17
% 10.51/10.75  # Proof object simplifying inferences  : 49
% 10.51/10.75  # Training examples: 0 positive, 0 negative
% 10.51/10.75  # Parsed axioms                        : 11
% 10.51/10.75  # Removed by relevancy pruning/SinE    : 0
% 10.51/10.75  # Initial clauses                      : 26
% 10.51/10.75  # Removed in clause preprocessing      : 2
% 10.51/10.75  # Initial clauses in saturation        : 24
% 10.51/10.75  # Processed clauses                    : 23371
% 10.51/10.75  # ...of these trivial                  : 106
% 10.51/10.75  # ...subsumed                          : 21279
% 10.51/10.75  # ...remaining for further processing  : 1986
% 10.51/10.75  # Other redundant clauses eliminated   : 0
% 10.51/10.75  # Clauses deleted for lack of memory   : 0
% 10.51/10.75  # Backward-subsumed                    : 148
% 10.51/10.75  # Backward-rewritten                   : 15
% 10.51/10.75  # Generated clauses                    : 697413
% 10.51/10.75  # ...of the previous two non-trivial   : 681620
% 10.51/10.75  # Contextual simplify-reflections      : 34
% 10.51/10.75  # Paramodulations                      : 697410
% 10.51/10.75  # Factorizations                       : 0
% 10.51/10.75  # Equation resolutions                 : 3
% 10.51/10.75  # Propositional unsat checks           : 0
% 10.51/10.75  #    Propositional check models        : 0
% 10.51/10.75  #    Propositional check unsatisfiable : 0
% 10.51/10.75  #    Propositional clauses             : 0
% 10.51/10.75  #    Propositional clauses after purity: 0
% 10.51/10.75  #    Propositional unsat core size     : 0
% 10.51/10.75  #    Propositional preprocessing time  : 0.000
% 10.51/10.75  #    Propositional encoding time       : 0.000
% 10.51/10.75  #    Propositional solver time         : 0.000
% 10.51/10.75  #    Success case prop preproc time    : 0.000
% 10.51/10.75  #    Success case prop encoding time   : 0.000
% 10.51/10.75  #    Success case prop solver time     : 0.000
% 10.51/10.75  # Current number of processed clauses  : 1799
% 10.51/10.75  #    Positive orientable unit clauses  : 45
% 10.51/10.75  #    Positive unorientable unit clauses: 2
% 10.51/10.75  #    Negative unit clauses             : 1
% 10.51/10.75  #    Non-unit-clauses                  : 1751
% 10.51/10.75  # Current number of unprocessed clauses: 657049
% 10.51/10.75  # ...number of literals in the above   : 3886074
% 10.51/10.75  # Current number of archived formulas  : 0
% 10.51/10.75  # Current number of archived clauses   : 189
% 10.51/10.75  # Clause-clause subsumption calls (NU) : 2102188
% 10.51/10.75  # Rec. Clause-clause subsumption calls : 999828
% 10.51/10.75  # Non-unit clause-clause subsumptions  : 21401
% 10.51/10.75  # Unit Clause-clause subsumption calls : 2416
% 10.51/10.75  # Rewrite failures with RHS unbound    : 0
% 10.51/10.75  # BW rewrite match attempts            : 1607
% 10.51/10.75  # BW rewrite match successes           : 22
% 10.51/10.75  # Condensation attempts                : 0
% 10.51/10.75  # Condensation successes               : 0
% 10.51/10.75  # Termbank termtop insertions          : 43670572
% 10.62/10.78  
% 10.62/10.78  # -------------------------------------------------
% 10.62/10.78  # User time                : 10.046 s
% 10.62/10.78  # System time              : 0.388 s
% 10.62/10.78  # Total time               : 10.435 s
% 10.62/10.78  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
