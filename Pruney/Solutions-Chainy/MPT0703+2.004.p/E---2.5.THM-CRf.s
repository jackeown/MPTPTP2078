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
% DateTime   : Thu Dec  3 10:55:14 EST 2020

% Result     : Theorem 19.99s
% Output     : CNFRefutation 19.99s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 705 expanded)
%              Number of clauses        :   67 ( 344 expanded)
%              Number of leaves         :   19 ( 177 expanded)
%              Depth                    :   17
%              Number of atoms          :  247 (1308 expanded)
%              Number of equality atoms :   68 ( 625 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t158_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2))
          & r1_tarski(X1,k2_relat_1(X3)) )
       => r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

fof(t38_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k4_xboole_0(X2,X1))
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(t148_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => k9_relat_1(X2,k10_relat_1(X2,X1)) = k3_xboole_0(X1,k9_relat_1(X2,k1_relat_1(X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

fof(t156_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(c_0_19,plain,(
    ! [X55,X56] : k1_setfam_1(k2_tarski(X55,X56)) = k3_xboole_0(X55,X56) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_20,plain,(
    ! [X53,X54] : k1_enumset1(X53,X53,X54) = k2_tarski(X53,X54) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_21,plain,(
    ! [X33,X34] : k4_xboole_0(X33,X34) = k5_xboole_0(X33,k3_xboole_0(X33,X34)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_22,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_24,plain,(
    ! [X22,X23,X24,X25,X26,X27,X28,X29] :
      ( ( r2_hidden(X25,X22)
        | ~ r2_hidden(X25,X24)
        | X24 != k4_xboole_0(X22,X23) )
      & ( ~ r2_hidden(X25,X23)
        | ~ r2_hidden(X25,X24)
        | X24 != k4_xboole_0(X22,X23) )
      & ( ~ r2_hidden(X26,X22)
        | r2_hidden(X26,X23)
        | r2_hidden(X26,X24)
        | X24 != k4_xboole_0(X22,X23) )
      & ( ~ r2_hidden(esk3_3(X27,X28,X29),X29)
        | ~ r2_hidden(esk3_3(X27,X28,X29),X27)
        | r2_hidden(esk3_3(X27,X28,X29),X28)
        | X29 = k4_xboole_0(X27,X28) )
      & ( r2_hidden(esk3_3(X27,X28,X29),X27)
        | r2_hidden(esk3_3(X27,X28,X29),X29)
        | X29 = k4_xboole_0(X27,X28) )
      & ( ~ r2_hidden(esk3_3(X27,X28,X29),X28)
        | r2_hidden(esk3_3(X27,X28,X29),X29)
        | X29 = k4_xboole_0(X27,X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_29,plain,(
    ! [X44] : k4_xboole_0(X44,k1_xboole_0) = X44 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_30,plain,(
    ! [X40,X41] : r1_tarski(k4_xboole_0(X40,X41),X40) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_31,plain,
    ( X3 != k5_xboole_0(X4,k1_setfam_1(k1_enumset1(X4,X4,X2)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_33,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_34,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_35,plain,(
    ! [X38,X39] :
      ( ~ r1_tarski(X38,X39)
      | k2_xboole_0(X38,X39) = X39 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k1_enumset1(X2,X2,X3))))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k1_xboole_0))) = X1 ),
    inference(rw,[status(thm)],[c_0_32,c_0_28])).

fof(c_0_38,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_39,plain,(
    ! [X35,X36,X37] :
      ( ~ r1_tarski(k2_xboole_0(X35,X36),X37)
      | r1_tarski(X35,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_40,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))),X1) ),
    inference(rw,[status(thm)],[c_0_33,c_0_28])).

cnf(c_0_41,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_37])).

fof(c_0_47,plain,(
    ! [X51,X52] : k4_xboole_0(X51,k4_xboole_0(X51,X52)) = k3_xboole_0(X51,X52) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_48,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( r2_hidden(X16,X13)
        | ~ r2_hidden(X16,X15)
        | X15 != k3_xboole_0(X13,X14) )
      & ( r2_hidden(X16,X14)
        | ~ r2_hidden(X16,X15)
        | X15 != k3_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X13)
        | ~ r2_hidden(X17,X14)
        | r2_hidden(X17,X15)
        | X15 != k3_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X20)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X18)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X19)
        | X20 = k3_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X18)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k3_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X19)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k3_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_49,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,plain,
    ( r1_tarski(k1_xboole_0,X1)
    | ~ r2_hidden(esk1_2(k1_xboole_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_45,c_0_42])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

fof(c_0_53,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( ( r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2))
            & r1_tarski(X1,k2_relat_1(X3)) )
         => r1_tarski(X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t158_funct_1])).

cnf(c_0_54,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_49])).

cnf(c_0_57,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_44])).

fof(c_0_58,plain,(
    ! [X42,X43] :
      ( ~ r1_tarski(X42,k4_xboole_0(X43,X42))
      | X42 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).

fof(c_0_59,plain,(
    ! [X45,X46,X47] :
      ( ~ r1_tarski(X45,k2_xboole_0(X46,X47))
      | r1_tarski(k4_xboole_0(X45,X46),X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

fof(c_0_61,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & v1_funct_1(esk6_0)
    & r1_tarski(k10_relat_1(esk6_0,esk4_0),k10_relat_1(esk6_0,esk5_0))
    & r1_tarski(esk4_0,k2_relat_1(esk6_0))
    & ~ r1_tarski(esk4_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_53])])])).

cnf(c_0_62,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))))) = k1_setfam_1(k1_enumset1(X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_26]),c_0_28]),c_0_28])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,X2)
    | X3 != k1_setfam_1(k1_enumset1(X2,X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_55,c_0_26])).

cnf(c_0_64,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_65,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X1)
    | r2_hidden(esk3_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_66,plain,
    ( k1_xboole_0 = X1
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_67,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_68,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X4)
    | ~ r1_tarski(X4,X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_60])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(esk4_0,k2_relat_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_71,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k1_enumset1(X2,X2,X3))))
    | ~ r2_hidden(X1,k1_setfam_1(k1_enumset1(X2,X2,X3))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_62])).

cnf(c_0_72,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_setfam_1(k1_enumset1(X2,X2,X3))) ),
    inference(er,[status(thm)],[c_0_63])).

cnf(c_0_73,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_57]),c_0_43])).

cnf(c_0_74,plain,
    ( X3 = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))
    | r2_hidden(esk3_3(X1,X2,X3),X3)
    | r2_hidden(esk3_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_65,c_0_28])).

cnf(c_0_75,plain,
    ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,X1))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_66,c_0_40])).

fof(c_0_76,plain,(
    ! [X61,X62] :
      ( ~ v1_relat_1(X62)
      | ~ v1_funct_1(X62)
      | r1_tarski(k9_relat_1(X62,k10_relat_1(X62,X61)),X61) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

fof(c_0_77,plain,(
    ! [X63,X64] :
      ( ~ v1_relat_1(X64)
      | ~ v1_funct_1(X64)
      | k9_relat_1(X64,k10_relat_1(X64,X63)) = k3_xboole_0(X63,k9_relat_1(X64,k1_relat_1(X64))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_funct_1])])).

cnf(c_0_78,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k1_enumset1(X2,X2,X1)))) ),
    inference(rw,[status(thm)],[c_0_67,c_0_28])).

cnf(c_0_79,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[c_0_68,c_0_28])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(esk4_0,k2_xboole_0(X1,X2))
    | ~ r1_tarski(k2_relat_1(esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_81,plain,
    ( ~ r2_hidden(X1,k1_setfam_1(k1_enumset1(X2,X2,k1_xboole_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_37]),c_0_72])).

cnf(c_0_82,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_3(k1_xboole_0,X2,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75])).

cnf(c_0_83,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

fof(c_0_84,plain,(
    ! [X58,X59,X60] :
      ( ~ v1_relat_1(X60)
      | ~ r1_tarski(X58,X59)
      | r1_tarski(k9_relat_1(X60,X58),k9_relat_1(X60,X59)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t156_relat_1])])).

cnf(c_0_85,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = k3_xboole_0(X2,k9_relat_1(X1,k1_relat_1(X1)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

fof(c_0_86,plain,(
    ! [X57] :
      ( ~ v1_relat_1(X57)
      | k9_relat_1(X57,k1_relat_1(X57)) = k2_relat_1(X57) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

cnf(c_0_87,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) = k1_xboole_0
    | ~ r1_tarski(X1,k2_xboole_0(X2,k5_xboole_0(X3,k1_setfam_1(k1_enumset1(X3,X3,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))))))) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_88,negated_conjecture,
    ( r1_tarski(esk4_0,k2_xboole_0(k2_relat_1(esk6_0),X1)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_46])).

cnf(c_0_89,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_90,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,k9_relat_1(X3,k10_relat_1(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_83])).

cnf(c_0_91,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_92,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(X1,k1_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[c_0_85,c_0_26])).

cnf(c_0_93,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_94,negated_conjecture,
    ( k5_xboole_0(esk4_0,k1_setfam_1(k1_enumset1(esk4_0,esk4_0,k2_relat_1(esk6_0)))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_95,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_37,c_0_89])).

cnf(c_0_96,plain,
    ( r1_tarski(k9_relat_1(X1,X2),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k10_relat_1(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_97,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk6_0,esk4_0),k10_relat_1(esk6_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_98,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_99,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_100,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,k2_relat_1(X2))) = k9_relat_1(X2,k10_relat_1(X2,X1))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_101,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(esk4_0,esk4_0,k2_relat_1(esk6_0))) = esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_94]),c_0_89]),c_0_95])).

cnf(c_0_102,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk6_0,k10_relat_1(esk6_0,esk4_0)),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_98]),c_0_99])])).

cnf(c_0_103,negated_conjecture,
    ( k9_relat_1(esk6_0,k10_relat_1(esk6_0,esk4_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_98]),c_0_99])])).

cnf(c_0_104,negated_conjecture,
    ( ~ r1_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_105,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_103]),c_0_104]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:52:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 19.99/20.17  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 19.99/20.17  # and selection function SelectMaxLComplexAvoidPosPred.
% 19.99/20.17  #
% 19.99/20.17  # Preprocessing time       : 0.030 s
% 19.99/20.17  
% 19.99/20.17  # Proof found!
% 19.99/20.17  # SZS status Theorem
% 19.99/20.17  # SZS output start CNFRefutation
% 19.99/20.17  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 19.99/20.17  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 19.99/20.17  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 19.99/20.17  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 19.99/20.17  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 19.99/20.17  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 19.99/20.17  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 19.99/20.17  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 19.99/20.17  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 19.99/20.17  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 19.99/20.17  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 19.99/20.17  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 19.99/20.17  fof(t158_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2))&r1_tarski(X1,k2_relat_1(X3)))=>r1_tarski(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_1)).
% 19.99/20.17  fof(t38_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,k4_xboole_0(X2,X1))=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 19.99/20.17  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 19.99/20.17  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 19.99/20.17  fof(t148_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=k3_xboole_0(X1,k9_relat_1(X2,k1_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_funct_1)).
% 19.99/20.17  fof(t156_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 19.99/20.17  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 19.99/20.17  fof(c_0_19, plain, ![X55, X56]:k1_setfam_1(k2_tarski(X55,X56))=k3_xboole_0(X55,X56), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 19.99/20.17  fof(c_0_20, plain, ![X53, X54]:k1_enumset1(X53,X53,X54)=k2_tarski(X53,X54), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 19.99/20.17  fof(c_0_21, plain, ![X33, X34]:k4_xboole_0(X33,X34)=k5_xboole_0(X33,k3_xboole_0(X33,X34)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 19.99/20.17  cnf(c_0_22, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 19.99/20.17  cnf(c_0_23, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 19.99/20.17  fof(c_0_24, plain, ![X22, X23, X24, X25, X26, X27, X28, X29]:((((r2_hidden(X25,X22)|~r2_hidden(X25,X24)|X24!=k4_xboole_0(X22,X23))&(~r2_hidden(X25,X23)|~r2_hidden(X25,X24)|X24!=k4_xboole_0(X22,X23)))&(~r2_hidden(X26,X22)|r2_hidden(X26,X23)|r2_hidden(X26,X24)|X24!=k4_xboole_0(X22,X23)))&((~r2_hidden(esk3_3(X27,X28,X29),X29)|(~r2_hidden(esk3_3(X27,X28,X29),X27)|r2_hidden(esk3_3(X27,X28,X29),X28))|X29=k4_xboole_0(X27,X28))&((r2_hidden(esk3_3(X27,X28,X29),X27)|r2_hidden(esk3_3(X27,X28,X29),X29)|X29=k4_xboole_0(X27,X28))&(~r2_hidden(esk3_3(X27,X28,X29),X28)|r2_hidden(esk3_3(X27,X28,X29),X29)|X29=k4_xboole_0(X27,X28))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 19.99/20.17  cnf(c_0_25, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 19.99/20.17  cnf(c_0_26, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 19.99/20.17  cnf(c_0_27, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 19.99/20.17  cnf(c_0_28, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 19.99/20.17  fof(c_0_29, plain, ![X44]:k4_xboole_0(X44,k1_xboole_0)=X44, inference(variable_rename,[status(thm)],[t3_boole])).
% 19.99/20.17  fof(c_0_30, plain, ![X40, X41]:r1_tarski(k4_xboole_0(X40,X41),X40), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 19.99/20.17  cnf(c_0_31, plain, (X3!=k5_xboole_0(X4,k1_setfam_1(k1_enumset1(X4,X4,X2)))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 19.99/20.17  cnf(c_0_32, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_29])).
% 19.99/20.17  cnf(c_0_33, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 19.99/20.17  fof(c_0_34, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 19.99/20.17  fof(c_0_35, plain, ![X38, X39]:(~r1_tarski(X38,X39)|k2_xboole_0(X38,X39)=X39), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 19.99/20.17  cnf(c_0_36, plain, (~r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k1_enumset1(X2,X2,X3))))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_31])).
% 19.99/20.17  cnf(c_0_37, plain, (k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k1_xboole_0)))=X1), inference(rw,[status(thm)],[c_0_32, c_0_28])).
% 19.99/20.17  fof(c_0_38, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 19.99/20.17  fof(c_0_39, plain, ![X35, X36, X37]:(~r1_tarski(k2_xboole_0(X35,X36),X37)|r1_tarski(X35,X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 19.99/20.17  cnf(c_0_40, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))),X1)), inference(rw,[status(thm)],[c_0_33, c_0_28])).
% 19.99/20.17  cnf(c_0_41, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 19.99/20.17  cnf(c_0_42, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 19.99/20.17  cnf(c_0_43, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 19.99/20.17  cnf(c_0_44, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 19.99/20.17  cnf(c_0_45, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 19.99/20.17  cnf(c_0_46, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_40, c_0_37])).
% 19.99/20.17  fof(c_0_47, plain, ![X51, X52]:k4_xboole_0(X51,k4_xboole_0(X51,X52))=k3_xboole_0(X51,X52), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 19.99/20.17  fof(c_0_48, plain, ![X13, X14, X15, X16, X17, X18, X19, X20]:((((r2_hidden(X16,X13)|~r2_hidden(X16,X15)|X15!=k3_xboole_0(X13,X14))&(r2_hidden(X16,X14)|~r2_hidden(X16,X15)|X15!=k3_xboole_0(X13,X14)))&(~r2_hidden(X17,X13)|~r2_hidden(X17,X14)|r2_hidden(X17,X15)|X15!=k3_xboole_0(X13,X14)))&((~r2_hidden(esk2_3(X18,X19,X20),X20)|(~r2_hidden(esk2_3(X18,X19,X20),X18)|~r2_hidden(esk2_3(X18,X19,X20),X19))|X20=k3_xboole_0(X18,X19))&((r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k3_xboole_0(X18,X19))&(r2_hidden(esk2_3(X18,X19,X20),X19)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k3_xboole_0(X18,X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 19.99/20.17  cnf(c_0_49, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 19.99/20.17  cnf(c_0_50, plain, (r1_tarski(k1_xboole_0,X1)|~r2_hidden(esk1_2(k1_xboole_0,X1),X2)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 19.99/20.17  cnf(c_0_51, plain, (r1_tarski(X1,X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_45, c_0_42])).
% 19.99/20.17  cnf(c_0_52, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 19.99/20.17  fof(c_0_53, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2))&r1_tarski(X1,k2_relat_1(X3)))=>r1_tarski(X1,X2)))), inference(assume_negation,[status(cth)],[t158_funct_1])).
% 19.99/20.17  cnf(c_0_54, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 19.99/20.17  cnf(c_0_55, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 19.99/20.17  cnf(c_0_56, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_42, c_0_49])).
% 19.99/20.17  cnf(c_0_57, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_50, c_0_44])).
% 19.99/20.17  fof(c_0_58, plain, ![X42, X43]:(~r1_tarski(X42,k4_xboole_0(X43,X42))|X42=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).
% 19.99/20.17  fof(c_0_59, plain, ![X45, X46, X47]:(~r1_tarski(X45,k2_xboole_0(X46,X47))|r1_tarski(k4_xboole_0(X45,X46),X47)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 19.99/20.17  cnf(c_0_60, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 19.99/20.17  fof(c_0_61, negated_conjecture, ((v1_relat_1(esk6_0)&v1_funct_1(esk6_0))&((r1_tarski(k10_relat_1(esk6_0,esk4_0),k10_relat_1(esk6_0,esk5_0))&r1_tarski(esk4_0,k2_relat_1(esk6_0)))&~r1_tarski(esk4_0,esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_53])])])).
% 19.99/20.17  cnf(c_0_62, plain, (k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))))))=k1_setfam_1(k1_enumset1(X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_26]), c_0_28]), c_0_28])).
% 19.99/20.17  cnf(c_0_63, plain, (r2_hidden(X1,X2)|X3!=k1_setfam_1(k1_enumset1(X2,X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_55, c_0_26])).
% 19.99/20.17  cnf(c_0_64, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 19.99/20.17  cnf(c_0_65, plain, (r2_hidden(esk3_3(X1,X2,X3),X1)|r2_hidden(esk3_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 19.99/20.17  cnf(c_0_66, plain, (k1_xboole_0=X1|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 19.99/20.17  cnf(c_0_67, plain, (X1=k1_xboole_0|~r1_tarski(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 19.99/20.17  cnf(c_0_68, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 19.99/20.17  cnf(c_0_69, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(X1,X4)|~r1_tarski(X4,X2)), inference(spm,[status(thm)],[c_0_51, c_0_60])).
% 19.99/20.17  cnf(c_0_70, negated_conjecture, (r1_tarski(esk4_0,k2_relat_1(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 19.99/20.17  cnf(c_0_71, plain, (~r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k1_enumset1(X2,X2,X3))))|~r2_hidden(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))), inference(spm,[status(thm)],[c_0_36, c_0_62])).
% 19.99/20.17  cnf(c_0_72, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))), inference(er,[status(thm)],[c_0_63])).
% 19.99/20.17  cnf(c_0_73, plain, (~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_57]), c_0_43])).
% 19.99/20.17  cnf(c_0_74, plain, (X3=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))|r2_hidden(esk3_3(X1,X2,X3),X3)|r2_hidden(esk3_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_65, c_0_28])).
% 19.99/20.17  cnf(c_0_75, plain, (k5_xboole_0(k1_xboole_0,k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,X1)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_66, c_0_40])).
% 19.99/20.17  fof(c_0_76, plain, ![X61, X62]:(~v1_relat_1(X62)|~v1_funct_1(X62)|r1_tarski(k9_relat_1(X62,k10_relat_1(X62,X61)),X61)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 19.99/20.17  fof(c_0_77, plain, ![X63, X64]:(~v1_relat_1(X64)|~v1_funct_1(X64)|k9_relat_1(X64,k10_relat_1(X64,X63))=k3_xboole_0(X63,k9_relat_1(X64,k1_relat_1(X64)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_funct_1])])).
% 19.99/20.17  cnf(c_0_78, plain, (X1=k1_xboole_0|~r1_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k1_enumset1(X2,X2,X1))))), inference(rw,[status(thm)],[c_0_67, c_0_28])).
% 19.99/20.17  cnf(c_0_79, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[c_0_68, c_0_28])).
% 19.99/20.17  cnf(c_0_80, negated_conjecture, (r1_tarski(esk4_0,k2_xboole_0(X1,X2))|~r1_tarski(k2_relat_1(esk6_0),X1)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 19.99/20.17  cnf(c_0_81, plain, (~r2_hidden(X1,k1_setfam_1(k1_enumset1(X2,X2,k1_xboole_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_37]), c_0_72])).
% 19.99/20.17  cnf(c_0_82, plain, (X1=k1_xboole_0|r2_hidden(esk3_3(k1_xboole_0,X2,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75])).
% 19.99/20.17  cnf(c_0_83, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 19.99/20.17  fof(c_0_84, plain, ![X58, X59, X60]:(~v1_relat_1(X60)|(~r1_tarski(X58,X59)|r1_tarski(k9_relat_1(X60,X58),k9_relat_1(X60,X59)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t156_relat_1])])).
% 19.99/20.17  cnf(c_0_85, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=k3_xboole_0(X2,k9_relat_1(X1,k1_relat_1(X1)))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 19.99/20.17  fof(c_0_86, plain, ![X57]:(~v1_relat_1(X57)|k9_relat_1(X57,k1_relat_1(X57))=k2_relat_1(X57)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 19.99/20.17  cnf(c_0_87, plain, (k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))=k1_xboole_0|~r1_tarski(X1,k2_xboole_0(X2,k5_xboole_0(X3,k1_setfam_1(k1_enumset1(X3,X3,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))))))))), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 19.99/20.17  cnf(c_0_88, negated_conjecture, (r1_tarski(esk4_0,k2_xboole_0(k2_relat_1(esk6_0),X1))), inference(spm,[status(thm)],[c_0_80, c_0_46])).
% 19.99/20.17  cnf(c_0_89, plain, (k1_setfam_1(k1_enumset1(X1,X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 19.99/20.17  cnf(c_0_90, plain, (r1_tarski(X1,X2)|~v1_funct_1(X3)|~v1_relat_1(X3)|~r1_tarski(X1,k9_relat_1(X3,k10_relat_1(X3,X2)))), inference(spm,[status(thm)],[c_0_51, c_0_83])).
% 19.99/20.17  cnf(c_0_91, plain, (r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 19.99/20.17  cnf(c_0_92, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(X1,k1_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[c_0_85, c_0_26])).
% 19.99/20.17  cnf(c_0_93, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_86])).
% 19.99/20.17  cnf(c_0_94, negated_conjecture, (k5_xboole_0(esk4_0,k1_setfam_1(k1_enumset1(esk4_0,esk4_0,k2_relat_1(esk6_0))))=k1_xboole_0), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 19.99/20.17  cnf(c_0_95, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_37, c_0_89])).
% 19.99/20.17  cnf(c_0_96, plain, (r1_tarski(k9_relat_1(X1,X2),X3)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(X2,k10_relat_1(X1,X3))), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 19.99/20.17  cnf(c_0_97, negated_conjecture, (r1_tarski(k10_relat_1(esk6_0,esk4_0),k10_relat_1(esk6_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 19.99/20.17  cnf(c_0_98, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 19.99/20.17  cnf(c_0_99, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 19.99/20.17  cnf(c_0_100, plain, (k1_setfam_1(k1_enumset1(X1,X1,k2_relat_1(X2)))=k9_relat_1(X2,k10_relat_1(X2,X1))|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 19.99/20.17  cnf(c_0_101, negated_conjecture, (k1_setfam_1(k1_enumset1(esk4_0,esk4_0,k2_relat_1(esk6_0)))=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_94]), c_0_89]), c_0_95])).
% 19.99/20.17  cnf(c_0_102, negated_conjecture, (r1_tarski(k9_relat_1(esk6_0,k10_relat_1(esk6_0,esk4_0)),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_98]), c_0_99])])).
% 19.99/20.17  cnf(c_0_103, negated_conjecture, (k9_relat_1(esk6_0,k10_relat_1(esk6_0,esk4_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_98]), c_0_99])])).
% 19.99/20.17  cnf(c_0_104, negated_conjecture, (~r1_tarski(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 19.99/20.17  cnf(c_0_105, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_102, c_0_103]), c_0_104]), ['proof']).
% 19.99/20.17  # SZS output end CNFRefutation
% 19.99/20.17  # Proof object total steps             : 106
% 19.99/20.17  # Proof object clause steps            : 67
% 19.99/20.17  # Proof object formula steps           : 39
% 19.99/20.17  # Proof object conjectures             : 15
% 19.99/20.17  # Proof object clause conjectures      : 12
% 19.99/20.17  # Proof object formula conjectures     : 3
% 19.99/20.17  # Proof object initial clauses used    : 25
% 19.99/20.17  # Proof object initial formulas used   : 19
% 19.99/20.17  # Proof object generating inferences   : 27
% 19.99/20.17  # Proof object simplifying inferences  : 29
% 19.99/20.17  # Training examples: 0 positive, 0 negative
% 19.99/20.17  # Parsed axioms                        : 21
% 19.99/20.17  # Removed by relevancy pruning/SinE    : 0
% 19.99/20.17  # Initial clauses                      : 39
% 19.99/20.17  # Removed in clause preprocessing      : 3
% 19.99/20.17  # Initial clauses in saturation        : 36
% 19.99/20.17  # Processed clauses                    : 17015
% 19.99/20.17  # ...of these trivial                  : 1636
% 19.99/20.17  # ...subsumed                          : 11968
% 19.99/20.17  # ...remaining for further processing  : 3411
% 19.99/20.17  # Other redundant clauses eliminated   : 8
% 19.99/20.17  # Clauses deleted for lack of memory   : 0
% 19.99/20.17  # Backward-subsumed                    : 228
% 19.99/20.17  # Backward-rewritten                   : 185
% 19.99/20.17  # Generated clauses                    : 1585768
% 19.99/20.17  # ...of the previous two non-trivial   : 1547802
% 19.99/20.17  # Contextual simplify-reflections      : 61
% 19.99/20.17  # Paramodulations                      : 1585040
% 19.99/20.17  # Factorizations                       : 720
% 19.99/20.17  # Equation resolutions                 : 8
% 19.99/20.17  # Propositional unsat checks           : 0
% 19.99/20.17  #    Propositional check models        : 0
% 19.99/20.17  #    Propositional check unsatisfiable : 0
% 19.99/20.17  #    Propositional clauses             : 0
% 19.99/20.17  #    Propositional clauses after purity: 0
% 19.99/20.17  #    Propositional unsat core size     : 0
% 19.99/20.17  #    Propositional preprocessing time  : 0.000
% 19.99/20.17  #    Propositional encoding time       : 0.000
% 19.99/20.17  #    Propositional solver time         : 0.000
% 19.99/20.17  #    Success case prop preproc time    : 0.000
% 19.99/20.17  #    Success case prop encoding time   : 0.000
% 19.99/20.17  #    Success case prop solver time     : 0.000
% 19.99/20.17  # Current number of processed clauses  : 2990
% 19.99/20.17  #    Positive orientable unit clauses  : 293
% 19.99/20.17  #    Positive unorientable unit clauses: 1
% 19.99/20.17  #    Negative unit clauses             : 3
% 19.99/20.17  #    Non-unit-clauses                  : 2693
% 19.99/20.17  # Current number of unprocessed clauses: 1530166
% 19.99/20.17  # ...number of literals in the above   : 7225815
% 19.99/20.17  # Current number of archived formulas  : 0
% 19.99/20.17  # Current number of archived clauses   : 416
% 19.99/20.17  # Clause-clause subsumption calls (NU) : 1213352
% 19.99/20.17  # Rec. Clause-clause subsumption calls : 504702
% 19.99/20.17  # Non-unit clause-clause subsumptions  : 10654
% 19.99/20.17  # Unit Clause-clause subsumption calls : 1828
% 19.99/20.17  # Rewrite failures with RHS unbound    : 0
% 19.99/20.17  # BW rewrite match attempts            : 9446
% 19.99/20.17  # BW rewrite match successes           : 23
% 19.99/20.17  # Condensation attempts                : 0
% 19.99/20.17  # Condensation successes               : 0
% 19.99/20.17  # Termbank termtop insertions          : 46292308
% 19.99/20.22  
% 19.99/20.22  # -------------------------------------------------
% 19.99/20.22  # User time                : 19.271 s
% 19.99/20.22  # System time              : 0.613 s
% 19.99/20.22  # Total time               : 19.884 s
% 19.99/20.22  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
