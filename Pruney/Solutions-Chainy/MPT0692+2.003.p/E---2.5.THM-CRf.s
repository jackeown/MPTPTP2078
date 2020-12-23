%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:53 EST 2020

% Result     : Theorem 0.53s
% Output     : CNFRefutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 145 expanded)
%              Number of clauses        :   42 (  62 expanded)
%              Number of leaves         :   17 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :  204 ( 363 expanded)
%              Number of equality atoms :   59 ( 118 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t147_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,k2_relat_1(X2))
       => k9_relat_1(X2,k10_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(d13_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( X3 = k10_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ( r2_hidden(X4,k1_relat_1(X1))
                & r2_hidden(k1_funct_1(X1,X4),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t138_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => k10_relat_1(X3,k6_subset_1(X1,X2)) = k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t174_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ~ ( X1 != k1_xboole_0
          & r1_tarski(X1,k2_relat_1(X2))
          & k10_relat_1(X2,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).

fof(t146_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( r1_tarski(X1,k2_relat_1(X2))
         => k9_relat_1(X2,k10_relat_1(X2,X1)) = X1 ) ) ),
    inference(assume_negation,[status(cth)],[t147_funct_1])).

fof(c_0_18,plain,(
    ! [X17,X18,X19] :
      ( ~ r1_tarski(X17,X18)
      | ~ r1_tarski(X18,X19)
      | r1_tarski(X17,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_19,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & v1_funct_1(esk4_0)
    & r1_tarski(esk3_0,k2_relat_1(esk4_0))
    & k9_relat_1(esk4_0,k10_relat_1(esk4_0,esk3_0)) != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(esk3_0,k2_relat_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_22,plain,(
    ! [X33,X34,X35,X36,X37,X38,X39] :
      ( ( r2_hidden(X36,k1_relat_1(X33))
        | ~ r2_hidden(X36,X35)
        | X35 != k10_relat_1(X33,X34)
        | ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33) )
      & ( r2_hidden(k1_funct_1(X33,X36),X34)
        | ~ r2_hidden(X36,X35)
        | X35 != k10_relat_1(X33,X34)
        | ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33) )
      & ( ~ r2_hidden(X37,k1_relat_1(X33))
        | ~ r2_hidden(k1_funct_1(X33,X37),X34)
        | r2_hidden(X37,X35)
        | X35 != k10_relat_1(X33,X34)
        | ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33) )
      & ( ~ r2_hidden(esk2_3(X33,X38,X39),X39)
        | ~ r2_hidden(esk2_3(X33,X38,X39),k1_relat_1(X33))
        | ~ r2_hidden(k1_funct_1(X33,esk2_3(X33,X38,X39)),X38)
        | X39 = k10_relat_1(X33,X38)
        | ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33) )
      & ( r2_hidden(esk2_3(X33,X38,X39),k1_relat_1(X33))
        | r2_hidden(esk2_3(X33,X38,X39),X39)
        | X39 = k10_relat_1(X33,X38)
        | ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33) )
      & ( r2_hidden(k1_funct_1(X33,esk2_3(X33,X38,X39)),X38)
        | r2_hidden(esk2_3(X33,X38,X39),X39)
        | X39 = k10_relat_1(X33,X38)
        | ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_funct_1])])])])])])).

fof(c_0_23,plain,(
    ! [X29,X30] : k1_setfam_1(k2_tarski(X29,X30)) = k3_xboole_0(X29,X30) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_24,plain,(
    ! [X25,X26] : k1_enumset1(X25,X25,X26) = k2_tarski(X25,X26) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(X1,k2_relat_1(esk4_0))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_26,plain,(
    ! [X20,X21] : r1_tarski(k4_xboole_0(X20,X21),X20) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_27,plain,(
    ! [X13,X14] :
      ( ( r1_tarski(X13,X14)
        | X13 != X14 )
      & ( r1_tarski(X14,X13)
        | X13 != X14 )
      & ( ~ r1_tarski(X13,X14)
        | ~ r1_tarski(X14,X13)
        | X13 = X14 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_28,plain,(
    ! [X41,X42,X43] :
      ( ~ v1_relat_1(X43)
      | ~ v1_funct_1(X43)
      | k10_relat_1(X43,k6_subset_1(X41,X42)) = k6_subset_1(k10_relat_1(X43,X41),k10_relat_1(X43,X42)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t138_funct_1])])).

fof(c_0_29,plain,(
    ! [X27,X28] : k6_subset_1(X27,X28) = k4_xboole_0(X27,X28) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,X3)
    | X3 != k10_relat_1(X2,X4)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_31,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_32,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_33,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_35,plain,(
    ! [X23,X24] : k4_xboole_0(X23,k4_xboole_0(X23,X24)) = k3_xboole_0(X23,X24) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(X1,k2_relat_1(esk4_0))
    | ~ r1_tarski(X2,esk3_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_25])).

cnf(c_0_37,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_39,plain,(
    ! [X15,X16] :
      ( ( k4_xboole_0(X15,X16) != k1_xboole_0
        | r1_tarski(X15,X16) )
      & ( ~ r1_tarski(X15,X16)
        | k4_xboole_0(X15,X16) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_40,plain,
    ( k10_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k10_relat_1(X2,X3)) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_43,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_47,plain,(
    ! [X31,X32] :
      ( ~ v1_relat_1(X32)
      | X31 = k1_xboole_0
      | ~ r1_tarski(X31,k2_relat_1(X32))
      | k10_relat_1(X32,X31) != k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t174_relat_1])])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(X1,k2_relat_1(esk4_0))
    | ~ r1_tarski(X1,k4_xboole_0(esk3_0,X2)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_51,plain,
    ( k10_relat_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41]),c_0_41])).

fof(c_0_52,plain,(
    ! [X46,X47] :
      ( ~ v1_relat_1(X47)
      | ~ r1_tarski(X46,k1_relat_1(X47))
      | r1_tarski(X46,k10_relat_1(X47,k9_relat_1(X47,X46))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).

cnf(c_0_53,plain,
    ( r2_hidden(esk1_2(k10_relat_1(X1,X2),X3),k1_relat_1(X1))
    | r1_tarski(k10_relat_1(X1,X2),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_54,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_55,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_56,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k1_setfam_1(k1_enumset1(X2,X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45]),c_0_45])).

cnf(c_0_57,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k1_enumset1(X1,X1,X2)) ),
    inference(rw,[status(thm)],[c_0_46,c_0_45])).

fof(c_0_58,plain,(
    ! [X22] : k4_xboole_0(X22,k1_xboole_0) = X22 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_59,plain,
    ( X2 = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k2_relat_1(X1))
    | k10_relat_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk3_0,X1),k2_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_61,plain,
    ( k10_relat_1(X1,k4_xboole_0(X2,X3)) = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_62,plain,
    ( r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk1_2(k10_relat_1(esk4_0,X1),X2),k1_relat_1(esk4_0))
    | r1_tarski(k10_relat_1(esk4_0,X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])])).

cnf(c_0_65,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57]),c_0_57])).

cnf(c_0_66,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_67,negated_conjecture,
    ( k4_xboole_0(esk3_0,X1) = k1_xboole_0
    | k10_relat_1(esk4_0,k4_xboole_0(esk3_0,X1)) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_55])])).

cnf(c_0_68,plain,
    ( k10_relat_1(X1,k4_xboole_0(X2,k9_relat_1(X1,k10_relat_1(X1,X2)))) = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk4_0,X1),k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_70,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_50]),c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( k4_xboole_0(esk3_0,k9_relat_1(esk4_0,k10_relat_1(esk4_0,esk3_0))) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_54]),c_0_55]),c_0_69])])).

cnf(c_0_72,negated_conjecture,
    ( k9_relat_1(esk4_0,k10_relat_1(esk4_0,esk3_0)) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_73,plain,(
    ! [X44,X45] :
      ( ~ v1_relat_1(X45)
      | ~ v1_funct_1(X45)
      | r1_tarski(k9_relat_1(X45,k10_relat_1(X45,X44)),X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

cnf(c_0_74,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk4_0,k10_relat_1(esk4_0,esk3_0)),esk3_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_66]),c_0_72])).

cnf(c_0_75,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_76,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_54]),c_0_55])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:35:50 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.53/0.73  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.53/0.73  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.53/0.73  #
% 0.53/0.73  # Preprocessing time       : 0.028 s
% 0.53/0.73  # Presaturation interreduction done
% 0.53/0.73  
% 0.53/0.73  # Proof found!
% 0.53/0.73  # SZS status Theorem
% 0.53/0.73  # SZS output start CNFRefutation
% 0.53/0.73  fof(t147_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(X1,k2_relat_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 0.53/0.73  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.53/0.73  fof(d13_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,k1_relat_1(X1))&r2_hidden(k1_funct_1(X1,X4),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_funct_1)).
% 0.53/0.73  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.53/0.73  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.53/0.73  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.53/0.73  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.53/0.73  fof(t138_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>k10_relat_1(X3,k6_subset_1(X1,X2))=k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_funct_1)).
% 0.53/0.73  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.53/0.73  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.53/0.73  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.53/0.73  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.53/0.73  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.53/0.73  fof(t174_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>~(((X1!=k1_xboole_0&r1_tarski(X1,k2_relat_1(X2)))&k10_relat_1(X2,X1)=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_relat_1)).
% 0.53/0.73  fof(t146_funct_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 0.53/0.73  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.53/0.73  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 0.53/0.73  fof(c_0_17, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(X1,k2_relat_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=X1))), inference(assume_negation,[status(cth)],[t147_funct_1])).
% 0.53/0.73  fof(c_0_18, plain, ![X17, X18, X19]:(~r1_tarski(X17,X18)|~r1_tarski(X18,X19)|r1_tarski(X17,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.53/0.73  fof(c_0_19, negated_conjecture, ((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&(r1_tarski(esk3_0,k2_relat_1(esk4_0))&k9_relat_1(esk4_0,k10_relat_1(esk4_0,esk3_0))!=esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.53/0.73  cnf(c_0_20, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.53/0.73  cnf(c_0_21, negated_conjecture, (r1_tarski(esk3_0,k2_relat_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.53/0.73  fof(c_0_22, plain, ![X33, X34, X35, X36, X37, X38, X39]:((((r2_hidden(X36,k1_relat_1(X33))|~r2_hidden(X36,X35)|X35!=k10_relat_1(X33,X34)|(~v1_relat_1(X33)|~v1_funct_1(X33)))&(r2_hidden(k1_funct_1(X33,X36),X34)|~r2_hidden(X36,X35)|X35!=k10_relat_1(X33,X34)|(~v1_relat_1(X33)|~v1_funct_1(X33))))&(~r2_hidden(X37,k1_relat_1(X33))|~r2_hidden(k1_funct_1(X33,X37),X34)|r2_hidden(X37,X35)|X35!=k10_relat_1(X33,X34)|(~v1_relat_1(X33)|~v1_funct_1(X33))))&((~r2_hidden(esk2_3(X33,X38,X39),X39)|(~r2_hidden(esk2_3(X33,X38,X39),k1_relat_1(X33))|~r2_hidden(k1_funct_1(X33,esk2_3(X33,X38,X39)),X38))|X39=k10_relat_1(X33,X38)|(~v1_relat_1(X33)|~v1_funct_1(X33)))&((r2_hidden(esk2_3(X33,X38,X39),k1_relat_1(X33))|r2_hidden(esk2_3(X33,X38,X39),X39)|X39=k10_relat_1(X33,X38)|(~v1_relat_1(X33)|~v1_funct_1(X33)))&(r2_hidden(k1_funct_1(X33,esk2_3(X33,X38,X39)),X38)|r2_hidden(esk2_3(X33,X38,X39),X39)|X39=k10_relat_1(X33,X38)|(~v1_relat_1(X33)|~v1_funct_1(X33)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_funct_1])])])])])])).
% 0.53/0.73  fof(c_0_23, plain, ![X29, X30]:k1_setfam_1(k2_tarski(X29,X30))=k3_xboole_0(X29,X30), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.53/0.73  fof(c_0_24, plain, ![X25, X26]:k1_enumset1(X25,X25,X26)=k2_tarski(X25,X26), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.53/0.73  cnf(c_0_25, negated_conjecture, (r1_tarski(X1,k2_relat_1(esk4_0))|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.53/0.73  fof(c_0_26, plain, ![X20, X21]:r1_tarski(k4_xboole_0(X20,X21),X20), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.53/0.73  fof(c_0_27, plain, ![X13, X14]:(((r1_tarski(X13,X14)|X13!=X14)&(r1_tarski(X14,X13)|X13!=X14))&(~r1_tarski(X13,X14)|~r1_tarski(X14,X13)|X13=X14)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.53/0.73  fof(c_0_28, plain, ![X41, X42, X43]:(~v1_relat_1(X43)|~v1_funct_1(X43)|k10_relat_1(X43,k6_subset_1(X41,X42))=k6_subset_1(k10_relat_1(X43,X41),k10_relat_1(X43,X42))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t138_funct_1])])).
% 0.53/0.73  fof(c_0_29, plain, ![X27, X28]:k6_subset_1(X27,X28)=k4_xboole_0(X27,X28), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.53/0.73  cnf(c_0_30, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(X1,X3)|X3!=k10_relat_1(X2,X4)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.53/0.73  fof(c_0_31, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.53/0.73  fof(c_0_32, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.53/0.73  cnf(c_0_33, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.53/0.73  cnf(c_0_34, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.53/0.73  fof(c_0_35, plain, ![X23, X24]:k4_xboole_0(X23,k4_xboole_0(X23,X24))=k3_xboole_0(X23,X24), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.53/0.73  cnf(c_0_36, negated_conjecture, (r1_tarski(X1,k2_relat_1(esk4_0))|~r1_tarski(X2,esk3_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_20, c_0_25])).
% 0.53/0.73  cnf(c_0_37, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.53/0.73  cnf(c_0_38, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.53/0.73  fof(c_0_39, plain, ![X15, X16]:((k4_xboole_0(X15,X16)!=k1_xboole_0|r1_tarski(X15,X16))&(~r1_tarski(X15,X16)|k4_xboole_0(X15,X16)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.53/0.73  cnf(c_0_40, plain, (k10_relat_1(X1,k6_subset_1(X2,X3))=k6_subset_1(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.53/0.73  cnf(c_0_41, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.53/0.73  cnf(c_0_42, plain, (r2_hidden(X1,k1_relat_1(X2))|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k10_relat_1(X2,X3))), inference(er,[status(thm)],[c_0_30])).
% 0.53/0.73  cnf(c_0_43, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.53/0.73  cnf(c_0_44, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.53/0.73  cnf(c_0_45, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 0.53/0.73  cnf(c_0_46, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.53/0.73  fof(c_0_47, plain, ![X31, X32]:(~v1_relat_1(X32)|(X31=k1_xboole_0|~r1_tarski(X31,k2_relat_1(X32))|k10_relat_1(X32,X31)!=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t174_relat_1])])).
% 0.53/0.73  cnf(c_0_48, negated_conjecture, (r1_tarski(X1,k2_relat_1(esk4_0))|~r1_tarski(X1,k4_xboole_0(esk3_0,X2))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.53/0.73  cnf(c_0_49, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_38])).
% 0.53/0.73  cnf(c_0_50, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.53/0.73  cnf(c_0_51, plain, (k10_relat_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41]), c_0_41])).
% 0.53/0.73  fof(c_0_52, plain, ![X46, X47]:(~v1_relat_1(X47)|(~r1_tarski(X46,k1_relat_1(X47))|r1_tarski(X46,k10_relat_1(X47,k9_relat_1(X47,X46))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).
% 0.53/0.73  cnf(c_0_53, plain, (r2_hidden(esk1_2(k10_relat_1(X1,X2),X3),k1_relat_1(X1))|r1_tarski(k10_relat_1(X1,X2),X3)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.53/0.73  cnf(c_0_54, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.53/0.73  cnf(c_0_55, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.53/0.73  cnf(c_0_56, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k1_setfam_1(k1_enumset1(X2,X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45]), c_0_45])).
% 0.53/0.73  cnf(c_0_57, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k1_enumset1(X1,X1,X2))), inference(rw,[status(thm)],[c_0_46, c_0_45])).
% 0.53/0.73  fof(c_0_58, plain, ![X22]:k4_xboole_0(X22,k1_xboole_0)=X22, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.53/0.73  cnf(c_0_59, plain, (X2=k1_xboole_0|~v1_relat_1(X1)|~r1_tarski(X2,k2_relat_1(X1))|k10_relat_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.53/0.73  cnf(c_0_60, negated_conjecture, (r1_tarski(k4_xboole_0(esk3_0,X1),k2_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.53/0.73  cnf(c_0_61, plain, (k10_relat_1(X1,k4_xboole_0(X2,X3))=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.53/0.73  cnf(c_0_62, plain, (r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.53/0.73  cnf(c_0_63, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.53/0.73  cnf(c_0_64, negated_conjecture, (r2_hidden(esk1_2(k10_relat_1(esk4_0,X1),X2),k1_relat_1(esk4_0))|r1_tarski(k10_relat_1(esk4_0,X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])])).
% 0.53/0.73  cnf(c_0_65, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57]), c_0_57])).
% 0.53/0.73  cnf(c_0_66, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.53/0.73  cnf(c_0_67, negated_conjecture, (k4_xboole_0(esk3_0,X1)=k1_xboole_0|k10_relat_1(esk4_0,k4_xboole_0(esk3_0,X1))!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_55])])).
% 0.53/0.73  cnf(c_0_68, plain, (k10_relat_1(X1,k4_xboole_0(X2,k9_relat_1(X1,k10_relat_1(X1,X2))))=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.53/0.73  cnf(c_0_69, negated_conjecture, (r1_tarski(k10_relat_1(esk4_0,X1),k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.53/0.73  cnf(c_0_70, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X2|~r1_tarski(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_50]), c_0_66])).
% 0.53/0.73  cnf(c_0_71, negated_conjecture, (k4_xboole_0(esk3_0,k9_relat_1(esk4_0,k10_relat_1(esk4_0,esk3_0)))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_54]), c_0_55]), c_0_69])])).
% 0.53/0.73  cnf(c_0_72, negated_conjecture, (k9_relat_1(esk4_0,k10_relat_1(esk4_0,esk3_0))!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.53/0.73  fof(c_0_73, plain, ![X44, X45]:(~v1_relat_1(X45)|~v1_funct_1(X45)|r1_tarski(k9_relat_1(X45,k10_relat_1(X45,X44)),X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 0.53/0.73  cnf(c_0_74, negated_conjecture, (~r1_tarski(k9_relat_1(esk4_0,k10_relat_1(esk4_0,esk3_0)),esk3_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_66]), c_0_72])).
% 0.53/0.73  cnf(c_0_75, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.53/0.73  cnf(c_0_76, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_54]), c_0_55])]), ['proof']).
% 0.53/0.73  # SZS output end CNFRefutation
% 0.53/0.73  # Proof object total steps             : 77
% 0.53/0.73  # Proof object clause steps            : 42
% 0.53/0.73  # Proof object formula steps           : 35
% 0.53/0.73  # Proof object conjectures             : 17
% 0.53/0.73  # Proof object clause conjectures      : 14
% 0.53/0.73  # Proof object formula conjectures     : 3
% 0.53/0.73  # Proof object initial clauses used    : 21
% 0.53/0.73  # Proof object initial formulas used   : 17
% 0.53/0.73  # Proof object generating inferences   : 14
% 0.53/0.73  # Proof object simplifying inferences  : 24
% 0.53/0.73  # Training examples: 0 positive, 0 negative
% 0.53/0.73  # Parsed axioms                        : 17
% 0.53/0.73  # Removed by relevancy pruning/SinE    : 0
% 0.53/0.73  # Initial clauses                      : 30
% 0.53/0.73  # Removed in clause preprocessing      : 3
% 0.53/0.73  # Initial clauses in saturation        : 27
% 0.53/0.73  # Processed clauses                    : 4577
% 0.53/0.73  # ...of these trivial                  : 36
% 0.53/0.73  # ...subsumed                          : 3847
% 0.53/0.73  # ...remaining for further processing  : 694
% 0.53/0.73  # Other redundant clauses eliminated   : 82
% 0.53/0.73  # Clauses deleted for lack of memory   : 0
% 0.53/0.73  # Backward-subsumed                    : 57
% 0.53/0.73  # Backward-rewritten                   : 13
% 0.53/0.73  # Generated clauses                    : 32301
% 0.53/0.73  # ...of the previous two non-trivial   : 26930
% 0.53/0.73  # Contextual simplify-reflections      : 20
% 0.53/0.73  # Paramodulations                      : 32217
% 0.53/0.73  # Factorizations                       : 2
% 0.53/0.73  # Equation resolutions                 : 82
% 0.53/0.73  # Propositional unsat checks           : 0
% 0.53/0.73  #    Propositional check models        : 0
% 0.53/0.73  #    Propositional check unsatisfiable : 0
% 0.53/0.73  #    Propositional clauses             : 0
% 0.53/0.73  #    Propositional clauses after purity: 0
% 0.53/0.73  #    Propositional unsat core size     : 0
% 0.53/0.73  #    Propositional preprocessing time  : 0.000
% 0.53/0.73  #    Propositional encoding time       : 0.000
% 0.53/0.73  #    Propositional solver time         : 0.000
% 0.53/0.73  #    Success case prop preproc time    : 0.000
% 0.53/0.74  #    Success case prop encoding time   : 0.000
% 0.53/0.74  #    Success case prop solver time     : 0.000
% 0.53/0.74  # Current number of processed clauses  : 593
% 0.53/0.74  #    Positive orientable unit clauses  : 48
% 0.53/0.74  #    Positive unorientable unit clauses: 1
% 0.53/0.74  #    Negative unit clauses             : 9
% 0.53/0.74  #    Non-unit-clauses                  : 535
% 0.53/0.74  # Current number of unprocessed clauses: 22314
% 0.53/0.74  # ...number of literals in the above   : 92493
% 0.53/0.74  # Current number of archived formulas  : 0
% 0.53/0.74  # Current number of archived clauses   : 99
% 0.53/0.74  # Clause-clause subsumption calls (NU) : 80975
% 0.53/0.74  # Rec. Clause-clause subsumption calls : 50021
% 0.53/0.74  # Non-unit clause-clause subsumptions  : 2725
% 0.53/0.74  # Unit Clause-clause subsumption calls : 682
% 0.53/0.74  # Rewrite failures with RHS unbound    : 0
% 0.53/0.74  # BW rewrite match attempts            : 172
% 0.53/0.74  # BW rewrite match successes           : 12
% 0.53/0.74  # Condensation attempts                : 0
% 0.53/0.74  # Condensation successes               : 0
% 0.53/0.74  # Termbank termtop insertions          : 467755
% 0.53/0.74  
% 0.53/0.74  # -------------------------------------------------
% 0.53/0.74  # User time                : 0.371 s
% 0.53/0.74  # System time              : 0.015 s
% 0.53/0.74  # Total time               : 0.386 s
% 0.53/0.74  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
