%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:02 EST 2020

% Result     : Theorem 0.50s
% Output     : CNFRefutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 508 expanded)
%              Number of clauses        :   61 ( 225 expanded)
%              Number of leaves         :   18 ( 129 expanded)
%              Depth                    :   24
%              Number of atoms          :  249 (1328 expanded)
%              Number of equality atoms :   54 ( 304 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t45_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(t138_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => k10_relat_1(X3,k6_subset_1(X1,X2)) = k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(t109_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k4_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

fof(t14_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2)
        & ! [X4] :
            ( ( r1_tarski(X1,X4)
              & r1_tarski(X3,X4) )
           => r1_tarski(X2,X4) ) )
     => X2 = k2_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_xboole_1)).

fof(t152_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v2_funct_1(X2)
       => r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

fof(t178_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

fof(t167_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(t146_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(t123_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( v2_funct_1(X3)
       => k9_relat_1(X3,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(c_0_18,plain,(
    ! [X19,X20,X21] :
      ( ~ r1_tarski(X19,X20)
      | ~ r1_tarski(X20,X21)
      | r1_tarski(X19,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_19,plain,(
    ! [X31,X32] : r1_tarski(X31,k2_xboole_0(X31,X32)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_20,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_25,plain,(
    ! [X29,X30] :
      ( ~ r1_tarski(X29,X30)
      | X30 = k2_xboole_0(X29,k4_xboole_0(X30,X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).

fof(c_0_26,plain,(
    ! [X7,X8] :
      ( ( k4_xboole_0(X7,X8) != k1_xboole_0
        | r1_tarski(X7,X8) )
      & ( ~ r1_tarski(X7,X8)
        | k4_xboole_0(X7,X8) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,X2) = X3
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,plain,
    ( X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_29,plain,(
    ! [X22] : r1_tarski(k1_xboole_0,X22) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_34,plain,(
    ! [X23,X24,X25] :
      ( ~ r1_tarski(X23,k2_xboole_0(X24,X25))
      | r1_tarski(k4_xboole_0(X23,X24),X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

cnf(c_0_35,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_30])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_31])).

fof(c_0_37,plain,(
    ! [X43,X44,X45] :
      ( ~ v1_relat_1(X45)
      | ~ v1_funct_1(X45)
      | k10_relat_1(X45,k6_subset_1(X43,X44)) = k6_subset_1(k10_relat_1(X45,X43),k10_relat_1(X45,X44)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t138_funct_1])])).

fof(c_0_38,plain,(
    ! [X33,X34] : k6_subset_1(X33,X34) = k4_xboole_0(X33,X34) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_39,plain,
    ( k1_xboole_0 = X1
    | ~ r1_tarski(X2,k1_xboole_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_36])])).

fof(c_0_42,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_tarski(X9,X10)
      | r1_tarski(k4_xboole_0(X9,X11),X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_xboole_1])])).

cnf(c_0_43,plain,
    ( k10_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( k1_xboole_0 = X1
    | ~ r1_tarski(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X2,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

cnf(c_0_46,plain,
    ( r1_tarski(k4_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_47,plain,
    ( k10_relat_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44]),c_0_44])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,k4_xboole_0(X3,X4))
    | ~ r1_tarski(X3,X4) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

fof(c_0_49,plain,(
    ! [X15,X16,X17] :
      ( ( r1_tarski(X15,esk1_3(X15,X16,X17))
        | ~ r1_tarski(X15,X16)
        | ~ r1_tarski(X17,X16)
        | X16 = k2_xboole_0(X15,X17) )
      & ( r1_tarski(X17,esk1_3(X15,X16,X17))
        | ~ r1_tarski(X15,X16)
        | ~ r1_tarski(X17,X16)
        | X16 = k2_xboole_0(X15,X17) )
      & ( ~ r1_tarski(X16,esk1_3(X15,X16,X17))
        | ~ r1_tarski(X15,X16)
        | ~ r1_tarski(X17,X16)
        | X16 = k2_xboole_0(X15,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_xboole_1])])])])).

cnf(c_0_50,plain,
    ( k10_relat_1(X1,k4_xboole_0(X2,X3)) = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_47])).

cnf(c_0_51,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_48,c_0_33])).

fof(c_0_52,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( v2_funct_1(X2)
         => r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t152_funct_1])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,esk1_3(X2,X3,X1))
    | X3 = k2_xboole_0(X2,X1)
    | ~ r1_tarski(X2,X3)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_54,plain,(
    ! [X37,X38,X39] :
      ( ~ v1_relat_1(X39)
      | ~ r1_tarski(X37,X38)
      | r1_tarski(k10_relat_1(X39,X37),k10_relat_1(X39,X38)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t178_relat_1])])).

cnf(c_0_55,plain,
    ( k10_relat_1(X1,k4_xboole_0(X2,X2)) = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_36])).

cnf(c_0_56,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_33])).

fof(c_0_57,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & v2_funct_1(esk3_0)
    & ~ r1_tarski(k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0)),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_52])])])).

cnf(c_0_58,plain,
    ( X1 = k2_xboole_0(k1_xboole_0,X2)
    | r1_tarski(X2,esk1_3(k1_xboole_0,X1,X2))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_33])).

cnf(c_0_59,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_60,plain,
    ( k10_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_63,plain,
    ( X1 = k2_xboole_0(X2,X3)
    | ~ r1_tarski(X1,esk1_3(X2,X1,X3))
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_64,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1
    | r1_tarski(X1,esk1_3(k1_xboole_0,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_36])).

cnf(c_0_65,plain,
    ( k10_relat_1(X1,X2) = k10_relat_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( k10_relat_1(esk3_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62])])).

cnf(c_0_67,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_36]),c_0_33])])).

fof(c_0_68,plain,(
    ! [X35,X36] :
      ( ~ v1_relat_1(X36)
      | r1_tarski(k10_relat_1(X36,X35),k1_relat_1(X36)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).

cnf(c_0_69,negated_conjecture,
    ( k10_relat_1(esk3_0,X1) = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_62]),c_0_33])])).

cnf(c_0_70,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_67]),c_0_33])])).

cnf(c_0_71,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( k10_relat_1(esk3_0,k4_xboole_0(X1,X2)) = k10_relat_1(esk3_0,X1)
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_69]),c_0_70]),c_0_61]),c_0_62])])).

fof(c_0_73,plain,(
    ! [X48,X49] :
      ( ~ v1_relat_1(X49)
      | ~ r1_tarski(X48,k1_relat_1(X49))
      | r1_tarski(X48,k10_relat_1(X49,k9_relat_1(X49,X48))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk3_0,X1),k1_relat_1(esk3_0))
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_62])])).

fof(c_0_75,plain,(
    ! [X46,X47] :
      ( ~ v1_relat_1(X47)
      | ~ v1_funct_1(X47)
      | r1_tarski(k9_relat_1(X47,k10_relat_1(X47,X46)),X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

cnf(c_0_76,plain,
    ( r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk3_0,X1),k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_33])).

fof(c_0_78,plain,(
    ! [X40,X41,X42] :
      ( ~ v1_relat_1(X42)
      | ~ v1_funct_1(X42)
      | ~ v2_funct_1(X42)
      | k9_relat_1(X42,k6_subset_1(X40,X41)) = k6_subset_1(k9_relat_1(X42,X40),k9_relat_1(X42,X41)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_funct_1])])).

cnf(c_0_79,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk3_0,X1),k10_relat_1(esk3_0,k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_62])])).

cnf(c_0_81,plain,
    ( k9_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_82,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,k9_relat_1(X3,k10_relat_1(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_79])).

cnf(c_0_83,negated_conjecture,
    ( k10_relat_1(esk3_0,k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1))) = k10_relat_1(esk3_0,X1)
    | ~ r1_tarski(k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_80]),c_0_62])])).

cnf(c_0_84,plain,
    ( k9_relat_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_44]),c_0_44])).

cnf(c_0_85,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,k9_relat_1(X2,k10_relat_1(X2,X3)))),X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_79])).

cnf(c_0_86,negated_conjecture,
    ( k10_relat_1(esk3_0,k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1))) = k10_relat_1(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_79]),c_0_61]),c_0_62])])).

cnf(c_0_87,plain,
    ( k9_relat_1(X1,k4_xboole_0(X2,X3)) = k1_xboole_0
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_84])).

cnf(c_0_88,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_61]),c_0_62])])).

cnf(c_0_89,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_90,plain,(
    ! [X26,X27,X28] :
      ( ~ r1_tarski(k4_xboole_0(X26,X27),X28)
      | r1_tarski(X26,k2_xboole_0(X27,X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_91,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k10_relat_1(X3,k9_relat_1(X3,k4_xboole_0(X1,X2))))
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,k1_relat_1(X3)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_46])).

cnf(c_0_92,negated_conjecture,
    ( k9_relat_1(esk3_0,k4_xboole_0(k10_relat_1(esk3_0,k9_relat_1(esk3_0,X1)),X1)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_89]),c_0_61]),c_0_62])])).

cnf(c_0_93,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_94,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k10_relat_1(esk3_0,k9_relat_1(esk3_0,X1)),X1),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_66]),c_0_62]),c_0_77])])).

cnf(c_0_95,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0)),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_96,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk3_0,k9_relat_1(esk3_0,X1)),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_41])).

cnf(c_0_97,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_96])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:22:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.50/0.70  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.50/0.70  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.50/0.70  #
% 0.50/0.70  # Preprocessing time       : 0.028 s
% 0.50/0.70  # Presaturation interreduction done
% 0.50/0.70  
% 0.50/0.70  # Proof found!
% 0.50/0.70  # SZS status Theorem
% 0.50/0.70  # SZS output start CNFRefutation
% 0.50/0.70  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.50/0.70  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.50/0.70  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.50/0.70  fof(t45_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>X2=k2_xboole_0(X1,k4_xboole_0(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 0.50/0.70  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.50/0.70  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.50/0.70  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 0.50/0.70  fof(t138_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>k10_relat_1(X3,k6_subset_1(X1,X2))=k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_funct_1)).
% 0.50/0.70  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.50/0.70  fof(t109_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k4_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_xboole_1)).
% 0.50/0.70  fof(t14_xboole_1, axiom, ![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X3,X2))&![X4]:((r1_tarski(X1,X4)&r1_tarski(X3,X4))=>r1_tarski(X2,X4)))=>X2=k2_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_xboole_1)).
% 0.50/0.70  fof(t152_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v2_funct_1(X2)=>r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_funct_1)).
% 0.50/0.70  fof(t178_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_relat_1)).
% 0.50/0.70  fof(t167_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 0.50/0.70  fof(t146_funct_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 0.50/0.70  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 0.50/0.70  fof(t123_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(v2_funct_1(X3)=>k9_relat_1(X3,k6_subset_1(X1,X2))=k6_subset_1(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_funct_1)).
% 0.50/0.70  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 0.50/0.70  fof(c_0_18, plain, ![X19, X20, X21]:(~r1_tarski(X19,X20)|~r1_tarski(X20,X21)|r1_tarski(X19,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.50/0.70  fof(c_0_19, plain, ![X31, X32]:r1_tarski(X31,k2_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.50/0.70  fof(c_0_20, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.50/0.70  cnf(c_0_21, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.50/0.70  cnf(c_0_22, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.50/0.70  cnf(c_0_23, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.50/0.70  cnf(c_0_24, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.50/0.70  fof(c_0_25, plain, ![X29, X30]:(~r1_tarski(X29,X30)|X30=k2_xboole_0(X29,k4_xboole_0(X30,X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).
% 0.50/0.70  fof(c_0_26, plain, ![X7, X8]:((k4_xboole_0(X7,X8)!=k1_xboole_0|r1_tarski(X7,X8))&(~r1_tarski(X7,X8)|k4_xboole_0(X7,X8)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.50/0.70  cnf(c_0_27, plain, (k2_xboole_0(X1,X2)=X3|~r1_tarski(k2_xboole_0(X1,X2),X3)|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.50/0.70  cnf(c_0_28, plain, (X2=k2_xboole_0(X1,k4_xboole_0(X2,X1))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.50/0.70  fof(c_0_29, plain, ![X22]:r1_tarski(k1_xboole_0,X22), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.50/0.70  cnf(c_0_30, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.50/0.70  cnf(c_0_31, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.50/0.70  cnf(c_0_32, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.50/0.70  cnf(c_0_33, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.50/0.70  fof(c_0_34, plain, ![X23, X24, X25]:(~r1_tarski(X23,k2_xboole_0(X24,X25))|r1_tarski(k4_xboole_0(X23,X24),X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 0.50/0.70  cnf(c_0_35, plain, (k2_xboole_0(X1,k1_xboole_0)=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_28, c_0_30])).
% 0.50/0.70  cnf(c_0_36, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_31])).
% 0.50/0.70  fof(c_0_37, plain, ![X43, X44, X45]:(~v1_relat_1(X45)|~v1_funct_1(X45)|k10_relat_1(X45,k6_subset_1(X43,X44))=k6_subset_1(k10_relat_1(X45,X43),k10_relat_1(X45,X44))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t138_funct_1])])).
% 0.50/0.70  fof(c_0_38, plain, ![X33, X34]:k6_subset_1(X33,X34)=k4_xboole_0(X33,X34), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.50/0.70  cnf(c_0_39, plain, (k1_xboole_0=X1|~r1_tarski(X2,k1_xboole_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.50/0.70  cnf(c_0_40, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.50/0.70  cnf(c_0_41, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_36])])).
% 0.50/0.71  fof(c_0_42, plain, ![X9, X10, X11]:(~r1_tarski(X9,X10)|r1_tarski(k4_xboole_0(X9,X11),X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_xboole_1])])).
% 0.50/0.71  cnf(c_0_43, plain, (k10_relat_1(X1,k6_subset_1(X2,X3))=k6_subset_1(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.50/0.71  cnf(c_0_44, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.50/0.71  cnf(c_0_45, plain, (k1_xboole_0=X1|~r1_tarski(X1,k4_xboole_0(X2,X3))|~r1_tarski(X2,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])).
% 0.50/0.71  cnf(c_0_46, plain, (r1_tarski(k4_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.50/0.71  cnf(c_0_47, plain, (k10_relat_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44]), c_0_44])).
% 0.50/0.71  cnf(c_0_48, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,k4_xboole_0(X3,X4))|~r1_tarski(X3,X4)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.50/0.71  fof(c_0_49, plain, ![X15, X16, X17]:(((r1_tarski(X15,esk1_3(X15,X16,X17))|(~r1_tarski(X15,X16)|~r1_tarski(X17,X16))|X16=k2_xboole_0(X15,X17))&(r1_tarski(X17,esk1_3(X15,X16,X17))|(~r1_tarski(X15,X16)|~r1_tarski(X17,X16))|X16=k2_xboole_0(X15,X17)))&(~r1_tarski(X16,esk1_3(X15,X16,X17))|(~r1_tarski(X15,X16)|~r1_tarski(X17,X16))|X16=k2_xboole_0(X15,X17))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_xboole_1])])])])).
% 0.50/0.71  cnf(c_0_50, plain, (k10_relat_1(X1,k4_xboole_0(X2,X3))=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))), inference(spm,[status(thm)],[c_0_30, c_0_47])).
% 0.50/0.71  cnf(c_0_51, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_48, c_0_33])).
% 0.50/0.71  fof(c_0_52, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v2_funct_1(X2)=>r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1)))), inference(assume_negation,[status(cth)],[t152_funct_1])).
% 0.50/0.71  cnf(c_0_53, plain, (r1_tarski(X1,esk1_3(X2,X3,X1))|X3=k2_xboole_0(X2,X1)|~r1_tarski(X2,X3)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.50/0.71  fof(c_0_54, plain, ![X37, X38, X39]:(~v1_relat_1(X39)|(~r1_tarski(X37,X38)|r1_tarski(k10_relat_1(X39,X37),k10_relat_1(X39,X38)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t178_relat_1])])).
% 0.50/0.71  cnf(c_0_55, plain, (k10_relat_1(X1,k4_xboole_0(X2,X2))=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_50, c_0_36])).
% 0.50/0.71  cnf(c_0_56, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_51, c_0_33])).
% 0.50/0.71  fof(c_0_57, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&(v2_funct_1(esk3_0)&~r1_tarski(k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0)),esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_52])])])).
% 0.50/0.71  cnf(c_0_58, plain, (X1=k2_xboole_0(k1_xboole_0,X2)|r1_tarski(X2,esk1_3(k1_xboole_0,X1,X2))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_53, c_0_33])).
% 0.50/0.71  cnf(c_0_59, plain, (r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.50/0.71  cnf(c_0_60, plain, (k10_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.50/0.71  cnf(c_0_61, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.50/0.71  cnf(c_0_62, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.50/0.71  cnf(c_0_63, plain, (X1=k2_xboole_0(X2,X3)|~r1_tarski(X1,esk1_3(X2,X1,X3))|~r1_tarski(X2,X1)|~r1_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.50/0.71  cnf(c_0_64, plain, (k2_xboole_0(k1_xboole_0,X1)=X1|r1_tarski(X1,esk1_3(k1_xboole_0,X1,X1))), inference(spm,[status(thm)],[c_0_58, c_0_36])).
% 0.50/0.71  cnf(c_0_65, plain, (k10_relat_1(X1,X2)=k10_relat_1(X1,X3)|~v1_relat_1(X1)|~r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_23, c_0_59])).
% 0.50/0.71  cnf(c_0_66, negated_conjecture, (k10_relat_1(esk3_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62])])).
% 0.50/0.71  cnf(c_0_67, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_36]), c_0_33])])).
% 0.50/0.71  fof(c_0_68, plain, ![X35, X36]:(~v1_relat_1(X36)|r1_tarski(k10_relat_1(X36,X35),k1_relat_1(X36))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).
% 0.50/0.71  cnf(c_0_69, negated_conjecture, (k10_relat_1(esk3_0,X1)=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_62]), c_0_33])])).
% 0.50/0.71  cnf(c_0_70, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_67]), c_0_33])])).
% 0.50/0.71  cnf(c_0_71, plain, (r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.50/0.71  cnf(c_0_72, negated_conjecture, (k10_relat_1(esk3_0,k4_xboole_0(X1,X2))=k10_relat_1(esk3_0,X1)|~r1_tarski(X2,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_69]), c_0_70]), c_0_61]), c_0_62])])).
% 0.50/0.71  fof(c_0_73, plain, ![X48, X49]:(~v1_relat_1(X49)|(~r1_tarski(X48,k1_relat_1(X49))|r1_tarski(X48,k10_relat_1(X49,k9_relat_1(X49,X48))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).
% 0.50/0.71  cnf(c_0_74, negated_conjecture, (r1_tarski(k10_relat_1(esk3_0,X1),k1_relat_1(esk3_0))|~r1_tarski(X2,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_62])])).
% 0.50/0.71  fof(c_0_75, plain, ![X46, X47]:(~v1_relat_1(X47)|~v1_funct_1(X47)|r1_tarski(k9_relat_1(X47,k10_relat_1(X47,X46)),X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 0.50/0.71  cnf(c_0_76, plain, (r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.50/0.71  cnf(c_0_77, negated_conjecture, (r1_tarski(k10_relat_1(esk3_0,X1),k1_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_74, c_0_33])).
% 0.50/0.71  fof(c_0_78, plain, ![X40, X41, X42]:(~v1_relat_1(X42)|~v1_funct_1(X42)|(~v2_funct_1(X42)|k9_relat_1(X42,k6_subset_1(X40,X41))=k6_subset_1(k9_relat_1(X42,X40),k9_relat_1(X42,X41)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_funct_1])])).
% 0.50/0.71  cnf(c_0_79, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.50/0.71  cnf(c_0_80, negated_conjecture, (r1_tarski(k10_relat_1(esk3_0,X1),k10_relat_1(esk3_0,k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_62])])).
% 0.50/0.71  cnf(c_0_81, plain, (k9_relat_1(X1,k6_subset_1(X2,X3))=k6_subset_1(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.50/0.71  cnf(c_0_82, plain, (r1_tarski(X1,X2)|~v1_funct_1(X3)|~v1_relat_1(X3)|~r1_tarski(X1,k9_relat_1(X3,k10_relat_1(X3,X2)))), inference(spm,[status(thm)],[c_0_21, c_0_79])).
% 0.50/0.71  cnf(c_0_83, negated_conjecture, (k10_relat_1(esk3_0,k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)))=k10_relat_1(esk3_0,X1)|~r1_tarski(k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_80]), c_0_62])])).
% 0.50/0.71  cnf(c_0_84, plain, (k9_relat_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_44]), c_0_44])).
% 0.50/0.71  cnf(c_0_85, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,k9_relat_1(X2,k10_relat_1(X2,X3)))),X3)|~v1_funct_1(X2)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_82, c_0_79])).
% 0.50/0.71  cnf(c_0_86, negated_conjecture, (k10_relat_1(esk3_0,k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)))=k10_relat_1(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_79]), c_0_61]), c_0_62])])).
% 0.50/0.71  cnf(c_0_87, plain, (k9_relat_1(X1,k4_xboole_0(X2,X3))=k1_xboole_0|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))), inference(spm,[status(thm)],[c_0_30, c_0_84])).
% 0.50/0.71  cnf(c_0_88, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_61]), c_0_62])])).
% 0.50/0.71  cnf(c_0_89, negated_conjecture, (v2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.50/0.71  fof(c_0_90, plain, ![X26, X27, X28]:(~r1_tarski(k4_xboole_0(X26,X27),X28)|r1_tarski(X26,k2_xboole_0(X27,X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 0.50/0.71  cnf(c_0_91, plain, (r1_tarski(k4_xboole_0(X1,X2),k10_relat_1(X3,k9_relat_1(X3,k4_xboole_0(X1,X2))))|~v1_relat_1(X3)|~r1_tarski(X1,k1_relat_1(X3))), inference(spm,[status(thm)],[c_0_76, c_0_46])).
% 0.50/0.71  cnf(c_0_92, negated_conjecture, (k9_relat_1(esk3_0,k4_xboole_0(k10_relat_1(esk3_0,k9_relat_1(esk3_0,X1)),X1))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_89]), c_0_61]), c_0_62])])).
% 0.50/0.71  cnf(c_0_93, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.50/0.71  cnf(c_0_94, negated_conjecture, (r1_tarski(k4_xboole_0(k10_relat_1(esk3_0,k9_relat_1(esk3_0,X1)),X1),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_66]), c_0_62]), c_0_77])])).
% 0.50/0.71  cnf(c_0_95, negated_conjecture, (~r1_tarski(k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0)),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.50/0.71  cnf(c_0_96, negated_conjecture, (r1_tarski(k10_relat_1(esk3_0,k9_relat_1(esk3_0,X1)),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_41])).
% 0.50/0.71  cnf(c_0_97, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_95, c_0_96])]), ['proof']).
% 0.50/0.71  # SZS output end CNFRefutation
% 0.50/0.71  # Proof object total steps             : 98
% 0.50/0.71  # Proof object clause steps            : 61
% 0.50/0.71  # Proof object formula steps           : 37
% 0.50/0.71  # Proof object conjectures             : 20
% 0.50/0.71  # Proof object clause conjectures      : 17
% 0.50/0.71  # Proof object formula conjectures     : 3
% 0.50/0.71  # Proof object initial clauses used    : 23
% 0.50/0.71  # Proof object initial formulas used   : 18
% 0.50/0.71  # Proof object generating inferences   : 34
% 0.50/0.71  # Proof object simplifying inferences  : 45
% 0.50/0.71  # Training examples: 0 positive, 0 negative
% 0.50/0.71  # Parsed axioms                        : 19
% 0.50/0.71  # Removed by relevancy pruning/SinE    : 0
% 0.50/0.71  # Initial clauses                      : 27
% 0.50/0.71  # Removed in clause preprocessing      : 1
% 0.50/0.71  # Initial clauses in saturation        : 26
% 0.50/0.71  # Processed clauses                    : 2609
% 0.50/0.71  # ...of these trivial                  : 17
% 0.50/0.71  # ...subsumed                          : 2026
% 0.50/0.71  # ...remaining for further processing  : 566
% 0.50/0.71  # Other redundant clauses eliminated   : 4
% 0.50/0.71  # Clauses deleted for lack of memory   : 0
% 0.50/0.71  # Backward-subsumed                    : 40
% 0.50/0.71  # Backward-rewritten                   : 34
% 0.50/0.71  # Generated clauses                    : 20365
% 0.50/0.71  # ...of the previous two non-trivial   : 16813
% 0.50/0.71  # Contextual simplify-reflections      : 0
% 0.50/0.71  # Paramodulations                      : 20361
% 0.50/0.71  # Factorizations                       : 0
% 0.50/0.71  # Equation resolutions                 : 4
% 0.50/0.71  # Propositional unsat checks           : 0
% 0.50/0.71  #    Propositional check models        : 0
% 0.50/0.71  #    Propositional check unsatisfiable : 0
% 0.50/0.71  #    Propositional clauses             : 0
% 0.50/0.71  #    Propositional clauses after purity: 0
% 0.50/0.71  #    Propositional unsat core size     : 0
% 0.50/0.71  #    Propositional preprocessing time  : 0.000
% 0.50/0.71  #    Propositional encoding time       : 0.000
% 0.50/0.71  #    Propositional solver time         : 0.000
% 0.50/0.71  #    Success case prop preproc time    : 0.000
% 0.50/0.71  #    Success case prop encoding time   : 0.000
% 0.50/0.71  #    Success case prop solver time     : 0.000
% 0.50/0.71  # Current number of processed clauses  : 465
% 0.50/0.71  #    Positive orientable unit clauses  : 59
% 0.50/0.71  #    Positive unorientable unit clauses: 0
% 0.50/0.71  #    Negative unit clauses             : 3
% 0.50/0.71  #    Non-unit-clauses                  : 403
% 0.50/0.71  # Current number of unprocessed clauses: 13901
% 0.50/0.71  # ...number of literals in the above   : 50614
% 0.50/0.71  # Current number of archived formulas  : 0
% 0.50/0.71  # Current number of archived clauses   : 100
% 0.50/0.71  # Clause-clause subsumption calls (NU) : 40671
% 0.50/0.71  # Rec. Clause-clause subsumption calls : 29307
% 0.50/0.71  # Non-unit clause-clause subsumptions  : 2060
% 0.50/0.71  # Unit Clause-clause subsumption calls : 196
% 0.50/0.71  # Rewrite failures with RHS unbound    : 0
% 0.50/0.71  # BW rewrite match attempts            : 204
% 0.50/0.71  # BW rewrite match successes           : 30
% 0.50/0.71  # Condensation attempts                : 0
% 0.50/0.71  # Condensation successes               : 0
% 0.50/0.71  # Termbank termtop insertions          : 295952
% 0.50/0.71  
% 0.50/0.71  # -------------------------------------------------
% 0.50/0.71  # User time                : 0.331 s
% 0.50/0.71  # System time              : 0.014 s
% 0.50/0.71  # Total time               : 0.346 s
% 0.50/0.71  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
