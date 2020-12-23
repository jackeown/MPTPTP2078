%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:02 EST 2020

% Result     : Theorem 0.39s
% Output     : CNFRefutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 158 expanded)
%              Number of clauses        :   40 (  66 expanded)
%              Number of leaves         :   15 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :  140 ( 361 expanded)
%              Number of equality atoms :   39 (  83 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t152_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v2_funct_1(X2)
       => r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

fof(t167_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(t123_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( v2_funct_1(X3)
       => k9_relat_1(X3,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(t138_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => k10_relat_1(X3,k6_subset_1(X1,X2)) = k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t146_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(c_0_15,plain,(
    ! [X28,X29,X30] :
      ( ~ r1_tarski(k2_xboole_0(X28,X29),X30)
      | r1_tarski(X28,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

fof(c_0_16,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_17,plain,(
    ! [X31,X32] :
      ( ~ r1_tarski(X31,X32)
      | k2_xboole_0(X31,X32) = X32 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_18,plain,(
    ! [X34,X35] : r1_tarski(k4_xboole_0(X34,X35),X34) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( v2_funct_1(X2)
         => r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t152_funct_1])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X52,X53] :
      ( ~ v1_relat_1(X53)
      | r1_tarski(k10_relat_1(X53,X52),k1_relat_1(X53)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).

fof(c_0_25,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & v1_funct_1(esk5_0)
    & v2_funct_1(esk5_0)
    & ~ r1_tarski(k10_relat_1(esk5_0,k9_relat_1(esk5_0,esk4_0)),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_26,plain,(
    ! [X70,X71] :
      ( ~ v1_relat_1(X71)
      | ~ v1_funct_1(X71)
      | r1_tarski(k9_relat_1(X71,k10_relat_1(X71,X70)),X70) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

fof(c_0_27,plain,(
    ! [X64,X65,X66] :
      ( ~ v1_relat_1(X66)
      | ~ v1_funct_1(X66)
      | ~ v2_funct_1(X66)
      | k9_relat_1(X66,k6_subset_1(X64,X65)) = k6_subset_1(k9_relat_1(X66,X64),k9_relat_1(X66,X65)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_funct_1])])).

fof(c_0_28,plain,(
    ! [X46,X47] : k6_subset_1(X46,X47) = k4_xboole_0(X46,X47) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_29,plain,(
    ! [X67,X68,X69] :
      ( ~ v1_relat_1(X69)
      | ~ v1_funct_1(X69)
      | k10_relat_1(X69,k6_subset_1(X67,X68)) = k6_subset_1(k10_relat_1(X69,X67),k10_relat_1(X69,X68)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t138_funct_1])])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(k2_xboole_0(X3,X1),X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_21])).

cnf(c_0_32,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_34,plain,(
    ! [X26,X27] :
      ( ( k4_xboole_0(X26,X27) != k1_xboole_0
        | r1_tarski(X26,X27) )
      & ( ~ r1_tarski(X26,X27)
        | k4_xboole_0(X26,X27) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_35,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( k9_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( k10_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_40,plain,(
    ! [X24,X25] :
      ( ( r1_tarski(X24,X25)
        | X24 != X25 )
      & ( r1_tarski(X25,X24)
        | X24 != X25 )
      & ( ~ r1_tarski(X24,X25)
        | ~ r1_tarski(X25,X24)
        | X24 = X25 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_41,plain,(
    ! [X72,X73] :
      ( ~ v1_relat_1(X73)
      | ~ r1_tarski(X72,k1_relat_1(X73))
      | r1_tarski(X72,k10_relat_1(X73,k9_relat_1(X73,X72))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).

cnf(c_0_42,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk5_0,X1),k1_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk5_0,k10_relat_1(esk5_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_33])])).

cnf(c_0_46,plain,
    ( k9_relat_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38]),c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( v2_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_48,plain,
    ( k10_relat_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_38]),c_0_38])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,plain,
    ( r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k10_relat_1(esk5_0,X1),X2),k1_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( k4_xboole_0(k9_relat_1(esk5_0,k10_relat_1(esk5_0,X1)),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( k4_xboole_0(k9_relat_1(esk5_0,X1),k9_relat_1(esk5_0,X2)) = k9_relat_1(esk5_0,k4_xboole_0(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_36]),c_0_33])])).

cnf(c_0_54,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_23])).

cnf(c_0_55,negated_conjecture,
    ( k4_xboole_0(k10_relat_1(esk5_0,X1),k10_relat_1(esk5_0,X2)) = k10_relat_1(esk5_0,k4_xboole_0(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_36]),c_0_33])])).

fof(c_0_56,plain,(
    ! [X36,X37] : k2_xboole_0(X36,k4_xboole_0(X37,X36)) = k2_xboole_0(X36,X37) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_49])).

fof(c_0_58,plain,(
    ! [X40,X41,X42] :
      ( ~ r1_tarski(k4_xboole_0(X40,X41),X42)
      | r1_tarski(X40,k2_xboole_0(X41,X42)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k10_relat_1(esk5_0,X1),X2),k10_relat_1(esk5_0,k9_relat_1(esk5_0,k4_xboole_0(k10_relat_1(esk5_0,X1),X2)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_33])])).

cnf(c_0_60,negated_conjecture,
    ( k9_relat_1(esk5_0,k4_xboole_0(k10_relat_1(esk5_0,k9_relat_1(esk5_0,X1)),X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_61,negated_conjecture,
    ( k10_relat_1(esk5_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_55]),c_0_54])).

cnf(c_0_62,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_63,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_57])).

cnf(c_0_64,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_22,c_0_57])).

cnf(c_0_65,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k10_relat_1(esk5_0,k9_relat_1(esk5_0,X1)),X1),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])).

cnf(c_0_67,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])).

cnf(c_0_68,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(esk5_0,k9_relat_1(esk5_0,esk4_0)),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk5_0,k9_relat_1(esk5_0,X1)),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_69])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:59:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.39/0.60  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.39/0.60  # and selection function SelectCQArNTNpEqFirst.
% 0.39/0.60  #
% 0.39/0.60  # Preprocessing time       : 0.029 s
% 0.39/0.60  # Presaturation interreduction done
% 0.39/0.60  
% 0.39/0.60  # Proof found!
% 0.39/0.60  # SZS status Theorem
% 0.39/0.60  # SZS output start CNFRefutation
% 0.39/0.60  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.39/0.60  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.39/0.60  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.39/0.60  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.39/0.60  fof(t152_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v2_funct_1(X2)=>r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_funct_1)).
% 0.39/0.60  fof(t167_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 0.39/0.60  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 0.39/0.60  fof(t123_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(v2_funct_1(X3)=>k9_relat_1(X3,k6_subset_1(X1,X2))=k6_subset_1(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_funct_1)).
% 0.39/0.60  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.39/0.60  fof(t138_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>k10_relat_1(X3,k6_subset_1(X1,X2))=k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_funct_1)).
% 0.39/0.60  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.39/0.60  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.39/0.60  fof(t146_funct_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 0.39/0.60  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.39/0.60  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 0.39/0.60  fof(c_0_15, plain, ![X28, X29, X30]:(~r1_tarski(k2_xboole_0(X28,X29),X30)|r1_tarski(X28,X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.39/0.60  fof(c_0_16, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.39/0.60  fof(c_0_17, plain, ![X31, X32]:(~r1_tarski(X31,X32)|k2_xboole_0(X31,X32)=X32), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.39/0.60  fof(c_0_18, plain, ![X34, X35]:r1_tarski(k4_xboole_0(X34,X35),X34), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.39/0.60  fof(c_0_19, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v2_funct_1(X2)=>r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1)))), inference(assume_negation,[status(cth)],[t152_funct_1])).
% 0.39/0.60  cnf(c_0_20, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.39/0.60  cnf(c_0_21, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.39/0.60  cnf(c_0_22, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.39/0.60  cnf(c_0_23, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.39/0.60  fof(c_0_24, plain, ![X52, X53]:(~v1_relat_1(X53)|r1_tarski(k10_relat_1(X53,X52),k1_relat_1(X53))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).
% 0.39/0.60  fof(c_0_25, negated_conjecture, ((v1_relat_1(esk5_0)&v1_funct_1(esk5_0))&(v2_funct_1(esk5_0)&~r1_tarski(k10_relat_1(esk5_0,k9_relat_1(esk5_0,esk4_0)),esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.39/0.60  fof(c_0_26, plain, ![X70, X71]:(~v1_relat_1(X71)|~v1_funct_1(X71)|r1_tarski(k9_relat_1(X71,k10_relat_1(X71,X70)),X70)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 0.39/0.60  fof(c_0_27, plain, ![X64, X65, X66]:(~v1_relat_1(X66)|~v1_funct_1(X66)|(~v2_funct_1(X66)|k9_relat_1(X66,k6_subset_1(X64,X65))=k6_subset_1(k9_relat_1(X66,X64),k9_relat_1(X66,X65)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_funct_1])])).
% 0.39/0.60  fof(c_0_28, plain, ![X46, X47]:k6_subset_1(X46,X47)=k4_xboole_0(X46,X47), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.39/0.60  fof(c_0_29, plain, ![X67, X68, X69]:(~v1_relat_1(X69)|~v1_funct_1(X69)|k10_relat_1(X69,k6_subset_1(X67,X68))=k6_subset_1(k10_relat_1(X69,X67),k10_relat_1(X69,X68))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t138_funct_1])])).
% 0.39/0.60  cnf(c_0_30, plain, (r1_tarski(X1,X2)|~r1_tarski(k2_xboole_0(X3,X1),X2)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.39/0.60  cnf(c_0_31, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_21])).
% 0.39/0.60  cnf(c_0_32, plain, (r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.39/0.60  cnf(c_0_33, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.39/0.60  fof(c_0_34, plain, ![X26, X27]:((k4_xboole_0(X26,X27)!=k1_xboole_0|r1_tarski(X26,X27))&(~r1_tarski(X26,X27)|k4_xboole_0(X26,X27)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.39/0.60  cnf(c_0_35, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.39/0.60  cnf(c_0_36, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.39/0.60  cnf(c_0_37, plain, (k9_relat_1(X1,k6_subset_1(X2,X3))=k6_subset_1(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.39/0.60  cnf(c_0_38, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.39/0.60  cnf(c_0_39, plain, (k10_relat_1(X1,k6_subset_1(X2,X3))=k6_subset_1(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.39/0.60  fof(c_0_40, plain, ![X24, X25]:(((r1_tarski(X24,X25)|X24!=X25)&(r1_tarski(X25,X24)|X24!=X25))&(~r1_tarski(X24,X25)|~r1_tarski(X25,X24)|X24=X25)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.39/0.60  fof(c_0_41, plain, ![X72, X73]:(~v1_relat_1(X73)|(~r1_tarski(X72,k1_relat_1(X73))|r1_tarski(X72,k10_relat_1(X73,k9_relat_1(X73,X72))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).
% 0.39/0.60  cnf(c_0_42, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.39/0.60  cnf(c_0_43, negated_conjecture, (r1_tarski(k10_relat_1(esk5_0,X1),k1_relat_1(esk5_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.39/0.60  cnf(c_0_44, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.39/0.60  cnf(c_0_45, negated_conjecture, (r1_tarski(k9_relat_1(esk5_0,k10_relat_1(esk5_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_33])])).
% 0.39/0.60  cnf(c_0_46, plain, (k9_relat_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38]), c_0_38])).
% 0.39/0.60  cnf(c_0_47, negated_conjecture, (v2_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.39/0.60  cnf(c_0_48, plain, (k10_relat_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_38]), c_0_38])).
% 0.39/0.60  cnf(c_0_49, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.39/0.60  cnf(c_0_50, plain, (r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.39/0.60  cnf(c_0_51, negated_conjecture, (r1_tarski(k4_xboole_0(k10_relat_1(esk5_0,X1),X2),k1_relat_1(esk5_0))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.39/0.60  cnf(c_0_52, negated_conjecture, (k4_xboole_0(k9_relat_1(esk5_0,k10_relat_1(esk5_0,X1)),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.39/0.60  cnf(c_0_53, negated_conjecture, (k4_xboole_0(k9_relat_1(esk5_0,X1),k9_relat_1(esk5_0,X2))=k9_relat_1(esk5_0,k4_xboole_0(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_36]), c_0_33])])).
% 0.39/0.60  cnf(c_0_54, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_44, c_0_23])).
% 0.39/0.60  cnf(c_0_55, negated_conjecture, (k4_xboole_0(k10_relat_1(esk5_0,X1),k10_relat_1(esk5_0,X2))=k10_relat_1(esk5_0,k4_xboole_0(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_36]), c_0_33])])).
% 0.39/0.60  fof(c_0_56, plain, ![X36, X37]:k2_xboole_0(X36,k4_xboole_0(X37,X36))=k2_xboole_0(X36,X37), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.39/0.60  cnf(c_0_57, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_49])).
% 0.39/0.60  fof(c_0_58, plain, ![X40, X41, X42]:(~r1_tarski(k4_xboole_0(X40,X41),X42)|r1_tarski(X40,k2_xboole_0(X41,X42))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 0.39/0.60  cnf(c_0_59, negated_conjecture, (r1_tarski(k4_xboole_0(k10_relat_1(esk5_0,X1),X2),k10_relat_1(esk5_0,k9_relat_1(esk5_0,k4_xboole_0(k10_relat_1(esk5_0,X1),X2))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_33])])).
% 0.39/0.60  cnf(c_0_60, negated_conjecture, (k9_relat_1(esk5_0,k4_xboole_0(k10_relat_1(esk5_0,k9_relat_1(esk5_0,X1)),X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.39/0.60  cnf(c_0_61, negated_conjecture, (k10_relat_1(esk5_0,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_55]), c_0_54])).
% 0.39/0.60  cnf(c_0_62, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.39/0.60  cnf(c_0_63, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_44, c_0_57])).
% 0.39/0.60  cnf(c_0_64, plain, (k2_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_22, c_0_57])).
% 0.39/0.60  cnf(c_0_65, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.39/0.60  cnf(c_0_66, negated_conjecture, (r1_tarski(k4_xboole_0(k10_relat_1(esk5_0,k9_relat_1(esk5_0,X1)),X1),k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])).
% 0.39/0.60  cnf(c_0_67, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])).
% 0.39/0.60  cnf(c_0_68, negated_conjecture, (~r1_tarski(k10_relat_1(esk5_0,k9_relat_1(esk5_0,esk4_0)),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.39/0.60  cnf(c_0_69, negated_conjecture, (r1_tarski(k10_relat_1(esk5_0,k9_relat_1(esk5_0,X1)),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67])).
% 0.39/0.60  cnf(c_0_70, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_69])]), ['proof']).
% 0.39/0.60  # SZS output end CNFRefutation
% 0.39/0.60  # Proof object total steps             : 71
% 0.39/0.60  # Proof object clause steps            : 40
% 0.39/0.60  # Proof object formula steps           : 31
% 0.39/0.60  # Proof object conjectures             : 19
% 0.39/0.60  # Proof object clause conjectures      : 16
% 0.39/0.60  # Proof object formula conjectures     : 3
% 0.39/0.60  # Proof object initial clauses used    : 18
% 0.39/0.60  # Proof object initial formulas used   : 15
% 0.39/0.60  # Proof object generating inferences   : 18
% 0.39/0.60  # Proof object simplifying inferences  : 22
% 0.39/0.60  # Training examples: 0 positive, 0 negative
% 0.39/0.60  # Parsed axioms                        : 27
% 0.39/0.60  # Removed by relevancy pruning/SinE    : 0
% 0.39/0.60  # Initial clauses                      : 45
% 0.39/0.60  # Removed in clause preprocessing      : 2
% 0.39/0.60  # Initial clauses in saturation        : 43
% 0.39/0.60  # Processed clauses                    : 2411
% 0.39/0.60  # ...of these trivial                  : 185
% 0.39/0.60  # ...subsumed                          : 1609
% 0.39/0.60  # ...remaining for further processing  : 617
% 0.39/0.60  # Other redundant clauses eliminated   : 24
% 0.39/0.60  # Clauses deleted for lack of memory   : 0
% 0.39/0.60  # Backward-subsumed                    : 10
% 0.39/0.60  # Backward-rewritten                   : 85
% 0.39/0.60  # Generated clauses                    : 15612
% 0.39/0.60  # ...of the previous two non-trivial   : 10219
% 0.39/0.60  # Contextual simplify-reflections      : 0
% 0.39/0.60  # Paramodulations                      : 15562
% 0.39/0.60  # Factorizations                       : 26
% 0.39/0.60  # Equation resolutions                 : 24
% 0.39/0.60  # Propositional unsat checks           : 0
% 0.39/0.60  #    Propositional check models        : 0
% 0.39/0.60  #    Propositional check unsatisfiable : 0
% 0.39/0.60  #    Propositional clauses             : 0
% 0.39/0.60  #    Propositional clauses after purity: 0
% 0.39/0.60  #    Propositional unsat core size     : 0
% 0.39/0.60  #    Propositional preprocessing time  : 0.000
% 0.39/0.60  #    Propositional encoding time       : 0.000
% 0.39/0.60  #    Propositional solver time         : 0.000
% 0.39/0.60  #    Success case prop preproc time    : 0.000
% 0.39/0.60  #    Success case prop encoding time   : 0.000
% 0.39/0.60  #    Success case prop solver time     : 0.000
% 0.39/0.60  # Current number of processed clauses  : 472
% 0.39/0.60  #    Positive orientable unit clauses  : 206
% 0.39/0.60  #    Positive unorientable unit clauses: 2
% 0.39/0.60  #    Negative unit clauses             : 16
% 0.39/0.60  #    Non-unit-clauses                  : 248
% 0.39/0.60  # Current number of unprocessed clauses: 7716
% 0.39/0.60  # ...number of literals in the above   : 15464
% 0.39/0.60  # Current number of archived formulas  : 0
% 0.39/0.60  # Current number of archived clauses   : 139
% 0.39/0.60  # Clause-clause subsumption calls (NU) : 11084
% 0.39/0.60  # Rec. Clause-clause subsumption calls : 8311
% 0.39/0.60  # Non-unit clause-clause subsumptions  : 1354
% 0.39/0.60  # Unit Clause-clause subsumption calls : 244
% 0.39/0.60  # Rewrite failures with RHS unbound    : 0
% 0.39/0.60  # BW rewrite match attempts            : 584
% 0.39/0.60  # BW rewrite match successes           : 50
% 0.39/0.60  # Condensation attempts                : 0
% 0.39/0.60  # Condensation successes               : 0
% 0.39/0.60  # Termbank termtop insertions          : 245958
% 0.39/0.60  
% 0.39/0.60  # -------------------------------------------------
% 0.39/0.60  # User time                : 0.234 s
% 0.39/0.60  # System time              : 0.019 s
% 0.39/0.60  # Total time               : 0.253 s
% 0.39/0.60  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
