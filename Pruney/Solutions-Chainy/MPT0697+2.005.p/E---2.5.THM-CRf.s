%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:02 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 248 expanded)
%              Number of clauses        :   47 ( 104 expanded)
%              Number of leaves         :   15 (  62 expanded)
%              Depth                    :   13
%              Number of atoms          :  200 ( 693 expanded)
%              Number of equality atoms :   49 ( 137 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t152_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v2_funct_1(X2)
       => r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

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

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t146_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t123_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( v2_funct_1(X3)
       => k9_relat_1(X3,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).

fof(t45_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(c_0_15,plain,(
    ! [X31,X32,X33,X34,X35,X36,X37] :
      ( ( r2_hidden(X34,k1_relat_1(X31))
        | ~ r2_hidden(X34,X33)
        | X33 != k10_relat_1(X31,X32)
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) )
      & ( r2_hidden(k1_funct_1(X31,X34),X32)
        | ~ r2_hidden(X34,X33)
        | X33 != k10_relat_1(X31,X32)
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) )
      & ( ~ r2_hidden(X35,k1_relat_1(X31))
        | ~ r2_hidden(k1_funct_1(X31,X35),X32)
        | r2_hidden(X35,X33)
        | X33 != k10_relat_1(X31,X32)
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) )
      & ( ~ r2_hidden(esk2_3(X31,X36,X37),X37)
        | ~ r2_hidden(esk2_3(X31,X36,X37),k1_relat_1(X31))
        | ~ r2_hidden(k1_funct_1(X31,esk2_3(X31,X36,X37)),X36)
        | X37 = k10_relat_1(X31,X36)
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) )
      & ( r2_hidden(esk2_3(X31,X36,X37),k1_relat_1(X31))
        | r2_hidden(esk2_3(X31,X36,X37),X37)
        | X37 = k10_relat_1(X31,X36)
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) )
      & ( r2_hidden(k1_funct_1(X31,esk2_3(X31,X36,X37)),X36)
        | r2_hidden(esk2_3(X31,X36,X37),X37)
        | X37 = k10_relat_1(X31,X36)
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_funct_1])])])])])])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( v2_funct_1(X2)
         => r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t152_funct_1])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,X3)
    | X3 != k10_relat_1(X2,X4)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_18,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & v1_funct_1(esk4_0)
    & v2_funct_1(esk4_0)
    & ~ r1_tarski(k10_relat_1(esk4_0,k9_relat_1(esk4_0,esk3_0)),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_19,plain,(
    ! [X42,X43,X44] :
      ( ~ v1_relat_1(X44)
      | ~ v1_funct_1(X44)
      | k10_relat_1(X44,k6_subset_1(X42,X43)) = k6_subset_1(k10_relat_1(X44,X42),k10_relat_1(X44,X43)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t138_funct_1])])).

fof(c_0_20,plain,(
    ! [X29,X30] : k6_subset_1(X29,X30) = k4_xboole_0(X29,X30) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k10_relat_1(X2,X3)) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_25,plain,(
    ! [X45,X46] :
      ( ~ v1_relat_1(X46)
      | ~ v1_funct_1(X46)
      | r1_tarski(k9_relat_1(X46,k10_relat_1(X46,X45)),X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

cnf(c_0_26,plain,
    ( k10_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_28,plain,(
    ! [X13,X14] :
      ( ( k4_xboole_0(X13,X14) != k1_xboole_0
        | r1_tarski(X13,X14) )
      & ( ~ r1_tarski(X13,X14)
        | k4_xboole_0(X13,X14) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_29,plain,(
    ! [X21,X22] : r1_tarski(k4_xboole_0(X21,X22),X21) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_30,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_31,plain,(
    ! [X18,X19] :
      ( ~ r1_tarski(X18,X19)
      | k2_xboole_0(X18,X19) = X19 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_32,plain,(
    ! [X47,X48] :
      ( ~ v1_relat_1(X48)
      | ~ r1_tarski(X47,k1_relat_1(X48))
      | r1_tarski(X47,k10_relat_1(X48,k9_relat_1(X48,X47))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(esk4_0))
    | ~ r2_hidden(X1,k10_relat_1(esk4_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_34,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( k10_relat_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_27])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_40,plain,(
    ! [X15,X16,X17] :
      ( ~ r1_tarski(k2_xboole_0(X15,X16),X17)
      | r1_tarski(X15,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_41,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_42,plain,(
    ! [X39,X40,X41] :
      ( ~ v1_relat_1(X41)
      | ~ v1_funct_1(X41)
      | ~ v2_funct_1(X41)
      | k9_relat_1(X41,k6_subset_1(X39,X40)) = k6_subset_1(k9_relat_1(X41,X39),k9_relat_1(X41,X40)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_funct_1])])).

cnf(c_0_43,plain,
    ( r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk1_2(k10_relat_1(esk4_0,X1),X2),k1_relat_1(esk4_0))
    | r1_tarski(k10_relat_1(esk4_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk4_0,k10_relat_1(esk4_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_22]),c_0_23])])).

cnf(c_0_47,negated_conjecture,
    ( k10_relat_1(esk4_0,k4_xboole_0(X1,X2)) = k4_xboole_0(k10_relat_1(esk4_0,X1),k10_relat_1(esk4_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_22]),c_0_23])])).

cnf(c_0_48,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_49,plain,(
    ! [X24,X25] :
      ( ~ r1_tarski(X24,X25)
      | X25 = k2_xboole_0(X24,k4_xboole_0(X25,X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_52,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_41,c_0_38])).

cnf(c_0_53,plain,
    ( k9_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(X1,k10_relat_1(esk4_0,k9_relat_1(esk4_0,X1)))
    | ~ r1_tarski(X1,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_23])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk4_0,X1),k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_56,negated_conjecture,
    ( k4_xboole_0(k9_relat_1(esk4_0,k10_relat_1(esk4_0,X1)),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_46])).

cnf(c_0_57,negated_conjecture,
    ( k10_relat_1(esk4_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_47]),c_0_48])).

cnf(c_0_58,plain,
    ( X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_50])).

cnf(c_0_60,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_61,plain,
    ( k9_relat_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_27]),c_0_27])).

cnf(c_0_62,negated_conjecture,
    ( v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk4_0,X1),k10_relat_1(esk4_0,k9_relat_1(esk4_0,k10_relat_1(esk4_0,X1)))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_64,negated_conjecture,
    ( k4_xboole_0(k10_relat_1(esk4_0,k9_relat_1(esk4_0,k10_relat_1(esk4_0,X1))),k10_relat_1(esk4_0,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_56]),c_0_57])).

cnf(c_0_65,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_50]),c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k10_relat_1(esk4_0,X1),X2),k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_55])).

cnf(c_0_67,negated_conjecture,
    ( k9_relat_1(esk4_0,k4_xboole_0(X1,X2)) = k4_xboole_0(k9_relat_1(esk4_0,X1),k9_relat_1(esk4_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_22]),c_0_23])])).

cnf(c_0_68,negated_conjecture,
    ( k10_relat_1(esk4_0,k9_relat_1(esk4_0,k10_relat_1(esk4_0,X1))) = k10_relat_1(esk4_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_63]),c_0_64]),c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k10_relat_1(esk4_0,X1),X2),k4_xboole_0(k10_relat_1(esk4_0,X1),k10_relat_1(esk4_0,k9_relat_1(esk4_0,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_66]),c_0_67]),c_0_47]),c_0_68])).

fof(c_0_70,plain,(
    ! [X23] : k4_xboole_0(X23,k1_xboole_0) = X23 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k10_relat_1(esk4_0,k9_relat_1(esk4_0,X1)),X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_59])).

cnf(c_0_72,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_74,negated_conjecture,
    ( k4_xboole_0(k10_relat_1(esk4_0,k9_relat_1(esk4_0,X1)),X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_71]),c_0_72])).

cnf(c_0_75,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(esk4_0,k9_relat_1(esk4_0,esk3_0)),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk4_0,k9_relat_1(esk4_0,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_76])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:19:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 2.07/2.27  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S002A
% 2.07/2.27  # and selection function SelectNegativeLiterals.
% 2.07/2.27  #
% 2.07/2.27  # Preprocessing time       : 0.028 s
% 2.07/2.27  # Presaturation interreduction done
% 2.07/2.27  
% 2.07/2.27  # Proof found!
% 2.07/2.27  # SZS status Theorem
% 2.07/2.27  # SZS output start CNFRefutation
% 2.07/2.27  fof(d13_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,k1_relat_1(X1))&r2_hidden(k1_funct_1(X1,X4),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_funct_1)).
% 2.07/2.27  fof(t152_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v2_funct_1(X2)=>r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_funct_1)).
% 2.07/2.27  fof(t138_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>k10_relat_1(X3,k6_subset_1(X1,X2))=k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_funct_1)).
% 2.07/2.27  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.07/2.27  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.07/2.27  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 2.07/2.27  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.07/2.27  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.07/2.27  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.07/2.27  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.07/2.27  fof(t146_funct_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 2.07/2.27  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.07/2.27  fof(t123_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(v2_funct_1(X3)=>k9_relat_1(X3,k6_subset_1(X1,X2))=k6_subset_1(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_funct_1)).
% 2.07/2.27  fof(t45_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>X2=k2_xboole_0(X1,k4_xboole_0(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 2.07/2.27  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.07/2.27  fof(c_0_15, plain, ![X31, X32, X33, X34, X35, X36, X37]:((((r2_hidden(X34,k1_relat_1(X31))|~r2_hidden(X34,X33)|X33!=k10_relat_1(X31,X32)|(~v1_relat_1(X31)|~v1_funct_1(X31)))&(r2_hidden(k1_funct_1(X31,X34),X32)|~r2_hidden(X34,X33)|X33!=k10_relat_1(X31,X32)|(~v1_relat_1(X31)|~v1_funct_1(X31))))&(~r2_hidden(X35,k1_relat_1(X31))|~r2_hidden(k1_funct_1(X31,X35),X32)|r2_hidden(X35,X33)|X33!=k10_relat_1(X31,X32)|(~v1_relat_1(X31)|~v1_funct_1(X31))))&((~r2_hidden(esk2_3(X31,X36,X37),X37)|(~r2_hidden(esk2_3(X31,X36,X37),k1_relat_1(X31))|~r2_hidden(k1_funct_1(X31,esk2_3(X31,X36,X37)),X36))|X37=k10_relat_1(X31,X36)|(~v1_relat_1(X31)|~v1_funct_1(X31)))&((r2_hidden(esk2_3(X31,X36,X37),k1_relat_1(X31))|r2_hidden(esk2_3(X31,X36,X37),X37)|X37=k10_relat_1(X31,X36)|(~v1_relat_1(X31)|~v1_funct_1(X31)))&(r2_hidden(k1_funct_1(X31,esk2_3(X31,X36,X37)),X36)|r2_hidden(esk2_3(X31,X36,X37),X37)|X37=k10_relat_1(X31,X36)|(~v1_relat_1(X31)|~v1_funct_1(X31)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_funct_1])])])])])])).
% 2.07/2.27  fof(c_0_16, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v2_funct_1(X2)=>r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1)))), inference(assume_negation,[status(cth)],[t152_funct_1])).
% 2.07/2.27  cnf(c_0_17, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(X1,X3)|X3!=k10_relat_1(X2,X4)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.07/2.27  fof(c_0_18, negated_conjecture, ((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&(v2_funct_1(esk4_0)&~r1_tarski(k10_relat_1(esk4_0,k9_relat_1(esk4_0,esk3_0)),esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 2.07/2.27  fof(c_0_19, plain, ![X42, X43, X44]:(~v1_relat_1(X44)|~v1_funct_1(X44)|k10_relat_1(X44,k6_subset_1(X42,X43))=k6_subset_1(k10_relat_1(X44,X42),k10_relat_1(X44,X43))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t138_funct_1])])).
% 2.07/2.27  fof(c_0_20, plain, ![X29, X30]:k6_subset_1(X29,X30)=k4_xboole_0(X29,X30), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 2.07/2.27  cnf(c_0_21, plain, (r2_hidden(X1,k1_relat_1(X2))|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k10_relat_1(X2,X3))), inference(er,[status(thm)],[c_0_17])).
% 2.07/2.27  cnf(c_0_22, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.07/2.27  cnf(c_0_23, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.07/2.27  fof(c_0_24, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 2.07/2.27  fof(c_0_25, plain, ![X45, X46]:(~v1_relat_1(X46)|~v1_funct_1(X46)|r1_tarski(k9_relat_1(X46,k10_relat_1(X46,X45)),X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 2.07/2.27  cnf(c_0_26, plain, (k10_relat_1(X1,k6_subset_1(X2,X3))=k6_subset_1(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 2.07/2.27  cnf(c_0_27, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.07/2.27  fof(c_0_28, plain, ![X13, X14]:((k4_xboole_0(X13,X14)!=k1_xboole_0|r1_tarski(X13,X14))&(~r1_tarski(X13,X14)|k4_xboole_0(X13,X14)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 2.07/2.27  fof(c_0_29, plain, ![X21, X22]:r1_tarski(k4_xboole_0(X21,X22),X21), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 2.07/2.27  fof(c_0_30, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 2.07/2.27  fof(c_0_31, plain, ![X18, X19]:(~r1_tarski(X18,X19)|k2_xboole_0(X18,X19)=X19), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 2.07/2.27  fof(c_0_32, plain, ![X47, X48]:(~v1_relat_1(X48)|(~r1_tarski(X47,k1_relat_1(X48))|r1_tarski(X47,k10_relat_1(X48,k9_relat_1(X48,X47))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).
% 2.07/2.27  cnf(c_0_33, negated_conjecture, (r2_hidden(X1,k1_relat_1(esk4_0))|~r2_hidden(X1,k10_relat_1(esk4_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])])).
% 2.07/2.27  cnf(c_0_34, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 2.07/2.27  cnf(c_0_35, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 2.07/2.27  cnf(c_0_36, plain, (k10_relat_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_27])).
% 2.07/2.27  cnf(c_0_37, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 2.07/2.27  cnf(c_0_38, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 2.07/2.27  cnf(c_0_39, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 2.07/2.27  fof(c_0_40, plain, ![X15, X16, X17]:(~r1_tarski(k2_xboole_0(X15,X16),X17)|r1_tarski(X15,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 2.07/2.27  cnf(c_0_41, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 2.07/2.27  fof(c_0_42, plain, ![X39, X40, X41]:(~v1_relat_1(X41)|~v1_funct_1(X41)|(~v2_funct_1(X41)|k9_relat_1(X41,k6_subset_1(X39,X40))=k6_subset_1(k9_relat_1(X41,X39),k9_relat_1(X41,X40)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_funct_1])])).
% 2.07/2.27  cnf(c_0_43, plain, (r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 2.07/2.27  cnf(c_0_44, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 2.07/2.27  cnf(c_0_45, negated_conjecture, (r2_hidden(esk1_2(k10_relat_1(esk4_0,X1),X2),k1_relat_1(esk4_0))|r1_tarski(k10_relat_1(esk4_0,X1),X2)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 2.07/2.27  cnf(c_0_46, negated_conjecture, (r1_tarski(k9_relat_1(esk4_0,k10_relat_1(esk4_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_22]), c_0_23])])).
% 2.07/2.27  cnf(c_0_47, negated_conjecture, (k10_relat_1(esk4_0,k4_xboole_0(X1,X2))=k4_xboole_0(k10_relat_1(esk4_0,X1),k10_relat_1(esk4_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_22]), c_0_23])])).
% 2.07/2.27  cnf(c_0_48, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 2.07/2.27  fof(c_0_49, plain, ![X24, X25]:(~r1_tarski(X24,X25)|X25=k2_xboole_0(X24,k4_xboole_0(X25,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).
% 2.07/2.27  cnf(c_0_50, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_39])).
% 2.07/2.27  cnf(c_0_51, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 2.07/2.27  cnf(c_0_52, plain, (k2_xboole_0(k4_xboole_0(X1,X2),X1)=X1), inference(spm,[status(thm)],[c_0_41, c_0_38])).
% 2.07/2.27  cnf(c_0_53, plain, (k9_relat_1(X1,k6_subset_1(X2,X3))=k6_subset_1(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 2.07/2.27  cnf(c_0_54, negated_conjecture, (r1_tarski(X1,k10_relat_1(esk4_0,k9_relat_1(esk4_0,X1)))|~r1_tarski(X1,k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_43, c_0_23])).
% 2.07/2.27  cnf(c_0_55, negated_conjecture, (r1_tarski(k10_relat_1(esk4_0,X1),k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 2.07/2.27  cnf(c_0_56, negated_conjecture, (k4_xboole_0(k9_relat_1(esk4_0,k10_relat_1(esk4_0,X1)),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_37, c_0_46])).
% 2.07/2.27  cnf(c_0_57, negated_conjecture, (k10_relat_1(esk4_0,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_47]), c_0_48])).
% 2.07/2.27  cnf(c_0_58, plain, (X2=k2_xboole_0(X1,k4_xboole_0(X2,X1))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 2.07/2.27  cnf(c_0_59, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_37, c_0_50])).
% 2.07/2.27  cnf(c_0_60, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 2.07/2.27  cnf(c_0_61, plain, (k9_relat_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_27]), c_0_27])).
% 2.07/2.27  cnf(c_0_62, negated_conjecture, (v2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.07/2.27  cnf(c_0_63, negated_conjecture, (r1_tarski(k10_relat_1(esk4_0,X1),k10_relat_1(esk4_0,k9_relat_1(esk4_0,k10_relat_1(esk4_0,X1))))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 2.07/2.27  cnf(c_0_64, negated_conjecture, (k4_xboole_0(k10_relat_1(esk4_0,k9_relat_1(esk4_0,k10_relat_1(esk4_0,X1))),k10_relat_1(esk4_0,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_56]), c_0_57])).
% 2.07/2.27  cnf(c_0_65, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_50]), c_0_59])).
% 2.07/2.27  cnf(c_0_66, negated_conjecture, (r1_tarski(k4_xboole_0(k10_relat_1(esk4_0,X1),X2),k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_60, c_0_55])).
% 2.07/2.27  cnf(c_0_67, negated_conjecture, (k9_relat_1(esk4_0,k4_xboole_0(X1,X2))=k4_xboole_0(k9_relat_1(esk4_0,X1),k9_relat_1(esk4_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_22]), c_0_23])])).
% 2.07/2.27  cnf(c_0_68, negated_conjecture, (k10_relat_1(esk4_0,k9_relat_1(esk4_0,k10_relat_1(esk4_0,X1)))=k10_relat_1(esk4_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_63]), c_0_64]), c_0_65])).
% 2.07/2.27  cnf(c_0_69, negated_conjecture, (r1_tarski(k4_xboole_0(k10_relat_1(esk4_0,X1),X2),k4_xboole_0(k10_relat_1(esk4_0,X1),k10_relat_1(esk4_0,k9_relat_1(esk4_0,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_66]), c_0_67]), c_0_47]), c_0_68])).
% 2.07/2.27  fof(c_0_70, plain, ![X23]:k4_xboole_0(X23,k1_xboole_0)=X23, inference(variable_rename,[status(thm)],[t3_boole])).
% 2.07/2.27  cnf(c_0_71, negated_conjecture, (r1_tarski(k4_xboole_0(k10_relat_1(esk4_0,k9_relat_1(esk4_0,X1)),X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_69, c_0_59])).
% 2.07/2.27  cnf(c_0_72, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_70])).
% 2.07/2.27  cnf(c_0_73, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 2.07/2.27  cnf(c_0_74, negated_conjecture, (k4_xboole_0(k10_relat_1(esk4_0,k9_relat_1(esk4_0,X1)),X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_71]), c_0_72])).
% 2.07/2.27  cnf(c_0_75, negated_conjecture, (~r1_tarski(k10_relat_1(esk4_0,k9_relat_1(esk4_0,esk3_0)),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.07/2.27  cnf(c_0_76, negated_conjecture, (r1_tarski(k10_relat_1(esk4_0,k9_relat_1(esk4_0,X1)),X1)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 2.07/2.27  cnf(c_0_77, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_76])]), ['proof']).
% 2.07/2.27  # SZS output end CNFRefutation
% 2.07/2.27  # Proof object total steps             : 78
% 2.07/2.27  # Proof object clause steps            : 47
% 2.07/2.27  # Proof object formula steps           : 31
% 2.07/2.27  # Proof object conjectures             : 25
% 2.07/2.27  # Proof object clause conjectures      : 22
% 2.07/2.27  # Proof object formula conjectures     : 3
% 2.07/2.27  # Proof object initial clauses used    : 20
% 2.07/2.27  # Proof object initial formulas used   : 15
% 2.07/2.27  # Proof object generating inferences   : 23
% 2.07/2.27  # Proof object simplifying inferences  : 26
% 2.07/2.27  # Training examples: 0 positive, 0 negative
% 2.07/2.27  # Parsed axioms                        : 18
% 2.07/2.27  # Removed by relevancy pruning/SinE    : 0
% 2.07/2.27  # Initial clauses                      : 31
% 2.07/2.27  # Removed in clause preprocessing      : 1
% 2.07/2.27  # Initial clauses in saturation        : 30
% 2.07/2.27  # Processed clauses                    : 6090
% 2.07/2.27  # ...of these trivial                  : 957
% 2.07/2.27  # ...subsumed                          : 3485
% 2.07/2.27  # ...remaining for further processing  : 1648
% 2.07/2.27  # Other redundant clauses eliminated   : 190
% 2.07/2.27  # Clauses deleted for lack of memory   : 0
% 2.07/2.27  # Backward-subsumed                    : 24
% 2.07/2.27  # Backward-rewritten                   : 156
% 2.07/2.27  # Generated clauses                    : 249271
% 2.07/2.27  # ...of the previous two non-trivial   : 206576
% 2.07/2.27  # Contextual simplify-reflections      : 31
% 2.07/2.27  # Paramodulations                      : 249030
% 2.07/2.27  # Factorizations                       : 32
% 2.07/2.27  # Equation resolutions                 : 209
% 2.07/2.27  # Propositional unsat checks           : 0
% 2.07/2.27  #    Propositional check models        : 0
% 2.07/2.27  #    Propositional check unsatisfiable : 0
% 2.07/2.27  #    Propositional clauses             : 0
% 2.07/2.27  #    Propositional clauses after purity: 0
% 2.07/2.27  #    Propositional unsat core size     : 0
% 2.07/2.27  #    Propositional preprocessing time  : 0.000
% 2.07/2.27  #    Propositional encoding time       : 0.000
% 2.07/2.27  #    Propositional solver time         : 0.000
% 2.07/2.27  #    Success case prop preproc time    : 0.000
% 2.07/2.27  #    Success case prop encoding time   : 0.000
% 2.07/2.27  #    Success case prop solver time     : 0.000
% 2.07/2.27  # Current number of processed clauses  : 1437
% 2.07/2.27  #    Positive orientable unit clauses  : 465
% 2.07/2.27  #    Positive unorientable unit clauses: 0
% 2.07/2.27  #    Negative unit clauses             : 0
% 2.07/2.27  #    Non-unit-clauses                  : 972
% 2.07/2.27  # Current number of unprocessed clauses: 199363
% 2.07/2.27  # ...number of literals in the above   : 800414
% 2.07/2.27  # Current number of archived formulas  : 0
% 2.07/2.27  # Current number of archived clauses   : 210
% 2.07/2.27  # Clause-clause subsumption calls (NU) : 143023
% 2.07/2.27  # Rec. Clause-clause subsumption calls : 102778
% 2.07/2.27  # Non-unit clause-clause subsumptions  : 3539
% 2.07/2.27  # Unit Clause-clause subsumption calls : 15161
% 2.07/2.27  # Rewrite failures with RHS unbound    : 0
% 2.07/2.27  # BW rewrite match attempts            : 1933
% 2.07/2.27  # BW rewrite match successes           : 42
% 2.07/2.27  # Condensation attempts                : 0
% 2.07/2.27  # Condensation successes               : 0
% 2.07/2.27  # Termbank termtop insertions          : 6400772
% 2.07/2.28  
% 2.07/2.28  # -------------------------------------------------
% 2.07/2.28  # User time                : 1.859 s
% 2.07/2.28  # System time              : 0.082 s
% 2.07/2.28  # Total time               : 1.941 s
% 2.07/2.28  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
