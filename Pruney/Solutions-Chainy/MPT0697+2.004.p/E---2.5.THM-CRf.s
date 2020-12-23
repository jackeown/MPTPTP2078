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
% DateTime   : Thu Dec  3 10:55:02 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 165 expanded)
%              Number of clauses        :   46 (  70 expanded)
%              Number of leaves         :   15 (  40 expanded)
%              Depth                    :   13
%              Number of atoms          :  206 ( 515 expanded)
%              Number of equality atoms :   43 (  71 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    4 (   2 average)

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

fof(t178_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

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

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(t138_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => k10_relat_1(X3,k6_subset_1(X1,X2)) = k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(c_0_15,plain,(
    ! [X29,X30,X31,X32,X33,X34,X35] :
      ( ( r2_hidden(X32,k1_relat_1(X29))
        | ~ r2_hidden(X32,X31)
        | X31 != k10_relat_1(X29,X30)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( r2_hidden(k1_funct_1(X29,X32),X30)
        | ~ r2_hidden(X32,X31)
        | X31 != k10_relat_1(X29,X30)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( ~ r2_hidden(X33,k1_relat_1(X29))
        | ~ r2_hidden(k1_funct_1(X29,X33),X30)
        | r2_hidden(X33,X31)
        | X31 != k10_relat_1(X29,X30)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( ~ r2_hidden(esk2_3(X29,X34,X35),X35)
        | ~ r2_hidden(esk2_3(X29,X34,X35),k1_relat_1(X29))
        | ~ r2_hidden(k1_funct_1(X29,esk2_3(X29,X34,X35)),X34)
        | X35 = k10_relat_1(X29,X34)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( r2_hidden(esk2_3(X29,X34,X35),k1_relat_1(X29))
        | r2_hidden(esk2_3(X29,X34,X35),X35)
        | X35 = k10_relat_1(X29,X34)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( r2_hidden(k1_funct_1(X29,esk2_3(X29,X34,X35)),X34)
        | r2_hidden(esk2_3(X29,X34,X35),X35)
        | X35 = k10_relat_1(X29,X34)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) ) ) ),
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
    ! [X26,X27,X28] :
      ( ~ v1_relat_1(X28)
      | ~ r1_tarski(X26,X27)
      | r1_tarski(k10_relat_1(X28,X26),k10_relat_1(X28,X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t178_relat_1])])).

fof(c_0_20,plain,(
    ! [X43,X44] :
      ( ~ v1_relat_1(X44)
      | ~ v1_funct_1(X44)
      | r1_tarski(k9_relat_1(X44,k10_relat_1(X44,X43)),X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

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
    ! [X18,X19] :
      ( ~ r1_tarski(X18,X19)
      | k2_xboole_0(X18,X19) = X19 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_26,plain,(
    ! [X21,X22] : r1_tarski(k4_xboole_0(X21,X22),X21) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_27,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_29,plain,(
    ! [X45,X46] :
      ( ~ v1_relat_1(X46)
      | ~ r1_tarski(X45,k1_relat_1(X46))
      | r1_tarski(X45,k10_relat_1(X46,k9_relat_1(X46,X45))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(esk4_0))
    | ~ r2_hidden(X1,k10_relat_1(esk4_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_31,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_32,plain,(
    ! [X15,X16,X17] :
      ( ~ r1_tarski(k2_xboole_0(X15,X16),X17)
      | r1_tarski(X15,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_33,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_35,plain,(
    ! [X37,X38,X39] :
      ( ~ v1_relat_1(X39)
      | ~ v1_funct_1(X39)
      | ~ v2_funct_1(X39)
      | k9_relat_1(X39,k6_subset_1(X37,X38)) = k6_subset_1(k9_relat_1(X39,X37),k9_relat_1(X39,X38)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_funct_1])])).

fof(c_0_36,plain,(
    ! [X24,X25] : k6_subset_1(X24,X25) = k4_xboole_0(X24,X25) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_37,plain,(
    ! [X40,X41,X42] :
      ( ~ v1_relat_1(X42)
      | ~ v1_funct_1(X42)
      | k10_relat_1(X42,k6_subset_1(X40,X41)) = k6_subset_1(k10_relat_1(X42,X40),k10_relat_1(X42,X41)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t138_funct_1])])).

fof(c_0_38,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk4_0,X1),k10_relat_1(esk4_0,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_23])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk4_0,k10_relat_1(esk4_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_22]),c_0_23])])).

cnf(c_0_41,plain,
    ( r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk1_2(k10_relat_1(esk4_0,X1),X2),k1_relat_1(esk4_0))
    | r1_tarski(k10_relat_1(esk4_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_46,plain,
    ( k9_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_47,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_48,plain,
    ( k10_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_49,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk4_0,k9_relat_1(esk4_0,k10_relat_1(esk4_0,X1))),k10_relat_1(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(X1,k10_relat_1(esk4_0,k9_relat_1(esk4_0,X1)))
    | ~ r1_tarski(X1,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_23])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk4_0,X1),k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_53,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_54,plain,
    ( k9_relat_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_56,plain,
    ( k10_relat_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_47]),c_0_47])).

cnf(c_0_57,negated_conjecture,
    ( k10_relat_1(esk4_0,k9_relat_1(esk4_0,k10_relat_1(esk4_0,X1))) = k10_relat_1(esk4_0,X1)
    | ~ r1_tarski(k10_relat_1(esk4_0,X1),k10_relat_1(esk4_0,k9_relat_1(esk4_0,k10_relat_1(esk4_0,X1)))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk4_0,X1),k10_relat_1(esk4_0,k9_relat_1(esk4_0,k10_relat_1(esk4_0,X1)))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

fof(c_0_59,plain,(
    ! [X13,X14] :
      ( ( k4_xboole_0(X13,X14) != k1_xboole_0
        | r1_tarski(X13,X14) )
      & ( ~ r1_tarski(X13,X14)
        | k4_xboole_0(X13,X14) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k10_relat_1(esk4_0,X1),X2),k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( k9_relat_1(esk4_0,k4_xboole_0(X1,X2)) = k4_xboole_0(k9_relat_1(esk4_0,X1),k9_relat_1(esk4_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_22]),c_0_23])])).

cnf(c_0_63,negated_conjecture,
    ( k10_relat_1(esk4_0,k4_xboole_0(X1,X2)) = k4_xboole_0(k10_relat_1(esk4_0,X1),k10_relat_1(esk4_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_22]),c_0_23])])).

cnf(c_0_64,negated_conjecture,
    ( k10_relat_1(esk4_0,k9_relat_1(esk4_0,k10_relat_1(esk4_0,X1))) = k10_relat_1(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_58])])).

cnf(c_0_65,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k10_relat_1(esk4_0,X1),X2),k4_xboole_0(k10_relat_1(esk4_0,X1),k10_relat_1(esk4_0,k9_relat_1(esk4_0,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_61]),c_0_62]),c_0_63]),c_0_64])).

cnf(c_0_68,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

fof(c_0_69,plain,(
    ! [X23] : k4_xboole_0(X23,k1_xboole_0) = X23 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k10_relat_1(esk4_0,k9_relat_1(esk4_0,X1)),X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_71,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_72,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_73,negated_conjecture,
    ( k4_xboole_0(k10_relat_1(esk4_0,k9_relat_1(esk4_0,X1)),X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_70]),c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(esk4_0,k9_relat_1(esk4_0,esk3_0)),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk4_0,k9_relat_1(esk4_0,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_76,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_75])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:24:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 2.52/2.68  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S002A
% 2.52/2.68  # and selection function SelectNegativeLiterals.
% 2.52/2.68  #
% 2.52/2.68  # Preprocessing time       : 0.027 s
% 2.52/2.68  # Presaturation interreduction done
% 2.52/2.68  
% 2.52/2.68  # Proof found!
% 2.52/2.68  # SZS status Theorem
% 2.52/2.68  # SZS output start CNFRefutation
% 2.52/2.68  fof(d13_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,k1_relat_1(X1))&r2_hidden(k1_funct_1(X1,X4),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_funct_1)).
% 2.52/2.68  fof(t152_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v2_funct_1(X2)=>r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_funct_1)).
% 2.52/2.68  fof(t178_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_relat_1)).
% 2.52/2.68  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 2.52/2.68  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.52/2.68  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.52/2.68  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.52/2.68  fof(t146_funct_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 2.52/2.68  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.52/2.68  fof(t123_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(v2_funct_1(X3)=>k9_relat_1(X3,k6_subset_1(X1,X2))=k6_subset_1(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_funct_1)).
% 2.52/2.68  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.52/2.68  fof(t138_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>k10_relat_1(X3,k6_subset_1(X1,X2))=k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_funct_1)).
% 2.52/2.68  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.52/2.68  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.52/2.68  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.52/2.68  fof(c_0_15, plain, ![X29, X30, X31, X32, X33, X34, X35]:((((r2_hidden(X32,k1_relat_1(X29))|~r2_hidden(X32,X31)|X31!=k10_relat_1(X29,X30)|(~v1_relat_1(X29)|~v1_funct_1(X29)))&(r2_hidden(k1_funct_1(X29,X32),X30)|~r2_hidden(X32,X31)|X31!=k10_relat_1(X29,X30)|(~v1_relat_1(X29)|~v1_funct_1(X29))))&(~r2_hidden(X33,k1_relat_1(X29))|~r2_hidden(k1_funct_1(X29,X33),X30)|r2_hidden(X33,X31)|X31!=k10_relat_1(X29,X30)|(~v1_relat_1(X29)|~v1_funct_1(X29))))&((~r2_hidden(esk2_3(X29,X34,X35),X35)|(~r2_hidden(esk2_3(X29,X34,X35),k1_relat_1(X29))|~r2_hidden(k1_funct_1(X29,esk2_3(X29,X34,X35)),X34))|X35=k10_relat_1(X29,X34)|(~v1_relat_1(X29)|~v1_funct_1(X29)))&((r2_hidden(esk2_3(X29,X34,X35),k1_relat_1(X29))|r2_hidden(esk2_3(X29,X34,X35),X35)|X35=k10_relat_1(X29,X34)|(~v1_relat_1(X29)|~v1_funct_1(X29)))&(r2_hidden(k1_funct_1(X29,esk2_3(X29,X34,X35)),X34)|r2_hidden(esk2_3(X29,X34,X35),X35)|X35=k10_relat_1(X29,X34)|(~v1_relat_1(X29)|~v1_funct_1(X29)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_funct_1])])])])])])).
% 2.52/2.68  fof(c_0_16, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v2_funct_1(X2)=>r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1)))), inference(assume_negation,[status(cth)],[t152_funct_1])).
% 2.52/2.68  cnf(c_0_17, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(X1,X3)|X3!=k10_relat_1(X2,X4)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.52/2.68  fof(c_0_18, negated_conjecture, ((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&(v2_funct_1(esk4_0)&~r1_tarski(k10_relat_1(esk4_0,k9_relat_1(esk4_0,esk3_0)),esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 2.52/2.68  fof(c_0_19, plain, ![X26, X27, X28]:(~v1_relat_1(X28)|(~r1_tarski(X26,X27)|r1_tarski(k10_relat_1(X28,X26),k10_relat_1(X28,X27)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t178_relat_1])])).
% 2.52/2.68  fof(c_0_20, plain, ![X43, X44]:(~v1_relat_1(X44)|~v1_funct_1(X44)|r1_tarski(k9_relat_1(X44,k10_relat_1(X44,X43)),X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 2.52/2.68  cnf(c_0_21, plain, (r2_hidden(X1,k1_relat_1(X2))|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k10_relat_1(X2,X3))), inference(er,[status(thm)],[c_0_17])).
% 2.52/2.68  cnf(c_0_22, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.52/2.68  cnf(c_0_23, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.52/2.68  fof(c_0_24, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 2.52/2.68  fof(c_0_25, plain, ![X18, X19]:(~r1_tarski(X18,X19)|k2_xboole_0(X18,X19)=X19), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 2.52/2.68  fof(c_0_26, plain, ![X21, X22]:r1_tarski(k4_xboole_0(X21,X22),X21), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 2.52/2.68  cnf(c_0_27, plain, (r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 2.52/2.68  cnf(c_0_28, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.52/2.68  fof(c_0_29, plain, ![X45, X46]:(~v1_relat_1(X46)|(~r1_tarski(X45,k1_relat_1(X46))|r1_tarski(X45,k10_relat_1(X46,k9_relat_1(X46,X45))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).
% 2.52/2.68  cnf(c_0_30, negated_conjecture, (r2_hidden(X1,k1_relat_1(esk4_0))|~r2_hidden(X1,k10_relat_1(esk4_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])])).
% 2.52/2.68  cnf(c_0_31, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 2.52/2.68  fof(c_0_32, plain, ![X15, X16, X17]:(~r1_tarski(k2_xboole_0(X15,X16),X17)|r1_tarski(X15,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 2.52/2.68  cnf(c_0_33, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 2.52/2.68  cnf(c_0_34, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 2.52/2.68  fof(c_0_35, plain, ![X37, X38, X39]:(~v1_relat_1(X39)|~v1_funct_1(X39)|(~v2_funct_1(X39)|k9_relat_1(X39,k6_subset_1(X37,X38))=k6_subset_1(k9_relat_1(X39,X37),k9_relat_1(X39,X38)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_funct_1])])).
% 2.52/2.68  fof(c_0_36, plain, ![X24, X25]:k6_subset_1(X24,X25)=k4_xboole_0(X24,X25), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 2.52/2.68  fof(c_0_37, plain, ![X40, X41, X42]:(~v1_relat_1(X42)|~v1_funct_1(X42)|k10_relat_1(X42,k6_subset_1(X40,X41))=k6_subset_1(k10_relat_1(X42,X40),k10_relat_1(X42,X41))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t138_funct_1])])).
% 2.52/2.68  fof(c_0_38, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 2.52/2.68  cnf(c_0_39, negated_conjecture, (r1_tarski(k10_relat_1(esk4_0,X1),k10_relat_1(esk4_0,X2))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_27, c_0_23])).
% 2.52/2.68  cnf(c_0_40, negated_conjecture, (r1_tarski(k9_relat_1(esk4_0,k10_relat_1(esk4_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_22]), c_0_23])])).
% 2.52/2.68  cnf(c_0_41, plain, (r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 2.52/2.68  cnf(c_0_42, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 2.52/2.68  cnf(c_0_43, negated_conjecture, (r2_hidden(esk1_2(k10_relat_1(esk4_0,X1),X2),k1_relat_1(esk4_0))|r1_tarski(k10_relat_1(esk4_0,X1),X2)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 2.52/2.68  cnf(c_0_44, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 2.52/2.68  cnf(c_0_45, plain, (k2_xboole_0(k4_xboole_0(X1,X2),X1)=X1), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 2.52/2.68  cnf(c_0_46, plain, (k9_relat_1(X1,k6_subset_1(X2,X3))=k6_subset_1(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 2.52/2.68  cnf(c_0_47, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 2.52/2.68  cnf(c_0_48, plain, (k10_relat_1(X1,k6_subset_1(X2,X3))=k6_subset_1(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 2.52/2.68  cnf(c_0_49, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 2.52/2.68  cnf(c_0_50, negated_conjecture, (r1_tarski(k10_relat_1(esk4_0,k9_relat_1(esk4_0,k10_relat_1(esk4_0,X1))),k10_relat_1(esk4_0,X1))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 2.52/2.68  cnf(c_0_51, negated_conjecture, (r1_tarski(X1,k10_relat_1(esk4_0,k9_relat_1(esk4_0,X1)))|~r1_tarski(X1,k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_41, c_0_23])).
% 2.52/2.68  cnf(c_0_52, negated_conjecture, (r1_tarski(k10_relat_1(esk4_0,X1),k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 2.52/2.68  cnf(c_0_53, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 2.52/2.68  cnf(c_0_54, plain, (k9_relat_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47]), c_0_47])).
% 2.52/2.68  cnf(c_0_55, negated_conjecture, (v2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.52/2.68  cnf(c_0_56, plain, (k10_relat_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_47]), c_0_47])).
% 2.52/2.68  cnf(c_0_57, negated_conjecture, (k10_relat_1(esk4_0,k9_relat_1(esk4_0,k10_relat_1(esk4_0,X1)))=k10_relat_1(esk4_0,X1)|~r1_tarski(k10_relat_1(esk4_0,X1),k10_relat_1(esk4_0,k9_relat_1(esk4_0,k10_relat_1(esk4_0,X1))))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 2.52/2.68  cnf(c_0_58, negated_conjecture, (r1_tarski(k10_relat_1(esk4_0,X1),k10_relat_1(esk4_0,k9_relat_1(esk4_0,k10_relat_1(esk4_0,X1))))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 2.52/2.68  fof(c_0_59, plain, ![X13, X14]:((k4_xboole_0(X13,X14)!=k1_xboole_0|r1_tarski(X13,X14))&(~r1_tarski(X13,X14)|k4_xboole_0(X13,X14)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 2.52/2.68  cnf(c_0_60, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_38])).
% 2.52/2.68  cnf(c_0_61, negated_conjecture, (r1_tarski(k4_xboole_0(k10_relat_1(esk4_0,X1),X2),k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_53, c_0_52])).
% 2.52/2.68  cnf(c_0_62, negated_conjecture, (k9_relat_1(esk4_0,k4_xboole_0(X1,X2))=k4_xboole_0(k9_relat_1(esk4_0,X1),k9_relat_1(esk4_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_22]), c_0_23])])).
% 2.52/2.68  cnf(c_0_63, negated_conjecture, (k10_relat_1(esk4_0,k4_xboole_0(X1,X2))=k4_xboole_0(k10_relat_1(esk4_0,X1),k10_relat_1(esk4_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_22]), c_0_23])])).
% 2.52/2.68  cnf(c_0_64, negated_conjecture, (k10_relat_1(esk4_0,k9_relat_1(esk4_0,k10_relat_1(esk4_0,X1)))=k10_relat_1(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_58])])).
% 2.52/2.68  cnf(c_0_65, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 2.52/2.68  cnf(c_0_66, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_60])).
% 2.52/2.68  cnf(c_0_67, negated_conjecture, (r1_tarski(k4_xboole_0(k10_relat_1(esk4_0,X1),X2),k4_xboole_0(k10_relat_1(esk4_0,X1),k10_relat_1(esk4_0,k9_relat_1(esk4_0,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_61]), c_0_62]), c_0_63]), c_0_64])).
% 2.52/2.68  cnf(c_0_68, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 2.52/2.68  fof(c_0_69, plain, ![X23]:k4_xboole_0(X23,k1_xboole_0)=X23, inference(variable_rename,[status(thm)],[t3_boole])).
% 2.52/2.68  cnf(c_0_70, negated_conjecture, (r1_tarski(k4_xboole_0(k10_relat_1(esk4_0,k9_relat_1(esk4_0,X1)),X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 2.52/2.68  cnf(c_0_71, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_69])).
% 2.52/2.68  cnf(c_0_72, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_59])).
% 2.52/2.68  cnf(c_0_73, negated_conjecture, (k4_xboole_0(k10_relat_1(esk4_0,k9_relat_1(esk4_0,X1)),X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_70]), c_0_71])).
% 2.52/2.68  cnf(c_0_74, negated_conjecture, (~r1_tarski(k10_relat_1(esk4_0,k9_relat_1(esk4_0,esk3_0)),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.52/2.68  cnf(c_0_75, negated_conjecture, (r1_tarski(k10_relat_1(esk4_0,k9_relat_1(esk4_0,X1)),X1)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 2.52/2.68  cnf(c_0_76, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_75])]), ['proof']).
% 2.52/2.68  # SZS output end CNFRefutation
% 2.52/2.68  # Proof object total steps             : 77
% 2.52/2.68  # Proof object clause steps            : 46
% 2.52/2.68  # Proof object formula steps           : 31
% 2.52/2.68  # Proof object conjectures             : 25
% 2.52/2.68  # Proof object clause conjectures      : 22
% 2.52/2.68  # Proof object formula conjectures     : 3
% 2.52/2.68  # Proof object initial clauses used    : 21
% 2.52/2.68  # Proof object initial formulas used   : 15
% 2.52/2.68  # Proof object generating inferences   : 20
% 2.52/2.68  # Proof object simplifying inferences  : 22
% 2.52/2.68  # Training examples: 0 positive, 0 negative
% 2.52/2.68  # Parsed axioms                        : 16
% 2.52/2.68  # Removed by relevancy pruning/SinE    : 0
% 2.52/2.68  # Initial clauses                      : 29
% 2.52/2.68  # Removed in clause preprocessing      : 1
% 2.52/2.68  # Initial clauses in saturation        : 28
% 2.52/2.68  # Processed clauses                    : 6785
% 2.52/2.68  # ...of these trivial                  : 1006
% 2.52/2.68  # ...subsumed                          : 3726
% 2.52/2.68  # ...remaining for further processing  : 2053
% 2.52/2.68  # Other redundant clauses eliminated   : 190
% 2.52/2.68  # Clauses deleted for lack of memory   : 0
% 2.52/2.68  # Backward-subsumed                    : 35
% 2.52/2.68  # Backward-rewritten                   : 194
% 2.52/2.68  # Generated clauses                    : 317855
% 2.52/2.68  # ...of the previous two non-trivial   : 269528
% 2.52/2.68  # Contextual simplify-reflections      : 37
% 2.52/2.68  # Paramodulations                      : 317594
% 2.52/2.68  # Factorizations                       : 52
% 2.52/2.68  # Equation resolutions                 : 209
% 2.52/2.68  # Propositional unsat checks           : 0
% 2.52/2.68  #    Propositional check models        : 0
% 2.52/2.68  #    Propositional check unsatisfiable : 0
% 2.52/2.68  #    Propositional clauses             : 0
% 2.52/2.68  #    Propositional clauses after purity: 0
% 2.52/2.68  #    Propositional unsat core size     : 0
% 2.52/2.68  #    Propositional preprocessing time  : 0.000
% 2.52/2.68  #    Propositional encoding time       : 0.000
% 2.52/2.68  #    Propositional solver time         : 0.000
% 2.52/2.68  #    Success case prop preproc time    : 0.000
% 2.52/2.68  #    Success case prop encoding time   : 0.000
% 2.52/2.68  #    Success case prop solver time     : 0.000
% 2.52/2.68  # Current number of processed clauses  : 1795
% 2.52/2.68  #    Positive orientable unit clauses  : 502
% 2.52/2.68  #    Positive unorientable unit clauses: 0
% 2.52/2.68  #    Negative unit clauses             : 0
% 2.52/2.68  #    Non-unit-clauses                  : 1293
% 2.52/2.68  # Current number of unprocessed clauses: 261227
% 2.52/2.68  # ...number of literals in the above   : 1087140
% 2.52/2.68  # Current number of archived formulas  : 0
% 2.52/2.68  # Current number of archived clauses   : 257
% 2.52/2.68  # Clause-clause subsumption calls (NU) : 244115
% 2.52/2.68  # Rec. Clause-clause subsumption calls : 165987
% 2.52/2.68  # Non-unit clause-clause subsumptions  : 3797
% 2.52/2.68  # Unit Clause-clause subsumption calls : 19452
% 2.52/2.68  # Rewrite failures with RHS unbound    : 0
% 2.52/2.68  # BW rewrite match attempts            : 2059
% 2.52/2.68  # BW rewrite match successes           : 40
% 2.52/2.68  # Condensation attempts                : 0
% 2.52/2.68  # Condensation successes               : 0
% 2.52/2.68  # Termbank termtop insertions          : 8345013
% 2.52/2.69  
% 2.52/2.69  # -------------------------------------------------
% 2.52/2.69  # User time                : 2.218 s
% 2.52/2.69  # System time              : 0.124 s
% 2.52/2.69  # Total time               : 2.343 s
% 2.52/2.69  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
