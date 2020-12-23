%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:30 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  119 (1101 expanded)
%              Number of clauses        :   70 ( 451 expanded)
%              Number of leaves         :   24 ( 302 expanded)
%              Depth                    :   24
%              Number of atoms          :  305 (2597 expanded)
%              Number of equality atoms :   90 ( 946 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t151_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k9_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(fc4_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v2_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t164_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ( r1_tarski(X1,k1_relat_1(X2))
          & v2_funct_1(X2) )
       => k10_relat_1(X2,k9_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t175_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t167_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(t43_funct_1,axiom,(
    ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t146_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(t147_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,k2_relat_1(X2))
       => k9_relat_1(X2,k10_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(t182_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(t148_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => k9_relat_1(X2,k10_relat_1(X2,X1)) = k3_xboole_0(X1,k9_relat_1(X2,k1_relat_1(X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

fof(t157_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2))
          & r1_tarski(X1,k1_relat_1(X3))
          & v2_funct_1(X3) )
       => r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

fof(c_0_24,plain,(
    ! [X11,X12,X14,X15,X16] :
      ( ( r2_hidden(esk2_2(X11,X12),X11)
        | r1_xboole_0(X11,X12) )
      & ( r2_hidden(esk2_2(X11,X12),X12)
        | r1_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X16,X14)
        | ~ r2_hidden(X16,X15)
        | ~ r1_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_25,plain,(
    ! [X36,X37] :
      ( ( k9_relat_1(X37,X36) != k1_xboole_0
        | r1_xboole_0(k1_relat_1(X37),X36)
        | ~ v1_relat_1(X37) )
      & ( ~ r1_xboole_0(k1_relat_1(X37),X36)
        | k9_relat_1(X37,X36) = k1_xboole_0
        | ~ v1_relat_1(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t151_relat_1])])])).

cnf(c_0_26,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_27,plain,
    ( r1_xboole_0(k1_relat_1(X1),X2)
    | k9_relat_1(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_28,plain,(
    ! [X45] :
      ( k1_relat_1(k6_relat_1(X45)) = X45
      & k2_relat_1(k6_relat_1(X45)) = X45 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_29,plain,(
    ! [X54] :
      ( v1_relat_1(k6_relat_1(X54))
      & v2_funct_1(k6_relat_1(X54)) ) ),
    inference(variable_rename,[status(thm)],[fc4_funct_1])).

cnf(c_0_30,plain,
    ( k9_relat_1(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_32,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_33,plain,(
    ! [X35] :
      ( ~ v1_relat_1(X35)
      | k9_relat_1(X35,k1_relat_1(X35)) = k2_relat_1(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

fof(c_0_34,plain,(
    ! [X46,X47,X48,X49,X50,X51,X52] :
      ( ( r2_hidden(X49,k1_relat_1(X46))
        | ~ r2_hidden(X49,X48)
        | X48 != k10_relat_1(X46,X47)
        | ~ v1_relat_1(X46)
        | ~ v1_funct_1(X46) )
      & ( r2_hidden(k1_funct_1(X46,X49),X47)
        | ~ r2_hidden(X49,X48)
        | X48 != k10_relat_1(X46,X47)
        | ~ v1_relat_1(X46)
        | ~ v1_funct_1(X46) )
      & ( ~ r2_hidden(X50,k1_relat_1(X46))
        | ~ r2_hidden(k1_funct_1(X46,X50),X47)
        | r2_hidden(X50,X48)
        | X48 != k10_relat_1(X46,X47)
        | ~ v1_relat_1(X46)
        | ~ v1_funct_1(X46) )
      & ( ~ r2_hidden(esk3_3(X46,X51,X52),X52)
        | ~ r2_hidden(esk3_3(X46,X51,X52),k1_relat_1(X46))
        | ~ r2_hidden(k1_funct_1(X46,esk3_3(X46,X51,X52)),X51)
        | X52 = k10_relat_1(X46,X51)
        | ~ v1_relat_1(X46)
        | ~ v1_funct_1(X46) )
      & ( r2_hidden(esk3_3(X46,X51,X52),k1_relat_1(X46))
        | r2_hidden(esk3_3(X46,X51,X52),X52)
        | X52 = k10_relat_1(X46,X51)
        | ~ v1_relat_1(X46)
        | ~ v1_funct_1(X46) )
      & ( r2_hidden(k1_funct_1(X46,esk3_3(X46,X51,X52)),X51)
        | r2_hidden(esk3_3(X46,X51,X52),X52)
        | X52 = k10_relat_1(X46,X51)
        | ~ v1_relat_1(X46)
        | ~ v1_funct_1(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_funct_1])])])])])])).

cnf(c_0_35,plain,
    ( k9_relat_1(k6_relat_1(X1),X2) != k1_xboole_0
    | ~ r2_hidden(X3,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])])).

cnf(c_0_36,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_37,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X4 != k10_relat_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_39,plain,(
    ! [X17,X18] :
      ( ( r1_tarski(X17,X18)
        | X17 != X18 )
      & ( r1_tarski(X18,X17)
        | X17 != X18 )
      & ( ~ r1_tarski(X17,X18)
        | ~ r1_tarski(X18,X17)
        | X17 = X18 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_40,plain,(
    ! [X21] : r1_tarski(k1_xboole_0,X21) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_31]),c_0_32])])])).

cnf(c_0_42,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k10_relat_1(X1,X3)) ),
    inference(er,[status(thm)],[c_0_38])).

fof(c_0_43,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_44,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,plain,
    ( ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k10_relat_1(X1,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_48,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( ( r1_tarski(X1,k1_relat_1(X2))
            & v2_funct_1(X2) )
         => k10_relat_1(X2,k9_relat_1(X2,X1)) = X1 ) ) ),
    inference(assume_negation,[status(cth)],[t164_funct_1])).

fof(c_0_49,plain,(
    ! [X19,X20] :
      ( ~ r1_tarski(X19,X20)
      | k2_xboole_0(X19,X20) = X20 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_50,plain,(
    ! [X40,X41,X42] :
      ( ~ v1_relat_1(X42)
      | k10_relat_1(X42,k2_xboole_0(X40,X41)) = k2_xboole_0(k10_relat_1(X42,X40),k10_relat_1(X42,X41)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t175_relat_1])])).

cnf(c_0_51,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_52,plain,
    ( r1_tarski(k10_relat_1(X1,k1_xboole_0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

fof(c_0_53,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & v1_funct_1(esk5_0)
    & r1_tarski(esk4_0,k1_relat_1(esk5_0))
    & v2_funct_1(esk5_0)
    & k10_relat_1(esk5_0,k9_relat_1(esk5_0,esk4_0)) != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_48])])])).

cnf(c_0_54,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_55,plain,
    ( k10_relat_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_56,plain,
    ( k10_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_59,plain,(
    ! [X33,X34] : k1_setfam_1(k2_tarski(X33,X34)) = k3_xboole_0(X33,X34) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_60,plain,(
    ! [X24,X25] : k1_enumset1(X24,X24,X25) = k2_tarski(X24,X25) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_61,plain,(
    ! [X38,X39] :
      ( ~ v1_relat_1(X39)
      | r1_tarski(k10_relat_1(X39,X38),k1_relat_1(X39)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).

cnf(c_0_62,plain,
    ( k10_relat_1(X1,k2_xboole_0(X2,X3)) = k10_relat_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( k10_relat_1(esk5_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])])).

fof(c_0_64,plain,(
    ! [X64,X65] : k5_relat_1(k6_relat_1(X65),k6_relat_1(X64)) = k6_relat_1(k3_xboole_0(X64,X65)) ),
    inference(variable_rename,[status(thm)],[t43_funct_1])).

cnf(c_0_65,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_66,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

fof(c_0_67,plain,(
    ! [X26,X27,X28] : k2_enumset1(X26,X26,X27,X28) = k1_enumset1(X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_68,plain,(
    ! [X29,X30,X31,X32] : k3_enumset1(X29,X29,X30,X31,X32) = k2_enumset1(X29,X30,X31,X32) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_69,plain,(
    ! [X22,X23] : k2_tarski(X22,X23) = k2_tarski(X23,X22) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_70,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_71,negated_conjecture,
    ( k10_relat_1(esk5_0,k2_xboole_0(k1_xboole_0,X1)) = k10_relat_1(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_58]),c_0_45])])).

fof(c_0_72,plain,(
    ! [X55,X56] :
      ( ~ v1_relat_1(X56)
      | ~ r1_tarski(X55,k1_relat_1(X56))
      | r1_tarski(X55,k10_relat_1(X56,k9_relat_1(X56,X55))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_74,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k3_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_75,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_76,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_77,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_78,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

fof(c_0_79,plain,(
    ! [X57,X58] :
      ( ~ v1_relat_1(X58)
      | ~ v1_funct_1(X58)
      | ~ r1_tarski(X57,k2_relat_1(X58))
      | k9_relat_1(X58,k10_relat_1(X58,X57)) = X57 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_funct_1])])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk5_0,X1),k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_58])])).

cnf(c_0_81,plain,
    ( r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_82,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_73])).

fof(c_0_83,plain,(
    ! [X43,X44] :
      ( ~ v1_relat_1(X43)
      | ~ v1_relat_1(X44)
      | k1_relat_1(k5_relat_1(X43,X44)) = k10_relat_1(X43,k1_relat_1(X44)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).

cnf(c_0_84,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_75]),c_0_76]),c_0_77])).

cnf(c_0_85,plain,
    ( k3_enumset1(X1,X1,X1,X1,X2) = k3_enumset1(X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_66]),c_0_66]),c_0_76]),c_0_76]),c_0_77]),c_0_77])).

cnf(c_0_86,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_87,negated_conjecture,
    ( k10_relat_1(esk5_0,X1) = k1_relat_1(esk5_0)
    | ~ r1_tarski(k1_relat_1(esk5_0),k10_relat_1(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_80])).

cnf(c_0_88,plain,
    ( r1_tarski(k1_relat_1(X1),k10_relat_1(X1,k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_36]),c_0_82])])).

cnf(c_0_89,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_90,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_84])).

cnf(c_0_91,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,k2_relat_1(X1))) = k2_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_82])).

cnf(c_0_92,negated_conjecture,
    ( k10_relat_1(esk5_0,k2_relat_1(esk5_0)) = k1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_58])])).

cnf(c_0_93,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k10_relat_1(k6_relat_1(X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_31]),c_0_32]),c_0_32])])).

fof(c_0_94,plain,(
    ! [X59,X60] :
      ( ~ v1_relat_1(X60)
      | ~ v1_funct_1(X60)
      | k9_relat_1(X60,k10_relat_1(X60,X59)) = k3_xboole_0(X59,k9_relat_1(X60,k1_relat_1(X60))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_funct_1])])).

cnf(c_0_95,negated_conjecture,
    ( k2_relat_1(esk5_0) = k9_relat_1(esk5_0,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_57]),c_0_58])])).

cnf(c_0_96,plain,
    ( k10_relat_1(k6_relat_1(X1),X2) = k10_relat_1(k6_relat_1(X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_93]),c_0_31]),c_0_32]),c_0_32])])).

cnf(c_0_97,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = k3_xboole_0(X2,k9_relat_1(X1,k1_relat_1(X1)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_98,negated_conjecture,
    ( k9_relat_1(esk5_0,k10_relat_1(esk5_0,X1)) = X1
    | ~ r1_tarski(X1,k9_relat_1(esk5_0,k1_relat_1(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_95]),c_0_57]),c_0_58])])).

cnf(c_0_99,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(X1),X2),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_96]),c_0_31]),c_0_32])])).

cnf(c_0_100,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = k1_setfam_1(k3_enumset1(X2,X2,X2,X2,k9_relat_1(X1,k1_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97,c_0_75]),c_0_76]),c_0_77])).

cnf(c_0_101,plain,
    ( k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)) = k10_relat_1(k6_relat_1(X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_84]),c_0_93])).

fof(c_0_102,plain,(
    ! [X61,X62,X63] :
      ( ~ v1_relat_1(X63)
      | ~ v1_funct_1(X63)
      | ~ r1_tarski(k9_relat_1(X63,X61),k9_relat_1(X63,X62))
      | ~ r1_tarski(X61,k1_relat_1(X63))
      | ~ v2_funct_1(X63)
      | r1_tarski(X61,X62) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t157_funct_1])])).

cnf(c_0_103,negated_conjecture,
    ( k9_relat_1(esk5_0,k10_relat_1(esk5_0,k10_relat_1(k6_relat_1(X1),k9_relat_1(esk5_0,k1_relat_1(esk5_0))))) = k10_relat_1(k6_relat_1(X1),k9_relat_1(esk5_0,k1_relat_1(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_104,plain,
    ( k10_relat_1(k6_relat_1(X1),k9_relat_1(X2,k1_relat_1(X2))) = k9_relat_1(X2,k10_relat_1(X2,X1))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(rw,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_105,plain,
    ( r1_tarski(X2,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_106,negated_conjecture,
    ( k9_relat_1(esk5_0,k10_relat_1(esk5_0,k9_relat_1(esk5_0,k10_relat_1(esk5_0,X1)))) = k9_relat_1(esk5_0,k10_relat_1(esk5_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_57]),c_0_58])])).

cnf(c_0_107,negated_conjecture,
    ( v2_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_108,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk5_0,k9_relat_1(esk5_0,k10_relat_1(esk5_0,X1))),X2)
    | ~ r1_tarski(k9_relat_1(esk5_0,k10_relat_1(esk5_0,X1)),k9_relat_1(esk5_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_107]),c_0_57]),c_0_58]),c_0_80])])).

cnf(c_0_109,plain,
    ( k10_relat_1(X1,k9_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X2)),X2)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_81])).

cnf(c_0_110,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk5_0,k9_relat_1(esk5_0,k10_relat_1(esk5_0,X1))),k10_relat_1(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_108,c_0_82])).

cnf(c_0_111,negated_conjecture,
    ( k10_relat_1(esk5_0,k9_relat_1(esk5_0,k10_relat_1(esk5_0,X1))) = k10_relat_1(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_58]),c_0_80])])).

cnf(c_0_112,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk5_0,X1),X2)
    | ~ r1_tarski(k9_relat_1(esk5_0,k10_relat_1(esk5_0,X1)),k9_relat_1(esk5_0,X2)) ),
    inference(rw,[status(thm)],[c_0_108,c_0_111])).

cnf(c_0_113,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_104]),c_0_31]),c_0_32])])).

cnf(c_0_114,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk5_0,k9_relat_1(esk5_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_57]),c_0_58])])).

cnf(c_0_115,negated_conjecture,
    ( k10_relat_1(esk5_0,k9_relat_1(esk5_0,esk4_0)) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_116,negated_conjecture,
    ( k10_relat_1(esk5_0,k9_relat_1(esk5_0,X1)) = X1
    | ~ r1_tarski(X1,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_114]),c_0_58])])).

cnf(c_0_117,negated_conjecture,
    ( r1_tarski(esk4_0,k1_relat_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_118,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_117])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n019.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 10:16:22 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  # Version: 2.5pre002
% 0.11/0.32  # No SInE strategy applied
% 0.11/0.32  # Trying AutoSched0 for 299 seconds
% 0.19/0.45  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.19/0.45  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.45  #
% 0.19/0.45  # Preprocessing time       : 0.028 s
% 0.19/0.45  
% 0.19/0.45  # Proof found!
% 0.19/0.45  # SZS status Theorem
% 0.19/0.45  # SZS output start CNFRefutation
% 0.19/0.45  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.19/0.45  fof(t151_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(k9_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 0.19/0.45  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.19/0.45  fof(fc4_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v2_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 0.19/0.45  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 0.19/0.45  fof(d13_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,k1_relat_1(X1))&r2_hidden(k1_funct_1(X1,X4),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_funct_1)).
% 0.19/0.45  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.45  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.45  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.45  fof(t164_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((r1_tarski(X1,k1_relat_1(X2))&v2_funct_1(X2))=>k10_relat_1(X2,k9_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t164_funct_1)).
% 0.19/0.45  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.19/0.45  fof(t175_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_relat_1)).
% 0.19/0.45  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.19/0.45  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.45  fof(t167_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 0.19/0.45  fof(t43_funct_1, axiom, ![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 0.19/0.45  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.45  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.45  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.19/0.45  fof(t146_funct_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 0.19/0.45  fof(t147_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(X1,k2_relat_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 0.19/0.45  fof(t182_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 0.19/0.45  fof(t148_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=k3_xboole_0(X1,k9_relat_1(X2,k1_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_funct_1)).
% 0.19/0.45  fof(t157_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(((r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2))&r1_tarski(X1,k1_relat_1(X3)))&v2_funct_1(X3))=>r1_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_funct_1)).
% 0.19/0.45  fof(c_0_24, plain, ![X11, X12, X14, X15, X16]:(((r2_hidden(esk2_2(X11,X12),X11)|r1_xboole_0(X11,X12))&(r2_hidden(esk2_2(X11,X12),X12)|r1_xboole_0(X11,X12)))&(~r2_hidden(X16,X14)|~r2_hidden(X16,X15)|~r1_xboole_0(X14,X15))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.19/0.45  fof(c_0_25, plain, ![X36, X37]:((k9_relat_1(X37,X36)!=k1_xboole_0|r1_xboole_0(k1_relat_1(X37),X36)|~v1_relat_1(X37))&(~r1_xboole_0(k1_relat_1(X37),X36)|k9_relat_1(X37,X36)=k1_xboole_0|~v1_relat_1(X37))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t151_relat_1])])])).
% 0.19/0.45  cnf(c_0_26, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.45  cnf(c_0_27, plain, (r1_xboole_0(k1_relat_1(X1),X2)|k9_relat_1(X1,X2)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.45  fof(c_0_28, plain, ![X45]:(k1_relat_1(k6_relat_1(X45))=X45&k2_relat_1(k6_relat_1(X45))=X45), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.19/0.45  fof(c_0_29, plain, ![X54]:(v1_relat_1(k6_relat_1(X54))&v2_funct_1(k6_relat_1(X54))), inference(variable_rename,[status(thm)],[fc4_funct_1])).
% 0.19/0.45  cnf(c_0_30, plain, (k9_relat_1(X1,X2)!=k1_xboole_0|~v1_relat_1(X1)|~r2_hidden(X3,k1_relat_1(X1))|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.45  cnf(c_0_31, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.45  cnf(c_0_32, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.45  fof(c_0_33, plain, ![X35]:(~v1_relat_1(X35)|k9_relat_1(X35,k1_relat_1(X35))=k2_relat_1(X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.19/0.45  fof(c_0_34, plain, ![X46, X47, X48, X49, X50, X51, X52]:((((r2_hidden(X49,k1_relat_1(X46))|~r2_hidden(X49,X48)|X48!=k10_relat_1(X46,X47)|(~v1_relat_1(X46)|~v1_funct_1(X46)))&(r2_hidden(k1_funct_1(X46,X49),X47)|~r2_hidden(X49,X48)|X48!=k10_relat_1(X46,X47)|(~v1_relat_1(X46)|~v1_funct_1(X46))))&(~r2_hidden(X50,k1_relat_1(X46))|~r2_hidden(k1_funct_1(X46,X50),X47)|r2_hidden(X50,X48)|X48!=k10_relat_1(X46,X47)|(~v1_relat_1(X46)|~v1_funct_1(X46))))&((~r2_hidden(esk3_3(X46,X51,X52),X52)|(~r2_hidden(esk3_3(X46,X51,X52),k1_relat_1(X46))|~r2_hidden(k1_funct_1(X46,esk3_3(X46,X51,X52)),X51))|X52=k10_relat_1(X46,X51)|(~v1_relat_1(X46)|~v1_funct_1(X46)))&((r2_hidden(esk3_3(X46,X51,X52),k1_relat_1(X46))|r2_hidden(esk3_3(X46,X51,X52),X52)|X52=k10_relat_1(X46,X51)|(~v1_relat_1(X46)|~v1_funct_1(X46)))&(r2_hidden(k1_funct_1(X46,esk3_3(X46,X51,X52)),X51)|r2_hidden(esk3_3(X46,X51,X52),X52)|X52=k10_relat_1(X46,X51)|(~v1_relat_1(X46)|~v1_funct_1(X46)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_funct_1])])])])])])).
% 0.19/0.45  cnf(c_0_35, plain, (k9_relat_1(k6_relat_1(X1),X2)!=k1_xboole_0|~r2_hidden(X3,X1)|~r2_hidden(X3,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])])).
% 0.19/0.45  cnf(c_0_36, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.45  cnf(c_0_37, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.45  cnf(c_0_38, plain, (r2_hidden(k1_funct_1(X1,X2),X3)|~r2_hidden(X2,X4)|X4!=k10_relat_1(X1,X3)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.45  fof(c_0_39, plain, ![X17, X18]:(((r1_tarski(X17,X18)|X17!=X18)&(r1_tarski(X18,X17)|X17!=X18))&(~r1_tarski(X17,X18)|~r1_tarski(X18,X17)|X17=X18)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.45  fof(c_0_40, plain, ![X21]:r1_tarski(k1_xboole_0,X21), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.45  cnf(c_0_41, plain, (~r2_hidden(X1,k1_xboole_0)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_31]), c_0_32])])])).
% 0.19/0.45  cnf(c_0_42, plain, (r2_hidden(k1_funct_1(X1,X2),X3)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k10_relat_1(X1,X3))), inference(er,[status(thm)],[c_0_38])).
% 0.19/0.45  fof(c_0_43, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.45  cnf(c_0_44, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.45  cnf(c_0_45, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.45  cnf(c_0_46, plain, (~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k10_relat_1(X1,k1_xboole_0))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.45  cnf(c_0_47, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.45  fof(c_0_48, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((r1_tarski(X1,k1_relat_1(X2))&v2_funct_1(X2))=>k10_relat_1(X2,k9_relat_1(X2,X1))=X1))), inference(assume_negation,[status(cth)],[t164_funct_1])).
% 0.19/0.45  fof(c_0_49, plain, ![X19, X20]:(~r1_tarski(X19,X20)|k2_xboole_0(X19,X20)=X20), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.19/0.45  fof(c_0_50, plain, ![X40, X41, X42]:(~v1_relat_1(X42)|k10_relat_1(X42,k2_xboole_0(X40,X41))=k2_xboole_0(k10_relat_1(X42,X40),k10_relat_1(X42,X41))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t175_relat_1])])).
% 0.19/0.45  cnf(c_0_51, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.45  cnf(c_0_52, plain, (r1_tarski(k10_relat_1(X1,k1_xboole_0),X2)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.45  fof(c_0_53, negated_conjecture, ((v1_relat_1(esk5_0)&v1_funct_1(esk5_0))&((r1_tarski(esk4_0,k1_relat_1(esk5_0))&v2_funct_1(esk5_0))&k10_relat_1(esk5_0,k9_relat_1(esk5_0,esk4_0))!=esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_48])])])).
% 0.19/0.45  cnf(c_0_54, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.45  cnf(c_0_55, plain, (k10_relat_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.45  cnf(c_0_56, plain, (k10_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.45  cnf(c_0_57, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.45  cnf(c_0_58, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.45  fof(c_0_59, plain, ![X33, X34]:k1_setfam_1(k2_tarski(X33,X34))=k3_xboole_0(X33,X34), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.19/0.45  fof(c_0_60, plain, ![X24, X25]:k1_enumset1(X24,X24,X25)=k2_tarski(X24,X25), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.45  fof(c_0_61, plain, ![X38, X39]:(~v1_relat_1(X39)|r1_tarski(k10_relat_1(X39,X38),k1_relat_1(X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).
% 0.19/0.45  cnf(c_0_62, plain, (k10_relat_1(X1,k2_xboole_0(X2,X3))=k10_relat_1(X1,X3)|~v1_relat_1(X1)|~r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.19/0.45  cnf(c_0_63, negated_conjecture, (k10_relat_1(esk5_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])])).
% 0.19/0.45  fof(c_0_64, plain, ![X64, X65]:k5_relat_1(k6_relat_1(X65),k6_relat_1(X64))=k6_relat_1(k3_xboole_0(X64,X65)), inference(variable_rename,[status(thm)],[t43_funct_1])).
% 0.19/0.45  cnf(c_0_65, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.19/0.45  cnf(c_0_66, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.45  fof(c_0_67, plain, ![X26, X27, X28]:k2_enumset1(X26,X26,X27,X28)=k1_enumset1(X26,X27,X28), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.45  fof(c_0_68, plain, ![X29, X30, X31, X32]:k3_enumset1(X29,X29,X30,X31,X32)=k2_enumset1(X29,X30,X31,X32), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.45  fof(c_0_69, plain, ![X22, X23]:k2_tarski(X22,X23)=k2_tarski(X23,X22), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.19/0.45  cnf(c_0_70, plain, (r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.45  cnf(c_0_71, negated_conjecture, (k10_relat_1(esk5_0,k2_xboole_0(k1_xboole_0,X1))=k10_relat_1(esk5_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_58]), c_0_45])])).
% 0.19/0.45  fof(c_0_72, plain, ![X55, X56]:(~v1_relat_1(X56)|(~r1_tarski(X55,k1_relat_1(X56))|r1_tarski(X55,k10_relat_1(X56,k9_relat_1(X56,X55))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).
% 0.19/0.45  cnf(c_0_73, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.45  cnf(c_0_74, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k3_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.19/0.45  cnf(c_0_75, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_65, c_0_66])).
% 0.19/0.45  cnf(c_0_76, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.19/0.45  cnf(c_0_77, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.19/0.45  cnf(c_0_78, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.19/0.45  fof(c_0_79, plain, ![X57, X58]:(~v1_relat_1(X58)|~v1_funct_1(X58)|(~r1_tarski(X57,k2_relat_1(X58))|k9_relat_1(X58,k10_relat_1(X58,X57))=X57)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_funct_1])])).
% 0.19/0.45  cnf(c_0_80, negated_conjecture, (r1_tarski(k10_relat_1(esk5_0,X1),k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_58])])).
% 0.19/0.45  cnf(c_0_81, plain, (r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.19/0.45  cnf(c_0_82, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_73])).
% 0.19/0.45  fof(c_0_83, plain, ![X43, X44]:(~v1_relat_1(X43)|(~v1_relat_1(X44)|k1_relat_1(k5_relat_1(X43,X44))=k10_relat_1(X43,k1_relat_1(X44)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).
% 0.19/0.45  cnf(c_0_84, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_75]), c_0_76]), c_0_77])).
% 0.19/0.45  cnf(c_0_85, plain, (k3_enumset1(X1,X1,X1,X1,X2)=k3_enumset1(X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_66]), c_0_66]), c_0_76]), c_0_76]), c_0_77]), c_0_77])).
% 0.19/0.45  cnf(c_0_86, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.19/0.45  cnf(c_0_87, negated_conjecture, (k10_relat_1(esk5_0,X1)=k1_relat_1(esk5_0)|~r1_tarski(k1_relat_1(esk5_0),k10_relat_1(esk5_0,X1))), inference(spm,[status(thm)],[c_0_44, c_0_80])).
% 0.19/0.45  cnf(c_0_88, plain, (r1_tarski(k1_relat_1(X1),k10_relat_1(X1,k2_relat_1(X1)))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_36]), c_0_82])])).
% 0.19/0.45  cnf(c_0_89, plain, (k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.19/0.45  cnf(c_0_90, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_84])).
% 0.19/0.45  cnf(c_0_91, plain, (k9_relat_1(X1,k10_relat_1(X1,k2_relat_1(X1)))=k2_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_86, c_0_82])).
% 0.19/0.45  cnf(c_0_92, negated_conjecture, (k10_relat_1(esk5_0,k2_relat_1(esk5_0))=k1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_58])])).
% 0.19/0.45  cnf(c_0_93, plain, (k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=k10_relat_1(k6_relat_1(X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_31]), c_0_32]), c_0_32])])).
% 0.19/0.45  fof(c_0_94, plain, ![X59, X60]:(~v1_relat_1(X60)|~v1_funct_1(X60)|k9_relat_1(X60,k10_relat_1(X60,X59))=k3_xboole_0(X59,k9_relat_1(X60,k1_relat_1(X60)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_funct_1])])).
% 0.19/0.45  cnf(c_0_95, negated_conjecture, (k2_relat_1(esk5_0)=k9_relat_1(esk5_0,k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_57]), c_0_58])])).
% 0.19/0.45  cnf(c_0_96, plain, (k10_relat_1(k6_relat_1(X1),X2)=k10_relat_1(k6_relat_1(X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_93]), c_0_31]), c_0_32]), c_0_32])])).
% 0.19/0.45  cnf(c_0_97, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=k3_xboole_0(X2,k9_relat_1(X1,k1_relat_1(X1)))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_94])).
% 0.19/0.45  cnf(c_0_98, negated_conjecture, (k9_relat_1(esk5_0,k10_relat_1(esk5_0,X1))=X1|~r1_tarski(X1,k9_relat_1(esk5_0,k1_relat_1(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_95]), c_0_57]), c_0_58])])).
% 0.19/0.45  cnf(c_0_99, plain, (r1_tarski(k10_relat_1(k6_relat_1(X1),X2),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_96]), c_0_31]), c_0_32])])).
% 0.19/0.45  cnf(c_0_100, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=k1_setfam_1(k3_enumset1(X2,X2,X2,X2,k9_relat_1(X1,k1_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97, c_0_75]), c_0_76]), c_0_77])).
% 0.19/0.45  cnf(c_0_101, plain, (k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))=k10_relat_1(k6_relat_1(X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_84]), c_0_93])).
% 0.19/0.45  fof(c_0_102, plain, ![X61, X62, X63]:(~v1_relat_1(X63)|~v1_funct_1(X63)|(~r1_tarski(k9_relat_1(X63,X61),k9_relat_1(X63,X62))|~r1_tarski(X61,k1_relat_1(X63))|~v2_funct_1(X63)|r1_tarski(X61,X62))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t157_funct_1])])).
% 0.19/0.45  cnf(c_0_103, negated_conjecture, (k9_relat_1(esk5_0,k10_relat_1(esk5_0,k10_relat_1(k6_relat_1(X1),k9_relat_1(esk5_0,k1_relat_1(esk5_0)))))=k10_relat_1(k6_relat_1(X1),k9_relat_1(esk5_0,k1_relat_1(esk5_0)))), inference(spm,[status(thm)],[c_0_98, c_0_99])).
% 0.19/0.45  cnf(c_0_104, plain, (k10_relat_1(k6_relat_1(X1),k9_relat_1(X2,k1_relat_1(X2)))=k9_relat_1(X2,k10_relat_1(X2,X1))|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(rw,[status(thm)],[c_0_100, c_0_101])).
% 0.19/0.45  cnf(c_0_105, plain, (r1_tarski(X2,X3)|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~r1_tarski(X2,k1_relat_1(X1))|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_102])).
% 0.19/0.45  cnf(c_0_106, negated_conjecture, (k9_relat_1(esk5_0,k10_relat_1(esk5_0,k9_relat_1(esk5_0,k10_relat_1(esk5_0,X1))))=k9_relat_1(esk5_0,k10_relat_1(esk5_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_57]), c_0_58])])).
% 0.19/0.45  cnf(c_0_107, negated_conjecture, (v2_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.45  cnf(c_0_108, negated_conjecture, (r1_tarski(k10_relat_1(esk5_0,k9_relat_1(esk5_0,k10_relat_1(esk5_0,X1))),X2)|~r1_tarski(k9_relat_1(esk5_0,k10_relat_1(esk5_0,X1)),k9_relat_1(esk5_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_107]), c_0_57]), c_0_58]), c_0_80])])).
% 0.19/0.45  cnf(c_0_109, plain, (k10_relat_1(X1,k9_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X2)),X2)|~r1_tarski(X2,k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_44, c_0_81])).
% 0.19/0.45  cnf(c_0_110, negated_conjecture, (r1_tarski(k10_relat_1(esk5_0,k9_relat_1(esk5_0,k10_relat_1(esk5_0,X1))),k10_relat_1(esk5_0,X1))), inference(spm,[status(thm)],[c_0_108, c_0_82])).
% 0.19/0.45  cnf(c_0_111, negated_conjecture, (k10_relat_1(esk5_0,k9_relat_1(esk5_0,k10_relat_1(esk5_0,X1)))=k10_relat_1(esk5_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_110]), c_0_58]), c_0_80])])).
% 0.19/0.45  cnf(c_0_112, negated_conjecture, (r1_tarski(k10_relat_1(esk5_0,X1),X2)|~r1_tarski(k9_relat_1(esk5_0,k10_relat_1(esk5_0,X1)),k9_relat_1(esk5_0,X2))), inference(rw,[status(thm)],[c_0_108, c_0_111])).
% 0.19/0.45  cnf(c_0_113, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_104]), c_0_31]), c_0_32])])).
% 0.19/0.45  cnf(c_0_114, negated_conjecture, (r1_tarski(k10_relat_1(esk5_0,k9_relat_1(esk5_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_113]), c_0_57]), c_0_58])])).
% 0.19/0.45  cnf(c_0_115, negated_conjecture, (k10_relat_1(esk5_0,k9_relat_1(esk5_0,esk4_0))!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.45  cnf(c_0_116, negated_conjecture, (k10_relat_1(esk5_0,k9_relat_1(esk5_0,X1))=X1|~r1_tarski(X1,k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_114]), c_0_58])])).
% 0.19/0.45  cnf(c_0_117, negated_conjecture, (r1_tarski(esk4_0,k1_relat_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.45  cnf(c_0_118, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116]), c_0_117])]), ['proof']).
% 0.19/0.45  # SZS output end CNFRefutation
% 0.19/0.45  # Proof object total steps             : 119
% 0.19/0.45  # Proof object clause steps            : 70
% 0.19/0.45  # Proof object formula steps           : 49
% 0.19/0.45  # Proof object conjectures             : 24
% 0.19/0.45  # Proof object clause conjectures      : 21
% 0.19/0.45  # Proof object formula conjectures     : 3
% 0.19/0.45  # Proof object initial clauses used    : 30
% 0.19/0.45  # Proof object initial formulas used   : 24
% 0.19/0.45  # Proof object generating inferences   : 32
% 0.19/0.45  # Proof object simplifying inferences  : 75
% 0.19/0.45  # Training examples: 0 positive, 0 negative
% 0.19/0.45  # Parsed axioms                        : 24
% 0.19/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.45  # Initial clauses                      : 42
% 0.19/0.45  # Removed in clause preprocessing      : 4
% 0.19/0.45  # Initial clauses in saturation        : 38
% 0.19/0.45  # Processed clauses                    : 974
% 0.19/0.45  # ...of these trivial                  : 149
% 0.19/0.45  # ...subsumed                          : 442
% 0.19/0.45  # ...remaining for further processing  : 383
% 0.19/0.45  # Other redundant clauses eliminated   : 49
% 0.19/0.45  # Clauses deleted for lack of memory   : 0
% 0.19/0.45  # Backward-subsumed                    : 7
% 0.19/0.45  # Backward-rewritten                   : 109
% 0.19/0.45  # Generated clauses                    : 7462
% 0.19/0.45  # ...of the previous two non-trivial   : 3355
% 0.19/0.45  # Contextual simplify-reflections      : 0
% 0.19/0.45  # Paramodulations                      : 7413
% 0.19/0.45  # Factorizations                       : 0
% 0.19/0.45  # Equation resolutions                 : 49
% 0.19/0.45  # Propositional unsat checks           : 0
% 0.19/0.45  #    Propositional check models        : 0
% 0.19/0.45  #    Propositional check unsatisfiable : 0
% 0.19/0.45  #    Propositional clauses             : 0
% 0.19/0.45  #    Propositional clauses after purity: 0
% 0.19/0.45  #    Propositional unsat core size     : 0
% 0.19/0.45  #    Propositional preprocessing time  : 0.000
% 0.19/0.45  #    Propositional encoding time       : 0.000
% 0.19/0.45  #    Propositional solver time         : 0.000
% 0.19/0.45  #    Success case prop preproc time    : 0.000
% 0.19/0.45  #    Success case prop encoding time   : 0.000
% 0.19/0.45  #    Success case prop solver time     : 0.000
% 0.19/0.45  # Current number of processed clauses  : 262
% 0.19/0.45  #    Positive orientable unit clauses  : 114
% 0.19/0.45  #    Positive unorientable unit clauses: 3
% 0.19/0.45  #    Negative unit clauses             : 2
% 0.19/0.45  #    Non-unit-clauses                  : 143
% 0.19/0.45  # Current number of unprocessed clauses: 2302
% 0.19/0.45  # ...number of literals in the above   : 5290
% 0.19/0.45  # Current number of archived formulas  : 0
% 0.19/0.45  # Current number of archived clauses   : 120
% 0.19/0.45  # Clause-clause subsumption calls (NU) : 4760
% 0.19/0.45  # Rec. Clause-clause subsumption calls : 2308
% 0.19/0.45  # Non-unit clause-clause subsumptions  : 254
% 0.19/0.45  # Unit Clause-clause subsumption calls : 68
% 0.19/0.45  # Rewrite failures with RHS unbound    : 0
% 0.19/0.45  # BW rewrite match attempts            : 293
% 0.19/0.45  # BW rewrite match successes           : 71
% 0.19/0.45  # Condensation attempts                : 0
% 0.19/0.45  # Condensation successes               : 0
% 0.19/0.45  # Termbank termtop insertions          : 105793
% 0.19/0.45  
% 0.19/0.45  # -------------------------------------------------
% 0.19/0.45  # User time                : 0.114 s
% 0.19/0.45  # System time              : 0.010 s
% 0.19/0.45  # Total time               : 0.125 s
% 0.19/0.45  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
