%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:31 EST 2020

% Result     : Theorem 0.56s
% Output     : CNFRefutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 377 expanded)
%              Number of clauses        :   50 ( 154 expanded)
%              Number of leaves         :   21 ( 110 expanded)
%              Depth                    :   10
%              Number of atoms          :  235 ( 758 expanded)
%              Number of equality atoms :   65 ( 304 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t175_funct_2,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( r1_tarski(k10_relat_1(X1,X3),X2)
         => k10_relat_1(X1,X3) = k10_relat_1(k7_relat_1(X1,X2),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

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

fof(t158_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2))
          & r1_tarski(X1,k2_relat_1(X3)) )
       => r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t146_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(t163_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(X1,k1_relat_1(X3))
          & r1_tarski(k9_relat_1(X3,X1),X2) )
       => r1_tarski(X1,k10_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

fof(t148_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => k9_relat_1(X2,k10_relat_1(X2,X1)) = k3_xboole_0(X1,k9_relat_1(X2,k1_relat_1(X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(t139_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2,X3] :
            ( r1_tarski(k10_relat_1(X1,X3),X2)
           => k10_relat_1(X1,X3) = k10_relat_1(k7_relat_1(X1,X2),X3) ) ) ),
    inference(assume_negation,[status(cth)],[t175_funct_2])).

fof(c_0_22,plain,(
    ! [X48] :
      ( ~ v1_relat_1(X48)
      | k10_relat_1(X48,k2_relat_1(X48)) = k1_relat_1(X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

fof(c_0_23,plain,(
    ! [X49] :
      ( k1_relat_1(k6_relat_1(X49)) = X49
      & k2_relat_1(k6_relat_1(X49)) = X49 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_24,plain,(
    ! [X58] :
      ( v1_relat_1(k6_relat_1(X58))
      & v1_funct_1(k6_relat_1(X58)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_25,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | X14 != X15 )
      & ( r1_tarski(X15,X14)
        | X14 != X15 )
      & ( ~ r1_tarski(X14,X15)
        | ~ r1_tarski(X15,X14)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_26,plain,(
    ! [X16,X17,X18] :
      ( ~ r1_tarski(X16,X17)
      | ~ r1_tarski(X17,X18)
      | r1_tarski(X16,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_27,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & r1_tarski(k10_relat_1(esk3_0,esk5_0),esk4_0)
    & k10_relat_1(esk3_0,esk5_0) != k10_relat_1(k7_relat_1(esk3_0,esk4_0),esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

fof(c_0_28,plain,(
    ! [X62,X63] :
      ( ~ v1_relat_1(X63)
      | ~ v1_funct_1(X63)
      | r1_tarski(k9_relat_1(X63,k10_relat_1(X63,X62)),X62) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

cnf(c_0_29,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_33,plain,(
    ! [X50,X51,X52,X53,X54,X55,X56] :
      ( ( r2_hidden(X53,k1_relat_1(X50))
        | ~ r2_hidden(X53,X52)
        | X52 != k10_relat_1(X50,X51)
        | ~ v1_relat_1(X50)
        | ~ v1_funct_1(X50) )
      & ( r2_hidden(k1_funct_1(X50,X53),X51)
        | ~ r2_hidden(X53,X52)
        | X52 != k10_relat_1(X50,X51)
        | ~ v1_relat_1(X50)
        | ~ v1_funct_1(X50) )
      & ( ~ r2_hidden(X54,k1_relat_1(X50))
        | ~ r2_hidden(k1_funct_1(X50,X54),X51)
        | r2_hidden(X54,X52)
        | X52 != k10_relat_1(X50,X51)
        | ~ v1_relat_1(X50)
        | ~ v1_funct_1(X50) )
      & ( ~ r2_hidden(esk2_3(X50,X55,X56),X56)
        | ~ r2_hidden(esk2_3(X50,X55,X56),k1_relat_1(X50))
        | ~ r2_hidden(k1_funct_1(X50,esk2_3(X50,X55,X56)),X55)
        | X56 = k10_relat_1(X50,X55)
        | ~ v1_relat_1(X50)
        | ~ v1_funct_1(X50) )
      & ( r2_hidden(esk2_3(X50,X55,X56),k1_relat_1(X50))
        | r2_hidden(esk2_3(X50,X55,X56),X56)
        | X56 = k10_relat_1(X50,X55)
        | ~ v1_relat_1(X50)
        | ~ v1_funct_1(X50) )
      & ( r2_hidden(k1_funct_1(X50,esk2_3(X50,X55,X56)),X55)
        | r2_hidden(esk2_3(X50,X55,X56),X56)
        | X56 = k10_relat_1(X50,X55)
        | ~ v1_relat_1(X50)
        | ~ v1_funct_1(X50) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_funct_1])])])])])])).

fof(c_0_34,plain,(
    ! [X68,X69,X70] :
      ( ~ v1_relat_1(X70)
      | ~ v1_funct_1(X70)
      | ~ r1_tarski(k10_relat_1(X70,X68),k10_relat_1(X70,X69))
      | ~ r1_tarski(X68,k2_relat_1(X70))
      | r1_tarski(X68,X69) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_funct_1])])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk3_0,esk5_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( k10_relat_1(k6_relat_1(X1),X1) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32])])).

cnf(c_0_40,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,X3)
    | X3 != k10_relat_1(X2,X4)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_42,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_43,plain,(
    ! [X46,X47] : k1_setfam_1(k2_tarski(X46,X47)) = k3_xboole_0(X46,X47) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_44,plain,(
    ! [X19,X20] : k1_enumset1(X19,X19,X20) = k2_tarski(X19,X20) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_45,plain,
    ( r1_tarski(X2,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ r1_tarski(X2,k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_35])).

fof(c_0_47,plain,(
    ! [X64,X65] :
      ( ~ v1_relat_1(X65)
      | ~ r1_tarski(X64,k1_relat_1(X65))
      | r1_tarski(X64,k10_relat_1(X65,k9_relat_1(X65,X64))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).

fof(c_0_48,plain,(
    ! [X71,X72,X73] :
      ( ~ v1_relat_1(X73)
      | ~ v1_funct_1(X73)
      | ~ r1_tarski(X71,k1_relat_1(X73))
      | ~ r1_tarski(k9_relat_1(X73,X71),X72)
      | r1_tarski(X71,k10_relat_1(X73,X72)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r1_tarski(X1,k10_relat_1(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_50,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(X1),X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_32])])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k10_relat_1(X2,X3)) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_52,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_53,plain,(
    ! [X66,X67] :
      ( ~ v1_relat_1(X67)
      | ~ v1_funct_1(X67)
      | k9_relat_1(X67,k10_relat_1(X67,X66)) = k3_xboole_0(X66,k9_relat_1(X67,k1_relat_1(X67))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_funct_1])])).

cnf(c_0_54,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_55,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_56,plain,(
    ! [X21,X22,X23] : k2_enumset1(X21,X21,X22,X23) = k1_enumset1(X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_57,plain,(
    ! [X24,X25,X26,X27] : k3_enumset1(X24,X24,X25,X26,X27) = k2_enumset1(X24,X25,X26,X27) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_58,plain,(
    ! [X28,X29,X30,X31,X32] : k4_enumset1(X28,X28,X29,X30,X31,X32) = k3_enumset1(X28,X29,X30,X31,X32) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_59,plain,(
    ! [X33,X34,X35,X36,X37,X38] : k5_enumset1(X33,X33,X34,X35,X36,X37,X38) = k4_enumset1(X33,X34,X35,X36,X37,X38) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_60,plain,(
    ! [X39,X40,X41,X42,X43,X44,X45] : k6_enumset1(X39,X39,X40,X41,X42,X43,X44,X45) = k5_enumset1(X39,X40,X41,X42,X43,X44,X45) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k10_relat_1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_39]),c_0_40]),c_0_32]),c_0_30]),c_0_46])])).

cnf(c_0_62,plain,
    ( r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_63,plain,
    ( r1_tarski(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk5_0)),k10_relat_1(esk3_0,esk5_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_65,plain,
    ( r2_hidden(esk1_2(k10_relat_1(X1,X2),X3),k1_relat_1(X1))
    | r1_tarski(k10_relat_1(X1,X2),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

fof(c_0_66,plain,(
    ! [X59,X60,X61] :
      ( ~ v1_relat_1(X61)
      | k10_relat_1(k7_relat_1(X61,X59),X60) = k3_xboole_0(X59,k10_relat_1(X61,X60)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).

cnf(c_0_67,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = k3_xboole_0(X2,k9_relat_1(X1,k1_relat_1(X1)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_68,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_69,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_70,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_71,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_72,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_73,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_74,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_75,plain,
    ( r1_tarski(X1,k9_relat_1(k6_relat_1(X1),X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_32]),c_0_31]),c_0_46])])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk3_0,esk5_0),k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk5_0)),esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_40]),c_0_32]),c_0_31]),c_0_46])])).

cnf(c_0_77,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_78,plain,
    ( r2_hidden(esk1_2(k10_relat_1(k6_relat_1(X1),X2),X3),X1)
    | r1_tarski(k10_relat_1(k6_relat_1(X1),X2),X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_40]),c_0_31]),c_0_32])])).

cnf(c_0_79,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k3_xboole_0(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_80,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k9_relat_1(X1,k1_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_68]),c_0_69]),c_0_70]),c_0_71]),c_0_72]),c_0_73])).

cnf(c_0_81,plain,
    ( k9_relat_1(k6_relat_1(X1),X1) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_50])])).

cnf(c_0_82,negated_conjecture,
    ( k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk5_0)),esk4_0) = k10_relat_1(esk3_0,esk5_0)
    | ~ r1_tarski(k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk5_0)),esk4_0),k10_relat_1(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_76])).

cnf(c_0_83,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(X1),X2),X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_84,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k10_relat_1(X1,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_68]),c_0_69]),c_0_70]),c_0_71]),c_0_72]),c_0_73])).

cnf(c_0_85,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k9_relat_1(k6_relat_1(X2),k10_relat_1(k6_relat_1(X2),X1)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_31]),c_0_40]),c_0_32])]),c_0_81])).

cnf(c_0_86,negated_conjecture,
    ( k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk5_0)),esk4_0) = k10_relat_1(esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_83])])).

cnf(c_0_87,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k10_relat_1(k7_relat_1(k6_relat_1(X2),X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_39]),c_0_32])])).

cnf(c_0_88,negated_conjecture,
    ( k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk5_0)),esk4_0),k10_relat_1(esk3_0,esk5_0)) = k10_relat_1(esk3_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_81]),c_0_87])).

cnf(c_0_89,plain,
    ( k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(X1,X2)),X3),k10_relat_1(X1,X2)) = k10_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_84,c_0_87])).

cnf(c_0_90,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_91,negated_conjecture,
    ( k10_relat_1(esk3_0,esk5_0) != k10_relat_1(k7_relat_1(esk3_0,esk4_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_92,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_90])]),c_0_91]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:35:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.56/0.74  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.56/0.74  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.56/0.74  #
% 0.56/0.74  # Preprocessing time       : 0.028 s
% 0.56/0.74  # Presaturation interreduction done
% 0.56/0.74  
% 0.56/0.74  # Proof found!
% 0.56/0.74  # SZS status Theorem
% 0.56/0.74  # SZS output start CNFRefutation
% 0.56/0.74  fof(t175_funct_2, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(r1_tarski(k10_relat_1(X1,X3),X2)=>k10_relat_1(X1,X3)=k10_relat_1(k7_relat_1(X1,X2),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 0.56/0.74  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 0.56/0.74  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.56/0.74  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.56/0.74  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.56/0.74  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.56/0.74  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 0.56/0.74  fof(d13_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,k1_relat_1(X1))&r2_hidden(k1_funct_1(X1,X4),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_funct_1)).
% 0.56/0.74  fof(t158_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2))&r1_tarski(X1,k2_relat_1(X3)))=>r1_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t158_funct_1)).
% 0.56/0.74  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.56/0.74  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.56/0.74  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.56/0.74  fof(t146_funct_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 0.56/0.74  fof(t163_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(X1,k1_relat_1(X3))&r1_tarski(k9_relat_1(X3,X1),X2))=>r1_tarski(X1,k10_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_funct_1)).
% 0.56/0.74  fof(t148_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=k3_xboole_0(X1,k9_relat_1(X2,k1_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_funct_1)).
% 0.56/0.74  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.56/0.74  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.56/0.74  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.56/0.74  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.56/0.74  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.56/0.74  fof(t139_funct_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 0.56/0.74  fof(c_0_21, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(r1_tarski(k10_relat_1(X1,X3),X2)=>k10_relat_1(X1,X3)=k10_relat_1(k7_relat_1(X1,X2),X3)))), inference(assume_negation,[status(cth)],[t175_funct_2])).
% 0.56/0.74  fof(c_0_22, plain, ![X48]:(~v1_relat_1(X48)|k10_relat_1(X48,k2_relat_1(X48))=k1_relat_1(X48)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.56/0.74  fof(c_0_23, plain, ![X49]:(k1_relat_1(k6_relat_1(X49))=X49&k2_relat_1(k6_relat_1(X49))=X49), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.56/0.74  fof(c_0_24, plain, ![X58]:(v1_relat_1(k6_relat_1(X58))&v1_funct_1(k6_relat_1(X58))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.56/0.74  fof(c_0_25, plain, ![X14, X15]:(((r1_tarski(X14,X15)|X14!=X15)&(r1_tarski(X15,X14)|X14!=X15))&(~r1_tarski(X14,X15)|~r1_tarski(X15,X14)|X14=X15)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.56/0.74  fof(c_0_26, plain, ![X16, X17, X18]:(~r1_tarski(X16,X17)|~r1_tarski(X17,X18)|r1_tarski(X16,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.56/0.74  fof(c_0_27, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&(r1_tarski(k10_relat_1(esk3_0,esk5_0),esk4_0)&k10_relat_1(esk3_0,esk5_0)!=k10_relat_1(k7_relat_1(esk3_0,esk4_0),esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.56/0.74  fof(c_0_28, plain, ![X62, X63]:(~v1_relat_1(X63)|~v1_funct_1(X63)|r1_tarski(k9_relat_1(X63,k10_relat_1(X63,X62)),X62)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 0.56/0.74  cnf(c_0_29, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.56/0.74  cnf(c_0_30, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.56/0.74  cnf(c_0_31, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.56/0.74  cnf(c_0_32, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.56/0.74  fof(c_0_33, plain, ![X50, X51, X52, X53, X54, X55, X56]:((((r2_hidden(X53,k1_relat_1(X50))|~r2_hidden(X53,X52)|X52!=k10_relat_1(X50,X51)|(~v1_relat_1(X50)|~v1_funct_1(X50)))&(r2_hidden(k1_funct_1(X50,X53),X51)|~r2_hidden(X53,X52)|X52!=k10_relat_1(X50,X51)|(~v1_relat_1(X50)|~v1_funct_1(X50))))&(~r2_hidden(X54,k1_relat_1(X50))|~r2_hidden(k1_funct_1(X50,X54),X51)|r2_hidden(X54,X52)|X52!=k10_relat_1(X50,X51)|(~v1_relat_1(X50)|~v1_funct_1(X50))))&((~r2_hidden(esk2_3(X50,X55,X56),X56)|(~r2_hidden(esk2_3(X50,X55,X56),k1_relat_1(X50))|~r2_hidden(k1_funct_1(X50,esk2_3(X50,X55,X56)),X55))|X56=k10_relat_1(X50,X55)|(~v1_relat_1(X50)|~v1_funct_1(X50)))&((r2_hidden(esk2_3(X50,X55,X56),k1_relat_1(X50))|r2_hidden(esk2_3(X50,X55,X56),X56)|X56=k10_relat_1(X50,X55)|(~v1_relat_1(X50)|~v1_funct_1(X50)))&(r2_hidden(k1_funct_1(X50,esk2_3(X50,X55,X56)),X55)|r2_hidden(esk2_3(X50,X55,X56),X56)|X56=k10_relat_1(X50,X55)|(~v1_relat_1(X50)|~v1_funct_1(X50)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_funct_1])])])])])])).
% 0.56/0.74  fof(c_0_34, plain, ![X68, X69, X70]:(~v1_relat_1(X70)|~v1_funct_1(X70)|(~r1_tarski(k10_relat_1(X70,X68),k10_relat_1(X70,X69))|~r1_tarski(X68,k2_relat_1(X70))|r1_tarski(X68,X69))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_funct_1])])).
% 0.56/0.74  cnf(c_0_35, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.56/0.74  cnf(c_0_36, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.56/0.74  cnf(c_0_37, negated_conjecture, (r1_tarski(k10_relat_1(esk3_0,esk5_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.56/0.74  cnf(c_0_38, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.56/0.74  cnf(c_0_39, plain, (k10_relat_1(k6_relat_1(X1),X1)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32])])).
% 0.56/0.74  cnf(c_0_40, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.56/0.74  cnf(c_0_41, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(X1,X3)|X3!=k10_relat_1(X2,X4)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.56/0.74  fof(c_0_42, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk1_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk1_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.56/0.74  fof(c_0_43, plain, ![X46, X47]:k1_setfam_1(k2_tarski(X46,X47))=k3_xboole_0(X46,X47), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.56/0.74  fof(c_0_44, plain, ![X19, X20]:k1_enumset1(X19,X19,X20)=k2_tarski(X19,X20), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.56/0.74  cnf(c_0_45, plain, (r1_tarski(X2,X3)|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~r1_tarski(X2,k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.56/0.74  cnf(c_0_46, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_35])).
% 0.56/0.74  fof(c_0_47, plain, ![X64, X65]:(~v1_relat_1(X65)|(~r1_tarski(X64,k1_relat_1(X65))|r1_tarski(X64,k10_relat_1(X65,k9_relat_1(X65,X64))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).
% 0.56/0.74  fof(c_0_48, plain, ![X71, X72, X73]:(~v1_relat_1(X73)|~v1_funct_1(X73)|(~r1_tarski(X71,k1_relat_1(X73))|~r1_tarski(k9_relat_1(X73,X71),X72)|r1_tarski(X71,k10_relat_1(X73,X72)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).
% 0.56/0.74  cnf(c_0_49, negated_conjecture, (r1_tarski(X1,esk4_0)|~r1_tarski(X1,k10_relat_1(esk3_0,esk5_0))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.56/0.74  cnf(c_0_50, plain, (r1_tarski(k9_relat_1(k6_relat_1(X1),X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_32])])).
% 0.56/0.74  cnf(c_0_51, plain, (r2_hidden(X1,k1_relat_1(X2))|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k10_relat_1(X2,X3))), inference(er,[status(thm)],[c_0_41])).
% 0.56/0.74  cnf(c_0_52, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.56/0.74  fof(c_0_53, plain, ![X66, X67]:(~v1_relat_1(X67)|~v1_funct_1(X67)|k9_relat_1(X67,k10_relat_1(X67,X66))=k3_xboole_0(X66,k9_relat_1(X67,k1_relat_1(X67)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_funct_1])])).
% 0.56/0.74  cnf(c_0_54, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.56/0.74  cnf(c_0_55, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.56/0.74  fof(c_0_56, plain, ![X21, X22, X23]:k2_enumset1(X21,X21,X22,X23)=k1_enumset1(X21,X22,X23), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.56/0.74  fof(c_0_57, plain, ![X24, X25, X26, X27]:k3_enumset1(X24,X24,X25,X26,X27)=k2_enumset1(X24,X25,X26,X27), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.56/0.74  fof(c_0_58, plain, ![X28, X29, X30, X31, X32]:k4_enumset1(X28,X28,X29,X30,X31,X32)=k3_enumset1(X28,X29,X30,X31,X32), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.56/0.74  fof(c_0_59, plain, ![X33, X34, X35, X36, X37, X38]:k5_enumset1(X33,X33,X34,X35,X36,X37,X38)=k4_enumset1(X33,X34,X35,X36,X37,X38), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.56/0.74  fof(c_0_60, plain, ![X39, X40, X41, X42, X43, X44, X45]:k6_enumset1(X39,X39,X40,X41,X42,X43,X44,X45)=k5_enumset1(X39,X40,X41,X42,X43,X44,X45), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.56/0.74  cnf(c_0_61, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k10_relat_1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_39]), c_0_40]), c_0_32]), c_0_30]), c_0_46])])).
% 0.56/0.74  cnf(c_0_62, plain, (r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.56/0.74  cnf(c_0_63, plain, (r1_tarski(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k1_relat_1(X1))|~r1_tarski(k9_relat_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.56/0.74  cnf(c_0_64, negated_conjecture, (r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk5_0)),k10_relat_1(esk3_0,esk5_0)),esk4_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.56/0.74  cnf(c_0_65, plain, (r2_hidden(esk1_2(k10_relat_1(X1,X2),X3),k1_relat_1(X1))|r1_tarski(k10_relat_1(X1,X2),X3)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.56/0.74  fof(c_0_66, plain, ![X59, X60, X61]:(~v1_relat_1(X61)|k10_relat_1(k7_relat_1(X61,X59),X60)=k3_xboole_0(X59,k10_relat_1(X61,X60))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).
% 0.56/0.74  cnf(c_0_67, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=k3_xboole_0(X2,k9_relat_1(X1,k1_relat_1(X1)))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.56/0.74  cnf(c_0_68, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_54, c_0_55])).
% 0.56/0.74  cnf(c_0_69, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.56/0.74  cnf(c_0_70, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.56/0.74  cnf(c_0_71, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.56/0.74  cnf(c_0_72, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.56/0.74  cnf(c_0_73, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.56/0.74  cnf(c_0_74, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.56/0.74  cnf(c_0_75, plain, (r1_tarski(X1,k9_relat_1(k6_relat_1(X1),X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_32]), c_0_31]), c_0_46])])).
% 0.56/0.74  cnf(c_0_76, negated_conjecture, (r1_tarski(k10_relat_1(esk3_0,esk5_0),k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk5_0)),esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_40]), c_0_32]), c_0_31]), c_0_46])])).
% 0.56/0.74  cnf(c_0_77, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.56/0.74  cnf(c_0_78, plain, (r2_hidden(esk1_2(k10_relat_1(k6_relat_1(X1),X2),X3),X1)|r1_tarski(k10_relat_1(k6_relat_1(X1),X2),X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_40]), c_0_31]), c_0_32])])).
% 0.56/0.74  cnf(c_0_79, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k3_xboole_0(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.56/0.74  cnf(c_0_80, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k9_relat_1(X1,k1_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_68]), c_0_69]), c_0_70]), c_0_71]), c_0_72]), c_0_73])).
% 0.56/0.74  cnf(c_0_81, plain, (k9_relat_1(k6_relat_1(X1),X1)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_50])])).
% 0.56/0.74  cnf(c_0_82, negated_conjecture, (k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk5_0)),esk4_0)=k10_relat_1(esk3_0,esk5_0)|~r1_tarski(k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk5_0)),esk4_0),k10_relat_1(esk3_0,esk5_0))), inference(spm,[status(thm)],[c_0_74, c_0_76])).
% 0.56/0.74  cnf(c_0_83, plain, (r1_tarski(k10_relat_1(k6_relat_1(X1),X2),X1)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.56/0.74  cnf(c_0_84, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k10_relat_1(X1,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_68]), c_0_69]), c_0_70]), c_0_71]), c_0_72]), c_0_73])).
% 0.56/0.74  cnf(c_0_85, plain, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k9_relat_1(k6_relat_1(X2),k10_relat_1(k6_relat_1(X2),X1))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_31]), c_0_40]), c_0_32])]), c_0_81])).
% 0.56/0.74  cnf(c_0_86, negated_conjecture, (k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk5_0)),esk4_0)=k10_relat_1(esk3_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_83])])).
% 0.56/0.74  cnf(c_0_87, plain, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k10_relat_1(k7_relat_1(k6_relat_1(X2),X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_39]), c_0_32])])).
% 0.56/0.74  cnf(c_0_88, negated_conjecture, (k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk5_0)),esk4_0),k10_relat_1(esk3_0,esk5_0))=k10_relat_1(esk3_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_81]), c_0_87])).
% 0.56/0.74  cnf(c_0_89, plain, (k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(X1,X2)),X3),k10_relat_1(X1,X2))=k10_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_84, c_0_87])).
% 0.56/0.74  cnf(c_0_90, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.56/0.74  cnf(c_0_91, negated_conjecture, (k10_relat_1(esk3_0,esk5_0)!=k10_relat_1(k7_relat_1(esk3_0,esk4_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.56/0.74  cnf(c_0_92, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_90])]), c_0_91]), ['proof']).
% 0.56/0.74  # SZS output end CNFRefutation
% 0.56/0.74  # Proof object total steps             : 93
% 0.56/0.74  # Proof object clause steps            : 50
% 0.56/0.74  # Proof object formula steps           : 43
% 0.56/0.74  # Proof object conjectures             : 13
% 0.56/0.74  # Proof object clause conjectures      : 10
% 0.56/0.74  # Proof object formula conjectures     : 3
% 0.56/0.74  # Proof object initial clauses used    : 27
% 0.56/0.74  # Proof object initial formulas used   : 21
% 0.56/0.74  # Proof object generating inferences   : 17
% 0.56/0.74  # Proof object simplifying inferences  : 53
% 0.56/0.74  # Training examples: 0 positive, 0 negative
% 0.56/0.74  # Parsed axioms                        : 21
% 0.56/0.74  # Removed by relevancy pruning/SinE    : 0
% 0.56/0.74  # Initial clauses                      : 35
% 0.56/0.74  # Removed in clause preprocessing      : 7
% 0.56/0.74  # Initial clauses in saturation        : 28
% 0.56/0.74  # Processed clauses                    : 2701
% 0.56/0.74  # ...of these trivial                  : 12
% 0.56/0.74  # ...subsumed                          : 1875
% 0.56/0.74  # ...remaining for further processing  : 814
% 0.56/0.74  # Other redundant clauses eliminated   : 5
% 0.56/0.74  # Clauses deleted for lack of memory   : 0
% 0.56/0.74  # Backward-subsumed                    : 26
% 0.56/0.74  # Backward-rewritten                   : 38
% 0.56/0.74  # Generated clauses                    : 20020
% 0.56/0.74  # ...of the previous two non-trivial   : 18372
% 0.56/0.74  # Contextual simplify-reflections      : 15
% 0.56/0.74  # Paramodulations                      : 20011
% 0.56/0.74  # Factorizations                       : 4
% 0.56/0.74  # Equation resolutions                 : 5
% 0.56/0.74  # Propositional unsat checks           : 0
% 0.56/0.74  #    Propositional check models        : 0
% 0.56/0.74  #    Propositional check unsatisfiable : 0
% 0.56/0.74  #    Propositional clauses             : 0
% 0.56/0.74  #    Propositional clauses after purity: 0
% 0.56/0.74  #    Propositional unsat core size     : 0
% 0.56/0.74  #    Propositional preprocessing time  : 0.000
% 0.56/0.74  #    Propositional encoding time       : 0.000
% 0.56/0.74  #    Propositional solver time         : 0.000
% 0.56/0.74  #    Success case prop preproc time    : 0.000
% 0.56/0.74  #    Success case prop encoding time   : 0.000
% 0.56/0.74  #    Success case prop solver time     : 0.000
% 0.56/0.74  # Current number of processed clauses  : 718
% 0.56/0.74  #    Positive orientable unit clauses  : 43
% 0.56/0.74  #    Positive unorientable unit clauses: 2
% 0.56/0.74  #    Negative unit clauses             : 1
% 0.56/0.74  #    Non-unit-clauses                  : 672
% 0.56/0.74  # Current number of unprocessed clauses: 15540
% 0.56/0.74  # ...number of literals in the above   : 76766
% 0.56/0.74  # Current number of archived formulas  : 0
% 0.56/0.74  # Current number of archived clauses   : 98
% 0.56/0.74  # Clause-clause subsumption calls (NU) : 90833
% 0.56/0.74  # Rec. Clause-clause subsumption calls : 51698
% 0.56/0.74  # Non-unit clause-clause subsumptions  : 1916
% 0.56/0.74  # Unit Clause-clause subsumption calls : 449
% 0.56/0.74  # Rewrite failures with RHS unbound    : 0
% 0.56/0.74  # BW rewrite match attempts            : 53
% 0.56/0.74  # BW rewrite match successes           : 16
% 0.56/0.74  # Condensation attempts                : 0
% 0.56/0.74  # Condensation successes               : 0
% 0.56/0.74  # Termbank termtop insertions          : 438766
% 0.56/0.74  
% 0.56/0.74  # -------------------------------------------------
% 0.56/0.74  # User time                : 0.384 s
% 0.56/0.74  # System time              : 0.013 s
% 0.56/0.74  # Total time               : 0.398 s
% 0.56/0.74  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
