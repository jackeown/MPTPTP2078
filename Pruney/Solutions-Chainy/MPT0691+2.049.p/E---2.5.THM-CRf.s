%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:48 EST 2020

% Result     : Theorem 0.48s
% Output     : CNFRefutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 446 expanded)
%              Number of clauses        :   62 ( 187 expanded)
%              Number of leaves         :   24 ( 120 expanded)
%              Depth                    :   10
%              Number of atoms          :  201 ( 891 expanded)
%              Number of equality atoms :   99 ( 359 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t146_funct_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(t139_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

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

fof(t14_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2)
        & ! [X4] :
            ( ( r1_tarski(X1,X4)
              & r1_tarski(X3,X4) )
           => r1_tarski(X2,X4) ) )
     => X2 = k2_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t175_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t167_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(t182_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(t162_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( r1_tarski(X2,X3)
         => k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X1,k1_relat_1(X2))
         => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    inference(assume_negation,[status(cth)],[t146_funct_1])).

fof(c_0_25,plain,(
    ! [X54,X55] : k1_setfam_1(k2_tarski(X54,X55)) = k3_xboole_0(X54,X55) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_26,plain,(
    ! [X27,X28] : k1_enumset1(X27,X27,X28) = k2_tarski(X27,X28) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_27,plain,(
    ! [X9,X10] :
      ( ( r1_tarski(X9,X10)
        | X9 != X10 )
      & ( r1_tarski(X10,X9)
        | X9 != X10 )
      & ( ~ r1_tarski(X9,X10)
        | ~ r1_tarski(X10,X9)
        | X9 = X10 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_28,plain,(
    ! [X65] :
      ( ~ v1_relat_1(X65)
      | k10_relat_1(X65,k2_relat_1(X65)) = k1_relat_1(X65) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

fof(c_0_29,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & r1_tarski(esk2_0,k1_relat_1(esk3_0))
    & ~ r1_tarski(esk2_0,k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

fof(c_0_30,plain,(
    ! [X76,X77,X78] :
      ( ~ v1_relat_1(X78)
      | k10_relat_1(k7_relat_1(X78,X76),X77) = k3_xboole_0(X76,k10_relat_1(X78,X77)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).

cnf(c_0_31,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_33,plain,(
    ! [X29,X30,X31] : k2_enumset1(X29,X29,X30,X31) = k1_enumset1(X29,X30,X31) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_34,plain,(
    ! [X32,X33,X34,X35] : k3_enumset1(X32,X32,X33,X34,X35) = k2_enumset1(X32,X33,X34,X35) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_35,plain,(
    ! [X36,X37,X38,X39,X40] : k4_enumset1(X36,X36,X37,X38,X39,X40) = k3_enumset1(X36,X37,X38,X39,X40) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_36,plain,(
    ! [X41,X42,X43,X44,X45,X46] : k5_enumset1(X41,X41,X42,X43,X44,X45,X46) = k4_enumset1(X41,X42,X43,X44,X45,X46) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_37,plain,(
    ! [X47,X48,X49,X50,X51,X52,X53] : k6_enumset1(X47,X47,X48,X49,X50,X51,X52,X53) = k5_enumset1(X47,X48,X49,X50,X51,X52,X53) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_38,plain,(
    ! [X18,X19,X20] :
      ( ( r1_tarski(X18,esk1_3(X18,X19,X20))
        | ~ r1_tarski(X18,X19)
        | ~ r1_tarski(X20,X19)
        | X19 = k2_xboole_0(X18,X20) )
      & ( r1_tarski(X20,esk1_3(X18,X19,X20))
        | ~ r1_tarski(X18,X19)
        | ~ r1_tarski(X20,X19)
        | X19 = k2_xboole_0(X18,X20) )
      & ( ~ r1_tarski(X19,esk1_3(X18,X19,X20))
        | ~ r1_tarski(X18,X19)
        | ~ r1_tarski(X20,X19)
        | X19 = k2_xboole_0(X18,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_xboole_1])])])])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_42,plain,(
    ! [X57,X58] :
      ( ~ v1_relat_1(X57)
      | v1_relat_1(k7_relat_1(X57,X58)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_43,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k3_xboole_0(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_44,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_45,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_49,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_50,plain,(
    ! [X66,X67,X68] :
      ( ~ v1_relat_1(X68)
      | k10_relat_1(X68,k2_xboole_0(X66,X67)) = k2_xboole_0(k10_relat_1(X68,X66),k10_relat_1(X68,X67)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t175_relat_1])])).

fof(c_0_51,plain,(
    ! [X56] : v1_relat_1(k6_relat_1(X56)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

cnf(c_0_52,plain,
    ( X1 = k2_xboole_0(X2,X3)
    | ~ r1_tarski(X1,esk1_3(X2,X1,X3))
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,esk1_3(X2,X3,X1))
    | X3 = k2_xboole_0(X2,X1)
    | ~ r1_tarski(X2,X3)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(esk2_0,k1_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_56,negated_conjecture,
    ( k1_relat_1(esk3_0) = k10_relat_1(esk3_0,k2_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

fof(c_0_57,plain,(
    ! [X63,X64] :
      ( ~ v1_relat_1(X64)
      | r1_tarski(k10_relat_1(X64,X63),k1_relat_1(X64)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).

fof(c_0_58,plain,(
    ! [X71] :
      ( k1_relat_1(k6_relat_1(X71)) = X71
      & k2_relat_1(k6_relat_1(X71)) = X71 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_59,plain,(
    ! [X69,X70] :
      ( ~ v1_relat_1(X69)
      | ~ v1_relat_1(X70)
      | k1_relat_1(k5_relat_1(X69,X70)) = k10_relat_1(X69,k1_relat_1(X70)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).

fof(c_0_60,plain,(
    ! [X74,X75] :
      ( ~ v1_relat_1(X75)
      | k7_relat_1(X75,X74) = k5_relat_1(k6_relat_1(X74),X75) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

cnf(c_0_61,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_62,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k10_relat_1(X1,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_46]),c_0_47]),c_0_48]),c_0_49])).

fof(c_0_63,plain,(
    ! [X13,X14] : k4_xboole_0(X13,X14) = k5_xboole_0(X13,k3_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_64,plain,(
    ! [X59] :
      ( ~ v1_relat_1(X59)
      | k9_relat_1(X59,k1_relat_1(X59)) = k2_relat_1(X59) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

cnf(c_0_65,plain,
    ( k10_relat_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_66,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_67,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(esk2_0,k10_relat_1(esk3_0,k2_relat_1(esk3_0))) ),
    inference(rw,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,esk1_3(X1,X2,X3))
    | X2 = k2_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_70,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_71,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_72,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_73,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_74,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k10_relat_1(k7_relat_1(X1,X2),k2_relat_1(k7_relat_1(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_61])).

cnf(c_0_75,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk3_0,X1),X2) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k10_relat_1(esk3_0,X2))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_41])).

fof(c_0_76,plain,(
    ! [X60,X61,X62] :
      ( ~ v1_relat_1(X60)
      | ~ r1_tarski(X61,X62)
      | k9_relat_1(k7_relat_1(X60,X62),X61) = k9_relat_1(X60,X61) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_relat_1])])])).

fof(c_0_77,plain,(
    ! [X11,X12] :
      ( ( k4_xboole_0(X11,X12) != k1_xboole_0
        | r1_tarski(X11,X12) )
      & ( ~ r1_tarski(X11,X12)
        | k4_xboole_0(X11,X12) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_78,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_79,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_80,plain,
    ( k10_relat_1(k6_relat_1(X1),k2_xboole_0(X2,X3)) = k2_xboole_0(k10_relat_1(k6_relat_1(X1),X2),k10_relat_1(k6_relat_1(X1),X3)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_81,negated_conjecture,
    ( k2_xboole_0(esk2_0,k10_relat_1(esk3_0,k2_relat_1(esk3_0))) = k10_relat_1(esk3_0,k2_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_82,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_83,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_69]),c_0_54])])).

cnf(c_0_84,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(X1),X2),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_66]),c_0_71])).

cnf(c_0_85,negated_conjecture,
    ( k1_relat_1(k5_relat_1(X1,esk3_0)) = k10_relat_1(X1,k10_relat_1(esk3_0,k2_relat_1(esk3_0)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_41]),c_0_56])).

cnf(c_0_86,negated_conjecture,
    ( k5_relat_1(k6_relat_1(X1),esk3_0) = k7_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_41])).

cnf(c_0_87,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk3_0,X1)) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k10_relat_1(esk3_0,k2_relat_1(k7_relat_1(esk3_0,X1))))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_41]),c_0_75])).

cnf(c_0_88,plain,
    ( k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

fof(c_0_89,plain,(
    ! [X8] : k3_xboole_0(X8,X8) = X8 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_90,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_91,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_78,c_0_44])).

cnf(c_0_92,plain,
    ( k9_relat_1(k7_relat_1(X1,X2),k1_relat_1(k7_relat_1(X1,X2))) = k2_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_79,c_0_61])).

cnf(c_0_93,negated_conjecture,
    ( k2_xboole_0(k10_relat_1(k6_relat_1(X1),esk2_0),k10_relat_1(k6_relat_1(X1),k10_relat_1(esk3_0,k2_relat_1(esk3_0)))) = k10_relat_1(k6_relat_1(X1),k10_relat_1(esk3_0,k2_relat_1(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_94,plain,
    ( k10_relat_1(k6_relat_1(X1),X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_66]),c_0_71]),c_0_82])).

cnf(c_0_95,plain,
    ( k2_xboole_0(X1,k10_relat_1(k6_relat_1(X1),X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_96,negated_conjecture,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k10_relat_1(esk3_0,k2_relat_1(k7_relat_1(esk3_0,X1))))) = k10_relat_1(k6_relat_1(X1),k10_relat_1(esk3_0,k2_relat_1(esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_66]),c_0_86]),c_0_87])).

cnf(c_0_97,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk3_0,X1),X2) = k9_relat_1(esk3_0,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_88,c_0_41])).

cnf(c_0_98,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_99,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_100,negated_conjecture,
    ( ~ r1_tarski(esk2_0,k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_101,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_91]),c_0_45]),c_0_46]),c_0_47]),c_0_48]),c_0_49])).

cnf(c_0_102,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk3_0,X1),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k10_relat_1(esk3_0,k2_relat_1(k7_relat_1(esk3_0,X1)))))) = k2_relat_1(k7_relat_1(esk3_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_41]),c_0_87])).

cnf(c_0_103,negated_conjecture,
    ( k1_setfam_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k10_relat_1(esk3_0,k2_relat_1(k7_relat_1(esk3_0,esk2_0))))) = esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_95]),c_0_96])).

cnf(c_0_104,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk3_0,X1),X1) = k9_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_97,c_0_54])).

cnf(c_0_105,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_98,c_0_91]),c_0_45]),c_0_46]),c_0_47]),c_0_48]),c_0_49])).

cnf(c_0_106,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_44]),c_0_45]),c_0_46]),c_0_47]),c_0_48]),c_0_49])).

cnf(c_0_107,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0))))) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_108,negated_conjecture,
    ( k9_relat_1(esk3_0,esk2_0) = k2_relat_1(k7_relat_1(esk3_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_104])).

cnf(c_0_109,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_54]),c_0_106])).

cnf(c_0_110,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_107,c_0_108]),c_0_103]),c_0_109])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:05:32 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.48/0.70  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0YI
% 0.48/0.70  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.48/0.70  #
% 0.48/0.70  # Preprocessing time       : 0.041 s
% 0.48/0.70  # Presaturation interreduction done
% 0.48/0.70  
% 0.48/0.70  # Proof found!
% 0.48/0.70  # SZS status Theorem
% 0.48/0.70  # SZS output start CNFRefutation
% 0.48/0.70  fof(t146_funct_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 0.48/0.70  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.48/0.70  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.48/0.70  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.48/0.70  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 0.48/0.70  fof(t139_funct_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 0.48/0.70  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.48/0.70  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.48/0.70  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.48/0.70  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.48/0.70  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.48/0.70  fof(t14_xboole_1, axiom, ![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X3,X2))&![X4]:((r1_tarski(X1,X4)&r1_tarski(X3,X4))=>r1_tarski(X2,X4)))=>X2=k2_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_xboole_1)).
% 0.48/0.70  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.48/0.70  fof(t175_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_relat_1)).
% 0.48/0.70  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.48/0.70  fof(t167_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 0.48/0.70  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.48/0.70  fof(t182_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 0.48/0.70  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 0.48/0.70  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.48/0.70  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 0.48/0.70  fof(t162_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 0.48/0.70  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.48/0.70  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.48/0.70  fof(c_0_24, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1)))))), inference(assume_negation,[status(cth)],[t146_funct_1])).
% 0.48/0.70  fof(c_0_25, plain, ![X54, X55]:k1_setfam_1(k2_tarski(X54,X55))=k3_xboole_0(X54,X55), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.48/0.70  fof(c_0_26, plain, ![X27, X28]:k1_enumset1(X27,X27,X28)=k2_tarski(X27,X28), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.48/0.70  fof(c_0_27, plain, ![X9, X10]:(((r1_tarski(X9,X10)|X9!=X10)&(r1_tarski(X10,X9)|X9!=X10))&(~r1_tarski(X9,X10)|~r1_tarski(X10,X9)|X9=X10)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.48/0.70  fof(c_0_28, plain, ![X65]:(~v1_relat_1(X65)|k10_relat_1(X65,k2_relat_1(X65))=k1_relat_1(X65)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.48/0.70  fof(c_0_29, negated_conjecture, (v1_relat_1(esk3_0)&(r1_tarski(esk2_0,k1_relat_1(esk3_0))&~r1_tarski(esk2_0,k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).
% 0.48/0.70  fof(c_0_30, plain, ![X76, X77, X78]:(~v1_relat_1(X78)|k10_relat_1(k7_relat_1(X78,X76),X77)=k3_xboole_0(X76,k10_relat_1(X78,X77))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).
% 0.48/0.70  cnf(c_0_31, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.48/0.70  cnf(c_0_32, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.48/0.70  fof(c_0_33, plain, ![X29, X30, X31]:k2_enumset1(X29,X29,X30,X31)=k1_enumset1(X29,X30,X31), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.48/0.70  fof(c_0_34, plain, ![X32, X33, X34, X35]:k3_enumset1(X32,X32,X33,X34,X35)=k2_enumset1(X32,X33,X34,X35), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.48/0.70  fof(c_0_35, plain, ![X36, X37, X38, X39, X40]:k4_enumset1(X36,X36,X37,X38,X39,X40)=k3_enumset1(X36,X37,X38,X39,X40), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.48/0.70  fof(c_0_36, plain, ![X41, X42, X43, X44, X45, X46]:k5_enumset1(X41,X41,X42,X43,X44,X45,X46)=k4_enumset1(X41,X42,X43,X44,X45,X46), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.48/0.70  fof(c_0_37, plain, ![X47, X48, X49, X50, X51, X52, X53]:k6_enumset1(X47,X47,X48,X49,X50,X51,X52,X53)=k5_enumset1(X47,X48,X49,X50,X51,X52,X53), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.48/0.70  fof(c_0_38, plain, ![X18, X19, X20]:(((r1_tarski(X18,esk1_3(X18,X19,X20))|(~r1_tarski(X18,X19)|~r1_tarski(X20,X19))|X19=k2_xboole_0(X18,X20))&(r1_tarski(X20,esk1_3(X18,X19,X20))|(~r1_tarski(X18,X19)|~r1_tarski(X20,X19))|X19=k2_xboole_0(X18,X20)))&(~r1_tarski(X19,esk1_3(X18,X19,X20))|(~r1_tarski(X18,X19)|~r1_tarski(X20,X19))|X19=k2_xboole_0(X18,X20))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_xboole_1])])])])).
% 0.48/0.70  cnf(c_0_39, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.48/0.70  cnf(c_0_40, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.48/0.70  cnf(c_0_41, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.48/0.70  fof(c_0_42, plain, ![X57, X58]:(~v1_relat_1(X57)|v1_relat_1(k7_relat_1(X57,X58))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.48/0.70  cnf(c_0_43, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k3_xboole_0(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.48/0.70  cnf(c_0_44, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 0.48/0.70  cnf(c_0_45, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.48/0.70  cnf(c_0_46, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.48/0.70  cnf(c_0_47, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.48/0.70  cnf(c_0_48, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.48/0.70  cnf(c_0_49, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.48/0.70  fof(c_0_50, plain, ![X66, X67, X68]:(~v1_relat_1(X68)|k10_relat_1(X68,k2_xboole_0(X66,X67))=k2_xboole_0(k10_relat_1(X68,X66),k10_relat_1(X68,X67))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t175_relat_1])])).
% 0.48/0.70  fof(c_0_51, plain, ![X56]:v1_relat_1(k6_relat_1(X56)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.48/0.70  cnf(c_0_52, plain, (X1=k2_xboole_0(X2,X3)|~r1_tarski(X1,esk1_3(X2,X1,X3))|~r1_tarski(X2,X1)|~r1_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.48/0.70  cnf(c_0_53, plain, (r1_tarski(X1,esk1_3(X2,X3,X1))|X3=k2_xboole_0(X2,X1)|~r1_tarski(X2,X3)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.48/0.70  cnf(c_0_54, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_39])).
% 0.48/0.70  cnf(c_0_55, negated_conjecture, (r1_tarski(esk2_0,k1_relat_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.48/0.70  cnf(c_0_56, negated_conjecture, (k1_relat_1(esk3_0)=k10_relat_1(esk3_0,k2_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.48/0.70  fof(c_0_57, plain, ![X63, X64]:(~v1_relat_1(X64)|r1_tarski(k10_relat_1(X64,X63),k1_relat_1(X64))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).
% 0.48/0.70  fof(c_0_58, plain, ![X71]:(k1_relat_1(k6_relat_1(X71))=X71&k2_relat_1(k6_relat_1(X71))=X71), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.48/0.70  fof(c_0_59, plain, ![X69, X70]:(~v1_relat_1(X69)|(~v1_relat_1(X70)|k1_relat_1(k5_relat_1(X69,X70))=k10_relat_1(X69,k1_relat_1(X70)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).
% 0.48/0.70  fof(c_0_60, plain, ![X74, X75]:(~v1_relat_1(X75)|k7_relat_1(X75,X74)=k5_relat_1(k6_relat_1(X74),X75)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.48/0.70  cnf(c_0_61, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.48/0.70  cnf(c_0_62, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k10_relat_1(X1,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_46]), c_0_47]), c_0_48]), c_0_49])).
% 0.48/0.70  fof(c_0_63, plain, ![X13, X14]:k4_xboole_0(X13,X14)=k5_xboole_0(X13,k3_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.48/0.70  fof(c_0_64, plain, ![X59]:(~v1_relat_1(X59)|k9_relat_1(X59,k1_relat_1(X59))=k2_relat_1(X59)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.48/0.70  cnf(c_0_65, plain, (k10_relat_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.48/0.70  cnf(c_0_66, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.48/0.70  cnf(c_0_67, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])])).
% 0.48/0.70  cnf(c_0_68, negated_conjecture, (r1_tarski(esk2_0,k10_relat_1(esk3_0,k2_relat_1(esk3_0)))), inference(rw,[status(thm)],[c_0_55, c_0_56])).
% 0.48/0.70  cnf(c_0_69, plain, (r1_tarski(X1,esk1_3(X1,X2,X3))|X2=k2_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.48/0.70  cnf(c_0_70, plain, (r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.48/0.70  cnf(c_0_71, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.48/0.70  cnf(c_0_72, plain, (k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.48/0.70  cnf(c_0_73, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.48/0.70  cnf(c_0_74, plain, (k1_relat_1(k7_relat_1(X1,X2))=k10_relat_1(k7_relat_1(X1,X2),k2_relat_1(k7_relat_1(X1,X2)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_40, c_0_61])).
% 0.48/0.70  cnf(c_0_75, negated_conjecture, (k10_relat_1(k7_relat_1(esk3_0,X1),X2)=k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k10_relat_1(esk3_0,X2)))), inference(spm,[status(thm)],[c_0_62, c_0_41])).
% 0.48/0.70  fof(c_0_76, plain, ![X60, X61, X62]:(~v1_relat_1(X60)|(~r1_tarski(X61,X62)|k9_relat_1(k7_relat_1(X60,X62),X61)=k9_relat_1(X60,X61))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_relat_1])])])).
% 0.48/0.70  fof(c_0_77, plain, ![X11, X12]:((k4_xboole_0(X11,X12)!=k1_xboole_0|r1_tarski(X11,X12))&(~r1_tarski(X11,X12)|k4_xboole_0(X11,X12)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.48/0.70  cnf(c_0_78, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.48/0.70  cnf(c_0_79, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.48/0.70  cnf(c_0_80, plain, (k10_relat_1(k6_relat_1(X1),k2_xboole_0(X2,X3))=k2_xboole_0(k10_relat_1(k6_relat_1(X1),X2),k10_relat_1(k6_relat_1(X1),X3))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.48/0.70  cnf(c_0_81, negated_conjecture, (k2_xboole_0(esk2_0,k10_relat_1(esk3_0,k2_relat_1(esk3_0)))=k10_relat_1(esk3_0,k2_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.48/0.70  cnf(c_0_82, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.48/0.70  cnf(c_0_83, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_69]), c_0_54])])).
% 0.48/0.70  cnf(c_0_84, plain, (r1_tarski(k10_relat_1(k6_relat_1(X1),X2),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_66]), c_0_71])).
% 0.48/0.70  cnf(c_0_85, negated_conjecture, (k1_relat_1(k5_relat_1(X1,esk3_0))=k10_relat_1(X1,k10_relat_1(esk3_0,k2_relat_1(esk3_0)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_41]), c_0_56])).
% 0.48/0.70  cnf(c_0_86, negated_conjecture, (k5_relat_1(k6_relat_1(X1),esk3_0)=k7_relat_1(esk3_0,X1)), inference(spm,[status(thm)],[c_0_73, c_0_41])).
% 0.48/0.70  cnf(c_0_87, negated_conjecture, (k1_relat_1(k7_relat_1(esk3_0,X1))=k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k10_relat_1(esk3_0,k2_relat_1(k7_relat_1(esk3_0,X1)))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_41]), c_0_75])).
% 0.48/0.70  cnf(c_0_88, plain, (k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.48/0.70  fof(c_0_89, plain, ![X8]:k3_xboole_0(X8,X8)=X8, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.48/0.70  cnf(c_0_90, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.48/0.70  cnf(c_0_91, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_78, c_0_44])).
% 0.48/0.70  cnf(c_0_92, plain, (k9_relat_1(k7_relat_1(X1,X2),k1_relat_1(k7_relat_1(X1,X2)))=k2_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_79, c_0_61])).
% 0.48/0.70  cnf(c_0_93, negated_conjecture, (k2_xboole_0(k10_relat_1(k6_relat_1(X1),esk2_0),k10_relat_1(k6_relat_1(X1),k10_relat_1(esk3_0,k2_relat_1(esk3_0))))=k10_relat_1(k6_relat_1(X1),k10_relat_1(esk3_0,k2_relat_1(esk3_0)))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.48/0.70  cnf(c_0_94, plain, (k10_relat_1(k6_relat_1(X1),X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_66]), c_0_71]), c_0_82])).
% 0.48/0.70  cnf(c_0_95, plain, (k2_xboole_0(X1,k10_relat_1(k6_relat_1(X1),X2))=X1), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.48/0.70  cnf(c_0_96, negated_conjecture, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k10_relat_1(esk3_0,k2_relat_1(k7_relat_1(esk3_0,X1)))))=k10_relat_1(k6_relat_1(X1),k10_relat_1(esk3_0,k2_relat_1(esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_66]), c_0_86]), c_0_87])).
% 0.48/0.70  cnf(c_0_97, negated_conjecture, (k9_relat_1(k7_relat_1(esk3_0,X1),X2)=k9_relat_1(esk3_0,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_88, c_0_41])).
% 0.48/0.70  cnf(c_0_98, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.48/0.70  cnf(c_0_99, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_89])).
% 0.48/0.70  cnf(c_0_100, negated_conjecture, (~r1_tarski(esk2_0,k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.48/0.70  cnf(c_0_101, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_91]), c_0_45]), c_0_46]), c_0_47]), c_0_48]), c_0_49])).
% 0.48/0.70  cnf(c_0_102, negated_conjecture, (k9_relat_1(k7_relat_1(esk3_0,X1),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k10_relat_1(esk3_0,k2_relat_1(k7_relat_1(esk3_0,X1))))))=k2_relat_1(k7_relat_1(esk3_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_41]), c_0_87])).
% 0.48/0.70  cnf(c_0_103, negated_conjecture, (k1_setfam_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k10_relat_1(esk3_0,k2_relat_1(k7_relat_1(esk3_0,esk2_0)))))=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_95]), c_0_96])).
% 0.48/0.70  cnf(c_0_104, negated_conjecture, (k9_relat_1(k7_relat_1(esk3_0,X1),X1)=k9_relat_1(esk3_0,X1)), inference(spm,[status(thm)],[c_0_97, c_0_54])).
% 0.48/0.70  cnf(c_0_105, plain, (k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_98, c_0_91]), c_0_45]), c_0_46]), c_0_47]), c_0_48]), c_0_49])).
% 0.48/0.70  cnf(c_0_106, plain, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_99, c_0_44]), c_0_45]), c_0_46]), c_0_47]), c_0_48]), c_0_49])).
% 0.48/0.70  cnf(c_0_107, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0)))))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_100, c_0_101])).
% 0.48/0.70  cnf(c_0_108, negated_conjecture, (k9_relat_1(esk3_0,esk2_0)=k2_relat_1(k7_relat_1(esk3_0,esk2_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_104])).
% 0.48/0.70  cnf(c_0_109, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_54]), c_0_106])).
% 0.48/0.70  cnf(c_0_110, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_107, c_0_108]), c_0_103]), c_0_109])]), ['proof']).
% 0.48/0.70  # SZS output end CNFRefutation
% 0.48/0.70  # Proof object total steps             : 111
% 0.48/0.70  # Proof object clause steps            : 62
% 0.48/0.70  # Proof object formula steps           : 49
% 0.48/0.70  # Proof object conjectures             : 22
% 0.48/0.70  # Proof object clause conjectures      : 19
% 0.48/0.70  # Proof object formula conjectures     : 3
% 0.48/0.70  # Proof object initial clauses used    : 30
% 0.48/0.70  # Proof object initial formulas used   : 24
% 0.48/0.70  # Proof object generating inferences   : 23
% 0.48/0.70  # Proof object simplifying inferences  : 48
% 0.48/0.70  # Training examples: 0 positive, 0 negative
% 0.48/0.70  # Parsed axioms                        : 28
% 0.48/0.70  # Removed by relevancy pruning/SinE    : 0
% 0.48/0.70  # Initial clauses                      : 36
% 0.48/0.70  # Removed in clause preprocessing      : 8
% 0.48/0.70  # Initial clauses in saturation        : 28
% 0.48/0.70  # Processed clauses                    : 1986
% 0.48/0.70  # ...of these trivial                  : 91
% 0.48/0.70  # ...subsumed                          : 1308
% 0.48/0.70  # ...remaining for further processing  : 587
% 0.48/0.70  # Other redundant clauses eliminated   : 2
% 0.48/0.70  # Clauses deleted for lack of memory   : 0
% 0.48/0.70  # Backward-subsumed                    : 0
% 0.48/0.70  # Backward-rewritten                   : 64
% 0.48/0.70  # Generated clauses                    : 23516
% 0.48/0.70  # ...of the previous two non-trivial   : 19599
% 0.48/0.70  # Contextual simplify-reflections      : 0
% 0.48/0.70  # Paramodulations                      : 23514
% 0.48/0.70  # Factorizations                       : 0
% 0.48/0.70  # Equation resolutions                 : 2
% 0.48/0.70  # Propositional unsat checks           : 0
% 0.48/0.70  #    Propositional check models        : 0
% 0.48/0.70  #    Propositional check unsatisfiable : 0
% 0.48/0.70  #    Propositional clauses             : 0
% 0.48/0.70  #    Propositional clauses after purity: 0
% 0.48/0.70  #    Propositional unsat core size     : 0
% 0.48/0.70  #    Propositional preprocessing time  : 0.000
% 0.48/0.70  #    Propositional encoding time       : 0.000
% 0.48/0.70  #    Propositional solver time         : 0.000
% 0.48/0.70  #    Success case prop preproc time    : 0.000
% 0.48/0.70  #    Success case prop encoding time   : 0.000
% 0.48/0.70  #    Success case prop solver time     : 0.000
% 0.48/0.70  # Current number of processed clauses  : 494
% 0.48/0.70  #    Positive orientable unit clauses  : 198
% 0.48/0.70  #    Positive unorientable unit clauses: 2
% 0.48/0.70  #    Negative unit clauses             : 0
% 0.48/0.70  #    Non-unit-clauses                  : 294
% 0.48/0.70  # Current number of unprocessed clauses: 17384
% 0.48/0.70  # ...number of literals in the above   : 31685
% 0.48/0.70  # Current number of archived formulas  : 0
% 0.48/0.70  # Current number of archived clauses   : 99
% 0.48/0.70  # Clause-clause subsumption calls (NU) : 14615
% 0.48/0.70  # Rec. Clause-clause subsumption calls : 9102
% 0.48/0.70  # Non-unit clause-clause subsumptions  : 609
% 0.48/0.70  # Unit Clause-clause subsumption calls : 164
% 0.48/0.70  # Rewrite failures with RHS unbound    : 0
% 0.48/0.70  # BW rewrite match attempts            : 905
% 0.48/0.70  # BW rewrite match successes           : 59
% 0.48/0.70  # Condensation attempts                : 0
% 0.48/0.70  # Condensation successes               : 0
% 0.48/0.70  # Termbank termtop insertions          : 563397
% 0.48/0.70  
% 0.48/0.70  # -------------------------------------------------
% 0.48/0.70  # User time                : 0.338 s
% 0.48/0.70  # System time              : 0.013 s
% 0.48/0.70  # Total time               : 0.351 s
% 0.48/0.70  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
