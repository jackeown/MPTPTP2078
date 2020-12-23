%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:27 EST 2020

% Result     : Theorem 0.98s
% Output     : CNFRefutation 0.98s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 633 expanded)
%              Number of clauses        :   79 ( 281 expanded)
%              Number of leaves         :   20 ( 173 expanded)
%              Depth                    :   21
%              Number of atoms          :  240 (1115 expanded)
%              Number of equality atoms :   71 ( 508 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t43_funct_1,axiom,(
    ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t88_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k7_relat_1(X2,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(t87_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(t146_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t175_funct_2,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( r1_tarski(k10_relat_1(X1,X3),X2)
         => k10_relat_1(X1,X3) = k10_relat_1(k7_relat_1(X1,X2),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

fof(t179_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( r1_tarski(X2,X3)
           => r1_tarski(k10_relat_1(X2,X1),k10_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t179_relat_1)).

fof(t181_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => k10_relat_1(k5_relat_1(X2,X3),X1) = k10_relat_1(X2,k10_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).

fof(c_0_20,plain,(
    ! [X21,X22] : k1_setfam_1(k2_tarski(X21,X22)) = k3_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_21,plain,(
    ! [X12,X13] : k1_enumset1(X12,X12,X13) = k2_tarski(X12,X13) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_22,plain,(
    ! [X45,X46] : k5_relat_1(k6_relat_1(X46),k6_relat_1(X45)) = k6_relat_1(k3_xboole_0(X45,X46)) ),
    inference(variable_rename,[status(thm)],[t43_funct_1])).

cnf(c_0_23,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_25,plain,(
    ! [X14,X15,X16] : k2_enumset1(X14,X14,X15,X16) = k1_enumset1(X14,X15,X16) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_26,plain,(
    ! [X17,X18,X19,X20] : k3_enumset1(X17,X17,X18,X19,X20) = k2_enumset1(X17,X18,X19,X20) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_27,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(X7,X8)
      | ~ r1_tarski(X8,X9)
      | r1_tarski(X7,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_28,plain,(
    ! [X36,X37] :
      ( ~ v1_relat_1(X37)
      | r1_tarski(k7_relat_1(X37,X36),X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).

fof(c_0_29,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_30,plain,(
    ! [X33] :
      ( k1_relat_1(k6_relat_1(X33)) = X33
      & k2_relat_1(k6_relat_1(X33)) = X33 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_31,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k3_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_33,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( r1_tarski(k7_relat_1(X1,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_37,plain,(
    ! [X34,X35] :
      ( ~ v1_relat_1(X35)
      | r1_tarski(k1_relat_1(k7_relat_1(X35,X34)),X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

fof(c_0_38,plain,(
    ! [X40,X41] :
      ( ~ v1_relat_1(X41)
      | ~ r1_tarski(k1_relat_1(X41),X40)
      | k7_relat_1(X41,X40) = X41 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k7_relat_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_44,plain,(
    ! [X42] :
      ( v1_relat_1(k6_relat_1(X42))
      & v1_funct_1(k6_relat_1(X42)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_45,plain,(
    ! [X25,X26] :
      ( ~ v1_relat_1(X26)
      | k2_relat_1(k7_relat_1(X26,X25)) = k9_relat_1(X26,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_46,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_39])).

fof(c_0_48,plain,(
    ! [X38,X39] :
      ( ~ v1_relat_1(X39)
      | k7_relat_1(X39,X38) = k5_relat_1(k6_relat_1(X38),X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

cnf(c_0_49,plain,
    ( k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)) = k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_50,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,k7_relat_1(X2,X3))),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_51,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_52,plain,(
    ! [X43,X44] :
      ( ~ v1_relat_1(X44)
      | ~ r1_tarski(X43,k1_relat_1(X44))
      | r1_tarski(X43,k10_relat_1(X44,k9_relat_1(X44,X43))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).

cnf(c_0_53,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_55,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,plain,
    ( k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(rw,[status(thm)],[c_0_41,c_0_49])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,k1_relat_1(k7_relat_1(X3,k7_relat_1(X2,X4)))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_50])).

cnf(c_0_58,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k6_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_40]),c_0_51])])).

fof(c_0_59,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X23)
      | v1_relat_1(k7_relat_1(X23,X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_60,plain,
    ( r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_61,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_62,plain,
    ( k7_relat_1(X1,k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)))) = k5_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X3,k7_relat_1(X2,X4))
    | ~ r1_tarski(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_51]),c_0_40])])).

cnf(c_0_64,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_65,plain,
    ( r1_tarski(k1_relat_1(X1),k10_relat_1(X1,k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_47])])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k5_relat_1(k5_relat_1(k6_relat_1(X3),k6_relat_1(X4)),X2)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_62])).

cnf(c_0_67,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,k1_relat_1(k7_relat_1(X3,k7_relat_1(k7_relat_1(X2,X4),X5)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_50]),c_0_64])).

cnf(c_0_69,plain,
    ( k7_relat_1(X1,k10_relat_1(X1,k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_65])).

cnf(c_0_70,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k5_relat_1(k7_relat_1(k6_relat_1(X3),X4),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_55]),c_0_51])])).

fof(c_0_71,plain,(
    ! [X10,X11] : k2_tarski(X10,X11) = k2_tarski(X11,X10) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_72,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X1)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_41])).

fof(c_0_73,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2,X3] :
            ( r1_tarski(k10_relat_1(X1,X3),X2)
           => k10_relat_1(X1,X3) = k10_relat_1(k7_relat_1(X1,X2),X3) ) ) ),
    inference(assume_negation,[status(cth)],[t175_funct_2])).

cnf(c_0_74,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X3,k7_relat_1(k7_relat_1(X2,X4),X5))
    | ~ r1_tarski(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_58]),c_0_51]),c_0_40])])).

cnf(c_0_75,plain,
    ( k7_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X1)) = k6_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_67]),c_0_51])])).

cnf(c_0_76,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k5_relat_1(k6_relat_1(X3),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_54]),c_0_51])])).

cnf(c_0_77,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_41])).

cnf(c_0_78,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_79,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) ),
    inference(rw,[status(thm)],[c_0_72,c_0_49])).

fof(c_0_80,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & r1_tarski(k10_relat_1(esk1_0,esk3_0),esk2_0)
    & k10_relat_1(esk1_0,esk3_0) != k10_relat_1(k7_relat_1(esk1_0,esk2_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_73])])])).

cnf(c_0_81,plain,
    ( r1_tarski(X1,k6_relat_1(X2))
    | ~ r1_tarski(X3,k7_relat_1(k6_relat_1(X2),X4))
    | ~ r1_tarski(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_51])])).

cnf(c_0_82,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_76,c_0_47])).

cnf(c_0_83,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_55]),c_0_51])])).

cnf(c_0_84,plain,
    ( k3_enumset1(X1,X1,X1,X1,X2) = k3_enumset1(X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_24]),c_0_24]),c_0_33]),c_0_33]),c_0_34]),c_0_34])).

cnf(c_0_85,plain,
    ( k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_55]),c_0_51])])).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk1_0,esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_87,plain,
    ( r1_tarski(X1,k6_relat_1(X2))
    | ~ r1_tarski(X1,k5_relat_1(k6_relat_1(X3),k7_relat_1(k6_relat_1(X2),X4))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_83])])).

cnf(c_0_88,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_84]),c_0_49])).

cnf(c_0_89,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k9_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_85]),c_0_51])])).

cnf(c_0_90,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,k10_relat_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_86])).

fof(c_0_91,plain,(
    ! [X27,X28,X29] :
      ( ~ v1_relat_1(X28)
      | ~ v1_relat_1(X29)
      | ~ r1_tarski(X28,X29)
      | r1_tarski(k10_relat_1(X28,X27),k10_relat_1(X29,X27)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t179_relat_1])])])).

cnf(c_0_92,plain,
    ( k7_relat_1(k6_relat_1(X1),X1) = k6_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_40]),c_0_51])])).

cnf(c_0_93,plain,
    ( r1_tarski(X1,k6_relat_1(X2))
    | ~ r1_tarski(X1,k5_relat_1(k6_relat_1(X3),k6_relat_1(X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_54]),c_0_51])])).

cnf(c_0_94,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k9_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_55]),c_0_89]),c_0_51])])).

cnf(c_0_95,plain,
    ( k6_relat_1(k9_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_55]),c_0_51])]),c_0_89])).

cnf(c_0_96,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,k10_relat_1(esk1_0,esk3_0))),esk2_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_90,c_0_43])).

cnf(c_0_97,plain,
    ( r1_tarski(k10_relat_1(X1,X3),k10_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_98,plain,
    ( k9_relat_1(k6_relat_1(X1),X1) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_92]),c_0_67]),c_0_51])])).

cnf(c_0_99,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k6_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_47])).

cnf(c_0_100,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_94]),c_0_95])).

cnf(c_0_101,negated_conjecture,
    ( k7_relat_1(k7_relat_1(X1,k10_relat_1(esk1_0,esk3_0)),esk2_0) = k7_relat_1(X1,k10_relat_1(esk1_0,esk3_0))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_96]),c_0_64])).

cnf(c_0_102,plain,
    ( r1_tarski(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4)
    | ~ r1_tarski(X1,k10_relat_1(X4,X3))
    | ~ r1_tarski(X4,X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_97])).

cnf(c_0_103,plain,
    ( r1_tarski(X1,k10_relat_1(k6_relat_1(X1),X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_98]),c_0_51]),c_0_40]),c_0_47])])).

cnf(c_0_104,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X2)) ),
    inference(rw,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_105,negated_conjecture,
    ( k7_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),esk2_0) = k6_relat_1(k10_relat_1(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_92]),c_0_51])])).

fof(c_0_106,plain,(
    ! [X30,X31,X32] :
      ( ~ v1_relat_1(X31)
      | ~ v1_relat_1(X32)
      | k10_relat_1(k5_relat_1(X31,X32),X30) = k10_relat_1(X31,k10_relat_1(X32,X30)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t181_relat_1])])])).

cnf(c_0_107,plain,
    ( r1_tarski(X1,k10_relat_1(X2,X1))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_51])])).

cnf(c_0_108,negated_conjecture,
    ( r1_tarski(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),k6_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_109,plain,
    ( k10_relat_1(k5_relat_1(X1,X2),X3) = k10_relat_1(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_106])).

cnf(c_0_110,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_111,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk1_0,esk3_0),k10_relat_1(k6_relat_1(esk2_0),k10_relat_1(esk1_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_51])])).

cnf(c_0_112,plain,
    ( k10_relat_1(k6_relat_1(X1),k10_relat_1(X2,X3)) = k10_relat_1(k7_relat_1(X2,X1),X3)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_55]),c_0_51])])).

cnf(c_0_113,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_114,plain,
    ( k10_relat_1(X1,X2) = k10_relat_1(X3,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X3,X2))
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_110,c_0_97])).

cnf(c_0_115,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk1_0,esk3_0),k10_relat_1(k7_relat_1(esk1_0,esk2_0),esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_113])])).

cnf(c_0_116,negated_conjecture,
    ( k10_relat_1(esk1_0,esk3_0) != k10_relat_1(k7_relat_1(esk1_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_117,negated_conjecture,
    ( ~ v1_relat_1(k7_relat_1(esk1_0,esk2_0))
    | ~ r1_tarski(k7_relat_1(esk1_0,esk2_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_115]),c_0_113])]),c_0_116])).

cnf(c_0_118,negated_conjecture,
    ( ~ r1_tarski(k7_relat_1(esk1_0,esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_64]),c_0_113])])).

cnf(c_0_119,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_36]),c_0_113])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n006.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 20:33:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.98/1.14  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.98/1.14  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.98/1.14  #
% 0.98/1.14  # Preprocessing time       : 0.027 s
% 0.98/1.14  # Presaturation interreduction done
% 0.98/1.14  
% 0.98/1.14  # Proof found!
% 0.98/1.14  # SZS status Theorem
% 0.98/1.14  # SZS output start CNFRefutation
% 0.98/1.14  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.98/1.14  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.98/1.14  fof(t43_funct_1, axiom, ![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 0.98/1.14  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.98/1.14  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.98/1.15  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.98/1.15  fof(t88_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k7_relat_1(X2,X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 0.98/1.15  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.98/1.15  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.98/1.15  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 0.98/1.15  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 0.98/1.15  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.98/1.15  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.98/1.15  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 0.98/1.15  fof(t146_funct_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 0.98/1.15  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.98/1.15  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.98/1.15  fof(t175_funct_2, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(r1_tarski(k10_relat_1(X1,X3),X2)=>k10_relat_1(X1,X3)=k10_relat_1(k7_relat_1(X1,X2),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 0.98/1.15  fof(t179_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X2,X3)=>r1_tarski(k10_relat_1(X2,X1),k10_relat_1(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t179_relat_1)).
% 0.98/1.15  fof(t181_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k10_relat_1(k5_relat_1(X2,X3),X1)=k10_relat_1(X2,k10_relat_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t181_relat_1)).
% 0.98/1.15  fof(c_0_20, plain, ![X21, X22]:k1_setfam_1(k2_tarski(X21,X22))=k3_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.98/1.15  fof(c_0_21, plain, ![X12, X13]:k1_enumset1(X12,X12,X13)=k2_tarski(X12,X13), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.98/1.15  fof(c_0_22, plain, ![X45, X46]:k5_relat_1(k6_relat_1(X46),k6_relat_1(X45))=k6_relat_1(k3_xboole_0(X45,X46)), inference(variable_rename,[status(thm)],[t43_funct_1])).
% 0.98/1.15  cnf(c_0_23, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.98/1.15  cnf(c_0_24, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.98/1.15  fof(c_0_25, plain, ![X14, X15, X16]:k2_enumset1(X14,X14,X15,X16)=k1_enumset1(X14,X15,X16), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.98/1.15  fof(c_0_26, plain, ![X17, X18, X19, X20]:k3_enumset1(X17,X17,X18,X19,X20)=k2_enumset1(X17,X18,X19,X20), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.98/1.15  fof(c_0_27, plain, ![X7, X8, X9]:(~r1_tarski(X7,X8)|~r1_tarski(X8,X9)|r1_tarski(X7,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.98/1.15  fof(c_0_28, plain, ![X36, X37]:(~v1_relat_1(X37)|r1_tarski(k7_relat_1(X37,X36),X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).
% 0.98/1.15  fof(c_0_29, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.98/1.15  fof(c_0_30, plain, ![X33]:(k1_relat_1(k6_relat_1(X33))=X33&k2_relat_1(k6_relat_1(X33))=X33), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.98/1.15  cnf(c_0_31, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k3_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.98/1.15  cnf(c_0_32, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.98/1.15  cnf(c_0_33, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.98/1.15  cnf(c_0_34, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.98/1.15  cnf(c_0_35, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.98/1.15  cnf(c_0_36, plain, (r1_tarski(k7_relat_1(X1,X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.98/1.15  fof(c_0_37, plain, ![X34, X35]:(~v1_relat_1(X35)|r1_tarski(k1_relat_1(k7_relat_1(X35,X34)),X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 0.98/1.15  fof(c_0_38, plain, ![X40, X41]:(~v1_relat_1(X41)|(~r1_tarski(k1_relat_1(X41),X40)|k7_relat_1(X41,X40)=X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 0.98/1.15  cnf(c_0_39, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.98/1.15  cnf(c_0_40, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.98/1.15  cnf(c_0_41, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34])).
% 0.98/1.15  cnf(c_0_42, plain, (r1_tarski(X1,X2)|~v1_relat_1(X2)|~r1_tarski(X1,k7_relat_1(X2,X3))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.98/1.15  cnf(c_0_43, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.98/1.15  fof(c_0_44, plain, ![X42]:(v1_relat_1(k6_relat_1(X42))&v1_funct_1(k6_relat_1(X42))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.98/1.15  fof(c_0_45, plain, ![X25, X26]:(~v1_relat_1(X26)|k2_relat_1(k7_relat_1(X26,X25))=k9_relat_1(X26,X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.98/1.15  cnf(c_0_46, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.98/1.15  cnf(c_0_47, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_39])).
% 0.98/1.15  fof(c_0_48, plain, ![X38, X39]:(~v1_relat_1(X39)|k7_relat_1(X39,X38)=k5_relat_1(k6_relat_1(X38),X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.98/1.15  cnf(c_0_49, plain, (k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))=k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.98/1.15  cnf(c_0_50, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,k7_relat_1(X2,X3))),X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.98/1.15  cnf(c_0_51, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.98/1.15  fof(c_0_52, plain, ![X43, X44]:(~v1_relat_1(X44)|(~r1_tarski(X43,k1_relat_1(X44))|r1_tarski(X43,k10_relat_1(X44,k9_relat_1(X44,X43))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).
% 0.98/1.15  cnf(c_0_53, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.98/1.15  cnf(c_0_54, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.98/1.15  cnf(c_0_55, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.98/1.15  cnf(c_0_56, plain, (k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))))=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(rw,[status(thm)],[c_0_41, c_0_49])).
% 0.98/1.15  cnf(c_0_57, plain, (r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X3)|~r1_tarski(X1,k1_relat_1(k7_relat_1(X3,k7_relat_1(X2,X4))))), inference(spm,[status(thm)],[c_0_35, c_0_50])).
% 0.98/1.15  cnf(c_0_58, plain, (k7_relat_1(k6_relat_1(X1),X2)=k6_relat_1(X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_40]), c_0_51])])).
% 0.98/1.15  fof(c_0_59, plain, ![X23, X24]:(~v1_relat_1(X23)|v1_relat_1(k7_relat_1(X23,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.98/1.15  cnf(c_0_60, plain, (r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.98/1.15  cnf(c_0_61, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.98/1.15  cnf(c_0_62, plain, (k7_relat_1(X1,k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3))))=k5_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)),X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.98/1.15  cnf(c_0_63, plain, (r1_tarski(X1,X2)|~v1_relat_1(X2)|~r1_tarski(X3,k7_relat_1(X2,X4))|~r1_tarski(X1,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_51]), c_0_40])])).
% 0.98/1.15  cnf(c_0_64, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.98/1.15  cnf(c_0_65, plain, (r1_tarski(k1_relat_1(X1),k10_relat_1(X1,k2_relat_1(X1)))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_47])])).
% 0.98/1.15  cnf(c_0_66, plain, (r1_tarski(X1,X2)|~v1_relat_1(X2)|~r1_tarski(X1,k5_relat_1(k5_relat_1(k6_relat_1(X3),k6_relat_1(X4)),X2))), inference(spm,[status(thm)],[c_0_42, c_0_62])).
% 0.98/1.15  cnf(c_0_67, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.98/1.15  cnf(c_0_68, plain, (r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X3)|~r1_tarski(X1,k1_relat_1(k7_relat_1(X3,k7_relat_1(k7_relat_1(X2,X4),X5))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_50]), c_0_64])).
% 0.98/1.15  cnf(c_0_69, plain, (k7_relat_1(X1,k10_relat_1(X1,k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_46, c_0_65])).
% 0.98/1.15  cnf(c_0_70, plain, (r1_tarski(X1,X2)|~v1_relat_1(X2)|~r1_tarski(X1,k5_relat_1(k7_relat_1(k6_relat_1(X3),X4),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_55]), c_0_51])])).
% 0.98/1.15  fof(c_0_71, plain, ![X10, X11]:k2_tarski(X10,X11)=k2_tarski(X11,X10), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.98/1.15  cnf(c_0_72, plain, (k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X1))), inference(spm,[status(thm)],[c_0_67, c_0_41])).
% 0.98/1.15  fof(c_0_73, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(r1_tarski(k10_relat_1(X1,X3),X2)=>k10_relat_1(X1,X3)=k10_relat_1(k7_relat_1(X1,X2),X3)))), inference(assume_negation,[status(cth)],[t175_funct_2])).
% 0.98/1.15  cnf(c_0_74, plain, (r1_tarski(X1,X2)|~v1_relat_1(X2)|~r1_tarski(X3,k7_relat_1(k7_relat_1(X2,X4),X5))|~r1_tarski(X1,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_58]), c_0_51]), c_0_40])])).
% 0.98/1.15  cnf(c_0_75, plain, (k7_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X1))=k6_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_67]), c_0_51])])).
% 0.98/1.15  cnf(c_0_76, plain, (r1_tarski(X1,X2)|~v1_relat_1(X2)|~r1_tarski(X1,k5_relat_1(k6_relat_1(X3),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_54]), c_0_51])])).
% 0.98/1.15  cnf(c_0_77, plain, (v1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))), inference(spm,[status(thm)],[c_0_51, c_0_41])).
% 0.98/1.15  cnf(c_0_78, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.98/1.15  cnf(c_0_79, plain, (k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))), inference(rw,[status(thm)],[c_0_72, c_0_49])).
% 0.98/1.15  fof(c_0_80, negated_conjecture, ((v1_relat_1(esk1_0)&v1_funct_1(esk1_0))&(r1_tarski(k10_relat_1(esk1_0,esk3_0),esk2_0)&k10_relat_1(esk1_0,esk3_0)!=k10_relat_1(k7_relat_1(esk1_0,esk2_0),esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_73])])])).
% 0.98/1.15  cnf(c_0_81, plain, (r1_tarski(X1,k6_relat_1(X2))|~r1_tarski(X3,k7_relat_1(k6_relat_1(X2),X4))|~r1_tarski(X1,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_51])])).
% 0.98/1.15  cnf(c_0_82, plain, (r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_76, c_0_47])).
% 0.98/1.15  cnf(c_0_83, plain, (v1_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_55]), c_0_51])])).
% 0.98/1.15  cnf(c_0_84, plain, (k3_enumset1(X1,X1,X1,X1,X2)=k3_enumset1(X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_24]), c_0_24]), c_0_33]), c_0_33]), c_0_34]), c_0_34])).
% 0.98/1.15  cnf(c_0_85, plain, (k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))=k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_55]), c_0_51])])).
% 0.98/1.15  cnf(c_0_86, negated_conjecture, (r1_tarski(k10_relat_1(esk1_0,esk3_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.98/1.15  cnf(c_0_87, plain, (r1_tarski(X1,k6_relat_1(X2))|~r1_tarski(X1,k5_relat_1(k6_relat_1(X3),k7_relat_1(k6_relat_1(X2),X4)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_83])])).
% 0.98/1.15  cnf(c_0_88, plain, (k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_84]), c_0_49])).
% 0.98/1.15  cnf(c_0_89, plain, (k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))=k9_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_85]), c_0_51])])).
% 0.98/1.15  cnf(c_0_90, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,k10_relat_1(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_35, c_0_86])).
% 0.98/1.15  fof(c_0_91, plain, ![X27, X28, X29]:(~v1_relat_1(X28)|(~v1_relat_1(X29)|(~r1_tarski(X28,X29)|r1_tarski(k10_relat_1(X28,X27),k10_relat_1(X29,X27))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t179_relat_1])])])).
% 0.98/1.15  cnf(c_0_92, plain, (k7_relat_1(k6_relat_1(X1),X1)=k6_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_40]), c_0_51])])).
% 0.98/1.15  cnf(c_0_93, plain, (r1_tarski(X1,k6_relat_1(X2))|~r1_tarski(X1,k5_relat_1(k6_relat_1(X3),k6_relat_1(X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_54]), c_0_51])])).
% 0.98/1.15  cnf(c_0_94, plain, (k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=k9_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_55]), c_0_89]), c_0_51])])).
% 0.98/1.15  cnf(c_0_95, plain, (k6_relat_1(k9_relat_1(k6_relat_1(X1),X2))=k7_relat_1(k6_relat_1(X1),X2)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_55]), c_0_51])]), c_0_89])).
% 0.98/1.15  cnf(c_0_96, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(X1,k10_relat_1(esk1_0,esk3_0))),esk2_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_90, c_0_43])).
% 0.98/1.15  cnf(c_0_97, plain, (r1_tarski(k10_relat_1(X1,X3),k10_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_91])).
% 0.98/1.15  cnf(c_0_98, plain, (k9_relat_1(k6_relat_1(X1),X1)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_92]), c_0_67]), c_0_51])])).
% 0.98/1.15  cnf(c_0_99, plain, (r1_tarski(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k6_relat_1(X2))), inference(spm,[status(thm)],[c_0_93, c_0_47])).
% 0.98/1.15  cnf(c_0_100, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k7_relat_1(k6_relat_1(X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_94]), c_0_95])).
% 0.98/1.15  cnf(c_0_101, negated_conjecture, (k7_relat_1(k7_relat_1(X1,k10_relat_1(esk1_0,esk3_0)),esk2_0)=k7_relat_1(X1,k10_relat_1(esk1_0,esk3_0))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_96]), c_0_64])).
% 0.98/1.15  cnf(c_0_102, plain, (r1_tarski(X1,k10_relat_1(X2,X3))|~v1_relat_1(X2)|~v1_relat_1(X4)|~r1_tarski(X1,k10_relat_1(X4,X3))|~r1_tarski(X4,X2)), inference(spm,[status(thm)],[c_0_35, c_0_97])).
% 0.98/1.15  cnf(c_0_103, plain, (r1_tarski(X1,k10_relat_1(k6_relat_1(X1),X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_98]), c_0_51]), c_0_40]), c_0_47])])).
% 0.98/1.15  cnf(c_0_104, plain, (r1_tarski(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X2))), inference(rw,[status(thm)],[c_0_99, c_0_100])).
% 0.98/1.15  cnf(c_0_105, negated_conjecture, (k7_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),esk2_0)=k6_relat_1(k10_relat_1(esk1_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_92]), c_0_51])])).
% 0.98/1.15  fof(c_0_106, plain, ![X30, X31, X32]:(~v1_relat_1(X31)|(~v1_relat_1(X32)|k10_relat_1(k5_relat_1(X31,X32),X30)=k10_relat_1(X31,k10_relat_1(X32,X30)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t181_relat_1])])])).
% 0.98/1.15  cnf(c_0_107, plain, (r1_tarski(X1,k10_relat_1(X2,X1))|~v1_relat_1(X2)|~r1_tarski(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_51])])).
% 0.98/1.15  cnf(c_0_108, negated_conjecture, (r1_tarski(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),k6_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_104, c_0_105])).
% 0.98/1.15  cnf(c_0_109, plain, (k10_relat_1(k5_relat_1(X1,X2),X3)=k10_relat_1(X1,k10_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_106])).
% 0.98/1.15  cnf(c_0_110, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.98/1.15  cnf(c_0_111, negated_conjecture, (r1_tarski(k10_relat_1(esk1_0,esk3_0),k10_relat_1(k6_relat_1(esk2_0),k10_relat_1(esk1_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_51])])).
% 0.98/1.15  cnf(c_0_112, plain, (k10_relat_1(k6_relat_1(X1),k10_relat_1(X2,X3))=k10_relat_1(k7_relat_1(X2,X1),X3)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_55]), c_0_51])])).
% 0.98/1.15  cnf(c_0_113, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.98/1.15  cnf(c_0_114, plain, (k10_relat_1(X1,X2)=k10_relat_1(X3,X2)|~v1_relat_1(X1)|~v1_relat_1(X3)|~r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X3,X2))|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_110, c_0_97])).
% 0.98/1.15  cnf(c_0_115, negated_conjecture, (r1_tarski(k10_relat_1(esk1_0,esk3_0),k10_relat_1(k7_relat_1(esk1_0,esk2_0),esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_113])])).
% 0.98/1.15  cnf(c_0_116, negated_conjecture, (k10_relat_1(esk1_0,esk3_0)!=k10_relat_1(k7_relat_1(esk1_0,esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.98/1.15  cnf(c_0_117, negated_conjecture, (~v1_relat_1(k7_relat_1(esk1_0,esk2_0))|~r1_tarski(k7_relat_1(esk1_0,esk2_0),esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_115]), c_0_113])]), c_0_116])).
% 0.98/1.15  cnf(c_0_118, negated_conjecture, (~r1_tarski(k7_relat_1(esk1_0,esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_64]), c_0_113])])).
% 0.98/1.15  cnf(c_0_119, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_36]), c_0_113])]), ['proof']).
% 0.98/1.15  # SZS output end CNFRefutation
% 0.98/1.15  # Proof object total steps             : 120
% 0.98/1.15  # Proof object clause steps            : 79
% 0.98/1.15  # Proof object formula steps           : 41
% 0.98/1.15  # Proof object conjectures             : 16
% 0.98/1.15  # Proof object clause conjectures      : 13
% 0.98/1.15  # Proof object formula conjectures     : 3
% 0.98/1.15  # Proof object initial clauses used    : 24
% 0.98/1.15  # Proof object initial formulas used   : 20
% 0.98/1.15  # Proof object generating inferences   : 47
% 0.98/1.15  # Proof object simplifying inferences  : 79
% 0.98/1.15  # Training examples: 0 positive, 0 negative
% 0.98/1.15  # Parsed axioms                        : 20
% 0.98/1.15  # Removed by relevancy pruning/SinE    : 0
% 0.98/1.15  # Initial clauses                      : 27
% 0.98/1.15  # Removed in clause preprocessing      : 4
% 0.98/1.15  # Initial clauses in saturation        : 23
% 0.98/1.15  # Processed clauses                    : 4783
% 0.98/1.15  # ...of these trivial                  : 31
% 0.98/1.15  # ...subsumed                          : 3598
% 0.98/1.15  # ...remaining for further processing  : 1154
% 0.98/1.15  # Other redundant clauses eliminated   : 2
% 0.98/1.15  # Clauses deleted for lack of memory   : 0
% 0.98/1.15  # Backward-subsumed                    : 179
% 0.98/1.15  # Backward-rewritten                   : 60
% 0.98/1.15  # Generated clauses                    : 43144
% 0.98/1.15  # ...of the previous two non-trivial   : 40761
% 0.98/1.15  # Contextual simplify-reflections      : 52
% 0.98/1.15  # Paramodulations                      : 43142
% 0.98/1.15  # Factorizations                       : 0
% 0.98/1.15  # Equation resolutions                 : 2
% 0.98/1.15  # Propositional unsat checks           : 0
% 0.98/1.15  #    Propositional check models        : 0
% 0.98/1.15  #    Propositional check unsatisfiable : 0
% 0.98/1.15  #    Propositional clauses             : 0
% 0.98/1.15  #    Propositional clauses after purity: 0
% 0.98/1.15  #    Propositional unsat core size     : 0
% 0.98/1.15  #    Propositional preprocessing time  : 0.000
% 0.98/1.15  #    Propositional encoding time       : 0.000
% 0.98/1.15  #    Propositional solver time         : 0.000
% 0.98/1.15  #    Success case prop preproc time    : 0.000
% 0.98/1.15  #    Success case prop encoding time   : 0.000
% 0.98/1.15  #    Success case prop solver time     : 0.000
% 0.98/1.15  # Current number of processed clauses  : 891
% 0.98/1.15  #    Positive orientable unit clauses  : 58
% 0.98/1.15  #    Positive unorientable unit clauses: 1
% 0.98/1.15  #    Negative unit clauses             : 2
% 0.98/1.15  #    Non-unit-clauses                  : 830
% 0.98/1.15  # Current number of unprocessed clauses: 35803
% 0.98/1.15  # ...number of literals in the above   : 194572
% 0.98/1.15  # Current number of archived formulas  : 0
% 0.98/1.15  # Current number of archived clauses   : 265
% 0.98/1.15  # Clause-clause subsumption calls (NU) : 452588
% 0.98/1.15  # Rec. Clause-clause subsumption calls : 95431
% 0.98/1.15  # Non-unit clause-clause subsumptions  : 3826
% 0.98/1.15  # Unit Clause-clause subsumption calls : 290
% 0.98/1.15  # Rewrite failures with RHS unbound    : 0
% 0.98/1.15  # BW rewrite match attempts            : 67
% 0.98/1.15  # BW rewrite match successes           : 24
% 0.98/1.15  # Condensation attempts                : 0
% 0.98/1.15  # Condensation successes               : 0
% 0.98/1.15  # Termbank termtop insertions          : 993626
% 0.98/1.15  
% 0.98/1.15  # -------------------------------------------------
% 0.98/1.15  # User time                : 0.791 s
% 0.98/1.15  # System time              : 0.022 s
% 0.98/1.15  # Total time               : 0.813 s
% 0.98/1.15  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
