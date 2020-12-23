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
% DateTime   : Thu Dec  3 10:55:55 EST 2020

% Result     : Theorem 0.77s
% Output     : CNFRefutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :  134 (1764 expanded)
%              Number of clauses        :   93 ( 825 expanded)
%              Number of leaves         :   20 ( 468 expanded)
%              Depth                    :   27
%              Number of atoms          :  264 (2451 expanded)
%              Number of equality atoms :   71 (1154 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal clause size      :   19 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t74_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( ~ r1_xboole_0(X1,k3_xboole_0(X2,X3))
        & r1_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t89_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t111_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k4_xboole_0(X1,X3),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_xboole_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(t88_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => k4_xboole_0(k2_xboole_0(X1,X2),X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

fof(t93_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

fof(t52_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(t84_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( ~ r1_xboole_0(X1,X2)
        & r1_xboole_0(X1,X3)
        & r1_xboole_0(X1,k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_xboole_1)).

fof(t107_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k5_xboole_0(X2,X3))
    <=> ( r1_tarski(X1,k2_xboole_0(X2,X3))
        & r1_xboole_0(X1,k3_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).

fof(t127_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_xboole_0(X1,X2)
        | r1_xboole_0(X3,X4) )
     => r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(t76_enumset1,axiom,(
    ! [X1] : k1_enumset1(X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

fof(t137_enumset1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1)) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

fof(d20_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( v5_funct_1(X2,X1)
          <=> ! [X3] :
                ( r2_hidden(X3,k1_relat_1(X2))
               => r2_hidden(k1_funct_1(X2,X3),k1_funct_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).

fof(s3_funct_1__e2_24__funct_1,axiom,(
    ! [X1,X2] :
    ? [X3] :
      ( v1_relat_1(X3)
      & v1_funct_1(X3)
      & k1_relat_1(X3) = X1
      & ! [X4] :
          ( r2_hidden(X4,X1)
         => k1_funct_1(X3,X4) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(t174_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => v5_funct_1(k1_xboole_0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

fof(t22_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

fof(c_0_20,plain,(
    ! [X20,X21,X22] :
      ( r1_xboole_0(X20,k3_xboole_0(X21,X22))
      | ~ r1_xboole_0(X20,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t74_xboole_1])])])).

fof(c_0_21,plain,(
    ! [X13] : k3_xboole_0(X13,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_22,plain,
    ( r1_xboole_0(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_24,plain,(
    ! [X30,X31] : r1_xboole_0(k3_xboole_0(X30,X31),k4_xboole_0(X30,X31)) ),
    inference(variable_rename,[status(thm)],[t89_xboole_1])).

cnf(c_0_25,plain,
    ( r1_xboole_0(X1,k1_xboole_0)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_27,plain,(
    ! [X11,X12] :
      ( ~ r1_tarski(X11,X12)
      | k3_xboole_0(X11,X12) = X11 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_28,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X2),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_29,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_30,plain,(
    ! [X23,X24] : r1_tarski(X23,k2_xboole_0(X23,X24)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_31,plain,(
    ! [X8,X9,X10] : k4_xboole_0(k3_xboole_0(X8,X9),k3_xboole_0(X10,X9)) = k3_xboole_0(k4_xboole_0(X8,X10),X9) ),
    inference(variable_rename,[status(thm)],[t111_xboole_1])).

fof(c_0_32,plain,(
    ! [X14,X15,X16] :
      ( ~ r1_tarski(X14,k2_xboole_0(X15,X16))
      | r1_tarski(k4_xboole_0(X14,X15),X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

fof(c_0_33,plain,(
    ! [X28,X29] :
      ( ~ r1_xboole_0(X28,X29)
      | k4_xboole_0(k2_xboole_0(X28,X29),X29) = X28 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_xboole_1])])).

cnf(c_0_34,plain,
    ( r1_xboole_0(X1,k1_xboole_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_36,plain,(
    ! [X32,X33] : k2_xboole_0(X32,X33) = k2_xboole_0(k5_xboole_0(X32,X33),k3_xboole_0(X32,X33)) ),
    inference(variable_rename,[status(thm)],[t93_xboole_1])).

fof(c_0_37,plain,(
    ! [X17,X18,X19] : k4_xboole_0(X17,k4_xboole_0(X18,X19)) = k2_xboole_0(k4_xboole_0(X17,X18),k3_xboole_0(X17,X19)) ),
    inference(variable_rename,[status(thm)],[t52_xboole_1])).

cnf(c_0_38,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k4_xboole_0(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_39,plain,(
    ! [X25,X26,X27] :
      ( r1_xboole_0(X25,X26)
      | ~ r1_xboole_0(X25,X27)
      | ~ r1_xboole_0(X25,k4_xboole_0(X26,X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t84_xboole_1])])])).

cnf(c_0_40,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_29])).

cnf(c_0_41,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_44,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_38]),c_0_23]),c_0_23])).

cnf(c_0_47,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,k2_xboole_0(X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

fof(c_0_49,plain,(
    ! [X5,X6,X7] :
      ( ( r1_tarski(X5,k2_xboole_0(X6,X7))
        | ~ r1_tarski(X5,k5_xboole_0(X6,X7)) )
      & ( r1_xboole_0(X5,k3_xboole_0(X6,X7))
        | ~ r1_tarski(X5,k5_xboole_0(X6,X7)) )
      & ( ~ r1_tarski(X5,k2_xboole_0(X6,X7))
        | ~ r1_xboole_0(X5,k3_xboole_0(X6,X7))
        | r1_tarski(X5,k5_xboole_0(X6,X7)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t107_xboole_1])])])).

cnf(c_0_50,plain,
    ( k4_xboole_0(k2_xboole_0(X1,k1_xboole_0),k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_51,plain,
    ( k2_xboole_0(k5_xboole_0(X1,k1_xboole_0),k1_xboole_0) = k2_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_23])).

cnf(c_0_52,plain,
    ( k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X1,X2),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_23])).

cnf(c_0_54,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_tarski(X2,k2_xboole_0(X3,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_43])])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_50])).

cnf(c_0_57,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_46]),c_0_35])])).

cnf(c_0_58,plain,
    ( k2_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_23]),c_0_46]),c_0_46])).

cnf(c_0_59,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k1_xboole_0),k1_xboole_0) = k4_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_46])).

cnf(c_0_60,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_tarski(X2,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])).

cnf(c_0_61,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_29]),c_0_57])]),c_0_58])).

cnf(c_0_62,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_59,c_0_50])).

cnf(c_0_63,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_43])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(k2_xboole_0(X1,k1_xboole_0),k2_xboole_0(k1_xboole_0,X2)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_50])).

cnf(c_0_65,plain,
    ( k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_52,c_0_61])).

cnf(c_0_66,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_48,c_0_62])).

cnf(c_0_67,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = X1
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_63])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,k3_xboole_0(k1_xboole_0,X2))
    | ~ r1_tarski(k2_xboole_0(X1,k1_xboole_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_69,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(k2_xboole_0(X1,X2),X2)
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_70,plain,
    ( r1_tarski(X1,k3_xboole_0(k1_xboole_0,X2))
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_68,c_0_62])).

cnf(c_0_71,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(k2_xboole_0(X1,k3_xboole_0(k1_xboole_0,X2)),k1_xboole_0)
    | ~ r1_tarski(k3_xboole_0(k1_xboole_0,X2),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_72,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0
    | ~ r1_tarski(k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)),k1_xboole_0)
    | ~ r1_tarski(k3_xboole_0(k1_xboole_0,X2),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_45])).

cnf(c_0_73,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0
    | ~ r1_tarski(k3_xboole_0(k1_xboole_0,X2),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_66]),c_0_57]),c_0_57])])).

cnf(c_0_74,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_50,c_0_62])).

cnf(c_0_75,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_23]),c_0_57])])).

cnf(c_0_76,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_45])).

cnf(c_0_77,plain,
    ( r1_xboole_0(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_78,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_74]),c_0_75]),c_0_74])).

cnf(c_0_79,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k1_xboole_0)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_66])).

cnf(c_0_80,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X2,X3))
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_77,c_0_29])).

cnf(c_0_81,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_62])).

cnf(c_0_82,plain,
    ( k2_xboole_0(k5_xboole_0(X1,X2),X1) = k2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_29])).

cnf(c_0_83,plain,
    ( k2_xboole_0(X1,X1) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_78,c_0_29])).

cnf(c_0_84,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(X1,X2),X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_76])).

cnf(c_0_85,plain,
    ( r1_tarski(X1,k5_xboole_0(X2,X3))
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_86,plain,
    ( r1_xboole_0(k5_xboole_0(X1,X2),X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_87,plain,
    ( k2_xboole_0(k5_xboole_0(X1,X1),X1) = k2_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_81])).

cnf(c_0_88,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_83,c_0_35])).

cnf(c_0_89,plain,
    ( r1_tarski(k4_xboole_0(X1,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_74])).

cnf(c_0_90,plain,
    ( r1_tarski(X1,k5_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_22])).

cnf(c_0_91,plain,
    ( k4_xboole_0(k2_xboole_0(k5_xboole_0(X1,X2),X1),X1) = k5_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_86])).

cnf(c_0_92,plain,
    ( k2_xboole_0(k5_xboole_0(X1,X1),X1) = X1 ),
    inference(rw,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_93,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_89])).

cnf(c_0_94,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),k5_xboole_0(X1,X2))
    | ~ r1_xboole_0(k2_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_90,c_0_81])).

cnf(c_0_95,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_93]),c_0_81])])).

fof(c_0_96,plain,(
    ! [X38,X39,X40,X41] :
      ( ( ~ r1_xboole_0(X38,X39)
        | r1_xboole_0(k2_zfmisc_1(X38,X40),k2_zfmisc_1(X39,X41)) )
      & ( ~ r1_xboole_0(X40,X41)
        | r1_xboole_0(k2_zfmisc_1(X38,X40),k2_zfmisc_1(X39,X41)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_zfmisc_1])])])).

cnf(c_0_97,plain,
    ( r1_xboole_0(k1_xboole_0,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_23])).

fof(c_0_98,plain,(
    ! [X42,X43,X44] :
      ( ( r2_hidden(X42,X43)
        | ~ r2_hidden(X42,k4_xboole_0(X43,k1_tarski(X44))) )
      & ( X42 != X44
        | ~ r2_hidden(X42,k4_xboole_0(X43,k1_tarski(X44))) )
      & ( ~ r2_hidden(X42,X43)
        | X42 = X44
        | r2_hidden(X42,k4_xboole_0(X43,k1_tarski(X44))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_99,plain,(
    ! [X37] : k1_enumset1(X37,X37,X37) = k1_tarski(X37) ),
    inference(variable_rename,[status(thm)],[t76_enumset1])).

fof(c_0_100,plain,(
    ! [X34,X35,X36] : k2_xboole_0(k2_tarski(X35,X34),k2_tarski(X36,X34)) = k1_enumset1(X34,X35,X36) ),
    inference(variable_rename,[status(thm)],[t137_enumset1])).

cnf(c_0_101,plain,
    ( r1_tarski(X1,k1_xboole_0)
    | ~ r1_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_88]),c_0_95])).

cnf(c_0_102,plain,
    ( r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_103,plain,
    ( r1_xboole_0(k1_xboole_0,X1)
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_97])).

cnf(c_0_104,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_97])).

cnf(c_0_105,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_106,plain,
    ( k1_enumset1(X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_107,plain,
    ( k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X2)) = k1_enumset1(X2,X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

fof(c_0_108,plain,(
    ! [X48,X49,X50] :
      ( ( ~ v5_funct_1(X49,X48)
        | ~ r2_hidden(X50,k1_relat_1(X49))
        | r2_hidden(k1_funct_1(X49,X50),k1_funct_1(X48,X50))
        | ~ v1_relat_1(X49)
        | ~ v1_funct_1(X49)
        | ~ v1_relat_1(X48)
        | ~ v1_funct_1(X48) )
      & ( r2_hidden(esk1_2(X48,X49),k1_relat_1(X49))
        | v5_funct_1(X49,X48)
        | ~ v1_relat_1(X49)
        | ~ v1_funct_1(X49)
        | ~ v1_relat_1(X48)
        | ~ v1_funct_1(X48) )
      & ( ~ r2_hidden(k1_funct_1(X49,esk1_2(X48,X49)),k1_funct_1(X48,esk1_2(X48,X49)))
        | v5_funct_1(X49,X48)
        | ~ v1_relat_1(X49)
        | ~ v1_funct_1(X49)
        | ~ v1_relat_1(X48)
        | ~ v1_funct_1(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_funct_1])])])])])).

fof(c_0_109,plain,(
    ! [X52,X53,X55] :
      ( v1_relat_1(esk2_2(X52,X53))
      & v1_funct_1(esk2_2(X52,X53))
      & k1_relat_1(esk2_2(X52,X53)) = X52
      & ( ~ r2_hidden(X55,X52)
        | k1_funct_1(esk2_2(X52,X53),X55) = X53 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).

fof(c_0_110,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => v5_funct_1(k1_xboole_0,X1) ) ),
    inference(assume_negation,[status(cth)],[t174_funct_1])).

fof(c_0_111,plain,(
    ! [X47] :
      ( ~ v1_relat_1(X47)
      | k3_xboole_0(X47,k2_zfmisc_1(k1_relat_1(X47),k2_relat_1(X47))) = X47 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_relat_1])])).

cnf(c_0_112,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k1_xboole_0)
    | ~ r1_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_113,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_103,c_0_104])])).

cnf(c_0_114,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X2,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_105,c_0_106]),c_0_107])).

cnf(c_0_115,plain,
    ( r2_hidden(esk1_2(X1,X2),k1_relat_1(X2))
    | v5_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_108])).

cnf(c_0_116,plain,
    ( v1_funct_1(esk2_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_109])).

cnf(c_0_117,plain,
    ( k1_relat_1(esk2_2(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_109])).

cnf(c_0_118,plain,
    ( v1_relat_1(esk2_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_109])).

fof(c_0_119,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & ~ v5_funct_1(k1_xboole_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_110])])])).

cnf(c_0_120,plain,
    ( k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_111])).

cnf(c_0_121,plain,
    ( r1_tarski(k2_zfmisc_1(k1_xboole_0,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_122,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1)))) ),
    inference(er,[status(thm)],[c_0_114])).

cnf(c_0_123,plain,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_113])).

cnf(c_0_124,plain,
    ( v5_funct_1(esk2_2(X1,X2),X3)
    | r2_hidden(esk1_2(X3,esk2_2(X1,X2)),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_117]),c_0_118])])).

cnf(c_0_125,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_119])).

cnf(c_0_126,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_119])).

cnf(c_0_127,plain,
    ( k3_xboole_0(esk2_2(X1,X2),k2_zfmisc_1(X1,k2_relat_1(esk2_2(X1,X2)))) = esk2_2(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_118]),c_0_117])).

cnf(c_0_128,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_121])).

cnf(c_0_129,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_122,c_0_123])).

cnf(c_0_130,negated_conjecture,
    ( v5_funct_1(esk2_2(X1,X2),esk3_0)
    | r2_hidden(esk1_2(esk3_0,esk2_2(X1,X2)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_125]),c_0_126])])).

cnf(c_0_131,plain,
    ( esk2_2(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_128]),c_0_23])).

cnf(c_0_132,negated_conjecture,
    ( ~ v5_funct_1(k1_xboole_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_119])).

cnf(c_0_133,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_130]),c_0_131]),c_0_132]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:38:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.77/0.91  # AutoSched0-Mode selected heuristic G_E___208_B01_00_F1_SE_CS_SP_PS_S04AN
% 0.77/0.91  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.77/0.91  #
% 0.77/0.91  # Preprocessing time       : 0.028 s
% 0.77/0.91  # Presaturation interreduction done
% 0.77/0.91  
% 0.77/0.91  # Proof found!
% 0.77/0.91  # SZS status Theorem
% 0.77/0.91  # SZS output start CNFRefutation
% 0.77/0.91  fof(t74_xboole_1, axiom, ![X1, X2, X3]:~((~(r1_xboole_0(X1,k3_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_xboole_1)).
% 0.77/0.91  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.77/0.91  fof(t89_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_xboole_1)).
% 0.77/0.91  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.77/0.91  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.77/0.92  fof(t111_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k4_xboole_0(X1,X3),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_xboole_1)).
% 0.77/0.92  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 0.77/0.92  fof(t88_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>k4_xboole_0(k2_xboole_0(X1,X2),X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_xboole_1)).
% 0.77/0.92  fof(t93_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_xboole_1)).
% 0.77/0.92  fof(t52_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 0.77/0.92  fof(t84_xboole_1, axiom, ![X1, X2, X3]:~(((~(r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3))&r1_xboole_0(X1,k4_xboole_0(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_xboole_1)).
% 0.77/0.92  fof(t107_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k5_xboole_0(X2,X3))<=>(r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,k3_xboole_0(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_xboole_1)).
% 0.77/0.92  fof(t127_zfmisc_1, axiom, ![X1, X2, X3, X4]:((r1_xboole_0(X1,X2)|r1_xboole_0(X3,X4))=>r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 0.77/0.92  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.77/0.92  fof(t76_enumset1, axiom, ![X1]:k1_enumset1(X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_enumset1)).
% 0.77/0.92  fof(t137_enumset1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1))=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 0.77/0.92  fof(d20_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v5_funct_1(X2,X1)<=>![X3]:(r2_hidden(X3,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X3),k1_funct_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_funct_1)).
% 0.77/0.92  fof(s3_funct_1__e2_24__funct_1, axiom, ![X1, X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&![X4]:(r2_hidden(X4,X1)=>k1_funct_1(X3,X4)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 0.77/0.92  fof(t174_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>v5_funct_1(k1_xboole_0,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_funct_1)).
% 0.77/0.92  fof(t22_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relat_1)).
% 0.77/0.92  fof(c_0_20, plain, ![X20, X21, X22]:(r1_xboole_0(X20,k3_xboole_0(X21,X22))|~r1_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t74_xboole_1])])])).
% 0.77/0.92  fof(c_0_21, plain, ![X13]:k3_xboole_0(X13,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.77/0.92  cnf(c_0_22, plain, (r1_xboole_0(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.77/0.92  cnf(c_0_23, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.77/0.92  fof(c_0_24, plain, ![X30, X31]:r1_xboole_0(k3_xboole_0(X30,X31),k4_xboole_0(X30,X31)), inference(variable_rename,[status(thm)],[t89_xboole_1])).
% 0.77/0.92  cnf(c_0_25, plain, (r1_xboole_0(X1,k1_xboole_0)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.77/0.92  cnf(c_0_26, plain, (r1_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.77/0.92  fof(c_0_27, plain, ![X11, X12]:(~r1_tarski(X11,X12)|k3_xboole_0(X11,X12)=X11), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.77/0.92  cnf(c_0_28, plain, (r1_xboole_0(k3_xboole_0(X1,X2),k1_xboole_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.77/0.92  cnf(c_0_29, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.77/0.92  fof(c_0_30, plain, ![X23, X24]:r1_tarski(X23,k2_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.77/0.92  fof(c_0_31, plain, ![X8, X9, X10]:k4_xboole_0(k3_xboole_0(X8,X9),k3_xboole_0(X10,X9))=k3_xboole_0(k4_xboole_0(X8,X10),X9), inference(variable_rename,[status(thm)],[t111_xboole_1])).
% 0.77/0.92  fof(c_0_32, plain, ![X14, X15, X16]:(~r1_tarski(X14,k2_xboole_0(X15,X16))|r1_tarski(k4_xboole_0(X14,X15),X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 0.77/0.92  fof(c_0_33, plain, ![X28, X29]:(~r1_xboole_0(X28,X29)|k4_xboole_0(k2_xboole_0(X28,X29),X29)=X28), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_xboole_1])])).
% 0.77/0.92  cnf(c_0_34, plain, (r1_xboole_0(X1,k1_xboole_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.77/0.92  cnf(c_0_35, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.77/0.92  fof(c_0_36, plain, ![X32, X33]:k2_xboole_0(X32,X33)=k2_xboole_0(k5_xboole_0(X32,X33),k3_xboole_0(X32,X33)), inference(variable_rename,[status(thm)],[t93_xboole_1])).
% 0.77/0.92  fof(c_0_37, plain, ![X17, X18, X19]:k4_xboole_0(X17,k4_xboole_0(X18,X19))=k2_xboole_0(k4_xboole_0(X17,X18),k3_xboole_0(X17,X19)), inference(variable_rename,[status(thm)],[t52_xboole_1])).
% 0.77/0.92  cnf(c_0_38, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k4_xboole_0(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.77/0.92  fof(c_0_39, plain, ![X25, X26, X27]:(r1_xboole_0(X25,X26)|~r1_xboole_0(X25,X27)|~r1_xboole_0(X25,k4_xboole_0(X26,X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t84_xboole_1])])])).
% 0.77/0.92  cnf(c_0_40, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_23, c_0_29])).
% 0.77/0.92  cnf(c_0_41, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.77/0.92  cnf(c_0_42, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.77/0.92  cnf(c_0_43, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.77/0.92  cnf(c_0_44, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.77/0.92  cnf(c_0_45, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.77/0.92  cnf(c_0_46, plain, (k4_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_38]), c_0_23]), c_0_23])).
% 0.77/0.92  cnf(c_0_47, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)|~r1_xboole_0(X1,k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.77/0.92  cnf(c_0_48, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,k2_xboole_0(X2,k1_xboole_0))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.77/0.92  fof(c_0_49, plain, ![X5, X6, X7]:(((r1_tarski(X5,k2_xboole_0(X6,X7))|~r1_tarski(X5,k5_xboole_0(X6,X7)))&(r1_xboole_0(X5,k3_xboole_0(X6,X7))|~r1_tarski(X5,k5_xboole_0(X6,X7))))&(~r1_tarski(X5,k2_xboole_0(X6,X7))|~r1_xboole_0(X5,k3_xboole_0(X6,X7))|r1_tarski(X5,k5_xboole_0(X6,X7)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t107_xboole_1])])])).
% 0.77/0.92  cnf(c_0_50, plain, (k4_xboole_0(k2_xboole_0(X1,k1_xboole_0),k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.77/0.92  cnf(c_0_51, plain, (k2_xboole_0(k5_xboole_0(X1,k1_xboole_0),k1_xboole_0)=k2_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_44, c_0_23])).
% 0.77/0.92  cnf(c_0_52, plain, (k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.77/0.92  cnf(c_0_53, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k1_xboole_0))=k2_xboole_0(k4_xboole_0(X1,X2),k1_xboole_0)), inference(spm,[status(thm)],[c_0_45, c_0_23])).
% 0.77/0.92  cnf(c_0_54, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)|~r1_tarski(X2,k2_xboole_0(X3,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_43])])).
% 0.77/0.92  cnf(c_0_55, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.77/0.92  cnf(c_0_56, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_50])).
% 0.77/0.92  cnf(c_0_57, plain, (r1_tarski(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_46]), c_0_35])])).
% 0.77/0.92  cnf(c_0_58, plain, (k2_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_23]), c_0_46]), c_0_46])).
% 0.77/0.92  cnf(c_0_59, plain, (k2_xboole_0(k4_xboole_0(X1,k1_xboole_0),k1_xboole_0)=k4_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_53, c_0_46])).
% 0.77/0.92  cnf(c_0_60, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)|~r1_tarski(X2,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])).
% 0.77/0.92  cnf(c_0_61, plain, (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_29]), c_0_57])]), c_0_58])).
% 0.77/0.92  cnf(c_0_62, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_59, c_0_50])).
% 0.77/0.92  cnf(c_0_63, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_60, c_0_43])).
% 0.77/0.92  cnf(c_0_64, plain, (r1_tarski(X1,X2)|~r1_tarski(k2_xboole_0(X1,k1_xboole_0),k2_xboole_0(k1_xboole_0,X2))), inference(spm,[status(thm)],[c_0_41, c_0_50])).
% 0.77/0.92  cnf(c_0_65, plain, (k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(rw,[status(thm)],[c_0_52, c_0_61])).
% 0.77/0.92  cnf(c_0_66, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_48, c_0_62])).
% 0.77/0.92  cnf(c_0_67, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=X1|~r1_tarski(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_42, c_0_63])).
% 0.77/0.92  cnf(c_0_68, plain, (r1_tarski(X1,k3_xboole_0(k1_xboole_0,X2))|~r1_tarski(k2_xboole_0(X1,k1_xboole_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.77/0.92  cnf(c_0_69, plain, (X1=k1_xboole_0|~r1_tarski(k2_xboole_0(X1,X2),X2)|~r1_tarski(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.77/0.92  cnf(c_0_70, plain, (r1_tarski(X1,k3_xboole_0(k1_xboole_0,X2))|~r1_tarski(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_68, c_0_62])).
% 0.77/0.92  cnf(c_0_71, plain, (X1=k1_xboole_0|~r1_tarski(k2_xboole_0(X1,k3_xboole_0(k1_xboole_0,X2)),k1_xboole_0)|~r1_tarski(k3_xboole_0(k1_xboole_0,X2),k1_xboole_0)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.77/0.92  cnf(c_0_72, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0|~r1_tarski(k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)),k1_xboole_0)|~r1_tarski(k3_xboole_0(k1_xboole_0,X2),k1_xboole_0)), inference(spm,[status(thm)],[c_0_71, c_0_45])).
% 0.77/0.92  cnf(c_0_73, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0|~r1_tarski(k3_xboole_0(k1_xboole_0,X2),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_66]), c_0_57]), c_0_57])])).
% 0.77/0.92  cnf(c_0_74, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_50, c_0_62])).
% 0.77/0.92  cnf(c_0_75, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_23]), c_0_57])])).
% 0.77/0.92  cnf(c_0_76, plain, (r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_35, c_0_45])).
% 0.77/0.92  cnf(c_0_77, plain, (r1_xboole_0(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.77/0.92  cnf(c_0_78, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_74]), c_0_75]), c_0_74])).
% 0.77/0.92  cnf(c_0_79, plain, (r1_tarski(k4_xboole_0(X1,X2),k1_xboole_0)|~r1_tarski(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_76, c_0_66])).
% 0.77/0.92  cnf(c_0_80, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k5_xboole_0(X2,X3))|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_77, c_0_29])).
% 0.77/0.92  cnf(c_0_81, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_35, c_0_62])).
% 0.77/0.92  cnf(c_0_82, plain, (k2_xboole_0(k5_xboole_0(X1,X2),X1)=k2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_44, c_0_29])).
% 0.77/0.92  cnf(c_0_83, plain, (k2_xboole_0(X1,X1)=X1|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_78, c_0_29])).
% 0.77/0.92  cnf(c_0_84, plain, (r1_tarski(k4_xboole_0(k4_xboole_0(X1,X2),X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_79, c_0_76])).
% 0.77/0.92  cnf(c_0_85, plain, (r1_tarski(X1,k5_xboole_0(X2,X3))|~r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.77/0.92  cnf(c_0_86, plain, (r1_xboole_0(k5_xboole_0(X1,X2),X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.77/0.92  cnf(c_0_87, plain, (k2_xboole_0(k5_xboole_0(X1,X1),X1)=k2_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_82, c_0_81])).
% 0.77/0.92  cnf(c_0_88, plain, (k2_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_83, c_0_35])).
% 0.77/0.92  cnf(c_0_89, plain, (r1_tarski(k4_xboole_0(X1,X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_84, c_0_74])).
% 0.77/0.92  cnf(c_0_90, plain, (r1_tarski(X1,k5_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_85, c_0_22])).
% 0.77/0.92  cnf(c_0_91, plain, (k4_xboole_0(k2_xboole_0(k5_xboole_0(X1,X2),X1),X1)=k5_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_42, c_0_86])).
% 0.77/0.92  cnf(c_0_92, plain, (k2_xboole_0(k5_xboole_0(X1,X1),X1)=X1), inference(rw,[status(thm)],[c_0_87, c_0_88])).
% 0.77/0.92  cnf(c_0_93, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_40, c_0_89])).
% 0.77/0.92  cnf(c_0_94, plain, (r1_tarski(k2_xboole_0(X1,X2),k5_xboole_0(X1,X2))|~r1_xboole_0(k2_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_90, c_0_81])).
% 0.77/0.92  cnf(c_0_95, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_93]), c_0_81])])).
% 0.77/0.92  fof(c_0_96, plain, ![X38, X39, X40, X41]:((~r1_xboole_0(X38,X39)|r1_xboole_0(k2_zfmisc_1(X38,X40),k2_zfmisc_1(X39,X41)))&(~r1_xboole_0(X40,X41)|r1_xboole_0(k2_zfmisc_1(X38,X40),k2_zfmisc_1(X39,X41)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_zfmisc_1])])])).
% 0.77/0.92  cnf(c_0_97, plain, (r1_xboole_0(k1_xboole_0,k4_xboole_0(X1,k1_xboole_0))), inference(spm,[status(thm)],[c_0_26, c_0_23])).
% 0.77/0.92  fof(c_0_98, plain, ![X42, X43, X44]:(((r2_hidden(X42,X43)|~r2_hidden(X42,k4_xboole_0(X43,k1_tarski(X44))))&(X42!=X44|~r2_hidden(X42,k4_xboole_0(X43,k1_tarski(X44)))))&(~r2_hidden(X42,X43)|X42=X44|r2_hidden(X42,k4_xboole_0(X43,k1_tarski(X44))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 0.77/0.92  fof(c_0_99, plain, ![X37]:k1_enumset1(X37,X37,X37)=k1_tarski(X37), inference(variable_rename,[status(thm)],[t76_enumset1])).
% 0.77/0.92  fof(c_0_100, plain, ![X34, X35, X36]:k2_xboole_0(k2_tarski(X35,X34),k2_tarski(X36,X34))=k1_enumset1(X34,X35,X36), inference(variable_rename,[status(thm)],[t137_enumset1])).
% 0.77/0.92  cnf(c_0_101, plain, (r1_tarski(X1,k1_xboole_0)|~r1_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_88]), c_0_95])).
% 0.77/0.92  cnf(c_0_102, plain, (r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_96])).
% 0.77/0.92  cnf(c_0_103, plain, (r1_xboole_0(k1_xboole_0,X1)|~r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_47, c_0_97])).
% 0.77/0.92  cnf(c_0_104, plain, (r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_25, c_0_97])).
% 0.77/0.92  cnf(c_0_105, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_98])).
% 0.77/0.92  cnf(c_0_106, plain, (k1_enumset1(X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_99])).
% 0.77/0.92  cnf(c_0_107, plain, (k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X2))=k1_enumset1(X2,X1,X3)), inference(split_conjunct,[status(thm)],[c_0_100])).
% 0.77/0.92  fof(c_0_108, plain, ![X48, X49, X50]:((~v5_funct_1(X49,X48)|(~r2_hidden(X50,k1_relat_1(X49))|r2_hidden(k1_funct_1(X49,X50),k1_funct_1(X48,X50)))|(~v1_relat_1(X49)|~v1_funct_1(X49))|(~v1_relat_1(X48)|~v1_funct_1(X48)))&((r2_hidden(esk1_2(X48,X49),k1_relat_1(X49))|v5_funct_1(X49,X48)|(~v1_relat_1(X49)|~v1_funct_1(X49))|(~v1_relat_1(X48)|~v1_funct_1(X48)))&(~r2_hidden(k1_funct_1(X49,esk1_2(X48,X49)),k1_funct_1(X48,esk1_2(X48,X49)))|v5_funct_1(X49,X48)|(~v1_relat_1(X49)|~v1_funct_1(X49))|(~v1_relat_1(X48)|~v1_funct_1(X48))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_funct_1])])])])])).
% 0.77/0.92  fof(c_0_109, plain, ![X52, X53, X55]:(((v1_relat_1(esk2_2(X52,X53))&v1_funct_1(esk2_2(X52,X53)))&k1_relat_1(esk2_2(X52,X53))=X52)&(~r2_hidden(X55,X52)|k1_funct_1(esk2_2(X52,X53),X55)=X53)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).
% 0.77/0.92  fof(c_0_110, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>v5_funct_1(k1_xboole_0,X1))), inference(assume_negation,[status(cth)],[t174_funct_1])).
% 0.77/0.92  fof(c_0_111, plain, ![X47]:(~v1_relat_1(X47)|k3_xboole_0(X47,k2_zfmisc_1(k1_relat_1(X47),k2_relat_1(X47)))=X47), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_relat_1])])).
% 0.77/0.92  cnf(c_0_112, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k1_xboole_0)|~r1_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_101, c_0_102])).
% 0.77/0.92  cnf(c_0_113, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_103, c_0_104])])).
% 0.77/0.92  cnf(c_0_114, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X2,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_105, c_0_106]), c_0_107])).
% 0.77/0.92  cnf(c_0_115, plain, (r2_hidden(esk1_2(X1,X2),k1_relat_1(X2))|v5_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_108])).
% 0.77/0.92  cnf(c_0_116, plain, (v1_funct_1(esk2_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_109])).
% 0.77/0.92  cnf(c_0_117, plain, (k1_relat_1(esk2_2(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_109])).
% 0.77/0.92  cnf(c_0_118, plain, (v1_relat_1(esk2_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_109])).
% 0.77/0.92  fof(c_0_119, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&~v5_funct_1(k1_xboole_0,esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_110])])])).
% 0.77/0.92  cnf(c_0_120, plain, (k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_111])).
% 0.77/0.92  cnf(c_0_121, plain, (r1_tarski(k2_zfmisc_1(k1_xboole_0,X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_112, c_0_113])).
% 0.77/0.92  cnf(c_0_122, plain, (~r2_hidden(X1,k4_xboole_0(X2,k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1))))), inference(er,[status(thm)],[c_0_114])).
% 0.77/0.92  cnf(c_0_123, plain, (k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_42, c_0_113])).
% 0.77/0.92  cnf(c_0_124, plain, (v5_funct_1(esk2_2(X1,X2),X3)|r2_hidden(esk1_2(X3,esk2_2(X1,X2)),X1)|~v1_funct_1(X3)|~v1_relat_1(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116]), c_0_117]), c_0_118])])).
% 0.77/0.92  cnf(c_0_125, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_119])).
% 0.77/0.92  cnf(c_0_126, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_119])).
% 0.77/0.92  cnf(c_0_127, plain, (k3_xboole_0(esk2_2(X1,X2),k2_zfmisc_1(X1,k2_relat_1(esk2_2(X1,X2))))=esk2_2(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_118]), c_0_117])).
% 0.77/0.92  cnf(c_0_128, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_40, c_0_121])).
% 0.77/0.92  cnf(c_0_129, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_122, c_0_123])).
% 0.77/0.92  cnf(c_0_130, negated_conjecture, (v5_funct_1(esk2_2(X1,X2),esk3_0)|r2_hidden(esk1_2(esk3_0,esk2_2(X1,X2)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_125]), c_0_126])])).
% 0.77/0.92  cnf(c_0_131, plain, (esk2_2(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_128]), c_0_23])).
% 0.77/0.92  cnf(c_0_132, negated_conjecture, (~v5_funct_1(k1_xboole_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_119])).
% 0.77/0.92  cnf(c_0_133, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_130]), c_0_131]), c_0_132]), ['proof']).
% 0.77/0.92  # SZS output end CNFRefutation
% 0.77/0.92  # Proof object total steps             : 134
% 0.77/0.92  # Proof object clause steps            : 93
% 0.77/0.92  # Proof object formula steps           : 41
% 0.77/0.92  # Proof object conjectures             : 8
% 0.77/0.92  # Proof object clause conjectures      : 5
% 0.77/0.92  # Proof object formula conjectures     : 3
% 0.77/0.92  # Proof object initial clauses used    : 26
% 0.77/0.92  # Proof object initial formulas used   : 20
% 0.77/0.92  # Proof object generating inferences   : 59
% 0.77/0.92  # Proof object simplifying inferences  : 43
% 0.77/0.92  # Training examples: 0 positive, 0 negative
% 0.77/0.92  # Parsed axioms                        : 21
% 0.77/0.92  # Removed by relevancy pruning/SinE    : 0
% 0.77/0.92  # Initial clauses                      : 33
% 0.77/0.92  # Removed in clause preprocessing      : 2
% 0.77/0.92  # Initial clauses in saturation        : 31
% 0.77/0.92  # Processed clauses                    : 5484
% 0.77/0.92  # ...of these trivial                  : 49
% 0.77/0.92  # ...subsumed                          : 4340
% 0.77/0.92  # ...remaining for further processing  : 1095
% 0.77/0.92  # Other redundant clauses eliminated   : 1
% 0.77/0.92  # Clauses deleted for lack of memory   : 0
% 0.77/0.92  # Backward-subsumed                    : 103
% 0.77/0.92  # Backward-rewritten                   : 211
% 0.77/0.92  # Generated clauses                    : 45886
% 0.77/0.92  # ...of the previous two non-trivial   : 40060
% 0.77/0.92  # Contextual simplify-reflections      : 28
% 0.77/0.92  # Paramodulations                      : 45885
% 0.77/0.92  # Factorizations                       : 0
% 0.77/0.92  # Equation resolutions                 : 1
% 0.77/0.92  # Propositional unsat checks           : 0
% 0.77/0.92  #    Propositional check models        : 0
% 0.77/0.92  #    Propositional check unsatisfiable : 0
% 0.77/0.92  #    Propositional clauses             : 0
% 0.77/0.92  #    Propositional clauses after purity: 0
% 0.77/0.92  #    Propositional unsat core size     : 0
% 0.77/0.92  #    Propositional preprocessing time  : 0.000
% 0.77/0.92  #    Propositional encoding time       : 0.000
% 0.77/0.92  #    Propositional solver time         : 0.000
% 0.77/0.92  #    Success case prop preproc time    : 0.000
% 0.77/0.92  #    Success case prop encoding time   : 0.000
% 0.77/0.92  #    Success case prop solver time     : 0.000
% 0.77/0.92  # Current number of processed clauses  : 749
% 0.77/0.92  #    Positive orientable unit clauses  : 102
% 0.77/0.92  #    Positive unorientable unit clauses: 4
% 0.77/0.92  #    Negative unit clauses             : 3
% 0.77/0.92  #    Non-unit-clauses                  : 640
% 0.77/0.92  # Current number of unprocessed clauses: 34016
% 0.77/0.92  # ...number of literals in the above   : 92958
% 0.77/0.92  # Current number of archived formulas  : 0
% 0.77/0.92  # Current number of archived clauses   : 347
% 0.77/0.92  # Clause-clause subsumption calls (NU) : 100357
% 0.77/0.92  # Rec. Clause-clause subsumption calls : 44578
% 0.77/0.92  # Non-unit clause-clause subsumptions  : 4269
% 0.77/0.92  # Unit Clause-clause subsumption calls : 306
% 0.77/0.92  # Rewrite failures with RHS unbound    : 0
% 0.77/0.92  # BW rewrite match attempts            : 371
% 0.77/0.92  # BW rewrite match successes           : 83
% 0.77/0.92  # Condensation attempts                : 0
% 0.77/0.92  # Condensation successes               : 0
% 0.77/0.92  # Termbank termtop insertions          : 830894
% 0.77/0.92  
% 0.77/0.92  # -------------------------------------------------
% 0.77/0.92  # User time                : 0.544 s
% 0.77/0.92  # System time              : 0.034 s
% 0.77/0.92  # Total time               : 0.578 s
% 0.77/0.92  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
