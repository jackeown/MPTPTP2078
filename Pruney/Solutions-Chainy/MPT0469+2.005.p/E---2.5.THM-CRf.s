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
% DateTime   : Thu Dec  3 10:48:46 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 726 expanded)
%              Number of clauses        :   59 ( 369 expanded)
%              Number of leaves         :   21 ( 209 expanded)
%              Depth                    :   10
%              Number of atoms          :  170 (1213 expanded)
%              Number of equality atoms :  108 ( 671 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(cc1_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(t24_relat_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( v1_relat_1(X5)
     => ( X5 = k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4))
       => ( k1_relat_1(X5) = k2_tarski(X1,X3)
          & k2_relat_1(X5) = k2_tarski(X2,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_relat_1)).

fof(fc7_relat_1,axiom,(
    ! [X1,X2,X3,X4] : v1_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_relat_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t13_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k2_xboole_0(X1,X2)) = k2_xboole_0(k1_relat_1(X1),k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relat_1)).

fof(dt_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(t37_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
        & k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(t60_relat_1,conjecture,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(t22_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(c_0_21,plain,(
    ! [X25] :
      ( ~ v1_xboole_0(X25)
      | v1_relat_1(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).

cnf(c_0_22,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_23,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(split_conjunct,[status(thm)],[d2_xboole_0])).

fof(c_0_24,plain,(
    ! [X10] : k2_xboole_0(X10,k1_xboole_0) = X10 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_25,plain,(
    ! [X34,X35,X36,X37,X38] :
      ( ( k1_relat_1(X38) = k2_tarski(X34,X36)
        | X38 != k2_tarski(k4_tarski(X34,X35),k4_tarski(X36,X37))
        | ~ v1_relat_1(X38) )
      & ( k2_relat_1(X38) = k2_tarski(X35,X37)
        | X38 != k2_tarski(k4_tarski(X34,X35),k4_tarski(X36,X37))
        | ~ v1_relat_1(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_relat_1])])])).

fof(c_0_26,plain,(
    ! [X27,X28,X29,X30] : v1_relat_1(k2_tarski(k4_tarski(X27,X28),k4_tarski(X29,X30))) ),
    inference(variable_rename,[status(thm)],[fc7_relat_1])).

fof(c_0_27,plain,(
    ! [X12,X13] : k4_xboole_0(X12,k2_xboole_0(X12,X13)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_28,plain,(
    ! [X31,X32] :
      ( ~ v1_relat_1(X31)
      | ~ v1_relat_1(X32)
      | k1_relat_1(k2_xboole_0(X31,X32)) = k2_xboole_0(k1_relat_1(X31),k1_relat_1(X32)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relat_1])])])).

cnf(c_0_29,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_32,plain,(
    ! [X26] :
      ( ~ v1_relat_1(X26)
      | v1_relat_1(k4_relat_1(X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).

fof(c_0_33,plain,(
    ! [X39] :
      ( ( k2_relat_1(X39) = k1_relat_1(k4_relat_1(X39))
        | ~ v1_relat_1(X39) )
      & ( k1_relat_1(X39) = k2_relat_1(k4_relat_1(X39))
        | ~ v1_relat_1(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).

cnf(c_0_34,plain,
    ( k2_relat_1(X1) = k2_tarski(X2,X3)
    | X1 != k2_tarski(k4_tarski(X4,X2),k4_tarski(X5,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( v1_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_36,plain,(
    ! [X20,X21,X22] :
      ( ( r2_hidden(X20,X21)
        | ~ r2_hidden(X20,k4_xboole_0(X21,k1_tarski(X22))) )
      & ( X20 != X22
        | ~ r2_hidden(X20,k4_xboole_0(X21,k1_tarski(X22))) )
      & ( ~ r2_hidden(X20,X21)
        | X20 = X22
        | r2_hidden(X20,k4_xboole_0(X21,k1_tarski(X22))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_37,plain,(
    ! [X15] : k2_tarski(X15,X15) = k1_tarski(X15) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_38,plain,(
    ! [X18,X19] : k2_xboole_0(k1_tarski(X18),X19) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

fof(c_0_39,plain,(
    ! [X8] :
      ( X8 = k1_xboole_0
      | r2_hidden(esk1_1(X8),X8) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_41,plain,(
    ! [X6,X7] : k2_xboole_0(X6,X7) = k2_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_42,plain,
    ( k1_relat_1(k2_xboole_0(X1,X2)) = k2_xboole_0(k1_relat_1(X1),k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_43,plain,
    ( v1_relat_1(o_0_0_xboole_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_44,plain,
    ( k2_xboole_0(X1,o_0_0_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_31,c_0_23])).

cnf(c_0_45,plain,
    ( v1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_46,plain,
    ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_47,plain,
    ( k2_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4))) = k2_tarski(X2,X4) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_34]),c_0_35])])).

cnf(c_0_48,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_49,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_50,plain,(
    ! [X14] : k4_xboole_0(k1_xboole_0,X14) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

fof(c_0_51,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t60_relat_1])).

cnf(c_0_52,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_53,plain,
    ( X1 = X3
    | r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_54,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_55,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[c_0_40,c_0_23])).

cnf(c_0_56,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_57,plain,
    ( k2_xboole_0(k1_relat_1(X1),k1_relat_1(o_0_0_xboole_0)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_58,plain,
    ( v1_relat_1(k4_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4)))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_35])).

cnf(c_0_59,plain,
    ( k1_relat_1(k4_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4)))) = k2_tarski(X2,X4) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_35]),c_0_47])).

cnf(c_0_60,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k2_tarski(X2,X2))) ),
    inference(rw,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_61,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_62,negated_conjecture,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(fof_nnf,[status(thm)],[c_0_51])).

cnf(c_0_63,plain,
    ( k2_xboole_0(k2_tarski(X1,X1),X2) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_52,c_0_49])).

cnf(c_0_64,plain,
    ( X1 = X3
    | r2_hidden(X1,k4_xboole_0(X2,k2_tarski(X3,X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_53,c_0_49])).

cnf(c_0_65,plain,
    ( X1 = o_0_0_xboole_0
    | r2_hidden(esk1_1(X1),X1) ),
    inference(rw,[status(thm)],[c_0_54,c_0_23])).

cnf(c_0_66,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_67,plain,
    ( k2_xboole_0(k2_tarski(X1,X2),k1_relat_1(o_0_0_xboole_0)) = k2_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59]),c_0_59])).

cnf(c_0_68,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k2_tarski(X1,X1))) ),
    inference(er,[status(thm)],[c_0_60])).

cnf(c_0_69,plain,
    ( k4_xboole_0(o_0_0_xboole_0,X1) = o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_23]),c_0_23])).

fof(c_0_70,plain,(
    ! [X33] :
      ( ~ v1_relat_1(X33)
      | k3_xboole_0(X33,k2_zfmisc_1(k1_relat_1(X33),k2_relat_1(X33))) = X33 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_relat_1])])).

fof(c_0_71,plain,(
    ! [X23,X24] : k1_setfam_1(k2_tarski(X23,X24)) = k3_xboole_0(X23,X24) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_72,plain,(
    ! [X11] : k3_xboole_0(X11,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_73,negated_conjecture,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_74,plain,
    ( k2_xboole_0(k2_tarski(X1,X1),X2) != o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[c_0_63,c_0_23])).

cnf(c_0_75,plain,
    ( esk1_1(X1) = X2
    | X1 = o_0_0_xboole_0
    | r2_hidden(esk1_1(X1),k4_xboole_0(X1,k2_tarski(X2,X2))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_76,plain,
    ( k4_xboole_0(k1_relat_1(o_0_0_xboole_0),k2_tarski(X1,X2)) = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_77,plain,
    ( ~ r2_hidden(X1,o_0_0_xboole_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_78,plain,
    ( k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_79,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_80,plain,
    ( k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_81,plain,(
    ! [X16,X17] :
      ( ( k2_zfmisc_1(X16,X17) != k1_xboole_0
        | X16 = k1_xboole_0
        | X17 = k1_xboole_0 )
      & ( X16 != k1_xboole_0
        | k2_zfmisc_1(X16,X17) = k1_xboole_0 )
      & ( X17 != k1_xboole_0
        | k2_zfmisc_1(X16,X17) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_82,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_83,negated_conjecture,
    ( k1_relat_1(o_0_0_xboole_0) != o_0_0_xboole_0
    | k2_relat_1(o_0_0_xboole_0) != o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_23]),c_0_23]),c_0_23]),c_0_23])).

cnf(c_0_84,plain,
    ( k2_relat_1(o_0_0_xboole_0) = k1_relat_1(k4_relat_1(o_0_0_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_43])).

cnf(c_0_85,plain,
    ( k2_tarski(X1,X1) != o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_74,c_0_44])).

cnf(c_0_86,plain,
    ( esk1_1(k1_relat_1(o_0_0_xboole_0)) = X1
    | k1_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77])).

cnf(c_0_87,plain,
    ( k1_setfam_1(k2_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) = X1
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_88,plain,
    ( v1_relat_1(k4_relat_1(o_0_0_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_43])).

cnf(c_0_89,plain,
    ( k2_relat_1(k4_relat_1(o_0_0_xboole_0)) = k1_relat_1(o_0_0_xboole_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_43])).

cnf(c_0_90,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_91,plain,
    ( k1_setfam_1(k2_tarski(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_82,c_0_79])).

cnf(c_0_92,negated_conjecture,
    ( k1_relat_1(k4_relat_1(o_0_0_xboole_0)) != o_0_0_xboole_0
    | k1_relat_1(o_0_0_xboole_0) != o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_93,plain,
    ( k1_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_86])).

cnf(c_0_94,plain,
    ( k1_setfam_1(k2_tarski(k4_relat_1(o_0_0_xboole_0),k2_zfmisc_1(k1_relat_1(k4_relat_1(o_0_0_xboole_0)),k1_relat_1(o_0_0_xboole_0)))) = k4_relat_1(o_0_0_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_89])).

cnf(c_0_95,plain,
    ( k2_zfmisc_1(X1,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(er,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_23]),c_0_23])])).

cnf(c_0_96,plain,
    ( k1_setfam_1(k2_tarski(X1,o_0_0_xboole_0)) = o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_23]),c_0_23])).

cnf(c_0_97,negated_conjecture,
    ( k1_relat_1(k4_relat_1(o_0_0_xboole_0)) != o_0_0_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_93])])).

cnf(c_0_98,plain,
    ( k4_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_93]),c_0_95]),c_0_96])).

cnf(c_0_99,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97,c_0_98]),c_0_93])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:57:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_B00_00_F1_SE_CS_SP_PS_S071I
% 0.19/0.37  # and selection function SelectCQArEqLast.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.027 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(cc1_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 0.19/0.37  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.37  fof(d2_xboole_0, axiom, k1_xboole_0=o_0_0_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_xboole_0)).
% 0.19/0.37  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.19/0.37  fof(t24_relat_1, axiom, ![X1, X2, X3, X4, X5]:(v1_relat_1(X5)=>(X5=k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4))=>(k1_relat_1(X5)=k2_tarski(X1,X3)&k2_relat_1(X5)=k2_tarski(X2,X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_relat_1)).
% 0.19/0.37  fof(fc7_relat_1, axiom, ![X1, X2, X3, X4]:v1_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_relat_1)).
% 0.19/0.37  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.19/0.37  fof(t13_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k2_xboole_0(X1,X2))=k2_xboole_0(k1_relat_1(X1),k1_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relat_1)).
% 0.19/0.37  fof(dt_k4_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>v1_relat_1(k4_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 0.19/0.37  fof(t37_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k4_relat_1(X1))&k1_relat_1(X1)=k2_relat_1(k4_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 0.19/0.37  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.19/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.37  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.19/0.37  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.19/0.37  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.19/0.37  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 0.19/0.37  fof(t60_relat_1, conjecture, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.19/0.37  fof(t22_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relat_1)).
% 0.19/0.37  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.19/0.37  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.19/0.37  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.37  fof(c_0_21, plain, ![X25]:(~v1_xboole_0(X25)|v1_relat_1(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).
% 0.19/0.37  cnf(c_0_22, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.37  cnf(c_0_23, plain, (k1_xboole_0=o_0_0_xboole_0), inference(split_conjunct,[status(thm)],[d2_xboole_0])).
% 0.19/0.37  fof(c_0_24, plain, ![X10]:k2_xboole_0(X10,k1_xboole_0)=X10, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.19/0.37  fof(c_0_25, plain, ![X34, X35, X36, X37, X38]:((k1_relat_1(X38)=k2_tarski(X34,X36)|X38!=k2_tarski(k4_tarski(X34,X35),k4_tarski(X36,X37))|~v1_relat_1(X38))&(k2_relat_1(X38)=k2_tarski(X35,X37)|X38!=k2_tarski(k4_tarski(X34,X35),k4_tarski(X36,X37))|~v1_relat_1(X38))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_relat_1])])])).
% 0.19/0.37  fof(c_0_26, plain, ![X27, X28, X29, X30]:v1_relat_1(k2_tarski(k4_tarski(X27,X28),k4_tarski(X29,X30))), inference(variable_rename,[status(thm)],[fc7_relat_1])).
% 0.19/0.37  fof(c_0_27, plain, ![X12, X13]:k4_xboole_0(X12,k2_xboole_0(X12,X13))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.19/0.37  fof(c_0_28, plain, ![X31, X32]:(~v1_relat_1(X31)|(~v1_relat_1(X32)|k1_relat_1(k2_xboole_0(X31,X32))=k2_xboole_0(k1_relat_1(X31),k1_relat_1(X32)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relat_1])])])).
% 0.19/0.37  cnf(c_0_29, plain, (v1_relat_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.37  cnf(c_0_30, plain, (v1_xboole_0(o_0_0_xboole_0)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.37  cnf(c_0_31, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.37  fof(c_0_32, plain, ![X26]:(~v1_relat_1(X26)|v1_relat_1(k4_relat_1(X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).
% 0.19/0.37  fof(c_0_33, plain, ![X39]:((k2_relat_1(X39)=k1_relat_1(k4_relat_1(X39))|~v1_relat_1(X39))&(k1_relat_1(X39)=k2_relat_1(k4_relat_1(X39))|~v1_relat_1(X39))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).
% 0.19/0.37  cnf(c_0_34, plain, (k2_relat_1(X1)=k2_tarski(X2,X3)|X1!=k2_tarski(k4_tarski(X4,X2),k4_tarski(X5,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.37  cnf(c_0_35, plain, (v1_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.37  fof(c_0_36, plain, ![X20, X21, X22]:(((r2_hidden(X20,X21)|~r2_hidden(X20,k4_xboole_0(X21,k1_tarski(X22))))&(X20!=X22|~r2_hidden(X20,k4_xboole_0(X21,k1_tarski(X22)))))&(~r2_hidden(X20,X21)|X20=X22|r2_hidden(X20,k4_xboole_0(X21,k1_tarski(X22))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 0.19/0.37  fof(c_0_37, plain, ![X15]:k2_tarski(X15,X15)=k1_tarski(X15), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.37  fof(c_0_38, plain, ![X18, X19]:k2_xboole_0(k1_tarski(X18),X19)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 0.19/0.37  fof(c_0_39, plain, ![X8]:(X8=k1_xboole_0|r2_hidden(esk1_1(X8),X8)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.19/0.37  cnf(c_0_40, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.37  fof(c_0_41, plain, ![X6, X7]:k2_xboole_0(X6,X7)=k2_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.19/0.37  cnf(c_0_42, plain, (k1_relat_1(k2_xboole_0(X1,X2))=k2_xboole_0(k1_relat_1(X1),k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.37  cnf(c_0_43, plain, (v1_relat_1(o_0_0_xboole_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.37  cnf(c_0_44, plain, (k2_xboole_0(X1,o_0_0_xboole_0)=X1), inference(rw,[status(thm)],[c_0_31, c_0_23])).
% 0.19/0.37  cnf(c_0_45, plain, (v1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.37  cnf(c_0_46, plain, (k2_relat_1(X1)=k1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.37  cnf(c_0_47, plain, (k2_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4)))=k2_tarski(X2,X4)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_34]), c_0_35])])).
% 0.19/0.37  cnf(c_0_48, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.37  cnf(c_0_49, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.37  fof(c_0_50, plain, ![X14]:k4_xboole_0(k1_xboole_0,X14)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.19/0.37  fof(c_0_51, negated_conjecture, ~((k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0)), inference(assume_negation,[status(cth)],[t60_relat_1])).
% 0.19/0.37  cnf(c_0_52, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.37  cnf(c_0_53, plain, (X1=X3|r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.37  cnf(c_0_54, plain, (X1=k1_xboole_0|r2_hidden(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.37  cnf(c_0_55, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=o_0_0_xboole_0), inference(rw,[status(thm)],[c_0_40, c_0_23])).
% 0.19/0.37  cnf(c_0_56, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.37  cnf(c_0_57, plain, (k2_xboole_0(k1_relat_1(X1),k1_relat_1(o_0_0_xboole_0))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])).
% 0.19/0.37  cnf(c_0_58, plain, (v1_relat_1(k4_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4))))), inference(spm,[status(thm)],[c_0_45, c_0_35])).
% 0.19/0.37  cnf(c_0_59, plain, (k1_relat_1(k4_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4))))=k2_tarski(X2,X4)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_35]), c_0_47])).
% 0.19/0.37  cnf(c_0_60, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k2_tarski(X2,X2)))), inference(rw,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.37  cnf(c_0_61, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.37  fof(c_0_62, negated_conjecture, (k1_relat_1(k1_xboole_0)!=k1_xboole_0|k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(fof_nnf,[status(thm)],[c_0_51])).
% 0.19/0.37  cnf(c_0_63, plain, (k2_xboole_0(k2_tarski(X1,X1),X2)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_52, c_0_49])).
% 0.19/0.37  cnf(c_0_64, plain, (X1=X3|r2_hidden(X1,k4_xboole_0(X2,k2_tarski(X3,X3)))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_53, c_0_49])).
% 0.19/0.37  cnf(c_0_65, plain, (X1=o_0_0_xboole_0|r2_hidden(esk1_1(X1),X1)), inference(rw,[status(thm)],[c_0_54, c_0_23])).
% 0.19/0.37  cnf(c_0_66, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=o_0_0_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.19/0.37  cnf(c_0_67, plain, (k2_xboole_0(k2_tarski(X1,X2),k1_relat_1(o_0_0_xboole_0))=k2_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59]), c_0_59])).
% 0.19/0.37  cnf(c_0_68, plain, (~r2_hidden(X1,k4_xboole_0(X2,k2_tarski(X1,X1)))), inference(er,[status(thm)],[c_0_60])).
% 0.19/0.37  cnf(c_0_69, plain, (k4_xboole_0(o_0_0_xboole_0,X1)=o_0_0_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_23]), c_0_23])).
% 0.19/0.37  fof(c_0_70, plain, ![X33]:(~v1_relat_1(X33)|k3_xboole_0(X33,k2_zfmisc_1(k1_relat_1(X33),k2_relat_1(X33)))=X33), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_relat_1])])).
% 0.19/0.38  fof(c_0_71, plain, ![X23, X24]:k1_setfam_1(k2_tarski(X23,X24))=k3_xboole_0(X23,X24), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.19/0.38  fof(c_0_72, plain, ![X11]:k3_xboole_0(X11,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.19/0.38  cnf(c_0_73, negated_conjecture, (k1_relat_1(k1_xboole_0)!=k1_xboole_0|k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.38  cnf(c_0_74, plain, (k2_xboole_0(k2_tarski(X1,X1),X2)!=o_0_0_xboole_0), inference(rw,[status(thm)],[c_0_63, c_0_23])).
% 0.19/0.38  cnf(c_0_75, plain, (esk1_1(X1)=X2|X1=o_0_0_xboole_0|r2_hidden(esk1_1(X1),k4_xboole_0(X1,k2_tarski(X2,X2)))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.19/0.38  cnf(c_0_76, plain, (k4_xboole_0(k1_relat_1(o_0_0_xboole_0),k2_tarski(X1,X2))=o_0_0_xboole_0), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.19/0.38  cnf(c_0_77, plain, (~r2_hidden(X1,o_0_0_xboole_0)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.19/0.38  cnf(c_0_78, plain, (k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.19/0.38  cnf(c_0_79, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.19/0.38  cnf(c_0_80, plain, (k1_relat_1(X1)=k2_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.38  fof(c_0_81, plain, ![X16, X17]:((k2_zfmisc_1(X16,X17)!=k1_xboole_0|(X16=k1_xboole_0|X17=k1_xboole_0))&((X16!=k1_xboole_0|k2_zfmisc_1(X16,X17)=k1_xboole_0)&(X17!=k1_xboole_0|k2_zfmisc_1(X16,X17)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.19/0.38  cnf(c_0_82, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.19/0.38  cnf(c_0_83, negated_conjecture, (k1_relat_1(o_0_0_xboole_0)!=o_0_0_xboole_0|k2_relat_1(o_0_0_xboole_0)!=o_0_0_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_23]), c_0_23]), c_0_23]), c_0_23])).
% 0.19/0.38  cnf(c_0_84, plain, (k2_relat_1(o_0_0_xboole_0)=k1_relat_1(k4_relat_1(o_0_0_xboole_0))), inference(spm,[status(thm)],[c_0_46, c_0_43])).
% 0.19/0.38  cnf(c_0_85, plain, (k2_tarski(X1,X1)!=o_0_0_xboole_0), inference(spm,[status(thm)],[c_0_74, c_0_44])).
% 0.19/0.38  cnf(c_0_86, plain, (esk1_1(k1_relat_1(o_0_0_xboole_0))=X1|k1_relat_1(o_0_0_xboole_0)=o_0_0_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77])).
% 0.19/0.38  cnf(c_0_87, plain, (k1_setfam_1(k2_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))=X1|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_78, c_0_79])).
% 0.19/0.38  cnf(c_0_88, plain, (v1_relat_1(k4_relat_1(o_0_0_xboole_0))), inference(spm,[status(thm)],[c_0_45, c_0_43])).
% 0.19/0.38  cnf(c_0_89, plain, (k2_relat_1(k4_relat_1(o_0_0_xboole_0))=k1_relat_1(o_0_0_xboole_0)), inference(spm,[status(thm)],[c_0_80, c_0_43])).
% 0.19/0.38  cnf(c_0_90, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.19/0.38  cnf(c_0_91, plain, (k1_setfam_1(k2_tarski(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_82, c_0_79])).
% 0.19/0.38  cnf(c_0_92, negated_conjecture, (k1_relat_1(k4_relat_1(o_0_0_xboole_0))!=o_0_0_xboole_0|k1_relat_1(o_0_0_xboole_0)!=o_0_0_xboole_0), inference(rw,[status(thm)],[c_0_83, c_0_84])).
% 0.19/0.38  cnf(c_0_93, plain, (k1_relat_1(o_0_0_xboole_0)=o_0_0_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_86])).
% 0.19/0.38  cnf(c_0_94, plain, (k1_setfam_1(k2_tarski(k4_relat_1(o_0_0_xboole_0),k2_zfmisc_1(k1_relat_1(k4_relat_1(o_0_0_xboole_0)),k1_relat_1(o_0_0_xboole_0))))=k4_relat_1(o_0_0_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_89])).
% 0.19/0.38  cnf(c_0_95, plain, (k2_zfmisc_1(X1,o_0_0_xboole_0)=o_0_0_xboole_0), inference(er,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_23]), c_0_23])])).
% 0.19/0.38  cnf(c_0_96, plain, (k1_setfam_1(k2_tarski(X1,o_0_0_xboole_0))=o_0_0_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_23]), c_0_23])).
% 0.19/0.38  cnf(c_0_97, negated_conjecture, (k1_relat_1(k4_relat_1(o_0_0_xboole_0))!=o_0_0_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_93])])).
% 0.19/0.38  cnf(c_0_98, plain, (k4_relat_1(o_0_0_xboole_0)=o_0_0_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_93]), c_0_95]), c_0_96])).
% 0.19/0.38  cnf(c_0_99, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97, c_0_98]), c_0_93])]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 100
% 0.19/0.38  # Proof object clause steps            : 59
% 0.19/0.38  # Proof object formula steps           : 41
% 0.19/0.38  # Proof object conjectures             : 8
% 0.19/0.38  # Proof object clause conjectures      : 5
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 23
% 0.19/0.38  # Proof object initial formulas used   : 21
% 0.19/0.38  # Proof object generating inferences   : 16
% 0.19/0.38  # Proof object simplifying inferences  : 41
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 21
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 27
% 0.19/0.38  # Removed in clause preprocessing      : 2
% 0.19/0.38  # Initial clauses in saturation        : 25
% 0.19/0.38  # Processed clauses                    : 126
% 0.19/0.38  # ...of these trivial                  : 5
% 0.19/0.38  # ...subsumed                          : 10
% 0.19/0.38  # ...remaining for further processing  : 111
% 0.19/0.38  # Other redundant clauses eliminated   : 5
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 38
% 0.19/0.38  # Generated clauses                    : 284
% 0.19/0.38  # ...of the previous two non-trivial   : 264
% 0.19/0.38  # Contextual simplify-reflections      : 1
% 0.19/0.38  # Paramodulations                      : 279
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 5
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 43
% 0.19/0.38  #    Positive orientable unit clauses  : 23
% 0.19/0.38  #    Positive unorientable unit clauses: 1
% 0.19/0.38  #    Negative unit clauses             : 5
% 0.19/0.38  #    Non-unit-clauses                  : 14
% 0.19/0.38  # Current number of unprocessed clauses: 188
% 0.19/0.38  # ...number of literals in the above   : 296
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 65
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 80
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 67
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 1
% 0.19/0.38  # Unit Clause-clause subsumption calls : 54
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 65
% 0.19/0.38  # BW rewrite match successes           : 15
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 5548
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.034 s
% 0.19/0.38  # System time              : 0.003 s
% 0.19/0.38  # Total time               : 0.038 s
% 0.19/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
