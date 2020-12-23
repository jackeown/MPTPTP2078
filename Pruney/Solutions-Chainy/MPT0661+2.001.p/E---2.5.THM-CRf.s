%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:10 EST 2020

% Result     : Theorem 0.16s
% Output     : CNFRefutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :  122 (11437 expanded)
%              Number of clauses        :   75 (4707 expanded)
%              Number of leaves         :   23 (3135 expanded)
%              Depth                    :   22
%              Number of atoms          :  279 (24848 expanded)
%              Number of equality atoms :  116 (12977 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t68_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( ( k1_relat_1(X2) = k3_xboole_0(k1_relat_1(X3),X1)
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X2))
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) )
           => X2 = k7_relat_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_funct_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t100_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(k7_relat_1(X3,X1),X2) = k7_relat_1(X3,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(t98_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t189_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k7_relat_1(X1,k1_relat_1(X2)) = k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,k1_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_relat_1)).

fof(t89_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(t91_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => k1_relat_1(k7_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(t87_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(t101_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X1),X1) = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_relat_1)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(t38_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,k3_xboole_0(k1_relat_1(X3),X2))
       => k1_funct_1(X3,X1) = k1_funct_1(k5_relat_1(k6_relat_1(X2),X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_1)).

fof(t78_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(t200_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( r1_tarski(k2_relat_1(X2),k1_relat_1(k7_relat_1(X3,X1)))
           => k5_relat_1(X2,k7_relat_1(X3,X1)) = k5_relat_1(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t200_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( k1_relat_1(X1) = k1_relat_1(X2)
              & ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

fof(fc8_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k7_relat_1(X1,X2))
        & v1_funct_1(k7_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( v1_relat_1(X3)
              & v1_funct_1(X3) )
           => ( ( k1_relat_1(X2) = k3_xboole_0(k1_relat_1(X3),X1)
                & ! [X4] :
                    ( r2_hidden(X4,k1_relat_1(X2))
                   => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) )
             => X2 = k7_relat_1(X3,X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t68_funct_1])).

fof(c_0_24,plain,(
    ! [X14,X15] : k1_setfam_1(k2_tarski(X14,X15)) = k3_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_25,plain,(
    ! [X9,X10] : k1_enumset1(X9,X9,X10) = k2_tarski(X9,X10) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_26,negated_conjecture,(
    ! [X53] :
      ( v1_relat_1(esk3_0)
      & v1_funct_1(esk3_0)
      & v1_relat_1(esk4_0)
      & v1_funct_1(esk4_0)
      & k1_relat_1(esk3_0) = k3_xboole_0(k1_relat_1(esk4_0),esk2_0)
      & ( ~ r2_hidden(X53,k1_relat_1(esk3_0))
        | k1_funct_1(esk3_0,X53) = k1_funct_1(esk4_0,X53) )
      & esk3_0 != k7_relat_1(esk4_0,esk2_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])])).

cnf(c_0_27,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_29,plain,(
    ! [X11,X12,X13] : k2_enumset1(X11,X11,X12,X13) = k1_enumset1(X11,X12,X13) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_30,plain,(
    ! [X7,X8] : k2_tarski(X7,X8) = k2_tarski(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_31,plain,(
    ! [X18,X19,X20] :
      ( ~ v1_relat_1(X20)
      | k7_relat_1(k7_relat_1(X20,X18),X19) = k7_relat_1(X20,k3_xboole_0(X18,X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).

cnf(c_0_32,negated_conjecture,
    ( k1_relat_1(esk3_0) = k3_xboole_0(k1_relat_1(esk4_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( k1_relat_1(esk3_0) = k1_setfam_1(k2_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),k1_relat_1(esk4_0),esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

cnf(c_0_38,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_enumset1(X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_28]),c_0_28]),c_0_34]),c_0_34])).

fof(c_0_39,plain,(
    ! [X40] :
      ( ~ v1_relat_1(X40)
      | k7_relat_1(X40,k1_relat_1(X40)) = X40 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).

fof(c_0_40,plain,(
    ! [X28] :
      ( k1_relat_1(k6_relat_1(X28)) = X28
      & k2_relat_1(k6_relat_1(X28)) = X28 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_41,plain,(
    ! [X41] :
      ( v1_relat_1(k6_relat_1(X41))
      & v1_funct_1(k6_relat_1(X41)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

cnf(c_0_42,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_33]),c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk4_0))) = k1_relat_1(esk3_0) ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_47,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X23)
      | ~ v1_relat_1(X24)
      | k7_relat_1(X23,k1_relat_1(X24)) = k7_relat_1(X23,k1_relat_1(k7_relat_1(X24,k1_relat_1(X23)))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t189_relat_1])])])).

cnf(c_0_48,negated_conjecture,
    ( k7_relat_1(k7_relat_1(X1,esk2_0),k1_relat_1(esk4_0)) = k7_relat_1(X1,k1_relat_1(esk3_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,plain,
    ( k7_relat_1(k6_relat_1(X1),X1) = k6_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])])).

fof(c_0_50,plain,(
    ! [X32,X33] :
      ( ~ v1_relat_1(X33)
      | r1_tarski(k1_relat_1(k7_relat_1(X33,X32)),k1_relat_1(X33)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t89_relat_1])])).

cnf(c_0_51,plain,
    ( k7_relat_1(X1,k1_relat_1(X2)) = k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,k1_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( k7_relat_1(k6_relat_1(esk2_0),k1_relat_1(esk4_0)) = k7_relat_1(k6_relat_1(esk2_0),k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_46])])).

cnf(c_0_53,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_54,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X16)
      | v1_relat_1(k7_relat_1(X16,X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_55,plain,(
    ! [X38,X39] :
      ( ~ v1_relat_1(X39)
      | ~ r1_tarski(k1_relat_1(X39),X38)
      | k7_relat_1(X39,X38) = X39 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

cnf(c_0_56,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( k7_relat_1(esk4_0,k1_relat_1(k7_relat_1(k6_relat_1(esk2_0),k1_relat_1(esk3_0)))) = k7_relat_1(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_45]),c_0_46]),c_0_53])])).

cnf(c_0_58,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

fof(c_0_59,plain,(
    ! [X36,X37] :
      ( ~ v1_relat_1(X37)
      | ~ r1_tarski(X36,k1_relat_1(X37))
      | k1_relat_1(k7_relat_1(X37,X36)) = X36 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).

fof(c_0_60,plain,(
    ! [X30,X31] :
      ( ~ v1_relat_1(X31)
      | r1_tarski(k1_relat_1(k7_relat_1(X31,X30)),X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

cnf(c_0_61,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk4_0,esk2_0)),k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_53])])).

cnf(c_0_63,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk4_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_57]),c_0_53])])).

cnf(c_0_64,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_65,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk4_0,esk2_0),k1_relat_1(esk4_0)) = k7_relat_1(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])])).

cnf(c_0_67,plain,
    ( k1_relat_1(k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,k1_relat_1(X1))))) = k1_relat_1(k7_relat_1(X2,k1_relat_1(X1)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( k7_relat_1(esk4_0,k1_relat_1(esk3_0)) = k7_relat_1(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_66]),c_0_53])])).

cnf(c_0_69,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_70,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X22)
      | k7_relat_1(k7_relat_1(X22,X21),X21) = k7_relat_1(X22,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t101_relat_1])])).

cnf(c_0_71,negated_conjecture,
    ( k1_relat_1(k7_relat_1(k6_relat_1(esk2_0),k1_relat_1(esk3_0))) = k1_relat_1(k7_relat_1(esk4_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_52]),c_0_57]),c_0_53]),c_0_46])])).

cnf(c_0_72,negated_conjecture,
    ( k7_relat_1(esk3_0,k1_relat_1(k7_relat_1(esk4_0,esk2_0))) = k7_relat_1(esk3_0,k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_68]),c_0_53]),c_0_69])])).

cnf(c_0_73,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X2) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( k7_relat_1(esk3_0,k1_relat_1(esk4_0)) = k7_relat_1(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_71]),c_0_72]),c_0_45]),c_0_46]),c_0_69])])).

cnf(c_0_75,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk3_0,esk2_0),k1_relat_1(esk4_0)) = k7_relat_1(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_69])])).

fof(c_0_76,plain,(
    ! [X34,X35] :
      ( ~ v1_relat_1(X35)
      | k1_relat_1(k7_relat_1(X35,X34)) = k3_xboole_0(k1_relat_1(X35),X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

cnf(c_0_77,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk3_0,k1_relat_1(esk4_0))) = k1_relat_1(k7_relat_1(esk4_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_72]),c_0_69]),c_0_53])])).

cnf(c_0_78,negated_conjecture,
    ( k7_relat_1(esk3_0,k1_relat_1(esk3_0)) = k7_relat_1(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_75]),c_0_69])])).

fof(c_0_79,plain,(
    ! [X44,X45,X46] :
      ( ~ v1_relat_1(X46)
      | ~ v1_funct_1(X46)
      | ~ r2_hidden(X44,k3_xboole_0(k1_relat_1(X46),X45))
      | k1_funct_1(X46,X44) = k1_funct_1(k5_relat_1(k6_relat_1(X45),X46),X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_funct_1])])).

cnf(c_0_80,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

fof(c_0_81,plain,(
    ! [X29] :
      ( ~ v1_relat_1(X29)
      | k5_relat_1(k6_relat_1(k1_relat_1(X29)),X29) = X29 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_relat_1])])).

cnf(c_0_82,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk4_0,esk2_0)) = k1_relat_1(k7_relat_1(esk3_0,esk2_0)) ),
    inference(rw,[status(thm)],[c_0_77,c_0_74])).

cnf(c_0_83,negated_conjecture,
    ( k7_relat_1(esk3_0,esk2_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_78]),c_0_69])])).

fof(c_0_84,plain,(
    ! [X25,X26,X27] :
      ( ~ v1_relat_1(X26)
      | ~ v1_relat_1(X27)
      | ~ r1_tarski(k2_relat_1(X26),k1_relat_1(k7_relat_1(X27,X25)))
      | k5_relat_1(X26,k7_relat_1(X27,X25)) = k5_relat_1(X26,X27) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t200_relat_1])])])).

fof(c_0_85,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_86,plain,(
    ! [X47,X48] :
      ( ( r2_hidden(esk1_2(X47,X48),k1_relat_1(X47))
        | k1_relat_1(X47) != k1_relat_1(X48)
        | X47 = X48
        | ~ v1_relat_1(X48)
        | ~ v1_funct_1(X48)
        | ~ v1_relat_1(X47)
        | ~ v1_funct_1(X47) )
      & ( k1_funct_1(X47,esk1_2(X47,X48)) != k1_funct_1(X48,esk1_2(X47,X48))
        | k1_relat_1(X47) != k1_relat_1(X48)
        | X47 = X48
        | ~ v1_relat_1(X48)
        | ~ v1_funct_1(X48)
        | ~ v1_relat_1(X47)
        | ~ v1_funct_1(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_1])])])])])).

fof(c_0_87,plain,(
    ! [X42,X43] :
      ( ( v1_relat_1(k7_relat_1(X42,X43))
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) )
      & ( v1_funct_1(k7_relat_1(X42,X43))
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).

cnf(c_0_88,plain,
    ( k1_funct_1(X1,X2) = k1_funct_1(k5_relat_1(k6_relat_1(X3),X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k3_xboole_0(k1_relat_1(X1),X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_89,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_33]),c_0_34])).

cnf(c_0_90,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_91,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk4_0,esk2_0)) = k1_relat_1(esk3_0) ),
    inference(rw,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_92,plain,
    ( k5_relat_1(X1,k7_relat_1(X2,X3)) = k5_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_93,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_94,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_95,plain,
    ( k7_relat_1(k6_relat_1(X1),k1_relat_1(k7_relat_1(X2,X1))) = k7_relat_1(k6_relat_1(X1),k1_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_45]),c_0_46])])).

cnf(c_0_96,negated_conjecture,
    ( k7_relat_1(esk3_0,k1_relat_1(esk4_0)) = esk3_0 ),
    inference(rw,[status(thm)],[c_0_74,c_0_83])).

cnf(c_0_97,plain,
    ( r2_hidden(esk1_2(X1,X2),k1_relat_1(X1))
    | X1 = X2
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_98,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_99,plain,
    ( v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_100,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_101,plain,
    ( k1_funct_1(X1,X2) = k1_funct_1(k5_relat_1(k6_relat_1(X3),X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_33]),c_0_34])).

cnf(c_0_102,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_45]),c_0_46])])).

cnf(c_0_103,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k1_relat_1(esk3_0)),k7_relat_1(esk4_0,esk2_0)) = k7_relat_1(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_63])])).

cnf(c_0_104,plain,
    ( k5_relat_1(k6_relat_1(X1),k7_relat_1(X2,X3)) = k5_relat_1(k6_relat_1(X1),X2)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k1_relat_1(k7_relat_1(X2,X3))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_46])])).

cnf(c_0_105,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_94])).

cnf(c_0_106,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_45]),c_0_46])])).

cnf(c_0_107,negated_conjecture,
    ( k7_relat_1(k6_relat_1(k1_relat_1(esk4_0)),k1_relat_1(esk3_0)) = k7_relat_1(k6_relat_1(k1_relat_1(esk4_0)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_52]),c_0_71]),c_0_82]),c_0_83]),c_0_45]),c_0_46])])).

cnf(c_0_108,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk3_0),k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_96]),c_0_69])])).

cnf(c_0_109,negated_conjecture,
    ( X1 = esk3_0
    | r2_hidden(esk1_2(X1,esk3_0),k1_relat_1(X1))
    | k1_relat_1(X1) != k1_relat_1(esk3_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_69])])).

cnf(c_0_110,negated_conjecture,
    ( v1_funct_1(k7_relat_1(esk4_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_57]),c_0_100]),c_0_53])])).

cnf(c_0_111,negated_conjecture,
    ( esk3_0 != k7_relat_1(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_112,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X3) = k1_funct_1(X2,X3)
    | ~ r2_hidden(X3,k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(X2)),X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(rw,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_113,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k1_relat_1(esk3_0)),esk4_0) = k7_relat_1(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_53]),c_0_82]),c_0_83]),c_0_105])])).

cnf(c_0_114,negated_conjecture,
    ( k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(esk4_0)),esk2_0)) = k1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_108])])).

cnf(c_0_115,negated_conjecture,
    ( k1_funct_1(esk3_0,X1) = k1_funct_1(esk4_0,X1)
    | ~ r2_hidden(X1,k1_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_116,negated_conjecture,
    ( r2_hidden(esk1_2(k7_relat_1(esk4_0,esk2_0),esk3_0),k1_relat_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_91]),c_0_110]),c_0_63])]),c_0_111])).

cnf(c_0_117,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk4_0,esk2_0),X1) = k1_funct_1(esk4_0,X1)
    | ~ r2_hidden(X1,k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_107]),c_0_113]),c_0_114]),c_0_100]),c_0_53])])).

cnf(c_0_118,negated_conjecture,
    ( k1_funct_1(esk4_0,esk1_2(k7_relat_1(esk4_0,esk2_0),esk3_0)) = k1_funct_1(esk3_0,esk1_2(k7_relat_1(esk4_0,esk2_0),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_115,c_0_116])).

cnf(c_0_119,plain,
    ( X1 = X2
    | k1_funct_1(X1,esk1_2(X1,X2)) != k1_funct_1(X2,esk1_2(X1,X2))
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_120,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk4_0,esk2_0),esk1_2(k7_relat_1(esk4_0,esk2_0),esk3_0)) = k1_funct_1(esk3_0,esk1_2(k7_relat_1(esk4_0,esk2_0),esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_116]),c_0_118])).

cnf(c_0_121,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_82]),c_0_83]),c_0_98]),c_0_110]),c_0_69]),c_0_63])]),c_0_111]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.31  % Computer   : n012.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.31  % CPULimit   : 60
% 0.16/0.31  % WCLimit    : 600
% 0.16/0.31  % DateTime   : Tue Dec  1 11:13:37 EST 2020
% 0.16/0.31  % CPUTime    : 
% 0.16/0.32  # Version: 2.5pre002
% 0.16/0.32  # No SInE strategy applied
% 0.16/0.32  # Trying AutoSched0 for 299 seconds
% 0.16/0.42  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.16/0.42  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.16/0.42  #
% 0.16/0.42  # Preprocessing time       : 0.028 s
% 0.16/0.42  # Presaturation interreduction done
% 0.16/0.42  
% 0.16/0.42  # Proof found!
% 0.16/0.42  # SZS status Theorem
% 0.16/0.42  # SZS output start CNFRefutation
% 0.16/0.42  fof(t68_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X2)=k3_xboole_0(k1_relat_1(X3),X1)&![X4]:(r2_hidden(X4,k1_relat_1(X2))=>k1_funct_1(X2,X4)=k1_funct_1(X3,X4)))=>X2=k7_relat_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_funct_1)).
% 0.16/0.42  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.16/0.42  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.16/0.42  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.16/0.42  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.16/0.42  fof(t100_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k7_relat_1(X3,k3_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 0.16/0.42  fof(t98_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 0.16/0.42  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.16/0.42  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.16/0.42  fof(t189_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k7_relat_1(X1,k1_relat_1(X2))=k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,k1_relat_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t189_relat_1)).
% 0.16/0.42  fof(t89_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),k1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t89_relat_1)).
% 0.16/0.42  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.16/0.42  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 0.16/0.42  fof(t91_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>k1_relat_1(k7_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 0.16/0.42  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 0.16/0.42  fof(t101_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(k7_relat_1(X2,X1),X1)=k7_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t101_relat_1)).
% 0.16/0.42  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 0.16/0.42  fof(t38_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k3_xboole_0(k1_relat_1(X3),X2))=>k1_funct_1(X3,X1)=k1_funct_1(k5_relat_1(k6_relat_1(X2),X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_1)).
% 0.16/0.42  fof(t78_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 0.16/0.42  fof(t200_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(k2_relat_1(X2),k1_relat_1(k7_relat_1(X3,X1)))=>k5_relat_1(X2,k7_relat_1(X3,X1))=k5_relat_1(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t200_relat_1)).
% 0.16/0.42  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.16/0.42  fof(t9_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((k1_relat_1(X1)=k1_relat_1(X2)&![X3]:(r2_hidden(X3,k1_relat_1(X1))=>k1_funct_1(X1,X3)=k1_funct_1(X2,X3)))=>X1=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 0.16/0.42  fof(fc8_funct_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k7_relat_1(X1,X2))&v1_funct_1(k7_relat_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_funct_1)).
% 0.16/0.42  fof(c_0_23, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X2)=k3_xboole_0(k1_relat_1(X3),X1)&![X4]:(r2_hidden(X4,k1_relat_1(X2))=>k1_funct_1(X2,X4)=k1_funct_1(X3,X4)))=>X2=k7_relat_1(X3,X1))))), inference(assume_negation,[status(cth)],[t68_funct_1])).
% 0.16/0.42  fof(c_0_24, plain, ![X14, X15]:k1_setfam_1(k2_tarski(X14,X15))=k3_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.16/0.42  fof(c_0_25, plain, ![X9, X10]:k1_enumset1(X9,X9,X10)=k2_tarski(X9,X10), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.16/0.42  fof(c_0_26, negated_conjecture, ![X53]:((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&((k1_relat_1(esk3_0)=k3_xboole_0(k1_relat_1(esk4_0),esk2_0)&(~r2_hidden(X53,k1_relat_1(esk3_0))|k1_funct_1(esk3_0,X53)=k1_funct_1(esk4_0,X53)))&esk3_0!=k7_relat_1(esk4_0,esk2_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])])).
% 0.16/0.42  cnf(c_0_27, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.16/0.42  cnf(c_0_28, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.16/0.42  fof(c_0_29, plain, ![X11, X12, X13]:k2_enumset1(X11,X11,X12,X13)=k1_enumset1(X11,X12,X13), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.16/0.42  fof(c_0_30, plain, ![X7, X8]:k2_tarski(X7,X8)=k2_tarski(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.16/0.42  fof(c_0_31, plain, ![X18, X19, X20]:(~v1_relat_1(X20)|k7_relat_1(k7_relat_1(X20,X18),X19)=k7_relat_1(X20,k3_xboole_0(X18,X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).
% 0.16/0.42  cnf(c_0_32, negated_conjecture, (k1_relat_1(esk3_0)=k3_xboole_0(k1_relat_1(esk4_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.16/0.42  cnf(c_0_33, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.16/0.42  cnf(c_0_34, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.16/0.42  cnf(c_0_35, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.16/0.42  cnf(c_0_36, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.16/0.42  cnf(c_0_37, negated_conjecture, (k1_relat_1(esk3_0)=k1_setfam_1(k2_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),k1_relat_1(esk4_0),esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33]), c_0_34])).
% 0.16/0.42  cnf(c_0_38, plain, (k2_enumset1(X1,X1,X1,X2)=k2_enumset1(X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_28]), c_0_28]), c_0_34]), c_0_34])).
% 0.16/0.42  fof(c_0_39, plain, ![X40]:(~v1_relat_1(X40)|k7_relat_1(X40,k1_relat_1(X40))=X40), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).
% 0.16/0.42  fof(c_0_40, plain, ![X28]:(k1_relat_1(k6_relat_1(X28))=X28&k2_relat_1(k6_relat_1(X28))=X28), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.16/0.42  fof(c_0_41, plain, ![X41]:(v1_relat_1(k6_relat_1(X41))&v1_funct_1(k6_relat_1(X41))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.16/0.42  cnf(c_0_42, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_33]), c_0_34])).
% 0.16/0.42  cnf(c_0_43, negated_conjecture, (k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk4_0)))=k1_relat_1(esk3_0)), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 0.16/0.42  cnf(c_0_44, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.16/0.42  cnf(c_0_45, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.16/0.42  cnf(c_0_46, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.16/0.42  fof(c_0_47, plain, ![X23, X24]:(~v1_relat_1(X23)|(~v1_relat_1(X24)|k7_relat_1(X23,k1_relat_1(X24))=k7_relat_1(X23,k1_relat_1(k7_relat_1(X24,k1_relat_1(X23)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t189_relat_1])])])).
% 0.16/0.42  cnf(c_0_48, negated_conjecture, (k7_relat_1(k7_relat_1(X1,esk2_0),k1_relat_1(esk4_0))=k7_relat_1(X1,k1_relat_1(esk3_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.16/0.42  cnf(c_0_49, plain, (k7_relat_1(k6_relat_1(X1),X1)=k6_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])])).
% 0.16/0.42  fof(c_0_50, plain, ![X32, X33]:(~v1_relat_1(X33)|r1_tarski(k1_relat_1(k7_relat_1(X33,X32)),k1_relat_1(X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t89_relat_1])])).
% 0.16/0.42  cnf(c_0_51, plain, (k7_relat_1(X1,k1_relat_1(X2))=k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,k1_relat_1(X1))))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.16/0.42  cnf(c_0_52, negated_conjecture, (k7_relat_1(k6_relat_1(esk2_0),k1_relat_1(esk4_0))=k7_relat_1(k6_relat_1(esk2_0),k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_46])])).
% 0.16/0.42  cnf(c_0_53, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.16/0.42  fof(c_0_54, plain, ![X16, X17]:(~v1_relat_1(X16)|v1_relat_1(k7_relat_1(X16,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.16/0.42  fof(c_0_55, plain, ![X38, X39]:(~v1_relat_1(X39)|(~r1_tarski(k1_relat_1(X39),X38)|k7_relat_1(X39,X38)=X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 0.16/0.42  cnf(c_0_56, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.16/0.42  cnf(c_0_57, negated_conjecture, (k7_relat_1(esk4_0,k1_relat_1(k7_relat_1(k6_relat_1(esk2_0),k1_relat_1(esk3_0))))=k7_relat_1(esk4_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_45]), c_0_46]), c_0_53])])).
% 0.16/0.42  cnf(c_0_58, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.16/0.42  fof(c_0_59, plain, ![X36, X37]:(~v1_relat_1(X37)|(~r1_tarski(X36,k1_relat_1(X37))|k1_relat_1(k7_relat_1(X37,X36))=X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).
% 0.16/0.42  fof(c_0_60, plain, ![X30, X31]:(~v1_relat_1(X31)|r1_tarski(k1_relat_1(k7_relat_1(X31,X30)),X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 0.16/0.42  cnf(c_0_61, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.16/0.42  cnf(c_0_62, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(esk4_0,esk2_0)),k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_53])])).
% 0.16/0.42  cnf(c_0_63, negated_conjecture, (v1_relat_1(k7_relat_1(esk4_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_57]), c_0_53])])).
% 0.16/0.42  cnf(c_0_64, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.16/0.42  cnf(c_0_65, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.16/0.42  cnf(c_0_66, negated_conjecture, (k7_relat_1(k7_relat_1(esk4_0,esk2_0),k1_relat_1(esk4_0))=k7_relat_1(esk4_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63])])).
% 0.16/0.42  cnf(c_0_67, plain, (k1_relat_1(k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,k1_relat_1(X1)))))=k1_relat_1(k7_relat_1(X2,k1_relat_1(X1)))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.16/0.42  cnf(c_0_68, negated_conjecture, (k7_relat_1(esk4_0,k1_relat_1(esk3_0))=k7_relat_1(esk4_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_66]), c_0_53])])).
% 0.16/0.42  cnf(c_0_69, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.16/0.42  fof(c_0_70, plain, ![X21, X22]:(~v1_relat_1(X22)|k7_relat_1(k7_relat_1(X22,X21),X21)=k7_relat_1(X22,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t101_relat_1])])).
% 0.16/0.42  cnf(c_0_71, negated_conjecture, (k1_relat_1(k7_relat_1(k6_relat_1(esk2_0),k1_relat_1(esk3_0)))=k1_relat_1(k7_relat_1(esk4_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_52]), c_0_57]), c_0_53]), c_0_46])])).
% 0.16/0.42  cnf(c_0_72, negated_conjecture, (k7_relat_1(esk3_0,k1_relat_1(k7_relat_1(esk4_0,esk2_0)))=k7_relat_1(esk3_0,k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_68]), c_0_53]), c_0_69])])).
% 0.16/0.42  cnf(c_0_73, plain, (k7_relat_1(k7_relat_1(X1,X2),X2)=k7_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.16/0.42  cnf(c_0_74, negated_conjecture, (k7_relat_1(esk3_0,k1_relat_1(esk4_0))=k7_relat_1(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_71]), c_0_72]), c_0_45]), c_0_46]), c_0_69])])).
% 0.16/0.42  cnf(c_0_75, negated_conjecture, (k7_relat_1(k7_relat_1(esk3_0,esk2_0),k1_relat_1(esk4_0))=k7_relat_1(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_69])])).
% 0.16/0.42  fof(c_0_76, plain, ![X34, X35]:(~v1_relat_1(X35)|k1_relat_1(k7_relat_1(X35,X34))=k3_xboole_0(k1_relat_1(X35),X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 0.16/0.42  cnf(c_0_77, negated_conjecture, (k1_relat_1(k7_relat_1(esk3_0,k1_relat_1(esk4_0)))=k1_relat_1(k7_relat_1(esk4_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_72]), c_0_69]), c_0_53])])).
% 0.16/0.42  cnf(c_0_78, negated_conjecture, (k7_relat_1(esk3_0,k1_relat_1(esk3_0))=k7_relat_1(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_75]), c_0_69])])).
% 0.16/0.42  fof(c_0_79, plain, ![X44, X45, X46]:(~v1_relat_1(X46)|~v1_funct_1(X46)|(~r2_hidden(X44,k3_xboole_0(k1_relat_1(X46),X45))|k1_funct_1(X46,X44)=k1_funct_1(k5_relat_1(k6_relat_1(X45),X46),X44))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_funct_1])])).
% 0.16/0.42  cnf(c_0_80, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.16/0.42  fof(c_0_81, plain, ![X29]:(~v1_relat_1(X29)|k5_relat_1(k6_relat_1(k1_relat_1(X29)),X29)=X29), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_relat_1])])).
% 0.16/0.42  cnf(c_0_82, negated_conjecture, (k1_relat_1(k7_relat_1(esk4_0,esk2_0))=k1_relat_1(k7_relat_1(esk3_0,esk2_0))), inference(rw,[status(thm)],[c_0_77, c_0_74])).
% 0.16/0.42  cnf(c_0_83, negated_conjecture, (k7_relat_1(esk3_0,esk2_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_78]), c_0_69])])).
% 0.16/0.42  fof(c_0_84, plain, ![X25, X26, X27]:(~v1_relat_1(X26)|(~v1_relat_1(X27)|(~r1_tarski(k2_relat_1(X26),k1_relat_1(k7_relat_1(X27,X25)))|k5_relat_1(X26,k7_relat_1(X27,X25))=k5_relat_1(X26,X27)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t200_relat_1])])])).
% 0.16/0.42  fof(c_0_85, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.16/0.42  fof(c_0_86, plain, ![X47, X48]:((r2_hidden(esk1_2(X47,X48),k1_relat_1(X47))|k1_relat_1(X47)!=k1_relat_1(X48)|X47=X48|(~v1_relat_1(X48)|~v1_funct_1(X48))|(~v1_relat_1(X47)|~v1_funct_1(X47)))&(k1_funct_1(X47,esk1_2(X47,X48))!=k1_funct_1(X48,esk1_2(X47,X48))|k1_relat_1(X47)!=k1_relat_1(X48)|X47=X48|(~v1_relat_1(X48)|~v1_funct_1(X48))|(~v1_relat_1(X47)|~v1_funct_1(X47)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_1])])])])])).
% 0.16/0.42  fof(c_0_87, plain, ![X42, X43]:((v1_relat_1(k7_relat_1(X42,X43))|(~v1_relat_1(X42)|~v1_funct_1(X42)))&(v1_funct_1(k7_relat_1(X42,X43))|(~v1_relat_1(X42)|~v1_funct_1(X42)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).
% 0.16/0.42  cnf(c_0_88, plain, (k1_funct_1(X1,X2)=k1_funct_1(k5_relat_1(k6_relat_1(X3),X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k3_xboole_0(k1_relat_1(X1),X3))), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.16/0.42  cnf(c_0_89, plain, (k1_relat_1(k7_relat_1(X1,X2))=k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_33]), c_0_34])).
% 0.16/0.42  cnf(c_0_90, plain, (k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.16/0.42  cnf(c_0_91, negated_conjecture, (k1_relat_1(k7_relat_1(esk4_0,esk2_0))=k1_relat_1(esk3_0)), inference(rw,[status(thm)],[c_0_82, c_0_83])).
% 0.16/0.42  cnf(c_0_92, plain, (k5_relat_1(X1,k7_relat_1(X2,X3))=k5_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.16/0.42  cnf(c_0_93, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.16/0.42  cnf(c_0_94, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.16/0.42  cnf(c_0_95, plain, (k7_relat_1(k6_relat_1(X1),k1_relat_1(k7_relat_1(X2,X1)))=k7_relat_1(k6_relat_1(X1),k1_relat_1(X2))|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_45]), c_0_46])])).
% 0.16/0.42  cnf(c_0_96, negated_conjecture, (k7_relat_1(esk3_0,k1_relat_1(esk4_0))=esk3_0), inference(rw,[status(thm)],[c_0_74, c_0_83])).
% 0.16/0.42  cnf(c_0_97, plain, (r2_hidden(esk1_2(X1,X2),k1_relat_1(X1))|X1=X2|k1_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.16/0.42  cnf(c_0_98, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.16/0.42  cnf(c_0_99, plain, (v1_funct_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.16/0.42  cnf(c_0_100, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.16/0.42  cnf(c_0_101, plain, (k1_funct_1(X1,X2)=k1_funct_1(k5_relat_1(k6_relat_1(X3),X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_33]), c_0_34])).
% 0.16/0.42  cnf(c_0_102, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_45]), c_0_46])])).
% 0.16/0.42  cnf(c_0_103, negated_conjecture, (k5_relat_1(k6_relat_1(k1_relat_1(esk3_0)),k7_relat_1(esk4_0,esk2_0))=k7_relat_1(esk4_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_63])])).
% 0.16/0.42  cnf(c_0_104, plain, (k5_relat_1(k6_relat_1(X1),k7_relat_1(X2,X3))=k5_relat_1(k6_relat_1(X1),X2)|~v1_relat_1(X2)|~r1_tarski(X1,k1_relat_1(k7_relat_1(X2,X3)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_46])])).
% 0.16/0.42  cnf(c_0_105, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_94])).
% 0.16/0.42  cnf(c_0_106, plain, (k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))=X2|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_45]), c_0_46])])).
% 0.16/0.42  cnf(c_0_107, negated_conjecture, (k7_relat_1(k6_relat_1(k1_relat_1(esk4_0)),k1_relat_1(esk3_0))=k7_relat_1(k6_relat_1(k1_relat_1(esk4_0)),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_52]), c_0_71]), c_0_82]), c_0_83]), c_0_45]), c_0_46])])).
% 0.16/0.42  cnf(c_0_108, negated_conjecture, (r1_tarski(k1_relat_1(esk3_0),k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_96]), c_0_69])])).
% 0.16/0.42  cnf(c_0_109, negated_conjecture, (X1=esk3_0|r2_hidden(esk1_2(X1,esk3_0),k1_relat_1(X1))|k1_relat_1(X1)!=k1_relat_1(esk3_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_69])])).
% 0.16/0.42  cnf(c_0_110, negated_conjecture, (v1_funct_1(k7_relat_1(esk4_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_57]), c_0_100]), c_0_53])])).
% 0.16/0.42  cnf(c_0_111, negated_conjecture, (esk3_0!=k7_relat_1(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.16/0.42  cnf(c_0_112, plain, (k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X3)=k1_funct_1(X2,X3)|~r2_hidden(X3,k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(X2)),X1)))|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(rw,[status(thm)],[c_0_101, c_0_102])).
% 0.16/0.42  cnf(c_0_113, negated_conjecture, (k5_relat_1(k6_relat_1(k1_relat_1(esk3_0)),esk4_0)=k7_relat_1(esk4_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_53]), c_0_82]), c_0_83]), c_0_105])])).
% 0.16/0.42  cnf(c_0_114, negated_conjecture, (k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(esk4_0)),esk2_0))=k1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_108])])).
% 0.16/0.42  cnf(c_0_115, negated_conjecture, (k1_funct_1(esk3_0,X1)=k1_funct_1(esk4_0,X1)|~r2_hidden(X1,k1_relat_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.16/0.42  cnf(c_0_116, negated_conjecture, (r2_hidden(esk1_2(k7_relat_1(esk4_0,esk2_0),esk3_0),k1_relat_1(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_91]), c_0_110]), c_0_63])]), c_0_111])).
% 0.16/0.42  cnf(c_0_117, negated_conjecture, (k1_funct_1(k7_relat_1(esk4_0,esk2_0),X1)=k1_funct_1(esk4_0,X1)|~r2_hidden(X1,k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_107]), c_0_113]), c_0_114]), c_0_100]), c_0_53])])).
% 0.16/0.42  cnf(c_0_118, negated_conjecture, (k1_funct_1(esk4_0,esk1_2(k7_relat_1(esk4_0,esk2_0),esk3_0))=k1_funct_1(esk3_0,esk1_2(k7_relat_1(esk4_0,esk2_0),esk3_0))), inference(spm,[status(thm)],[c_0_115, c_0_116])).
% 0.16/0.42  cnf(c_0_119, plain, (X1=X2|k1_funct_1(X1,esk1_2(X1,X2))!=k1_funct_1(X2,esk1_2(X1,X2))|k1_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.16/0.42  cnf(c_0_120, negated_conjecture, (k1_funct_1(k7_relat_1(esk4_0,esk2_0),esk1_2(k7_relat_1(esk4_0,esk2_0),esk3_0))=k1_funct_1(esk3_0,esk1_2(k7_relat_1(esk4_0,esk2_0),esk3_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_116]), c_0_118])).
% 0.16/0.42  cnf(c_0_121, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_120]), c_0_82]), c_0_83]), c_0_98]), c_0_110]), c_0_69]), c_0_63])]), c_0_111]), ['proof']).
% 0.16/0.42  # SZS output end CNFRefutation
% 0.16/0.42  # Proof object total steps             : 122
% 0.16/0.42  # Proof object clause steps            : 75
% 0.16/0.42  # Proof object formula steps           : 47
% 0.16/0.42  # Proof object conjectures             : 41
% 0.16/0.42  # Proof object clause conjectures      : 38
% 0.16/0.42  # Proof object formula conjectures     : 3
% 0.16/0.42  # Proof object initial clauses used    : 31
% 0.16/0.42  # Proof object initial formulas used   : 23
% 0.16/0.42  # Proof object generating inferences   : 32
% 0.16/0.42  # Proof object simplifying inferences  : 105
% 0.16/0.42  # Training examples: 0 positive, 0 negative
% 0.16/0.42  # Parsed axioms                        : 23
% 0.16/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.16/0.42  # Initial clauses                      : 35
% 0.16/0.42  # Removed in clause preprocessing      : 3
% 0.16/0.42  # Initial clauses in saturation        : 32
% 0.16/0.42  # Processed clauses                    : 659
% 0.16/0.42  # ...of these trivial                  : 78
% 0.16/0.42  # ...subsumed                          : 310
% 0.16/0.42  # ...remaining for further processing  : 271
% 0.16/0.42  # Other redundant clauses eliminated   : 16
% 0.16/0.42  # Clauses deleted for lack of memory   : 0
% 0.16/0.42  # Backward-subsumed                    : 1
% 0.16/0.42  # Backward-rewritten                   : 72
% 0.16/0.42  # Generated clauses                    : 5169
% 0.16/0.42  # ...of the previous two non-trivial   : 3557
% 0.16/0.42  # Contextual simplify-reflections      : 12
% 0.16/0.42  # Paramodulations                      : 5149
% 0.16/0.42  # Factorizations                       : 0
% 0.16/0.42  # Equation resolutions                 : 20
% 0.16/0.42  # Propositional unsat checks           : 0
% 0.16/0.42  #    Propositional check models        : 0
% 0.16/0.42  #    Propositional check unsatisfiable : 0
% 0.16/0.42  #    Propositional clauses             : 0
% 0.16/0.42  #    Propositional clauses after purity: 0
% 0.16/0.42  #    Propositional unsat core size     : 0
% 0.16/0.42  #    Propositional preprocessing time  : 0.000
% 0.16/0.42  #    Propositional encoding time       : 0.000
% 0.16/0.42  #    Propositional solver time         : 0.000
% 0.16/0.42  #    Success case prop preproc time    : 0.000
% 0.16/0.42  #    Success case prop encoding time   : 0.000
% 0.16/0.42  #    Success case prop solver time     : 0.000
% 0.16/0.42  # Current number of processed clauses  : 166
% 0.16/0.42  #    Positive orientable unit clauses  : 72
% 0.16/0.42  #    Positive unorientable unit clauses: 1
% 0.16/0.42  #    Negative unit clauses             : 1
% 0.16/0.42  #    Non-unit-clauses                  : 92
% 0.16/0.42  # Current number of unprocessed clauses: 2863
% 0.16/0.42  # ...number of literals in the above   : 7940
% 0.16/0.42  # Current number of archived formulas  : 0
% 0.16/0.42  # Current number of archived clauses   : 106
% 0.16/0.42  # Clause-clause subsumption calls (NU) : 2002
% 0.16/0.42  # Rec. Clause-clause subsumption calls : 1895
% 0.16/0.42  # Non-unit clause-clause subsumptions  : 323
% 0.16/0.42  # Unit Clause-clause subsumption calls : 35
% 0.16/0.42  # Rewrite failures with RHS unbound    : 0
% 0.16/0.42  # BW rewrite match attempts            : 141
% 0.16/0.42  # BW rewrite match successes           : 34
% 0.16/0.42  # Condensation attempts                : 0
% 0.16/0.42  # Condensation successes               : 0
% 0.16/0.42  # Termbank termtop insertions          : 98677
% 0.16/0.42  
% 0.16/0.42  # -------------------------------------------------
% 0.16/0.42  # User time                : 0.107 s
% 0.16/0.42  # System time              : 0.003 s
% 0.16/0.42  # Total time               : 0.110 s
% 0.16/0.42  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
