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
% DateTime   : Thu Dec  3 11:07:32 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 134 expanded)
%              Number of clauses        :   36 (  53 expanded)
%              Number of leaves         :   14 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :  162 ( 381 expanded)
%              Number of equality atoms :   28 (  76 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t175_funct_2,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( r1_tarski(k10_relat_1(X1,X3),X2)
         => k10_relat_1(X1,X3) = k10_relat_1(k7_relat_1(X1,X2),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(t103_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => k7_relat_1(k7_relat_1(X3,X2),X1) = k7_relat_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

fof(t91_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => k1_relat_1(k7_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(t170_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k10_relat_1(X2,k2_relat_1(X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t170_relat_1)).

fof(fc8_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k7_relat_1(X1,X2))
        & v1_funct_1(k7_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t162_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( r1_tarski(X2,X3)
         => k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

fof(t163_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(X1,k1_relat_1(X3))
          & r1_tarski(k9_relat_1(X3,X1),X2) )
       => r1_tarski(X1,k10_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(t89_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(t179_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( r1_tarski(X2,X3)
           => r1_tarski(k10_relat_1(X2,X1),k10_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t179_relat_1)).

fof(t88_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k7_relat_1(X2,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2,X3] :
            ( r1_tarski(k10_relat_1(X1,X3),X2)
           => k10_relat_1(X1,X3) = k10_relat_1(k7_relat_1(X1,X2),X3) ) ) ),
    inference(assume_negation,[status(cth)],[t175_funct_2])).

fof(c_0_15,plain,(
    ! [X14] :
      ( ~ v1_relat_1(X14)
      | k10_relat_1(X14,k2_relat_1(X14)) = k1_relat_1(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

fof(c_0_16,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & r1_tarski(k10_relat_1(esk1_0,esk3_0),esk2_0)
    & k10_relat_1(esk1_0,esk3_0) != k10_relat_1(k7_relat_1(esk1_0,esk2_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_17,plain,(
    ! [X8,X9,X10] :
      ( ~ v1_relat_1(X10)
      | ~ r1_tarski(X8,X9)
      | k7_relat_1(k7_relat_1(X10,X9),X8) = k7_relat_1(X10,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t103_relat_1])])).

fof(c_0_18,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X25)
      | ~ r1_tarski(X24,k1_relat_1(X25))
      | k1_relat_1(k7_relat_1(X25,X24)) = X24 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).

fof(c_0_19,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X16)
      | r1_tarski(k10_relat_1(X16,X15),k10_relat_1(X16,k2_relat_1(X16))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t170_relat_1])])).

cnf(c_0_20,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X26,X27] :
      ( ( v1_relat_1(k7_relat_1(X26,X27))
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( v1_funct_1(k7_relat_1(X26,X27))
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).

fof(c_0_23,plain,(
    ! [X6,X7] :
      ( ~ v1_relat_1(X6)
      | v1_relat_1(k7_relat_1(X6,X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_24,plain,
    ( k7_relat_1(k7_relat_1(X1,X3),X2) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( k10_relat_1(esk1_0,k2_relat_1(esk1_0)) = k1_relat_1(esk1_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_28,plain,(
    ! [X11,X12,X13] :
      ( ~ v1_relat_1(X11)
      | ~ r1_tarski(X12,X13)
      | k9_relat_1(k7_relat_1(X11,X13),X12) = k9_relat_1(X11,X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_relat_1])])])).

fof(c_0_29,plain,(
    ! [X30,X31,X32] :
      ( ~ v1_relat_1(X32)
      | ~ v1_funct_1(X32)
      | ~ r1_tarski(X30,k1_relat_1(X32))
      | ~ r1_tarski(k9_relat_1(X32,X30),X31)
      | r1_tarski(X30,k10_relat_1(X32,X31)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).

cnf(c_0_30,plain,
    ( v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_32,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_33,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X23)
      | r1_tarski(k1_relat_1(k7_relat_1(X23,X22)),k1_relat_1(X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t89_relat_1])])).

cnf(c_0_34,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk1_0,X1),X2) = k7_relat_1(esk1_0,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_21])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk1_0,esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_36,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk1_0,X1)) = X1
    | ~ r1_tarski(X1,k1_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_21])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk1_0,X1),k1_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_21])])).

cnf(c_0_38,plain,
    ( k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( r1_tarski(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,negated_conjecture,
    ( v1_funct_1(k7_relat_1(esk1_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_21])])).

cnf(c_0_41,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk1_0,X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_21])).

cnf(c_0_42,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk1_0,esk2_0),k10_relat_1(esk1_0,esk3_0)) = k7_relat_1(esk1_0,k10_relat_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk1_0,k10_relat_1(esk1_0,X1))) = k10_relat_1(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk1_0,X1),X2) = k9_relat_1(esk1_0,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_21])).

fof(c_0_46,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X29)
      | ~ v1_funct_1(X29)
      | r1_tarski(k9_relat_1(X29,k10_relat_1(X29,X28)),X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

fof(c_0_47,plain,(
    ! [X17,X18,X19] :
      ( ~ v1_relat_1(X18)
      | ~ v1_relat_1(X19)
      | ~ r1_tarski(X18,X19)
      | r1_tarski(k10_relat_1(X18,X17),k10_relat_1(X19,X17)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t179_relat_1])])])).

fof(c_0_48,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X21)
      | r1_tarski(k7_relat_1(X21,X20),X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(X1,k10_relat_1(k7_relat_1(esk1_0,X2),X3))
    | ~ r1_tarski(k9_relat_1(k7_relat_1(esk1_0,X2),X1),X3)
    | ~ r1_tarski(X1,k1_relat_1(k7_relat_1(esk1_0,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk1_0,esk3_0),k1_relat_1(k7_relat_1(esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_41])]),c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk1_0,esk2_0),k10_relat_1(esk1_0,esk3_0)) = k9_relat_1(esk1_0,k10_relat_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_35])).

cnf(c_0_52,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,plain,
    ( r1_tarski(k10_relat_1(X1,X3),k10_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_54,plain,
    ( r1_tarski(k7_relat_1(X1,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_55,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk1_0,esk3_0),k10_relat_1(k7_relat_1(esk1_0,esk2_0),X1))
    | ~ r1_tarski(k9_relat_1(esk1_0,k10_relat_1(esk1_0,esk3_0)),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk1_0,k10_relat_1(esk1_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_31]),c_0_21])])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(k10_relat_1(X1,X2),k10_relat_1(esk1_0,X2))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_21])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k7_relat_1(esk1_0,X1),esk1_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_21])).

cnf(c_0_60,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk1_0,esk3_0),k10_relat_1(k7_relat_1(esk1_0,esk2_0),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(k10_relat_1(k7_relat_1(esk1_0,X1),X2),k10_relat_1(esk1_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_41]),c_0_59])])).

cnf(c_0_63,negated_conjecture,
    ( k10_relat_1(esk1_0,esk3_0) != k10_relat_1(k7_relat_1(esk1_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62])]),c_0_63]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:37:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic G_E___107_C00_02_nc_F1_PI_AE_Q4_CS_SP_PS_S00EN
% 0.19/0.41  # and selection function PSelectSmallestOrientable.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.027 s
% 0.19/0.41  # Presaturation interreduction done
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(t175_funct_2, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(r1_tarski(k10_relat_1(X1,X3),X2)=>k10_relat_1(X1,X3)=k10_relat_1(k7_relat_1(X1,X2),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 0.19/0.41  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 0.19/0.41  fof(t103_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k7_relat_1(k7_relat_1(X3,X2),X1)=k7_relat_1(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_relat_1)).
% 0.19/0.41  fof(t91_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>k1_relat_1(k7_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 0.19/0.41  fof(t170_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k10_relat_1(X2,k2_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t170_relat_1)).
% 0.19/0.41  fof(fc8_funct_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k7_relat_1(X1,X2))&v1_funct_1(k7_relat_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_funct_1)).
% 0.19/0.41  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.19/0.41  fof(t162_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 0.19/0.41  fof(t163_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(X1,k1_relat_1(X3))&r1_tarski(k9_relat_1(X3,X1),X2))=>r1_tarski(X1,k10_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 0.19/0.41  fof(t89_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),k1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t89_relat_1)).
% 0.19/0.41  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 0.19/0.41  fof(t179_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X2,X3)=>r1_tarski(k10_relat_1(X2,X1),k10_relat_1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t179_relat_1)).
% 0.19/0.41  fof(t88_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k7_relat_1(X2,X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 0.19/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.41  fof(c_0_14, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(r1_tarski(k10_relat_1(X1,X3),X2)=>k10_relat_1(X1,X3)=k10_relat_1(k7_relat_1(X1,X2),X3)))), inference(assume_negation,[status(cth)],[t175_funct_2])).
% 0.19/0.41  fof(c_0_15, plain, ![X14]:(~v1_relat_1(X14)|k10_relat_1(X14,k2_relat_1(X14))=k1_relat_1(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.19/0.41  fof(c_0_16, negated_conjecture, ((v1_relat_1(esk1_0)&v1_funct_1(esk1_0))&(r1_tarski(k10_relat_1(esk1_0,esk3_0),esk2_0)&k10_relat_1(esk1_0,esk3_0)!=k10_relat_1(k7_relat_1(esk1_0,esk2_0),esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.19/0.41  fof(c_0_17, plain, ![X8, X9, X10]:(~v1_relat_1(X10)|(~r1_tarski(X8,X9)|k7_relat_1(k7_relat_1(X10,X9),X8)=k7_relat_1(X10,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t103_relat_1])])).
% 0.19/0.41  fof(c_0_18, plain, ![X24, X25]:(~v1_relat_1(X25)|(~r1_tarski(X24,k1_relat_1(X25))|k1_relat_1(k7_relat_1(X25,X24))=X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).
% 0.19/0.41  fof(c_0_19, plain, ![X15, X16]:(~v1_relat_1(X16)|r1_tarski(k10_relat_1(X16,X15),k10_relat_1(X16,k2_relat_1(X16)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t170_relat_1])])).
% 0.19/0.41  cnf(c_0_20, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.41  cnf(c_0_21, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.41  fof(c_0_22, plain, ![X26, X27]:((v1_relat_1(k7_relat_1(X26,X27))|(~v1_relat_1(X26)|~v1_funct_1(X26)))&(v1_funct_1(k7_relat_1(X26,X27))|(~v1_relat_1(X26)|~v1_funct_1(X26)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).
% 0.19/0.41  fof(c_0_23, plain, ![X6, X7]:(~v1_relat_1(X6)|v1_relat_1(k7_relat_1(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.19/0.41  cnf(c_0_24, plain, (k7_relat_1(k7_relat_1(X1,X3),X2)=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.41  cnf(c_0_25, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  cnf(c_0_26, plain, (r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,k2_relat_1(X1)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_27, negated_conjecture, (k10_relat_1(esk1_0,k2_relat_1(esk1_0))=k1_relat_1(esk1_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.41  fof(c_0_28, plain, ![X11, X12, X13]:(~v1_relat_1(X11)|(~r1_tarski(X12,X13)|k9_relat_1(k7_relat_1(X11,X13),X12)=k9_relat_1(X11,X12))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_relat_1])])])).
% 0.19/0.41  fof(c_0_29, plain, ![X30, X31, X32]:(~v1_relat_1(X32)|~v1_funct_1(X32)|(~r1_tarski(X30,k1_relat_1(X32))|~r1_tarski(k9_relat_1(X32,X30),X31)|r1_tarski(X30,k10_relat_1(X32,X31)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).
% 0.19/0.41  cnf(c_0_30, plain, (v1_funct_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.41  cnf(c_0_31, negated_conjecture, (v1_funct_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.41  cnf(c_0_32, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.41  fof(c_0_33, plain, ![X22, X23]:(~v1_relat_1(X23)|r1_tarski(k1_relat_1(k7_relat_1(X23,X22)),k1_relat_1(X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t89_relat_1])])).
% 0.19/0.41  cnf(c_0_34, negated_conjecture, (k7_relat_1(k7_relat_1(esk1_0,X1),X2)=k7_relat_1(esk1_0,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_24, c_0_21])).
% 0.19/0.41  cnf(c_0_35, negated_conjecture, (r1_tarski(k10_relat_1(esk1_0,esk3_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.41  cnf(c_0_36, negated_conjecture, (k1_relat_1(k7_relat_1(esk1_0,X1))=X1|~r1_tarski(X1,k1_relat_1(esk1_0))), inference(spm,[status(thm)],[c_0_25, c_0_21])).
% 0.19/0.41  cnf(c_0_37, negated_conjecture, (r1_tarski(k10_relat_1(esk1_0,X1),k1_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_21])])).
% 0.19/0.41  cnf(c_0_38, plain, (k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.41  cnf(c_0_39, plain, (r1_tarski(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k1_relat_1(X1))|~r1_tarski(k9_relat_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.41  cnf(c_0_40, negated_conjecture, (v1_funct_1(k7_relat_1(esk1_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_21])])).
% 0.19/0.41  cnf(c_0_41, negated_conjecture, (v1_relat_1(k7_relat_1(esk1_0,X1))), inference(spm,[status(thm)],[c_0_32, c_0_21])).
% 0.19/0.41  cnf(c_0_42, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.41  cnf(c_0_43, negated_conjecture, (k7_relat_1(k7_relat_1(esk1_0,esk2_0),k10_relat_1(esk1_0,esk3_0))=k7_relat_1(esk1_0,k10_relat_1(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.41  cnf(c_0_44, negated_conjecture, (k1_relat_1(k7_relat_1(esk1_0,k10_relat_1(esk1_0,X1)))=k10_relat_1(esk1_0,X1)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.41  cnf(c_0_45, negated_conjecture, (k9_relat_1(k7_relat_1(esk1_0,X1),X2)=k9_relat_1(esk1_0,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_38, c_0_21])).
% 0.19/0.41  fof(c_0_46, plain, ![X28, X29]:(~v1_relat_1(X29)|~v1_funct_1(X29)|r1_tarski(k9_relat_1(X29,k10_relat_1(X29,X28)),X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 0.19/0.41  fof(c_0_47, plain, ![X17, X18, X19]:(~v1_relat_1(X18)|(~v1_relat_1(X19)|(~r1_tarski(X18,X19)|r1_tarski(k10_relat_1(X18,X17),k10_relat_1(X19,X17))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t179_relat_1])])])).
% 0.19/0.41  fof(c_0_48, plain, ![X20, X21]:(~v1_relat_1(X21)|r1_tarski(k7_relat_1(X21,X20),X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).
% 0.19/0.41  cnf(c_0_49, negated_conjecture, (r1_tarski(X1,k10_relat_1(k7_relat_1(esk1_0,X2),X3))|~r1_tarski(k9_relat_1(k7_relat_1(esk1_0,X2),X1),X3)|~r1_tarski(X1,k1_relat_1(k7_relat_1(esk1_0,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])])).
% 0.19/0.41  cnf(c_0_50, negated_conjecture, (r1_tarski(k10_relat_1(esk1_0,esk3_0),k1_relat_1(k7_relat_1(esk1_0,esk2_0)))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_41])]), c_0_44])).
% 0.19/0.41  cnf(c_0_51, negated_conjecture, (k9_relat_1(k7_relat_1(esk1_0,esk2_0),k10_relat_1(esk1_0,esk3_0))=k9_relat_1(esk1_0,k10_relat_1(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_45, c_0_35])).
% 0.19/0.41  cnf(c_0_52, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.41  cnf(c_0_53, plain, (r1_tarski(k10_relat_1(X1,X3),k10_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.41  cnf(c_0_54, plain, (r1_tarski(k7_relat_1(X1,X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.41  fof(c_0_55, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.41  cnf(c_0_56, negated_conjecture, (r1_tarski(k10_relat_1(esk1_0,esk3_0),k10_relat_1(k7_relat_1(esk1_0,esk2_0),X1))|~r1_tarski(k9_relat_1(esk1_0,k10_relat_1(esk1_0,esk3_0)),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])).
% 0.19/0.41  cnf(c_0_57, negated_conjecture, (r1_tarski(k9_relat_1(esk1_0,k10_relat_1(esk1_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_31]), c_0_21])])).
% 0.19/0.41  cnf(c_0_58, negated_conjecture, (r1_tarski(k10_relat_1(X1,X2),k10_relat_1(esk1_0,X2))|~v1_relat_1(X1)|~r1_tarski(X1,esk1_0)), inference(spm,[status(thm)],[c_0_53, c_0_21])).
% 0.19/0.41  cnf(c_0_59, negated_conjecture, (r1_tarski(k7_relat_1(esk1_0,X1),esk1_0)), inference(spm,[status(thm)],[c_0_54, c_0_21])).
% 0.19/0.41  cnf(c_0_60, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.19/0.41  cnf(c_0_61, negated_conjecture, (r1_tarski(k10_relat_1(esk1_0,esk3_0),k10_relat_1(k7_relat_1(esk1_0,esk2_0),esk3_0))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.41  cnf(c_0_62, negated_conjecture, (r1_tarski(k10_relat_1(k7_relat_1(esk1_0,X1),X2),k10_relat_1(esk1_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_41]), c_0_59])])).
% 0.19/0.41  cnf(c_0_63, negated_conjecture, (k10_relat_1(esk1_0,esk3_0)!=k10_relat_1(k7_relat_1(esk1_0,esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.41  cnf(c_0_64, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62])]), c_0_63]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 65
% 0.19/0.41  # Proof object clause steps            : 36
% 0.19/0.41  # Proof object formula steps           : 29
% 0.19/0.41  # Proof object conjectures             : 26
% 0.19/0.41  # Proof object clause conjectures      : 23
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 17
% 0.19/0.41  # Proof object initial formulas used   : 14
% 0.19/0.41  # Proof object generating inferences   : 19
% 0.19/0.41  # Proof object simplifying inferences  : 17
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 14
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 20
% 0.19/0.41  # Removed in clause preprocessing      : 0
% 0.19/0.41  # Initial clauses in saturation        : 20
% 0.19/0.41  # Processed clauses                    : 285
% 0.19/0.41  # ...of these trivial                  : 47
% 0.19/0.41  # ...subsumed                          : 22
% 0.19/0.41  # ...remaining for further processing  : 216
% 0.19/0.41  # Other redundant clauses eliminated   : 2
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 1
% 0.19/0.41  # Backward-rewritten                   : 21
% 0.19/0.41  # Generated clauses                    : 2520
% 0.19/0.41  # ...of the previous two non-trivial   : 1570
% 0.19/0.41  # Contextual simplify-reflections      : 0
% 0.19/0.41  # Paramodulations                      : 2518
% 0.19/0.41  # Factorizations                       : 0
% 0.19/0.41  # Equation resolutions                 : 2
% 0.19/0.41  # Propositional unsat checks           : 0
% 0.19/0.41  #    Propositional check models        : 0
% 0.19/0.41  #    Propositional check unsatisfiable : 0
% 0.19/0.41  #    Propositional clauses             : 0
% 0.19/0.41  #    Propositional clauses after purity: 0
% 0.19/0.41  #    Propositional unsat core size     : 0
% 0.19/0.41  #    Propositional preprocessing time  : 0.000
% 0.19/0.41  #    Propositional encoding time       : 0.000
% 0.19/0.41  #    Propositional solver time         : 0.000
% 0.19/0.41  #    Success case prop preproc time    : 0.000
% 0.19/0.41  #    Success case prop encoding time   : 0.000
% 0.19/0.41  #    Success case prop solver time     : 0.000
% 0.19/0.41  # Current number of processed clauses  : 174
% 0.19/0.41  #    Positive orientable unit clauses  : 123
% 0.19/0.41  #    Positive unorientable unit clauses: 0
% 0.19/0.41  #    Negative unit clauses             : 1
% 0.19/0.41  #    Non-unit-clauses                  : 50
% 0.19/0.41  # Current number of unprocessed clauses: 1314
% 0.19/0.41  # ...number of literals in the above   : 1879
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 40
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 171
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 162
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 23
% 0.19/0.41  # Unit Clause-clause subsumption calls : 13
% 0.19/0.41  # Rewrite failures with RHS unbound    : 0
% 0.19/0.41  # BW rewrite match attempts            : 209
% 0.19/0.41  # BW rewrite match successes           : 20
% 0.19/0.41  # Condensation attempts                : 0
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 48670
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.059 s
% 0.19/0.41  # System time              : 0.006 s
% 0.19/0.41  # Total time               : 0.065 s
% 0.19/0.41  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
