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
% DateTime   : Thu Dec  3 10:50:53 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 195 expanded)
%              Number of clauses        :   45 (  82 expanded)
%              Number of leaves         :   19 (  53 expanded)
%              Depth                    :   13
%              Number of atoms          :  180 ( 346 expanded)
%              Number of equality atoms :   43 ( 115 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t154_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).

fof(t119_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k8_relat_1(X1,X2)) = k3_xboole_0(k2_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(t140_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(k8_relat_1(X1,X3),X2) = k8_relat_1(X1,k7_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t100_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(k7_relat_1(X3,X1),X2) = k7_relat_1(X3,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t125_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k8_relat_1(X1,X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(t105_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( r1_tarski(X2,X3)
           => r1_tarski(k7_relat_1(X2,X1),k7_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).

fof(t88_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k7_relat_1(X2,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(dt_k8_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => v1_relat_1(k8_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(c_0_19,plain,(
    ! [X18,X19] : k1_setfam_1(k2_tarski(X18,X19)) = k3_xboole_0(X18,X19) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_20,plain,(
    ! [X9,X10] : k1_enumset1(X9,X9,X10) = k2_tarski(X9,X10) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2))) ) ),
    inference(assume_negation,[status(cth)],[t154_relat_1])).

fof(c_0_22,plain,(
    ! [X34,X35] :
      ( ~ v1_relat_1(X35)
      | k2_relat_1(k8_relat_1(X34,X35)) = k3_xboole_0(k2_relat_1(X35),X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t119_relat_1])])).

cnf(c_0_23,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_25,plain,(
    ! [X11,X12,X13] : k2_enumset1(X11,X11,X12,X13) = k1_enumset1(X11,X12,X13) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_26,plain,(
    ! [X14,X15,X16,X17] : k3_enumset1(X14,X14,X15,X16,X17) = k2_enumset1(X14,X15,X16,X17) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_27,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & ~ r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

cnf(c_0_28,plain,
    ( k2_relat_1(k8_relat_1(X2,X1)) = k3_xboole_0(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_32,plain,(
    ! [X41,X42] :
      ( ~ v1_relat_1(X42)
      | k2_relat_1(k7_relat_1(X42,X41)) = k9_relat_1(X42,X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_33,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X24)
      | v1_relat_1(k7_relat_1(X24,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_34,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X22)
      | ~ m1_subset_1(X23,k1_zfmisc_1(X22))
      | v1_relat_1(X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_35,plain,(
    ! [X20,X21] :
      ( ( ~ m1_subset_1(X20,k1_zfmisc_1(X21))
        | r1_tarski(X20,X21) )
      & ( ~ r1_tarski(X20,X21)
        | m1_subset_1(X20,k1_zfmisc_1(X21)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_36,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( k2_relat_1(k8_relat_1(X2,X1)) = k1_setfam_1(k3_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_38,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_40,plain,(
    ! [X43,X44] :
      ( ( r1_tarski(k1_relat_1(X43),k1_relat_1(X44))
        | ~ r1_tarski(X43,X44)
        | ~ v1_relat_1(X44)
        | ~ v1_relat_1(X43) )
      & ( r1_tarski(k2_relat_1(X43),k2_relat_1(X44))
        | ~ r1_tarski(X43,X44)
        | ~ v1_relat_1(X44)
        | ~ v1_relat_1(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

cnf(c_0_41,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk3_0,k1_setfam_1(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))),k1_setfam_1(k3_enumset1(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_31]),c_0_31])).

cnf(c_0_44,plain,
    ( k1_setfam_1(k3_enumset1(k9_relat_1(X1,X2),k9_relat_1(X1,X2),k9_relat_1(X1,X2),k9_relat_1(X1,X2),X3)) = k2_relat_1(k8_relat_1(X3,k7_relat_1(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_46,plain,(
    ! [X38,X39,X40] :
      ( ~ v1_relat_1(X40)
      | k7_relat_1(k8_relat_1(X38,X40),X39) = k8_relat_1(X38,k7_relat_1(X40,X39)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t140_relat_1])])).

cnf(c_0_47,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_49,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_50,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk3_0,k1_setfam_1(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))),k2_relat_1(k8_relat_1(k9_relat_1(esk3_0,esk2_0),k7_relat_1(esk3_0,esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])])).

cnf(c_0_51,plain,
    ( k7_relat_1(k8_relat_1(X2,X1),X3) = k8_relat_1(X2,k7_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(csr,[status(thm)],[c_0_47,c_0_48])).

fof(c_0_53,plain,(
    ! [X28,X29,X30] :
      ( ~ v1_relat_1(X30)
      | k7_relat_1(k7_relat_1(X30,X28),X29) = k7_relat_1(X30,k3_xboole_0(X28,X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).

fof(c_0_54,plain,(
    ! [X7,X8] : k2_tarski(X7,X8) = k2_tarski(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_55,plain,(
    ! [X36,X37] :
      ( ~ v1_relat_1(X37)
      | ~ r1_tarski(k2_relat_1(X37),X36)
      | k8_relat_1(X36,X37) = X37 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_57,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk3_0,k1_setfam_1(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))),k2_relat_1(k7_relat_1(k8_relat_1(k9_relat_1(esk3_0,esk2_0),esk3_0),esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_45])])).

cnf(c_0_58,plain,
    ( r1_tarski(k2_relat_1(X1),k9_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k7_relat_1(X2,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_38]),c_0_39])).

cnf(c_0_59,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_60,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_61,plain,
    ( k8_relat_1(X2,X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_56])).

cnf(c_0_63,negated_conjecture,
    ( ~ v1_relat_1(k8_relat_1(k9_relat_1(esk3_0,esk2_0),esk3_0))
    | ~ r1_tarski(k9_relat_1(esk3_0,k1_setfam_1(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))),k9_relat_1(k8_relat_1(k9_relat_1(esk3_0,esk2_0),esk3_0),esk1_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_38])).

cnf(c_0_64,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X3,X4))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k7_relat_1(X1,X2),k7_relat_1(X3,X4)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_38])).

cnf(c_0_65,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_66,plain,
    ( k3_enumset1(X1,X1,X1,X1,X2) = k3_enumset1(X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_24]),c_0_24]),c_0_30]),c_0_30]),c_0_31]),c_0_31])).

fof(c_0_67,plain,(
    ! [X31,X32,X33] :
      ( ~ v1_relat_1(X32)
      | ~ v1_relat_1(X33)
      | ~ r1_tarski(X32,X33)
      | r1_tarski(k7_relat_1(X32,X31),k7_relat_1(X33,X31)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t105_relat_1])])])).

fof(c_0_68,plain,(
    ! [X45,X46] :
      ( ~ v1_relat_1(X46)
      | r1_tarski(k7_relat_1(X46,X45),X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).

cnf(c_0_69,plain,
    ( k8_relat_1(k2_relat_1(X1),X1) = X1
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

fof(c_0_70,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X27)
      | v1_relat_1(k8_relat_1(X26,X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).

cnf(c_0_71,negated_conjecture,
    ( ~ v1_relat_1(k8_relat_1(k9_relat_1(esk3_0,esk2_0),esk3_0))
    | ~ r1_tarski(k7_relat_1(esk3_0,k1_setfam_1(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))),k7_relat_1(k8_relat_1(k9_relat_1(esk3_0,esk2_0),esk3_0),esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_45])])).

cnf(c_0_72,plain,
    ( k7_relat_1(X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3))) = k7_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_73,plain,
    ( r1_tarski(k7_relat_1(X1,X3),k7_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_74,plain,
    ( r1_tarski(k7_relat_1(X1,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_75,plain,
    ( k7_relat_1(k8_relat_1(k2_relat_1(k7_relat_1(X1,X2)),X1),X2) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_51]),c_0_39])).

cnf(c_0_76,plain,
    ( v1_relat_1(k8_relat_1(X2,X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_77,negated_conjecture,
    ( ~ v1_relat_1(k8_relat_1(k9_relat_1(esk3_0,esk2_0),esk3_0))
    | ~ r1_tarski(k7_relat_1(k7_relat_1(esk3_0,esk2_0),esk1_0),k7_relat_1(k8_relat_1(k9_relat_1(esk3_0,esk2_0),esk3_0),esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_45])])).

cnf(c_0_78,plain,
    ( r1_tarski(k7_relat_1(X1,X2),k7_relat_1(X3,X2))
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,X3) ),
    inference(csr,[status(thm)],[c_0_73,c_0_48])).

cnf(c_0_79,plain,
    ( r1_tarski(k7_relat_1(X1,X2),k8_relat_1(k2_relat_1(k7_relat_1(X1,X2)),X1))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76])).

cnf(c_0_80,negated_conjecture,
    ( ~ v1_relat_1(k8_relat_1(k9_relat_1(esk3_0,esk2_0),esk3_0))
    | ~ r1_tarski(k7_relat_1(esk3_0,esk2_0),k8_relat_1(k9_relat_1(esk3_0,esk2_0),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_81,plain,
    ( r1_tarski(k7_relat_1(X1,X2),k8_relat_1(k9_relat_1(X1,X2),X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_79,c_0_38])).

cnf(c_0_82,negated_conjecture,
    ( ~ v1_relat_1(k8_relat_1(k9_relat_1(esk3_0,esk2_0),esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_45])])).

cnf(c_0_83,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_76]),c_0_45])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:30:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.44  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.44  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.44  #
% 0.21/0.44  # Preprocessing time       : 0.028 s
% 0.21/0.44  # Presaturation interreduction done
% 0.21/0.44  
% 0.21/0.44  # Proof found!
% 0.21/0.44  # SZS status Theorem
% 0.21/0.44  # SZS output start CNFRefutation
% 0.21/0.44  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.21/0.44  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.44  fof(t154_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_relat_1)).
% 0.21/0.44  fof(t119_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k8_relat_1(X1,X2))=k3_xboole_0(k2_relat_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_relat_1)).
% 0.21/0.44  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.21/0.44  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.21/0.44  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.21/0.44  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.21/0.44  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.21/0.44  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.21/0.44  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 0.21/0.44  fof(t140_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(k8_relat_1(X1,X3),X2)=k8_relat_1(X1,k7_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_relat_1)).
% 0.21/0.44  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.44  fof(t100_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k7_relat_1(X3,k3_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 0.21/0.44  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.21/0.44  fof(t125_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X2),X1)=>k8_relat_1(X1,X2)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 0.21/0.44  fof(t105_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X2,X3)=>r1_tarski(k7_relat_1(X2,X1),k7_relat_1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_relat_1)).
% 0.21/0.44  fof(t88_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k7_relat_1(X2,X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 0.21/0.44  fof(dt_k8_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>v1_relat_1(k8_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 0.21/0.44  fof(c_0_19, plain, ![X18, X19]:k1_setfam_1(k2_tarski(X18,X19))=k3_xboole_0(X18,X19), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.21/0.44  fof(c_0_20, plain, ![X9, X10]:k1_enumset1(X9,X9,X10)=k2_tarski(X9,X10), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.44  fof(c_0_21, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2))))), inference(assume_negation,[status(cth)],[t154_relat_1])).
% 0.21/0.44  fof(c_0_22, plain, ![X34, X35]:(~v1_relat_1(X35)|k2_relat_1(k8_relat_1(X34,X35))=k3_xboole_0(k2_relat_1(X35),X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t119_relat_1])])).
% 0.21/0.44  cnf(c_0_23, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.44  cnf(c_0_24, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.44  fof(c_0_25, plain, ![X11, X12, X13]:k2_enumset1(X11,X11,X12,X13)=k1_enumset1(X11,X12,X13), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.21/0.44  fof(c_0_26, plain, ![X14, X15, X16, X17]:k3_enumset1(X14,X14,X15,X16,X17)=k2_enumset1(X14,X15,X16,X17), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.21/0.44  fof(c_0_27, negated_conjecture, (v1_relat_1(esk3_0)&~r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.21/0.44  cnf(c_0_28, plain, (k2_relat_1(k8_relat_1(X2,X1))=k3_xboole_0(k2_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.44  cnf(c_0_29, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.21/0.44  cnf(c_0_30, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.44  cnf(c_0_31, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.44  fof(c_0_32, plain, ![X41, X42]:(~v1_relat_1(X42)|k2_relat_1(k7_relat_1(X42,X41))=k9_relat_1(X42,X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.21/0.44  fof(c_0_33, plain, ![X24, X25]:(~v1_relat_1(X24)|v1_relat_1(k7_relat_1(X24,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.21/0.44  fof(c_0_34, plain, ![X22, X23]:(~v1_relat_1(X22)|(~m1_subset_1(X23,k1_zfmisc_1(X22))|v1_relat_1(X23))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.21/0.44  fof(c_0_35, plain, ![X20, X21]:((~m1_subset_1(X20,k1_zfmisc_1(X21))|r1_tarski(X20,X21))&(~r1_tarski(X20,X21)|m1_subset_1(X20,k1_zfmisc_1(X21)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.21/0.44  cnf(c_0_36, negated_conjecture, (~r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.44  cnf(c_0_37, plain, (k2_relat_1(k8_relat_1(X2,X1))=k1_setfam_1(k3_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31])).
% 0.21/0.44  cnf(c_0_38, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.45  cnf(c_0_39, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.45  fof(c_0_40, plain, ![X43, X44]:((r1_tarski(k1_relat_1(X43),k1_relat_1(X44))|~r1_tarski(X43,X44)|~v1_relat_1(X44)|~v1_relat_1(X43))&(r1_tarski(k2_relat_1(X43),k2_relat_1(X44))|~r1_tarski(X43,X44)|~v1_relat_1(X44)|~v1_relat_1(X43))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.21/0.45  cnf(c_0_41, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.45  cnf(c_0_42, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.45  cnf(c_0_43, negated_conjecture, (~r1_tarski(k9_relat_1(esk3_0,k1_setfam_1(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))),k1_setfam_1(k3_enumset1(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_31]), c_0_31])).
% 0.21/0.45  cnf(c_0_44, plain, (k1_setfam_1(k3_enumset1(k9_relat_1(X1,X2),k9_relat_1(X1,X2),k9_relat_1(X1,X2),k9_relat_1(X1,X2),X3))=k2_relat_1(k8_relat_1(X3,k7_relat_1(X1,X2)))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])).
% 0.21/0.45  cnf(c_0_45, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.45  fof(c_0_46, plain, ![X38, X39, X40]:(~v1_relat_1(X40)|k7_relat_1(k8_relat_1(X38,X40),X39)=k8_relat_1(X38,k7_relat_1(X40,X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t140_relat_1])])).
% 0.21/0.45  cnf(c_0_47, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.21/0.45  cnf(c_0_48, plain, (v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.21/0.45  fof(c_0_49, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.45  cnf(c_0_50, negated_conjecture, (~r1_tarski(k9_relat_1(esk3_0,k1_setfam_1(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))),k2_relat_1(k8_relat_1(k9_relat_1(esk3_0,esk2_0),k7_relat_1(esk3_0,esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])])).
% 0.21/0.45  cnf(c_0_51, plain, (k7_relat_1(k8_relat_1(X2,X1),X3)=k8_relat_1(X2,k7_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.21/0.45  cnf(c_0_52, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(csr,[status(thm)],[c_0_47, c_0_48])).
% 0.21/0.45  fof(c_0_53, plain, ![X28, X29, X30]:(~v1_relat_1(X30)|k7_relat_1(k7_relat_1(X30,X28),X29)=k7_relat_1(X30,k3_xboole_0(X28,X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).
% 0.21/0.45  fof(c_0_54, plain, ![X7, X8]:k2_tarski(X7,X8)=k2_tarski(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.21/0.45  fof(c_0_55, plain, ![X36, X37]:(~v1_relat_1(X37)|(~r1_tarski(k2_relat_1(X37),X36)|k8_relat_1(X36,X37)=X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).
% 0.21/0.45  cnf(c_0_56, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.21/0.45  cnf(c_0_57, negated_conjecture, (~r1_tarski(k9_relat_1(esk3_0,k1_setfam_1(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))),k2_relat_1(k7_relat_1(k8_relat_1(k9_relat_1(esk3_0,esk2_0),esk3_0),esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_45])])).
% 0.21/0.45  cnf(c_0_58, plain, (r1_tarski(k2_relat_1(X1),k9_relat_1(X2,X3))|~v1_relat_1(X2)|~r1_tarski(X1,k7_relat_1(X2,X3))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_38]), c_0_39])).
% 0.21/0.45  cnf(c_0_59, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.21/0.45  cnf(c_0_60, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.21/0.45  cnf(c_0_61, plain, (k8_relat_1(X2,X1)=X1|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.21/0.45  cnf(c_0_62, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_56])).
% 0.21/0.45  cnf(c_0_63, negated_conjecture, (~v1_relat_1(k8_relat_1(k9_relat_1(esk3_0,esk2_0),esk3_0))|~r1_tarski(k9_relat_1(esk3_0,k1_setfam_1(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))),k9_relat_1(k8_relat_1(k9_relat_1(esk3_0,esk2_0),esk3_0),esk1_0))), inference(spm,[status(thm)],[c_0_57, c_0_38])).
% 0.21/0.45  cnf(c_0_64, plain, (r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X3,X4))|~v1_relat_1(X3)|~v1_relat_1(X1)|~r1_tarski(k7_relat_1(X1,X2),k7_relat_1(X3,X4))), inference(spm,[status(thm)],[c_0_58, c_0_38])).
% 0.21/0.45  cnf(c_0_65, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_29]), c_0_30]), c_0_31])).
% 0.21/0.45  cnf(c_0_66, plain, (k3_enumset1(X1,X1,X1,X1,X2)=k3_enumset1(X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_24]), c_0_24]), c_0_30]), c_0_30]), c_0_31]), c_0_31])).
% 0.21/0.45  fof(c_0_67, plain, ![X31, X32, X33]:(~v1_relat_1(X32)|(~v1_relat_1(X33)|(~r1_tarski(X32,X33)|r1_tarski(k7_relat_1(X32,X31),k7_relat_1(X33,X31))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t105_relat_1])])])).
% 0.21/0.45  fof(c_0_68, plain, ![X45, X46]:(~v1_relat_1(X46)|r1_tarski(k7_relat_1(X46,X45),X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).
% 0.21/0.45  cnf(c_0_69, plain, (k8_relat_1(k2_relat_1(X1),X1)=X1|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.21/0.45  fof(c_0_70, plain, ![X26, X27]:(~v1_relat_1(X27)|v1_relat_1(k8_relat_1(X26,X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).
% 0.21/0.45  cnf(c_0_71, negated_conjecture, (~v1_relat_1(k8_relat_1(k9_relat_1(esk3_0,esk2_0),esk3_0))|~r1_tarski(k7_relat_1(esk3_0,k1_setfam_1(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))),k7_relat_1(k8_relat_1(k9_relat_1(esk3_0,esk2_0),esk3_0),esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_45])])).
% 0.21/0.45  cnf(c_0_72, plain, (k7_relat_1(X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3)))=k7_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.21/0.45  cnf(c_0_73, plain, (r1_tarski(k7_relat_1(X1,X3),k7_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.21/0.45  cnf(c_0_74, plain, (r1_tarski(k7_relat_1(X1,X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.21/0.45  cnf(c_0_75, plain, (k7_relat_1(k8_relat_1(k2_relat_1(k7_relat_1(X1,X2)),X1),X2)=k7_relat_1(X1,X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_51]), c_0_39])).
% 0.21/0.45  cnf(c_0_76, plain, (v1_relat_1(k8_relat_1(X2,X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.21/0.45  cnf(c_0_77, negated_conjecture, (~v1_relat_1(k8_relat_1(k9_relat_1(esk3_0,esk2_0),esk3_0))|~r1_tarski(k7_relat_1(k7_relat_1(esk3_0,esk2_0),esk1_0),k7_relat_1(k8_relat_1(k9_relat_1(esk3_0,esk2_0),esk3_0),esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_45])])).
% 0.21/0.45  cnf(c_0_78, plain, (r1_tarski(k7_relat_1(X1,X2),k7_relat_1(X3,X2))|~v1_relat_1(X3)|~r1_tarski(X1,X3)), inference(csr,[status(thm)],[c_0_73, c_0_48])).
% 0.21/0.45  cnf(c_0_79, plain, (r1_tarski(k7_relat_1(X1,X2),k8_relat_1(k2_relat_1(k7_relat_1(X1,X2)),X1))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76])).
% 0.21/0.45  cnf(c_0_80, negated_conjecture, (~v1_relat_1(k8_relat_1(k9_relat_1(esk3_0,esk2_0),esk3_0))|~r1_tarski(k7_relat_1(esk3_0,esk2_0),k8_relat_1(k9_relat_1(esk3_0,esk2_0),esk3_0))), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.21/0.45  cnf(c_0_81, plain, (r1_tarski(k7_relat_1(X1,X2),k8_relat_1(k9_relat_1(X1,X2),X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_79, c_0_38])).
% 0.21/0.45  cnf(c_0_82, negated_conjecture, (~v1_relat_1(k8_relat_1(k9_relat_1(esk3_0,esk2_0),esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_45])])).
% 0.21/0.45  cnf(c_0_83, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_76]), c_0_45])]), ['proof']).
% 0.21/0.45  # SZS output end CNFRefutation
% 0.21/0.45  # Proof object total steps             : 84
% 0.21/0.45  # Proof object clause steps            : 45
% 0.21/0.45  # Proof object formula steps           : 39
% 0.21/0.45  # Proof object conjectures             : 14
% 0.21/0.45  # Proof object clause conjectures      : 11
% 0.21/0.45  # Proof object formula conjectures     : 3
% 0.21/0.45  # Proof object initial clauses used    : 20
% 0.21/0.45  # Proof object initial formulas used   : 19
% 0.21/0.45  # Proof object generating inferences   : 17
% 0.21/0.45  # Proof object simplifying inferences  : 38
% 0.21/0.45  # Training examples: 0 positive, 0 negative
% 0.21/0.45  # Parsed axioms                        : 19
% 0.21/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.45  # Initial clauses                      : 24
% 0.21/0.45  # Removed in clause preprocessing      : 4
% 0.21/0.45  # Initial clauses in saturation        : 20
% 0.21/0.45  # Processed clauses                    : 635
% 0.21/0.45  # ...of these trivial                  : 0
% 0.21/0.45  # ...subsumed                          : 365
% 0.21/0.45  # ...remaining for further processing  : 270
% 0.21/0.45  # Other redundant clauses eliminated   : 2
% 0.21/0.45  # Clauses deleted for lack of memory   : 0
% 0.21/0.45  # Backward-subsumed                    : 1
% 0.21/0.45  # Backward-rewritten                   : 0
% 0.21/0.45  # Generated clauses                    : 2840
% 0.21/0.45  # ...of the previous two non-trivial   : 2818
% 0.21/0.45  # Contextual simplify-reflections      : 53
% 0.21/0.45  # Paramodulations                      : 2838
% 0.21/0.45  # Factorizations                       : 0
% 0.21/0.45  # Equation resolutions                 : 2
% 0.21/0.45  # Propositional unsat checks           : 0
% 0.21/0.45  #    Propositional check models        : 0
% 0.21/0.45  #    Propositional check unsatisfiable : 0
% 0.21/0.45  #    Propositional clauses             : 0
% 0.21/0.45  #    Propositional clauses after purity: 0
% 0.21/0.45  #    Propositional unsat core size     : 0
% 0.21/0.45  #    Propositional preprocessing time  : 0.000
% 0.21/0.45  #    Propositional encoding time       : 0.000
% 0.21/0.45  #    Propositional solver time         : 0.000
% 0.21/0.45  #    Success case prop preproc time    : 0.000
% 0.21/0.45  #    Success case prop encoding time   : 0.000
% 0.21/0.45  #    Success case prop solver time     : 0.000
% 0.21/0.45  # Current number of processed clauses  : 248
% 0.21/0.45  #    Positive orientable unit clauses  : 2
% 0.21/0.45  #    Positive unorientable unit clauses: 1
% 0.21/0.45  #    Negative unit clauses             : 8
% 0.21/0.45  #    Non-unit-clauses                  : 237
% 0.21/0.45  # Current number of unprocessed clauses: 2221
% 0.21/0.45  # ...number of literals in the above   : 9819
% 0.21/0.45  # Current number of archived formulas  : 0
% 0.21/0.45  # Current number of archived clauses   : 24
% 0.21/0.45  # Clause-clause subsumption calls (NU) : 13812
% 0.21/0.45  # Rec. Clause-clause subsumption calls : 6468
% 0.21/0.45  # Non-unit clause-clause subsumptions  : 391
% 0.21/0.45  # Unit Clause-clause subsumption calls : 65
% 0.21/0.45  # Rewrite failures with RHS unbound    : 0
% 0.21/0.45  # BW rewrite match attempts            : 9
% 0.21/0.45  # BW rewrite match successes           : 8
% 0.21/0.45  # Condensation attempts                : 0
% 0.21/0.45  # Condensation successes               : 0
% 0.21/0.45  # Termbank termtop insertions          : 49932
% 0.21/0.45  
% 0.21/0.45  # -------------------------------------------------
% 0.21/0.45  # User time                : 0.097 s
% 0.21/0.45  # System time              : 0.006 s
% 0.21/0.45  # Total time               : 0.104 s
% 0.21/0.45  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
