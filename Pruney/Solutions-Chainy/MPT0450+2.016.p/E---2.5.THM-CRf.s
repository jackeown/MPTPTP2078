%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:32 EST 2020

% Result     : Theorem 0.42s
% Output     : CNFRefutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 661 expanded)
%              Number of clauses        :   45 ( 296 expanded)
%              Number of leaves         :   10 ( 175 expanded)
%              Depth                    :   13
%              Number of atoms          :  171 (1324 expanded)
%              Number of equality atoms :   32 ( 443 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t34_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k3_relat_1(X1),k3_relat_1(X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relat_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t31_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k3_relat_1(X1),k3_relat_1(X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t34_relat_1])).

fof(c_0_11,plain,(
    ! [X24,X25] : k1_setfam_1(k2_tarski(X24,X25)) = k3_xboole_0(X24,X25) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_12,plain,(
    ! [X19,X20] : k1_enumset1(X19,X19,X20) = k2_tarski(X19,X20) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & ~ r1_tarski(k3_relat_1(k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k3_relat_1(esk2_0),k3_relat_1(esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_14,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X21,X22,X23] : k2_enumset1(X21,X21,X22,X23) = k1_enumset1(X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_17,plain,(
    ! [X16,X17,X18] :
      ( ~ r1_tarski(X16,X17)
      | ~ r1_tarski(X16,X18)
      | r1_tarski(X16,k3_xboole_0(X17,X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

fof(c_0_18,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X28)
      | ~ m1_subset_1(X29,k1_zfmisc_1(X28))
      | v1_relat_1(X29) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_19,plain,(
    ! [X26,X27] :
      ( ( ~ m1_subset_1(X26,k1_zfmisc_1(X27))
        | r1_tarski(X26,X27) )
      & ( ~ r1_tarski(X26,X27)
        | m1_subset_1(X26,k1_zfmisc_1(X27)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_20,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k3_relat_1(esk2_0),k3_relat_1(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X30,X31] :
      ( ~ v1_relat_1(X30)
      | ~ v1_relat_1(X31)
      | ~ r1_tarski(X30,X31)
      | r1_tarski(k3_relat_1(X30),k3_relat_1(X31)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_relat_1])])])).

cnf(c_0_25,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_27,plain,(
    ! [X14,X15] : r1_tarski(k3_xboole_0(X14,X15),X14) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_28,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))),k1_setfam_1(k2_enumset1(k3_relat_1(esk2_0),k3_relat_1(esk2_0),k3_relat_1(esk2_0),k3_relat_1(esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_21]),c_0_22]),c_0_22])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_21]),c_0_22])).

cnf(c_0_30,plain,
    ( r1_tarski(k3_relat_1(X1),k3_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))),k3_relat_1(esk3_0))
    | ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))),k3_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,plain,
    ( r1_tarski(k3_relat_1(X1),k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(csr,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_36,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_21]),c_0_22])).

fof(c_0_37,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_38,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))),k3_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36])])).

cnf(c_0_39,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_40,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_42,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_34]),c_0_39])])).

cnf(c_0_46,plain,
    ( X3 = k1_setfam_1(k2_enumset1(X1,X1,X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_21]),c_0_22])).

cnf(c_0_47,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X4)
    | X4 != k1_setfam_1(k2_enumset1(X2,X2,X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_21]),c_0_22])).

cnf(c_0_49,plain,
    ( X3 = k1_setfam_1(k2_enumset1(X1,X1,X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_21]),c_0_22])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X2)
    | X3 != k1_setfam_1(k2_enumset1(X2,X2,X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_21]),c_0_22])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,X2)
    | X3 != k1_setfam_1(k2_enumset1(X4,X4,X4,X2))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_21]),c_0_22])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk1_3(esk2_0,esk3_0,X1),esk2_0)
    | r2_hidden(esk1_3(esk2_0,esk3_0,X1),X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,plain,
    ( X3 = k1_setfam_1(k2_enumset1(X1,X1,X1,X2))
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_21]),c_0_22])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk1_3(esk2_0,esk3_0,X1),esk3_0)
    | r2_hidden(esk1_3(esk2_0,esk3_0,X1),X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_49])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_setfam_1(k2_enumset1(X3,X3,X3,X2))) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk1_3(esk2_0,esk3_0,k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,X1))),k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,X1)))
    | r2_hidden(esk1_3(esk2_0,esk3_0,k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,X1))),esk2_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_36])).

cnf(c_0_59,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = k1_setfam_1(k2_enumset1(X3,X3,X3,X4))
    | ~ r2_hidden(esk1_3(X3,X4,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X4)
    | ~ r2_hidden(esk1_3(X3,X4,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X3)
    | ~ r2_hidden(esk1_3(X3,X4,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X2)
    | ~ r2_hidden(esk1_3(X3,X4,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk1_3(esk2_0,esk3_0,k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,X1))),esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_36]),c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk1_3(esk2_0,esk3_0,k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,X1))),esk2_0)
    | r2_hidden(esk1_3(esk2_0,esk3_0,k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,X1))),X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,X1)) = k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))
    | ~ r2_hidden(esk1_3(esk2_0,esk3_0,k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,X1))),esk2_0)
    | ~ r2_hidden(esk1_3(esk2_0,esk3_0,k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,X1))),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_60])])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk1_3(esk2_0,esk3_0,k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk2_0))),esk2_0) ),
    inference(ef,[status(thm)],[c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)) = k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_63])])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_64]),c_0_36])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:36:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.42/0.58  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.42/0.58  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.42/0.58  #
% 0.42/0.58  # Preprocessing time       : 0.027 s
% 0.42/0.58  # Presaturation interreduction done
% 0.42/0.58  
% 0.42/0.58  # Proof found!
% 0.42/0.58  # SZS status Theorem
% 0.42/0.58  # SZS output start CNFRefutation
% 0.42/0.58  fof(t34_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k3_relat_1(X1),k3_relat_1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relat_1)).
% 0.42/0.58  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.42/0.58  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.42/0.58  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.42/0.58  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.42/0.58  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.42/0.58  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.42/0.58  fof(t31_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 0.42/0.58  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.42/0.58  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.42/0.58  fof(c_0_10, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k3_relat_1(X1),k3_relat_1(X2)))))), inference(assume_negation,[status(cth)],[t34_relat_1])).
% 0.42/0.58  fof(c_0_11, plain, ![X24, X25]:k1_setfam_1(k2_tarski(X24,X25))=k3_xboole_0(X24,X25), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.42/0.58  fof(c_0_12, plain, ![X19, X20]:k1_enumset1(X19,X19,X20)=k2_tarski(X19,X20), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.42/0.58  fof(c_0_13, negated_conjecture, (v1_relat_1(esk2_0)&(v1_relat_1(esk3_0)&~r1_tarski(k3_relat_1(k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k3_relat_1(esk2_0),k3_relat_1(esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.42/0.58  cnf(c_0_14, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.42/0.58  cnf(c_0_15, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.42/0.58  fof(c_0_16, plain, ![X21, X22, X23]:k2_enumset1(X21,X21,X22,X23)=k1_enumset1(X21,X22,X23), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.42/0.58  fof(c_0_17, plain, ![X16, X17, X18]:(~r1_tarski(X16,X17)|~r1_tarski(X16,X18)|r1_tarski(X16,k3_xboole_0(X17,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.42/0.58  fof(c_0_18, plain, ![X28, X29]:(~v1_relat_1(X28)|(~m1_subset_1(X29,k1_zfmisc_1(X28))|v1_relat_1(X29))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.42/0.58  fof(c_0_19, plain, ![X26, X27]:((~m1_subset_1(X26,k1_zfmisc_1(X27))|r1_tarski(X26,X27))&(~r1_tarski(X26,X27)|m1_subset_1(X26,k1_zfmisc_1(X27)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.42/0.58  cnf(c_0_20, negated_conjecture, (~r1_tarski(k3_relat_1(k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k3_relat_1(esk2_0),k3_relat_1(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.42/0.58  cnf(c_0_21, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.42/0.58  cnf(c_0_22, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.42/0.58  cnf(c_0_23, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.42/0.58  fof(c_0_24, plain, ![X30, X31]:(~v1_relat_1(X30)|(~v1_relat_1(X31)|(~r1_tarski(X30,X31)|r1_tarski(k3_relat_1(X30),k3_relat_1(X31))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_relat_1])])])).
% 0.42/0.58  cnf(c_0_25, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.42/0.58  cnf(c_0_26, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.42/0.58  fof(c_0_27, plain, ![X14, X15]:r1_tarski(k3_xboole_0(X14,X15),X14), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.42/0.58  cnf(c_0_28, negated_conjecture, (~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))),k1_setfam_1(k2_enumset1(k3_relat_1(esk2_0),k3_relat_1(esk2_0),k3_relat_1(esk2_0),k3_relat_1(esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_21]), c_0_22]), c_0_22])).
% 0.42/0.58  cnf(c_0_29, plain, (r1_tarski(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_21]), c_0_22])).
% 0.42/0.58  cnf(c_0_30, plain, (r1_tarski(k3_relat_1(X1),k3_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.42/0.58  cnf(c_0_31, plain, (v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.42/0.58  cnf(c_0_32, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.42/0.58  cnf(c_0_33, negated_conjecture, (~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))),k3_relat_1(esk3_0))|~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))),k3_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.42/0.58  cnf(c_0_34, plain, (r1_tarski(k3_relat_1(X1),k3_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(csr,[status(thm)],[c_0_30, c_0_31])).
% 0.42/0.58  cnf(c_0_35, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.42/0.58  cnf(c_0_36, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_21]), c_0_22])).
% 0.42/0.58  fof(c_0_37, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6))&(r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k3_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k3_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))&(r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.42/0.58  cnf(c_0_38, negated_conjecture, (~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))),k3_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36])])).
% 0.42/0.58  cnf(c_0_39, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.42/0.58  cnf(c_0_40, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.42/0.58  cnf(c_0_41, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.42/0.58  cnf(c_0_42, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.42/0.58  cnf(c_0_43, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.42/0.58  cnf(c_0_44, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.42/0.58  cnf(c_0_45, negated_conjecture, (~r1_tarski(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_34]), c_0_39])])).
% 0.42/0.58  cnf(c_0_46, plain, (X3=k1_setfam_1(k2_enumset1(X1,X1,X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_21]), c_0_22])).
% 0.42/0.58  cnf(c_0_47, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.42/0.58  cnf(c_0_48, plain, (r2_hidden(X1,X4)|X4!=k1_setfam_1(k2_enumset1(X2,X2,X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_21]), c_0_22])).
% 0.42/0.58  cnf(c_0_49, plain, (X3=k1_setfam_1(k2_enumset1(X1,X1,X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_21]), c_0_22])).
% 0.42/0.58  cnf(c_0_50, plain, (r2_hidden(X1,X2)|X3!=k1_setfam_1(k2_enumset1(X2,X2,X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_21]), c_0_22])).
% 0.42/0.58  cnf(c_0_51, plain, (r2_hidden(X1,X2)|X3!=k1_setfam_1(k2_enumset1(X4,X4,X4,X2))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_21]), c_0_22])).
% 0.42/0.58  cnf(c_0_52, negated_conjecture, (r2_hidden(esk1_3(esk2_0,esk3_0,X1),esk2_0)|r2_hidden(esk1_3(esk2_0,esk3_0,X1),X1)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.42/0.58  cnf(c_0_53, plain, (X3=k1_setfam_1(k2_enumset1(X1,X1,X1,X2))|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_21]), c_0_22])).
% 0.42/0.58  cnf(c_0_54, plain, (r2_hidden(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_48])).
% 0.42/0.58  cnf(c_0_55, negated_conjecture, (r2_hidden(esk1_3(esk2_0,esk3_0,X1),esk3_0)|r2_hidden(esk1_3(esk2_0,esk3_0,X1),X1)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_45, c_0_49])).
% 0.42/0.58  cnf(c_0_56, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))), inference(er,[status(thm)],[c_0_50])).
% 0.42/0.58  cnf(c_0_57, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_setfam_1(k2_enumset1(X3,X3,X3,X2)))), inference(er,[status(thm)],[c_0_51])).
% 0.42/0.58  cnf(c_0_58, negated_conjecture, (r2_hidden(esk1_3(esk2_0,esk3_0,k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,X1))),k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,X1)))|r2_hidden(esk1_3(esk2_0,esk3_0,k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,X1))),esk2_0)), inference(spm,[status(thm)],[c_0_52, c_0_36])).
% 0.42/0.58  cnf(c_0_59, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=k1_setfam_1(k2_enumset1(X3,X3,X3,X4))|~r2_hidden(esk1_3(X3,X4,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X4)|~r2_hidden(esk1_3(X3,X4,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X3)|~r2_hidden(esk1_3(X3,X4,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X2)|~r2_hidden(esk1_3(X3,X4,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X1)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.42/0.58  cnf(c_0_60, negated_conjecture, (r2_hidden(esk1_3(esk2_0,esk3_0,k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,X1))),esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_36]), c_0_56])).
% 0.42/0.58  cnf(c_0_61, negated_conjecture, (r2_hidden(esk1_3(esk2_0,esk3_0,k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,X1))),esk2_0)|r2_hidden(esk1_3(esk2_0,esk3_0,k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,X1))),X1)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.42/0.58  cnf(c_0_62, negated_conjecture, (k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,X1))=k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))|~r2_hidden(esk1_3(esk2_0,esk3_0,k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,X1))),esk2_0)|~r2_hidden(esk1_3(esk2_0,esk3_0,k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,X1))),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_60])])).
% 0.42/0.58  cnf(c_0_63, negated_conjecture, (r2_hidden(esk1_3(esk2_0,esk3_0,k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk2_0))),esk2_0)), inference(ef,[status(thm)],[c_0_61])).
% 0.42/0.58  cnf(c_0_64, negated_conjecture, (k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))=k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_63])])).
% 0.42/0.58  cnf(c_0_65, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_64]), c_0_36])]), ['proof']).
% 0.42/0.58  # SZS output end CNFRefutation
% 0.42/0.58  # Proof object total steps             : 66
% 0.42/0.58  # Proof object clause steps            : 45
% 0.42/0.58  # Proof object formula steps           : 21
% 0.42/0.58  # Proof object conjectures             : 19
% 0.42/0.58  # Proof object clause conjectures      : 16
% 0.42/0.58  # Proof object formula conjectures     : 3
% 0.42/0.58  # Proof object initial clauses used    : 17
% 0.42/0.58  # Proof object initial formulas used   : 10
% 0.42/0.58  # Proof object generating inferences   : 13
% 0.42/0.58  # Proof object simplifying inferences  : 38
% 0.42/0.58  # Training examples: 0 positive, 0 negative
% 0.42/0.58  # Parsed axioms                        : 10
% 0.42/0.58  # Removed by relevancy pruning/SinE    : 0
% 0.42/0.58  # Initial clauses                      : 18
% 0.42/0.58  # Removed in clause preprocessing      : 3
% 0.42/0.58  # Initial clauses in saturation        : 15
% 0.42/0.58  # Processed clauses                    : 610
% 0.42/0.58  # ...of these trivial                  : 13
% 0.42/0.58  # ...subsumed                          : 297
% 0.42/0.58  # ...remaining for further processing  : 300
% 0.42/0.58  # Other redundant clauses eliminated   : 3
% 0.42/0.58  # Clauses deleted for lack of memory   : 0
% 0.42/0.58  # Backward-subsumed                    : 42
% 0.42/0.58  # Backward-rewritten                   : 71
% 0.42/0.58  # Generated clauses                    : 8770
% 0.42/0.58  # ...of the previous two non-trivial   : 8134
% 0.42/0.58  # Contextual simplify-reflections      : 36
% 0.42/0.58  # Paramodulations                      : 8655
% 0.42/0.58  # Factorizations                       : 112
% 0.42/0.58  # Equation resolutions                 : 3
% 0.42/0.58  # Propositional unsat checks           : 0
% 0.42/0.58  #    Propositional check models        : 0
% 0.42/0.58  #    Propositional check unsatisfiable : 0
% 0.42/0.58  #    Propositional clauses             : 0
% 0.42/0.58  #    Propositional clauses after purity: 0
% 0.42/0.58  #    Propositional unsat core size     : 0
% 0.42/0.58  #    Propositional preprocessing time  : 0.000
% 0.42/0.58  #    Propositional encoding time       : 0.000
% 0.42/0.58  #    Propositional solver time         : 0.000
% 0.42/0.58  #    Success case prop preproc time    : 0.000
% 0.42/0.58  #    Success case prop encoding time   : 0.000
% 0.42/0.58  #    Success case prop solver time     : 0.000
% 0.42/0.58  # Current number of processed clauses  : 169
% 0.42/0.58  #    Positive orientable unit clauses  : 12
% 0.42/0.58  #    Positive unorientable unit clauses: 0
% 0.42/0.58  #    Negative unit clauses             : 3
% 0.42/0.58  #    Non-unit-clauses                  : 154
% 0.42/0.58  # Current number of unprocessed clauses: 7383
% 0.42/0.58  # ...number of literals in the above   : 41175
% 0.42/0.58  # Current number of archived formulas  : 0
% 0.42/0.58  # Current number of archived clauses   : 131
% 0.42/0.58  # Clause-clause subsumption calls (NU) : 18213
% 0.42/0.58  # Rec. Clause-clause subsumption calls : 5878
% 0.42/0.58  # Non-unit clause-clause subsumptions  : 268
% 0.42/0.58  # Unit Clause-clause subsumption calls : 596
% 0.42/0.58  # Rewrite failures with RHS unbound    : 0
% 0.42/0.58  # BW rewrite match attempts            : 56
% 0.42/0.58  # BW rewrite match successes           : 9
% 0.42/0.58  # Condensation attempts                : 0
% 0.42/0.58  # Condensation successes               : 0
% 0.42/0.58  # Termbank termtop insertions          : 226661
% 0.42/0.58  
% 0.42/0.58  # -------------------------------------------------
% 0.42/0.58  # User time                : 0.225 s
% 0.42/0.58  # System time              : 0.010 s
% 0.42/0.58  # Total time               : 0.235 s
% 0.42/0.58  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
