%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:38 EST 2020

% Result     : Theorem 5.26s
% Output     : CNFRefutation 5.26s
% Verified   : 
% Statistics : Number of formulae       :  111 (1126 expanded)
%              Number of clauses        :   80 ( 483 expanded)
%              Number of leaves         :   15 ( 311 expanded)
%              Depth                    :   25
%              Number of atoms          :  304 (2842 expanded)
%              Number of equality atoms :  148 (1608 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(t8_setfam_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(k1_setfam_1(X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_setfam_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t52_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t48_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( r1_tarski(X1,X2)
               => r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(c_0_15,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21,X22,X23,X24] :
      ( ( ~ r2_hidden(X19,X18)
        | X19 = X15
        | X19 = X16
        | X19 = X17
        | X18 != k1_enumset1(X15,X16,X17) )
      & ( X20 != X15
        | r2_hidden(X20,X18)
        | X18 != k1_enumset1(X15,X16,X17) )
      & ( X20 != X16
        | r2_hidden(X20,X18)
        | X18 != k1_enumset1(X15,X16,X17) )
      & ( X20 != X17
        | r2_hidden(X20,X18)
        | X18 != k1_enumset1(X15,X16,X17) )
      & ( esk1_4(X21,X22,X23,X24) != X21
        | ~ r2_hidden(esk1_4(X21,X22,X23,X24),X24)
        | X24 = k1_enumset1(X21,X22,X23) )
      & ( esk1_4(X21,X22,X23,X24) != X22
        | ~ r2_hidden(esk1_4(X21,X22,X23,X24),X24)
        | X24 = k1_enumset1(X21,X22,X23) )
      & ( esk1_4(X21,X22,X23,X24) != X23
        | ~ r2_hidden(esk1_4(X21,X22,X23,X24),X24)
        | X24 = k1_enumset1(X21,X22,X23) )
      & ( r2_hidden(esk1_4(X21,X22,X23,X24),X24)
        | esk1_4(X21,X22,X23,X24) = X21
        | esk1_4(X21,X22,X23,X24) = X22
        | esk1_4(X21,X22,X23,X24) = X23
        | X24 = k1_enumset1(X21,X22,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_16,plain,(
    ! [X28,X29,X30] : k2_enumset1(X28,X28,X29,X30) = k1_enumset1(X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_17,plain,(
    ! [X31,X32,X33,X34] : k3_enumset1(X31,X31,X32,X33,X34) = k2_enumset1(X31,X32,X33,X34) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_18,plain,(
    ! [X35,X36,X37,X38,X39] : k4_enumset1(X35,X35,X36,X37,X38,X39) = k3_enumset1(X35,X36,X37,X38,X39) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_19,plain,(
    ! [X40,X41,X42,X43,X44,X45] : k5_enumset1(X40,X40,X41,X42,X43,X44,X45) = k4_enumset1(X40,X41,X42,X43,X44,X45) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_20,plain,(
    ! [X46,X47,X48,X49,X50,X51,X52] : k6_enumset1(X46,X46,X47,X48,X49,X50,X51,X52) = k5_enumset1(X46,X47,X48,X49,X50,X51,X52) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,plain,(
    ! [X57,X58,X59] :
      ( ~ r2_hidden(X57,X58)
      | ~ r1_tarski(X57,X59)
      | r1_tarski(k1_setfam_1(X58),X59) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_setfam_1])])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X2,X2,X2,X2,X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26])).

fof(c_0_29,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X2,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_31,plain,
    ( r1_tarski(k1_setfam_1(X2),X3)
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_28])])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X4,X4,X4,X4,X4,X2,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26])).

fof(c_0_35,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3] :
                ( v1_relat_1(X3)
               => r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t52_relat_1])).

fof(c_0_36,plain,(
    ! [X55,X56] :
      ( ( ~ m1_subset_1(X55,k1_zfmisc_1(X56))
        | r1_tarski(X55,X56) )
      & ( ~ r1_tarski(X55,X56)
        | m1_subset_1(X55,k1_zfmisc_1(X56)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_37,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)),X4)
    | ~ r1_tarski(X1,X4) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_34])])).

fof(c_0_40,plain,(
    ! [X62,X63,X64] :
      ( ~ v1_relat_1(X62)
      | ~ v1_relat_1(X63)
      | ~ v1_relat_1(X64)
      | ~ r1_tarski(X62,X63)
      | r1_tarski(k5_relat_1(X64,X62),k5_relat_1(X64,X63)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_relat_1])])])).

fof(c_0_41,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & v1_relat_1(esk4_0)
    & ~ r1_tarski(k5_relat_1(esk2_0,k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_35])])])).

fof(c_0_42,plain,(
    ! [X60,X61] :
      ( ~ v1_relat_1(X60)
      | ~ m1_subset_1(X61,k1_zfmisc_1(X60))
      | v1_relat_1(X61) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

cnf(c_0_43,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)),X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)),X4)
    | ~ r1_tarski(X2,X4) ),
    inference(spm,[status(thm)],[c_0_31,c_0_39])).

fof(c_0_46,plain,(
    ! [X53,X54] : k1_setfam_1(k2_tarski(X53,X54)) = k3_xboole_0(X53,X54) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_47,plain,(
    ! [X26,X27] : k1_enumset1(X26,X26,X27) = k2_tarski(X26,X27) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_48,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_49,plain,
    ( r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,plain,
    ( m1_subset_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_53,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_38])).

cnf(c_0_54,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_55,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_56,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_57,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X4)
    | esk1_4(X1,X2,X3,X4) = X1
    | esk1_4(X1,X2,X3,X4) = X2
    | esk1_4(X1,X2,X3,X4) = X3
    | X4 = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_58,plain,(
    ! [X12,X13,X14] :
      ( ~ r1_tarski(X12,X13)
      | ~ r1_tarski(X12,X14)
      | r1_tarski(X12,k3_xboole_0(X13,X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k5_relat_1(X1,X2),k5_relat_1(X1,esk4_0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X2,esk4_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_60,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_61,plain,
    ( v1_relat_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_63,plain,
    ( m1_subset_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_53])).

cnf(c_0_64,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk2_0,k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_65,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_66,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k6_enumset1(X4,X4,X4,X4,X4,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_56])).

cnf(c_0_67,plain,
    ( esk1_4(X1,X2,X3,X4) = X3
    | esk1_4(X1,X2,X3,X4) = X2
    | esk1_4(X1,X2,X3,X4) = X1
    | X4 = k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)
    | r2_hidden(esk1_4(X1,X2,X3,X4),X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk2_0,X1),k5_relat_1(esk2_0,esk4_0))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_70,negated_conjecture,
    ( v1_relat_1(k1_setfam_1(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,X1,X2))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_50])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(k5_relat_1(X1,X2),k5_relat_1(X1,esk3_0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X2,esk3_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_62])).

cnf(c_0_72,plain,
    ( v1_relat_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_63])).

cnf(c_0_73,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),k1_setfam_1(k6_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_65]),c_0_65]),c_0_22]),c_0_22]),c_0_23]),c_0_23]),c_0_24]),c_0_24]),c_0_25]),c_0_25]),c_0_26]),c_0_26])).

cnf(c_0_74,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3) = k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X6)
    | esk1_4(X4,X5,X6,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)) = X4
    | esk1_4(X4,X5,X6,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)) = X5
    | esk1_4(X4,X5,X6,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)) = X6
    | esk1_4(X4,X5,X6,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)) = X3
    | esk1_4(X4,X5,X6,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)) = X2
    | esk1_4(X4,X5,X6,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)) = X1 ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_75,plain,
    ( r1_tarski(X1,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_65]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,X1,X2))),k5_relat_1(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_44])])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk2_0,X1),k5_relat_1(esk2_0,esk3_0))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_60])).

cnf(c_0_78,negated_conjecture,
    ( v1_relat_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,esk3_0,X2))) ),
    inference(spm,[status(thm)],[c_0_72,c_0_62])).

cnf(c_0_79,negated_conjecture,
    ( esk1_4(X1,X2,X3,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) = esk3_0
    | esk1_4(X1,X2,X3,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) = esk4_0
    | esk1_4(X1,X2,X3,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) = X3
    | esk1_4(X1,X2,X3,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) = X2
    | esk1_4(X1,X2,X3,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) = X1
    | ~ r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))),k1_setfam_1(k6_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,X1,X2))),k1_setfam_1(k6_enumset1(k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),X3)))
    | ~ r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,X1,X2))),X3) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,esk3_0,X2))),k5_relat_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_53])])).

cnf(c_0_82,negated_conjecture,
    ( esk1_4(X1,X2,X3,k6_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))) = k5_relat_1(esk2_0,esk3_0)
    | esk1_4(X1,X2,X3,k6_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))) = k5_relat_1(esk2_0,esk4_0)
    | esk1_4(X1,X2,X3,k6_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))) = X3
    | esk1_4(X1,X2,X3,k6_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))) = X2
    | esk1_4(X1,X2,X3,k6_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))) = X1
    | esk1_4(X4,X5,X6,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) = esk4_0
    | esk1_4(X4,X5,X6,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) = esk3_0
    | esk1_4(X4,X5,X6,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) = X4
    | esk1_4(X4,X5,X6,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) = X5
    | esk1_4(X4,X5,X6,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) = X6
    | ~ r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X6))),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))) ),
    inference(spm,[status(thm)],[c_0_79,c_0_74])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk3_0,X1))),k1_setfam_1(k6_enumset1(k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_84,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_85,plain,
    ( X4 = k1_enumset1(X1,X2,X3)
    | esk1_4(X1,X2,X3,X4) != X2
    | ~ r2_hidden(esk1_4(X1,X2,X3,X4),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_86,negated_conjecture,
    ( esk1_4(k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk3_0),k6_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))) = k5_relat_1(esk2_0,esk4_0)
    | esk1_4(k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk3_0),k6_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))) = k5_relat_1(esk2_0,esk3_0)
    | esk1_4(esk4_0,esk3_0,X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) = esk3_0
    | esk1_4(esk4_0,esk3_0,X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) = esk4_0
    | esk1_4(esk4_0,esk3_0,X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) = X1 ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_87,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_88,plain,
    ( X4 = k1_enumset1(X1,X2,X3)
    | esk1_4(X1,X2,X3,X4) != X3
    | ~ r2_hidden(esk1_4(X1,X2,X3,X4),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_89,plain,
    ( X4 = k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)
    | esk1_4(X1,X2,X3,X4) != X2
    | ~ r2_hidden(esk1_4(X1,X2,X3,X4),X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_90,negated_conjecture,
    ( esk1_4(k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk3_0),k6_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))) = k5_relat_1(esk2_0,esk3_0)
    | esk1_4(k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk3_0),k6_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))) = k5_relat_1(esk2_0,esk4_0)
    | esk1_4(esk4_0,esk3_0,esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) = esk4_0
    | esk1_4(esk4_0,esk3_0,esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) = esk3_0 ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_86])])).

cnf(c_0_91,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_87])])).

cnf(c_0_92,plain,
    ( X4 = k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)
    | esk1_4(X1,X2,X3,X4) != X3
    | ~ r2_hidden(esk1_4(X1,X2,X3,X4),X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_93,negated_conjecture,
    ( k6_enumset1(k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk3_0)) = k6_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))
    | esk1_4(k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk3_0),k6_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))) = k5_relat_1(esk2_0,esk3_0)
    | esk1_4(esk4_0,esk3_0,esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) = esk3_0
    | esk1_4(esk4_0,esk3_0,esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_91])])).

cnf(c_0_94,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3) = k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X4)
    | esk1_4(X4,X5,X4,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)) = X1
    | esk1_4(X4,X5,X4,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)) = X2
    | esk1_4(X4,X5,X4,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)) = X3
    | esk1_4(X4,X5,X4,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)) = X4
    | esk1_4(X4,X5,X4,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)) = X5 ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_74])])).

cnf(c_0_95,negated_conjecture,
    ( k6_enumset1(k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk3_0)) = k6_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))
    | esk1_4(esk4_0,esk3_0,esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) = esk4_0
    | esk1_4(esk4_0,esk3_0,esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_32])])).

cnf(c_0_96,negated_conjecture,
    ( esk1_4(X1,X2,X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) = esk4_0
    | esk1_4(X1,X2,X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) = esk3_0
    | esk1_4(X1,X2,X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) = X2
    | esk1_4(X1,X2,X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) = X1
    | ~ r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X1))),k1_setfam_1(k6_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_94])).

cnf(c_0_97,negated_conjecture,
    ( esk1_4(esk4_0,esk3_0,esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) = esk3_0
    | esk1_4(esk4_0,esk3_0,esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) = esk4_0
    | r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk3_0,X1))),k1_setfam_1(k6_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_83,c_0_95])).

cnf(c_0_98,negated_conjecture,
    ( esk1_4(esk4_0,esk3_0,esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) = esk3_0
    | esk1_4(esk4_0,esk3_0,esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_99,negated_conjecture,
    ( k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk3_0,esk4_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)
    | esk1_4(esk4_0,esk3_0,esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_98]),c_0_91])])).

cnf(c_0_100,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)),X4)
    | ~ r1_tarski(X3,X4) ),
    inference(spm,[status(thm)],[c_0_31,c_0_91])).

cnf(c_0_101,negated_conjecture,
    ( k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk3_0,esk4_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_99]),c_0_32])])).

cnf(c_0_102,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_103,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_100,c_0_38])).

cnf(c_0_104,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),k1_setfam_1(k6_enumset1(k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),X1)))
    | ~ r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_101])).

cnf(c_0_105,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)) = X3
    | ~ r1_tarski(X3,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))) ),
    inference(spm,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_106,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),k1_setfam_1(k6_enumset1(k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)))))) ),
    inference(spm,[status(thm)],[c_0_104,c_0_38])).

cnf(c_0_107,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)),k1_setfam_1(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2)))
    | ~ r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)),X4) ),
    inference(spm,[status(thm)],[c_0_75,c_0_53])).

cnf(c_0_108,negated_conjecture,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))))) = k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_109,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k5_relat_1(esk2_0,esk4_0))))
    | ~ r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),X1) ),
    inference(spm,[status(thm)],[c_0_107,c_0_108])).

cnf(c_0_110,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_81]),c_0_73]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:58:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 5.26/5.43  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S002I
% 5.26/5.43  # and selection function SelectNegativeLiterals.
% 5.26/5.43  #
% 5.26/5.43  # Preprocessing time       : 0.028 s
% 5.26/5.43  # Presaturation interreduction done
% 5.26/5.43  
% 5.26/5.43  # Proof found!
% 5.26/5.43  # SZS status Theorem
% 5.26/5.43  # SZS output start CNFRefutation
% 5.26/5.43  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 5.26/5.43  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 5.26/5.43  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 5.26/5.43  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 5.26/5.43  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 5.26/5.43  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 5.26/5.43  fof(t8_setfam_1, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(k1_setfam_1(X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_setfam_1)).
% 5.26/5.43  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.26/5.43  fof(t52_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relat_1)).
% 5.26/5.43  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.26/5.43  fof(t48_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relat_1)).
% 5.26/5.43  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.26/5.43  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 5.26/5.43  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 5.26/5.43  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 5.26/5.43  fof(c_0_15, plain, ![X15, X16, X17, X18, X19, X20, X21, X22, X23, X24]:(((~r2_hidden(X19,X18)|(X19=X15|X19=X16|X19=X17)|X18!=k1_enumset1(X15,X16,X17))&(((X20!=X15|r2_hidden(X20,X18)|X18!=k1_enumset1(X15,X16,X17))&(X20!=X16|r2_hidden(X20,X18)|X18!=k1_enumset1(X15,X16,X17)))&(X20!=X17|r2_hidden(X20,X18)|X18!=k1_enumset1(X15,X16,X17))))&((((esk1_4(X21,X22,X23,X24)!=X21|~r2_hidden(esk1_4(X21,X22,X23,X24),X24)|X24=k1_enumset1(X21,X22,X23))&(esk1_4(X21,X22,X23,X24)!=X22|~r2_hidden(esk1_4(X21,X22,X23,X24),X24)|X24=k1_enumset1(X21,X22,X23)))&(esk1_4(X21,X22,X23,X24)!=X23|~r2_hidden(esk1_4(X21,X22,X23,X24),X24)|X24=k1_enumset1(X21,X22,X23)))&(r2_hidden(esk1_4(X21,X22,X23,X24),X24)|(esk1_4(X21,X22,X23,X24)=X21|esk1_4(X21,X22,X23,X24)=X22|esk1_4(X21,X22,X23,X24)=X23)|X24=k1_enumset1(X21,X22,X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 5.26/5.43  fof(c_0_16, plain, ![X28, X29, X30]:k2_enumset1(X28,X28,X29,X30)=k1_enumset1(X28,X29,X30), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 5.26/5.43  fof(c_0_17, plain, ![X31, X32, X33, X34]:k3_enumset1(X31,X31,X32,X33,X34)=k2_enumset1(X31,X32,X33,X34), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 5.26/5.43  fof(c_0_18, plain, ![X35, X36, X37, X38, X39]:k4_enumset1(X35,X35,X36,X37,X38,X39)=k3_enumset1(X35,X36,X37,X38,X39), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 5.26/5.43  fof(c_0_19, plain, ![X40, X41, X42, X43, X44, X45]:k5_enumset1(X40,X40,X41,X42,X43,X44,X45)=k4_enumset1(X40,X41,X42,X43,X44,X45), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 5.26/5.43  fof(c_0_20, plain, ![X46, X47, X48, X49, X50, X51, X52]:k6_enumset1(X46,X46,X47,X48,X49,X50,X51,X52)=k5_enumset1(X46,X47,X48,X49,X50,X51,X52), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 5.26/5.43  cnf(c_0_21, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 5.26/5.43  cnf(c_0_22, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 5.26/5.43  cnf(c_0_23, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 5.26/5.43  cnf(c_0_24, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 5.26/5.43  cnf(c_0_25, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 5.26/5.43  cnf(c_0_26, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 5.26/5.43  fof(c_0_27, plain, ![X57, X58, X59]:(~r2_hidden(X57,X58)|~r1_tarski(X57,X59)|r1_tarski(k1_setfam_1(X58),X59)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_setfam_1])])).
% 5.26/5.43  cnf(c_0_28, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X2,X2,X2,X2,X2,X2,X4,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26])).
% 5.26/5.43  fof(c_0_29, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 5.26/5.43  cnf(c_0_30, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X2,X5)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 5.26/5.43  cnf(c_0_31, plain, (r1_tarski(k1_setfam_1(X2),X3)|~r2_hidden(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 5.26/5.43  cnf(c_0_32, plain, (r2_hidden(X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_28])])).
% 5.26/5.43  cnf(c_0_33, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_29])).
% 5.26/5.43  cnf(c_0_34, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X4,X4,X4,X4,X4,X2,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26])).
% 5.26/5.43  fof(c_0_35, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))))))), inference(assume_negation,[status(cth)],[t52_relat_1])).
% 5.26/5.43  fof(c_0_36, plain, ![X55, X56]:((~m1_subset_1(X55,k1_zfmisc_1(X56))|r1_tarski(X55,X56))&(~r1_tarski(X55,X56)|m1_subset_1(X55,k1_zfmisc_1(X56)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 5.26/5.43  cnf(c_0_37, plain, (r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)),X4)|~r1_tarski(X1,X4)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 5.26/5.43  cnf(c_0_38, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_33])).
% 5.26/5.43  cnf(c_0_39, plain, (r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_34])])).
% 5.26/5.43  fof(c_0_40, plain, ![X62, X63, X64]:(~v1_relat_1(X62)|(~v1_relat_1(X63)|(~v1_relat_1(X64)|(~r1_tarski(X62,X63)|r1_tarski(k5_relat_1(X64,X62),k5_relat_1(X64,X63)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_relat_1])])])).
% 5.26/5.43  fof(c_0_41, negated_conjecture, (v1_relat_1(esk2_0)&(v1_relat_1(esk3_0)&(v1_relat_1(esk4_0)&~r1_tarski(k5_relat_1(esk2_0,k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_35])])])).
% 5.26/5.43  fof(c_0_42, plain, ![X60, X61]:(~v1_relat_1(X60)|(~m1_subset_1(X61,k1_zfmisc_1(X60))|v1_relat_1(X61))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 5.26/5.43  cnf(c_0_43, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 5.26/5.43  cnf(c_0_44, plain, (r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)),X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 5.26/5.44  cnf(c_0_45, plain, (r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)),X4)|~r1_tarski(X2,X4)), inference(spm,[status(thm)],[c_0_31, c_0_39])).
% 5.26/5.44  fof(c_0_46, plain, ![X53, X54]:k1_setfam_1(k2_tarski(X53,X54))=k3_xboole_0(X53,X54), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 5.26/5.44  fof(c_0_47, plain, ![X26, X27]:k1_enumset1(X26,X26,X27)=k2_tarski(X26,X27), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 5.26/5.44  cnf(c_0_48, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 5.26/5.44  cnf(c_0_49, plain, (r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 5.26/5.44  cnf(c_0_50, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 5.26/5.44  cnf(c_0_51, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 5.26/5.44  cnf(c_0_52, plain, (m1_subset_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 5.26/5.44  cnf(c_0_53, plain, (r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)),X2)), inference(spm,[status(thm)],[c_0_45, c_0_38])).
% 5.26/5.44  cnf(c_0_54, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 5.26/5.44  cnf(c_0_55, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 5.26/5.44  cnf(c_0_56, plain, (X1=X5|X1=X4|X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26])).
% 5.26/5.44  cnf(c_0_57, plain, (r2_hidden(esk1_4(X1,X2,X3,X4),X4)|esk1_4(X1,X2,X3,X4)=X1|esk1_4(X1,X2,X3,X4)=X2|esk1_4(X1,X2,X3,X4)=X3|X4=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 5.26/5.44  fof(c_0_58, plain, ![X12, X13, X14]:(~r1_tarski(X12,X13)|~r1_tarski(X12,X14)|r1_tarski(X12,k3_xboole_0(X13,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 5.26/5.44  cnf(c_0_59, negated_conjecture, (r1_tarski(k5_relat_1(X1,X2),k5_relat_1(X1,esk4_0))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X2,esk4_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 5.26/5.44  cnf(c_0_60, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 5.26/5.44  cnf(c_0_61, plain, (v1_relat_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 5.26/5.44  cnf(c_0_62, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 5.26/5.44  cnf(c_0_63, plain, (m1_subset_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_43, c_0_53])).
% 5.26/5.44  cnf(c_0_64, negated_conjecture, (~r1_tarski(k5_relat_1(esk2_0,k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 5.26/5.44  cnf(c_0_65, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_54, c_0_55])).
% 5.26/5.44  cnf(c_0_66, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k6_enumset1(X4,X4,X4,X4,X4,X4,X3,X2))), inference(er,[status(thm)],[c_0_56])).
% 5.26/5.44  cnf(c_0_67, plain, (esk1_4(X1,X2,X3,X4)=X3|esk1_4(X1,X2,X3,X4)=X2|esk1_4(X1,X2,X3,X4)=X1|X4=k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)|r2_hidden(esk1_4(X1,X2,X3,X4),X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26])).
% 5.26/5.44  cnf(c_0_68, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 5.26/5.44  cnf(c_0_69, negated_conjecture, (r1_tarski(k5_relat_1(esk2_0,X1),k5_relat_1(esk2_0,esk4_0))|~v1_relat_1(X1)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 5.26/5.44  cnf(c_0_70, negated_conjecture, (v1_relat_1(k1_setfam_1(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,X1,X2)))), inference(spm,[status(thm)],[c_0_61, c_0_50])).
% 5.26/5.44  cnf(c_0_71, negated_conjecture, (r1_tarski(k5_relat_1(X1,X2),k5_relat_1(X1,esk3_0))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X2,esk3_0)), inference(spm,[status(thm)],[c_0_49, c_0_62])).
% 5.26/5.44  cnf(c_0_72, plain, (v1_relat_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_51, c_0_63])).
% 5.26/5.44  cnf(c_0_73, negated_conjecture, (~r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),k1_setfam_1(k6_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_65]), c_0_65]), c_0_22]), c_0_22]), c_0_23]), c_0_23]), c_0_24]), c_0_24]), c_0_25]), c_0_25]), c_0_26]), c_0_26])).
% 5.26/5.44  cnf(c_0_74, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)=k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X6)|esk1_4(X4,X5,X6,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))=X4|esk1_4(X4,X5,X6,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))=X5|esk1_4(X4,X5,X6,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))=X6|esk1_4(X4,X5,X6,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))=X3|esk1_4(X4,X5,X6,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))=X2|esk1_4(X4,X5,X6,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))=X1), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 5.26/5.44  cnf(c_0_75, plain, (r1_tarski(X1,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_65]), c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26])).
% 5.26/5.44  cnf(c_0_76, negated_conjecture, (r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,X1,X2))),k5_relat_1(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_44])])).
% 5.26/5.44  cnf(c_0_77, negated_conjecture, (r1_tarski(k5_relat_1(esk2_0,X1),k5_relat_1(esk2_0,esk3_0))|~v1_relat_1(X1)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_71, c_0_60])).
% 5.26/5.44  cnf(c_0_78, negated_conjecture, (v1_relat_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,esk3_0,X2)))), inference(spm,[status(thm)],[c_0_72, c_0_62])).
% 5.26/5.44  cnf(c_0_79, negated_conjecture, (esk1_4(X1,X2,X3,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))=esk3_0|esk1_4(X1,X2,X3,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))=esk4_0|esk1_4(X1,X2,X3,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))=X3|esk1_4(X1,X2,X3,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))=X2|esk1_4(X1,X2,X3,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))=X1|~r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))),k1_setfam_1(k6_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))))), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 5.26/5.44  cnf(c_0_80, negated_conjecture, (r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,X1,X2))),k1_setfam_1(k6_enumset1(k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),X3)))|~r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,X1,X2))),X3)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 5.26/5.44  cnf(c_0_81, negated_conjecture, (r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,esk3_0,X2))),k5_relat_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_53])])).
% 5.26/5.44  cnf(c_0_82, negated_conjecture, (esk1_4(X1,X2,X3,k6_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0)))=k5_relat_1(esk2_0,esk3_0)|esk1_4(X1,X2,X3,k6_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0)))=k5_relat_1(esk2_0,esk4_0)|esk1_4(X1,X2,X3,k6_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0)))=X3|esk1_4(X1,X2,X3,k6_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0)))=X2|esk1_4(X1,X2,X3,k6_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0)))=X1|esk1_4(X4,X5,X6,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))=esk4_0|esk1_4(X4,X5,X6,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))=esk3_0|esk1_4(X4,X5,X6,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))=X4|esk1_4(X4,X5,X6,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))=X5|esk1_4(X4,X5,X6,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))=X6|~r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X6))),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)))), inference(spm,[status(thm)],[c_0_79, c_0_74])).
% 5.26/5.44  cnf(c_0_83, negated_conjecture, (r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk3_0,X1))),k1_setfam_1(k6_enumset1(k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk3_0))))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 5.26/5.44  cnf(c_0_84, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 5.26/5.44  cnf(c_0_85, plain, (X4=k1_enumset1(X1,X2,X3)|esk1_4(X1,X2,X3,X4)!=X2|~r2_hidden(esk1_4(X1,X2,X3,X4),X4)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 5.26/5.44  cnf(c_0_86, negated_conjecture, (esk1_4(k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk3_0),k6_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0)))=k5_relat_1(esk2_0,esk4_0)|esk1_4(k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk3_0),k6_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0)))=k5_relat_1(esk2_0,esk3_0)|esk1_4(esk4_0,esk3_0,X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))=esk3_0|esk1_4(esk4_0,esk3_0,X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))=esk4_0|esk1_4(esk4_0,esk3_0,X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))=X1), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 5.26/5.44  cnf(c_0_87, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26])).
% 5.26/5.44  cnf(c_0_88, plain, (X4=k1_enumset1(X1,X2,X3)|esk1_4(X1,X2,X3,X4)!=X3|~r2_hidden(esk1_4(X1,X2,X3,X4),X4)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 5.26/5.44  cnf(c_0_89, plain, (X4=k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)|esk1_4(X1,X2,X3,X4)!=X2|~r2_hidden(esk1_4(X1,X2,X3,X4),X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26])).
% 5.26/5.44  cnf(c_0_90, negated_conjecture, (esk1_4(k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk3_0),k6_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0)))=k5_relat_1(esk2_0,esk3_0)|esk1_4(k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk3_0),k6_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0)))=k5_relat_1(esk2_0,esk4_0)|esk1_4(esk4_0,esk3_0,esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))=esk4_0|esk1_4(esk4_0,esk3_0,esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))=esk3_0), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_86])])).
% 5.26/5.44  cnf(c_0_91, plain, (r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_87])])).
% 5.26/5.44  cnf(c_0_92, plain, (X4=k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)|esk1_4(X1,X2,X3,X4)!=X3|~r2_hidden(esk1_4(X1,X2,X3,X4),X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26])).
% 5.26/5.44  cnf(c_0_93, negated_conjecture, (k6_enumset1(k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk3_0))=k6_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))|esk1_4(k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk3_0),k6_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0)))=k5_relat_1(esk2_0,esk3_0)|esk1_4(esk4_0,esk3_0,esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))=esk3_0|esk1_4(esk4_0,esk3_0,esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_91])])).
% 5.26/5.44  cnf(c_0_94, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)=k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X4)|esk1_4(X4,X5,X4,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))=X1|esk1_4(X4,X5,X4,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))=X2|esk1_4(X4,X5,X4,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))=X3|esk1_4(X4,X5,X4,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))=X4|esk1_4(X4,X5,X4,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))=X5), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_74])])).
% 5.26/5.44  cnf(c_0_95, negated_conjecture, (k6_enumset1(k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk3_0))=k6_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))|esk1_4(esk4_0,esk3_0,esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))=esk4_0|esk1_4(esk4_0,esk3_0,esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_32])])).
% 5.26/5.44  cnf(c_0_96, negated_conjecture, (esk1_4(X1,X2,X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))=esk4_0|esk1_4(X1,X2,X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))=esk3_0|esk1_4(X1,X2,X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))=X2|esk1_4(X1,X2,X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))=X1|~r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X1))),k1_setfam_1(k6_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))))), inference(spm,[status(thm)],[c_0_73, c_0_94])).
% 5.26/5.44  cnf(c_0_97, negated_conjecture, (esk1_4(esk4_0,esk3_0,esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))=esk3_0|esk1_4(esk4_0,esk3_0,esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))=esk4_0|r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk3_0,X1))),k1_setfam_1(k6_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))))), inference(spm,[status(thm)],[c_0_83, c_0_95])).
% 5.26/5.44  cnf(c_0_98, negated_conjecture, (esk1_4(esk4_0,esk3_0,esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))=esk3_0|esk1_4(esk4_0,esk3_0,esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))=esk4_0), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 5.26/5.44  cnf(c_0_99, negated_conjecture, (k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk3_0,esk4_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)|esk1_4(esk4_0,esk3_0,esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_98]), c_0_91])])).
% 5.26/5.44  cnf(c_0_100, plain, (r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)),X4)|~r1_tarski(X3,X4)), inference(spm,[status(thm)],[c_0_31, c_0_91])).
% 5.26/5.44  cnf(c_0_101, negated_conjecture, (k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk3_0,esk4_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_99]), c_0_32])])).
% 5.26/5.44  cnf(c_0_102, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 5.26/5.44  cnf(c_0_103, plain, (r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)),X3)), inference(spm,[status(thm)],[c_0_100, c_0_38])).
% 5.26/5.44  cnf(c_0_104, negated_conjecture, (r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),k1_setfam_1(k6_enumset1(k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),X1)))|~r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),X1)), inference(spm,[status(thm)],[c_0_80, c_0_101])).
% 5.26/5.44  cnf(c_0_105, plain, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))=X3|~r1_tarski(X3,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)))), inference(spm,[status(thm)],[c_0_102, c_0_103])).
% 5.26/5.44  cnf(c_0_106, negated_conjecture, (r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),k1_setfam_1(k6_enumset1(k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))))))), inference(spm,[status(thm)],[c_0_104, c_0_38])).
% 5.26/5.44  cnf(c_0_107, plain, (r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)),k1_setfam_1(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2)))|~r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)),X4)), inference(spm,[status(thm)],[c_0_75, c_0_53])).
% 5.26/5.44  cnf(c_0_108, negated_conjecture, (k1_setfam_1(k6_enumset1(k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)))))=k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)))), inference(spm,[status(thm)],[c_0_105, c_0_106])).
% 5.26/5.44  cnf(c_0_109, negated_conjecture, (r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k5_relat_1(esk2_0,esk4_0))))|~r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),X1)), inference(spm,[status(thm)],[c_0_107, c_0_108])).
% 5.26/5.44  cnf(c_0_110, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_81]), c_0_73]), ['proof']).
% 5.26/5.44  # SZS output end CNFRefutation
% 5.26/5.44  # Proof object total steps             : 111
% 5.26/5.44  # Proof object clause steps            : 80
% 5.26/5.44  # Proof object formula steps           : 31
% 5.26/5.44  # Proof object conjectures             : 34
% 5.26/5.44  # Proof object clause conjectures      : 31
% 5.26/5.44  # Proof object formula conjectures     : 3
% 5.26/5.44  # Proof object initial clauses used    : 25
% 5.26/5.44  # Proof object initial formulas used   : 15
% 5.26/5.44  # Proof object generating inferences   : 40
% 5.26/5.44  # Proof object simplifying inferences  : 77
% 5.26/5.44  # Training examples: 0 positive, 0 negative
% 5.26/5.44  # Parsed axioms                        : 16
% 5.26/5.44  # Removed by relevancy pruning/SinE    : 0
% 5.26/5.44  # Initial clauses                      : 29
% 5.26/5.44  # Removed in clause preprocessing      : 7
% 5.26/5.44  # Initial clauses in saturation        : 22
% 5.26/5.44  # Processed clauses                    : 1867
% 5.26/5.44  # ...of these trivial                  : 54
% 5.26/5.44  # ...subsumed                          : 758
% 5.26/5.44  # ...remaining for further processing  : 1055
% 5.26/5.44  # Other redundant clauses eliminated   : 1115
% 5.26/5.44  # Clauses deleted for lack of memory   : 0
% 5.26/5.44  # Backward-subsumed                    : 52
% 5.26/5.44  # Backward-rewritten                   : 6
% 5.26/5.44  # Generated clauses                    : 56140
% 5.26/5.44  # ...of the previous two non-trivial   : 53446
% 5.26/5.44  # Contextual simplify-reflections      : 0
% 5.26/5.44  # Paramodulations                      : 54012
% 5.26/5.44  # Factorizations                       : 1014
% 5.26/5.44  # Equation resolutions                 : 1117
% 5.26/5.44  # Propositional unsat checks           : 0
% 5.26/5.44  #    Propositional check models        : 0
% 5.26/5.44  #    Propositional check unsatisfiable : 0
% 5.26/5.44  #    Propositional clauses             : 0
% 5.26/5.44  #    Propositional clauses after purity: 0
% 5.26/5.44  #    Propositional unsat core size     : 0
% 5.26/5.44  #    Propositional preprocessing time  : 0.000
% 5.26/5.44  #    Propositional encoding time       : 0.000
% 5.26/5.44  #    Propositional solver time         : 0.000
% 5.26/5.44  #    Success case prop preproc time    : 0.000
% 5.26/5.44  #    Success case prop encoding time   : 0.000
% 5.26/5.44  #    Success case prop solver time     : 0.000
% 5.26/5.44  # Current number of processed clauses  : 970
% 5.26/5.44  #    Positive orientable unit clauses  : 202
% 5.26/5.44  #    Positive unorientable unit clauses: 0
% 5.26/5.44  #    Negative unit clauses             : 1
% 5.26/5.44  #    Non-unit-clauses                  : 767
% 5.26/5.44  # Current number of unprocessed clauses: 51120
% 5.26/5.44  # ...number of literals in the above   : 600839
% 5.26/5.44  # Current number of archived formulas  : 0
% 5.26/5.44  # Current number of archived clauses   : 86
% 5.26/5.44  # Clause-clause subsumption calls (NU) : 128266
% 5.26/5.44  # Rec. Clause-clause subsumption calls : 23852
% 5.26/5.44  # Non-unit clause-clause subsumptions  : 810
% 5.26/5.44  # Unit Clause-clause subsumption calls : 11846
% 5.26/5.44  # Rewrite failures with RHS unbound    : 0
% 5.26/5.44  # BW rewrite match attempts            : 1334
% 5.26/5.44  # BW rewrite match successes           : 6
% 5.26/5.44  # Condensation attempts                : 0
% 5.26/5.44  # Condensation successes               : 0
% 5.26/5.44  # Termbank termtop insertions          : 3669356
% 5.26/5.44  
% 5.26/5.44  # -------------------------------------------------
% 5.26/5.44  # User time                : 5.030 s
% 5.26/5.44  # System time              : 0.074 s
% 5.26/5.44  # Total time               : 5.105 s
% 5.26/5.44  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
