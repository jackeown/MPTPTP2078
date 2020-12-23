%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:39 EST 2020

% Result     : Theorem 6.63s
% Output     : CNFRefutation 6.63s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 228 expanded)
%              Number of clauses        :   42 (  95 expanded)
%              Number of leaves         :   14 (  63 expanded)
%              Depth                    :   12
%              Number of atoms          :  166 ( 510 expanded)
%              Number of equality atoms :   54 ( 238 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

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

fof(t4_setfam_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(k1_setfam_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

fof(t52_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t48_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( r1_tarski(X1,X2)
               => r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(c_0_14,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20,X21,X22] :
      ( ( ~ r2_hidden(X17,X16)
        | X17 = X13
        | X17 = X14
        | X17 = X15
        | X16 != k1_enumset1(X13,X14,X15) )
      & ( X18 != X13
        | r2_hidden(X18,X16)
        | X16 != k1_enumset1(X13,X14,X15) )
      & ( X18 != X14
        | r2_hidden(X18,X16)
        | X16 != k1_enumset1(X13,X14,X15) )
      & ( X18 != X15
        | r2_hidden(X18,X16)
        | X16 != k1_enumset1(X13,X14,X15) )
      & ( esk1_4(X19,X20,X21,X22) != X19
        | ~ r2_hidden(esk1_4(X19,X20,X21,X22),X22)
        | X22 = k1_enumset1(X19,X20,X21) )
      & ( esk1_4(X19,X20,X21,X22) != X20
        | ~ r2_hidden(esk1_4(X19,X20,X21,X22),X22)
        | X22 = k1_enumset1(X19,X20,X21) )
      & ( esk1_4(X19,X20,X21,X22) != X21
        | ~ r2_hidden(esk1_4(X19,X20,X21,X22),X22)
        | X22 = k1_enumset1(X19,X20,X21) )
      & ( r2_hidden(esk1_4(X19,X20,X21,X22),X22)
        | esk1_4(X19,X20,X21,X22) = X19
        | esk1_4(X19,X20,X21,X22) = X20
        | esk1_4(X19,X20,X21,X22) = X21
        | X22 = k1_enumset1(X19,X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_15,plain,(
    ! [X26,X27,X28] : k2_enumset1(X26,X26,X27,X28) = k1_enumset1(X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_16,plain,(
    ! [X29,X30,X31,X32] : k3_enumset1(X29,X29,X30,X31,X32) = k2_enumset1(X29,X30,X31,X32) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_17,plain,(
    ! [X33,X34,X35,X36,X37] : k4_enumset1(X33,X33,X34,X35,X36,X37) = k3_enumset1(X33,X34,X35,X36,X37) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_18,plain,(
    ! [X38,X39,X40,X41,X42,X43] : k5_enumset1(X38,X38,X39,X40,X41,X42,X43) = k4_enumset1(X38,X39,X40,X41,X42,X43) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_19,plain,(
    ! [X44,X45,X46,X47,X48,X49,X50] : k6_enumset1(X44,X44,X45,X46,X47,X48,X49,X50) = k5_enumset1(X44,X45,X46,X47,X48,X49,X50) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,plain,(
    ! [X55,X56] :
      ( ~ r2_hidden(X55,X56)
      | r1_tarski(k1_setfam_1(X56),X55) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X2,X2,X2,X2,X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_29,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3] :
                ( v1_relat_1(X3)
               => r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t52_relat_1])).

fof(c_0_30,plain,(
    ! [X53,X54] :
      ( ( ~ m1_subset_1(X53,k1_zfmisc_1(X54))
        | r1_tarski(X53,X54) )
      & ( ~ r1_tarski(X53,X54)
        | m1_subset_1(X53,k1_zfmisc_1(X54)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_31,plain,
    ( r1_tarski(k1_setfam_1(X2),X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_27])])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25])).

fof(c_0_34,plain,(
    ! [X59,X60,X61] :
      ( ~ v1_relat_1(X59)
      | ~ v1_relat_1(X60)
      | ~ v1_relat_1(X61)
      | ~ r1_tarski(X59,X60)
      | r1_tarski(k5_relat_1(X61,X59),k5_relat_1(X61,X60)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_relat_1])])])).

fof(c_0_35,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & v1_relat_1(esk4_0)
    & ~ r1_tarski(k5_relat_1(esk2_0,k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).

fof(c_0_36,plain,(
    ! [X57,X58] :
      ( ~ v1_relat_1(X57)
      | ~ m1_subset_1(X58,k1_zfmisc_1(X57))
      | v1_relat_1(X58) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

cnf(c_0_37,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)),X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_33])])).

fof(c_0_40,plain,(
    ! [X51,X52] : k1_setfam_1(k2_tarski(X51,X52)) = k3_xboole_0(X51,X52) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_41,plain,(
    ! [X24,X25] : k1_enumset1(X24,X24,X25) = k2_tarski(X24,X25) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_42,plain,
    ( r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,plain,
    ( m1_subset_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_46,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_31,c_0_39])).

fof(c_0_47,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_tarski(X10,X11)
      | ~ r1_tarski(X10,X12)
      | r1_tarski(X10,k3_xboole_0(X11,X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_48,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(k5_relat_1(X1,X2),k5_relat_1(X1,esk3_0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X2,esk3_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_52,plain,
    ( v1_relat_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_54,plain,
    ( m1_subset_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_46])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_56,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk2_0,X1),k5_relat_1(esk2_0,esk3_0))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( v1_relat_1(k1_setfam_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1,X2))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_43])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k5_relat_1(X1,X2),k5_relat_1(X1,esk4_0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X2,esk4_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_53])).

cnf(c_0_60,plain,
    ( v1_relat_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)))
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_44,c_0_54])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1,X2))),k5_relat_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_38])])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk2_0,X1),k5_relat_1(esk2_0,esk4_0))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_51])).

cnf(c_0_64,negated_conjecture,
    ( v1_relat_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_53])).

cnf(c_0_65,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk2_0,k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1,X2))),k1_setfam_1(k6_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),X3)))
    | ~ r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1,X2))),X3) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,esk4_0))),k5_relat_1(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_46])])).

cnf(c_0_68,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),k1_setfam_1(k6_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_56]),c_0_56]),c_0_21]),c_0_21]),c_0_22]),c_0_22]),c_0_23]),c_0_23]),c_0_24]),c_0_24]),c_0_25]),c_0_25])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1,esk4_0))),k1_setfam_1(k6_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_69])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:12:55 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 6.63/6.79  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S002I
% 6.63/6.79  # and selection function SelectNegativeLiterals.
% 6.63/6.79  #
% 6.63/6.79  # Preprocessing time       : 0.042 s
% 6.63/6.79  # Presaturation interreduction done
% 6.63/6.79  
% 6.63/6.79  # Proof found!
% 6.63/6.79  # SZS status Theorem
% 6.63/6.79  # SZS output start CNFRefutation
% 6.63/6.79  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 6.63/6.79  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 6.63/6.79  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 6.63/6.79  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 6.63/6.79  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 6.63/6.79  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 6.63/6.79  fof(t4_setfam_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(k1_setfam_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 6.63/6.79  fof(t52_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relat_1)).
% 6.63/6.79  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.63/6.79  fof(t48_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relat_1)).
% 6.63/6.79  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.63/6.79  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 6.63/6.79  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 6.63/6.79  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 6.63/6.79  fof(c_0_14, plain, ![X13, X14, X15, X16, X17, X18, X19, X20, X21, X22]:(((~r2_hidden(X17,X16)|(X17=X13|X17=X14|X17=X15)|X16!=k1_enumset1(X13,X14,X15))&(((X18!=X13|r2_hidden(X18,X16)|X16!=k1_enumset1(X13,X14,X15))&(X18!=X14|r2_hidden(X18,X16)|X16!=k1_enumset1(X13,X14,X15)))&(X18!=X15|r2_hidden(X18,X16)|X16!=k1_enumset1(X13,X14,X15))))&((((esk1_4(X19,X20,X21,X22)!=X19|~r2_hidden(esk1_4(X19,X20,X21,X22),X22)|X22=k1_enumset1(X19,X20,X21))&(esk1_4(X19,X20,X21,X22)!=X20|~r2_hidden(esk1_4(X19,X20,X21,X22),X22)|X22=k1_enumset1(X19,X20,X21)))&(esk1_4(X19,X20,X21,X22)!=X21|~r2_hidden(esk1_4(X19,X20,X21,X22),X22)|X22=k1_enumset1(X19,X20,X21)))&(r2_hidden(esk1_4(X19,X20,X21,X22),X22)|(esk1_4(X19,X20,X21,X22)=X19|esk1_4(X19,X20,X21,X22)=X20|esk1_4(X19,X20,X21,X22)=X21)|X22=k1_enumset1(X19,X20,X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 6.63/6.79  fof(c_0_15, plain, ![X26, X27, X28]:k2_enumset1(X26,X26,X27,X28)=k1_enumset1(X26,X27,X28), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 6.63/6.79  fof(c_0_16, plain, ![X29, X30, X31, X32]:k3_enumset1(X29,X29,X30,X31,X32)=k2_enumset1(X29,X30,X31,X32), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 6.63/6.79  fof(c_0_17, plain, ![X33, X34, X35, X36, X37]:k4_enumset1(X33,X33,X34,X35,X36,X37)=k3_enumset1(X33,X34,X35,X36,X37), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 6.63/6.79  fof(c_0_18, plain, ![X38, X39, X40, X41, X42, X43]:k5_enumset1(X38,X38,X39,X40,X41,X42,X43)=k4_enumset1(X38,X39,X40,X41,X42,X43), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 6.63/6.79  fof(c_0_19, plain, ![X44, X45, X46, X47, X48, X49, X50]:k6_enumset1(X44,X44,X45,X46,X47,X48,X49,X50)=k5_enumset1(X44,X45,X46,X47,X48,X49,X50), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 6.63/6.79  cnf(c_0_20, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 6.63/6.79  cnf(c_0_21, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 6.63/6.79  cnf(c_0_22, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 6.63/6.79  cnf(c_0_23, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 6.63/6.79  cnf(c_0_24, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 6.63/6.79  cnf(c_0_25, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 6.63/6.79  fof(c_0_26, plain, ![X55, X56]:(~r2_hidden(X55,X56)|r1_tarski(k1_setfam_1(X56),X55)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).
% 6.63/6.79  cnf(c_0_27, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X2,X2,X2,X2,X2,X2,X4,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23]), c_0_24]), c_0_25])).
% 6.63/6.79  cnf(c_0_28, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 6.63/6.79  fof(c_0_29, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))))))), inference(assume_negation,[status(cth)],[t52_relat_1])).
% 6.63/6.79  fof(c_0_30, plain, ![X53, X54]:((~m1_subset_1(X53,k1_zfmisc_1(X54))|r1_tarski(X53,X54))&(~r1_tarski(X53,X54)|m1_subset_1(X53,k1_zfmisc_1(X54)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 6.63/6.79  cnf(c_0_31, plain, (r1_tarski(k1_setfam_1(X2),X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 6.63/6.79  cnf(c_0_32, plain, (r2_hidden(X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_27])])).
% 6.63/6.79  cnf(c_0_33, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_21]), c_0_22]), c_0_23]), c_0_24]), c_0_25])).
% 6.63/6.79  fof(c_0_34, plain, ![X59, X60, X61]:(~v1_relat_1(X59)|(~v1_relat_1(X60)|(~v1_relat_1(X61)|(~r1_tarski(X59,X60)|r1_tarski(k5_relat_1(X61,X59),k5_relat_1(X61,X60)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_relat_1])])])).
% 6.63/6.79  fof(c_0_35, negated_conjecture, (v1_relat_1(esk2_0)&(v1_relat_1(esk3_0)&(v1_relat_1(esk4_0)&~r1_tarski(k5_relat_1(esk2_0,k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).
% 6.63/6.79  fof(c_0_36, plain, ![X57, X58]:(~v1_relat_1(X57)|(~m1_subset_1(X58,k1_zfmisc_1(X57))|v1_relat_1(X58))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 6.63/6.79  cnf(c_0_37, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 6.63/6.79  cnf(c_0_38, plain, (r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)),X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 6.63/6.79  cnf(c_0_39, plain, (r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_33])])).
% 6.63/6.79  fof(c_0_40, plain, ![X51, X52]:k1_setfam_1(k2_tarski(X51,X52))=k3_xboole_0(X51,X52), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 6.63/6.79  fof(c_0_41, plain, ![X24, X25]:k1_enumset1(X24,X24,X25)=k2_tarski(X24,X25), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 6.63/6.79  cnf(c_0_42, plain, (r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 6.63/6.79  cnf(c_0_43, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 6.63/6.79  cnf(c_0_44, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 6.63/6.79  cnf(c_0_45, plain, (m1_subset_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 6.63/6.79  cnf(c_0_46, plain, (r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)),X3)), inference(spm,[status(thm)],[c_0_31, c_0_39])).
% 6.63/6.79  fof(c_0_47, plain, ![X10, X11, X12]:(~r1_tarski(X10,X11)|~r1_tarski(X10,X12)|r1_tarski(X10,k3_xboole_0(X11,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 6.63/6.79  cnf(c_0_48, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 6.63/6.79  cnf(c_0_49, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 6.63/6.79  cnf(c_0_50, negated_conjecture, (r1_tarski(k5_relat_1(X1,X2),k5_relat_1(X1,esk3_0))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X2,esk3_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 6.63/6.79  cnf(c_0_51, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 6.63/6.79  cnf(c_0_52, plain, (v1_relat_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 6.63/6.79  cnf(c_0_53, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 6.63/6.79  cnf(c_0_54, plain, (m1_subset_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_37, c_0_46])).
% 6.63/6.79  cnf(c_0_55, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 6.63/6.79  cnf(c_0_56, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_48, c_0_49])).
% 6.63/6.79  cnf(c_0_57, negated_conjecture, (r1_tarski(k5_relat_1(esk2_0,X1),k5_relat_1(esk2_0,esk3_0))|~v1_relat_1(X1)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 6.63/6.79  cnf(c_0_58, negated_conjecture, (v1_relat_1(k1_setfam_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1,X2)))), inference(spm,[status(thm)],[c_0_52, c_0_43])).
% 6.63/6.79  cnf(c_0_59, negated_conjecture, (r1_tarski(k5_relat_1(X1,X2),k5_relat_1(X1,esk4_0))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X2,esk4_0)), inference(spm,[status(thm)],[c_0_42, c_0_53])).
% 6.63/6.79  cnf(c_0_60, plain, (v1_relat_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)))|~v1_relat_1(X3)), inference(spm,[status(thm)],[c_0_44, c_0_54])).
% 6.63/6.79  cnf(c_0_61, plain, (r1_tarski(X1,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_56]), c_0_21]), c_0_22]), c_0_23]), c_0_24]), c_0_25])).
% 6.63/6.79  cnf(c_0_62, negated_conjecture, (r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1,X2))),k5_relat_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_38])])).
% 6.63/6.79  cnf(c_0_63, negated_conjecture, (r1_tarski(k5_relat_1(esk2_0,X1),k5_relat_1(esk2_0,esk4_0))|~v1_relat_1(X1)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_59, c_0_51])).
% 6.63/6.79  cnf(c_0_64, negated_conjecture, (v1_relat_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,esk4_0)))), inference(spm,[status(thm)],[c_0_60, c_0_53])).
% 6.63/6.79  cnf(c_0_65, negated_conjecture, (~r1_tarski(k5_relat_1(esk2_0,k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 6.63/6.79  cnf(c_0_66, negated_conjecture, (r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1,X2))),k1_setfam_1(k6_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),X3)))|~r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1,X2))),X3)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 6.63/6.79  cnf(c_0_67, negated_conjecture, (r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,esk4_0))),k5_relat_1(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_46])])).
% 6.63/6.79  cnf(c_0_68, negated_conjecture, (~r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),k1_setfam_1(k6_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_56]), c_0_56]), c_0_21]), c_0_21]), c_0_22]), c_0_22]), c_0_23]), c_0_23]), c_0_24]), c_0_24]), c_0_25]), c_0_25])).
% 6.63/6.79  cnf(c_0_69, negated_conjecture, (r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1,esk4_0))),k1_setfam_1(k6_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 6.63/6.79  cnf(c_0_70, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_69])]), ['proof']).
% 6.63/6.79  # SZS output end CNFRefutation
% 6.63/6.79  # Proof object total steps             : 71
% 6.63/6.79  # Proof object clause steps            : 42
% 6.63/6.79  # Proof object formula steps           : 29
% 6.63/6.79  # Proof object conjectures             : 19
% 6.63/6.79  # Proof object clause conjectures      : 16
% 6.63/6.79  # Proof object formula conjectures     : 3
% 6.63/6.79  # Proof object initial clauses used    : 18
% 6.63/6.79  # Proof object initial formulas used   : 14
% 6.63/6.79  # Proof object generating inferences   : 16
% 6.63/6.79  # Proof object simplifying inferences  : 39
% 6.63/6.79  # Training examples: 0 positive, 0 negative
% 6.63/6.79  # Parsed axioms                        : 15
% 6.63/6.79  # Removed by relevancy pruning/SinE    : 0
% 6.63/6.79  # Initial clauses                      : 26
% 6.63/6.79  # Removed in clause preprocessing      : 7
% 6.63/6.79  # Initial clauses in saturation        : 19
% 6.63/6.79  # Processed clauses                    : 1787
% 6.63/6.79  # ...of these trivial                  : 44
% 6.63/6.79  # ...subsumed                          : 461
% 6.63/6.79  # ...remaining for further processing  : 1282
% 6.63/6.79  # Other redundant clauses eliminated   : 970
% 6.63/6.79  # Clauses deleted for lack of memory   : 0
% 6.63/6.79  # Backward-subsumed                    : 61
% 6.63/6.79  # Backward-rewritten                   : 109
% 6.63/6.79  # Generated clauses                    : 86947
% 6.63/6.79  # ...of the previous two non-trivial   : 84250
% 6.63/6.79  # Contextual simplify-reflections      : 0
% 6.63/6.79  # Paramodulations                      : 85066
% 6.63/6.79  # Factorizations                       : 914
% 6.63/6.79  # Equation resolutions                 : 970
% 6.63/6.79  # Propositional unsat checks           : 0
% 6.63/6.79  #    Propositional check models        : 0
% 6.63/6.79  #    Propositional check unsatisfiable : 0
% 6.63/6.79  #    Propositional clauses             : 0
% 6.63/6.79  #    Propositional clauses after purity: 0
% 6.63/6.79  #    Propositional unsat core size     : 0
% 6.63/6.79  #    Propositional preprocessing time  : 0.000
% 6.63/6.79  #    Propositional encoding time       : 0.000
% 6.63/6.79  #    Propositional solver time         : 0.000
% 6.63/6.79  #    Success case prop preproc time    : 0.000
% 6.63/6.79  #    Success case prop encoding time   : 0.000
% 6.63/6.79  #    Success case prop solver time     : 0.000
% 6.63/6.79  # Current number of processed clauses  : 1089
% 6.63/6.79  #    Positive orientable unit clauses  : 203
% 6.63/6.79  #    Positive unorientable unit clauses: 0
% 6.63/6.79  #    Negative unit clauses             : 0
% 6.63/6.79  #    Non-unit-clauses                  : 886
% 6.63/6.79  # Current number of unprocessed clauses: 82060
% 6.63/6.79  # ...number of literals in the above   : 1272578
% 6.63/6.79  # Current number of archived formulas  : 0
% 6.63/6.79  # Current number of archived clauses   : 196
% 6.63/6.79  # Clause-clause subsumption calls (NU) : 464455
% 6.63/6.79  # Rec. Clause-clause subsumption calls : 31203
% 6.63/6.79  # Non-unit clause-clause subsumptions  : 518
% 6.63/6.79  # Unit Clause-clause subsumption calls : 30965
% 6.63/6.79  # Rewrite failures with RHS unbound    : 0
% 6.63/6.79  # BW rewrite match attempts            : 4267
% 6.63/6.79  # BW rewrite match successes           : 109
% 6.63/6.79  # Condensation attempts                : 0
% 6.63/6.79  # Condensation successes               : 0
% 6.63/6.79  # Termbank termtop insertions          : 7816412
% 6.63/6.80  
% 6.63/6.80  # -------------------------------------------------
% 6.63/6.80  # User time                : 6.396 s
% 6.63/6.80  # System time              : 0.068 s
% 6.63/6.80  # Total time               : 6.464 s
% 6.63/6.80  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
