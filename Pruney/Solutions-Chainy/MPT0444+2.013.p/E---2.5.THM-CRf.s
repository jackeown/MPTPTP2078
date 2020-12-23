%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:16 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 216 expanded)
%              Number of clauses        :   35 (  89 expanded)
%              Number of leaves         :   15 (  61 expanded)
%              Depth                    :   10
%              Number of atoms          :  178 ( 378 expanded)
%              Number of equality atoms :   72 ( 188 expanded)
%              Maximal formula depth    :   37 (   4 average)
%              Maximal clause size      :   52 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(d4_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] :
      ( X7 = k4_enumset1(X1,X2,X3,X4,X5,X6)
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ~ ( X8 != X1
              & X8 != X2
              & X8 != X3
              & X8 != X4
              & X8 != X5
              & X8 != X6 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_enumset1)).

fof(t27_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k2_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k2_relat_1(X1),k2_relat_1(X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_relat_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(t4_setfam_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(k1_setfam_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

fof(c_0_15,plain,(
    ! [X58,X59] : k1_setfam_1(k2_tarski(X58,X59)) = k3_xboole_0(X58,X59) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_16,plain,(
    ! [X14,X15] : k1_enumset1(X14,X14,X15) = k2_tarski(X14,X15) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_17,plain,(
    ! [X9,X10] : r1_tarski(k3_xboole_0(X9,X10),X9) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_18,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X16,X17,X18] : k2_enumset1(X16,X16,X17,X18) = k1_enumset1(X16,X17,X18) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_21,plain,(
    ! [X19,X20,X21,X22] : k3_enumset1(X19,X19,X20,X21,X22) = k2_enumset1(X19,X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_22,plain,(
    ! [X23,X24,X25,X26,X27] : k4_enumset1(X23,X23,X24,X25,X26,X27) = k3_enumset1(X23,X24,X25,X26,X27) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_23,plain,(
    ! [X28,X29,X30,X31,X32,X33] : k5_enumset1(X28,X28,X29,X30,X31,X32,X33) = k4_enumset1(X28,X29,X30,X31,X32,X33) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_24,plain,(
    ! [X34,X35,X36,X37,X38,X39,X40] : k6_enumset1(X34,X34,X35,X36,X37,X38,X39,X40) = k5_enumset1(X34,X35,X36,X37,X38,X39,X40) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_25,plain,(
    ! [X60,X61] :
      ( ( ~ m1_subset_1(X60,k1_zfmisc_1(X61))
        | r1_tarski(X60,X61) )
      & ( ~ r1_tarski(X60,X61)
        | m1_subset_1(X60,k1_zfmisc_1(X61)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_26,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_28,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_33,plain,(
    ! [X41,X42,X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53,X54,X55,X56] :
      ( ( ~ r2_hidden(X48,X47)
        | X48 = X41
        | X48 = X42
        | X48 = X43
        | X48 = X44
        | X48 = X45
        | X48 = X46
        | X47 != k4_enumset1(X41,X42,X43,X44,X45,X46) )
      & ( X49 != X41
        | r2_hidden(X49,X47)
        | X47 != k4_enumset1(X41,X42,X43,X44,X45,X46) )
      & ( X49 != X42
        | r2_hidden(X49,X47)
        | X47 != k4_enumset1(X41,X42,X43,X44,X45,X46) )
      & ( X49 != X43
        | r2_hidden(X49,X47)
        | X47 != k4_enumset1(X41,X42,X43,X44,X45,X46) )
      & ( X49 != X44
        | r2_hidden(X49,X47)
        | X47 != k4_enumset1(X41,X42,X43,X44,X45,X46) )
      & ( X49 != X45
        | r2_hidden(X49,X47)
        | X47 != k4_enumset1(X41,X42,X43,X44,X45,X46) )
      & ( X49 != X46
        | r2_hidden(X49,X47)
        | X47 != k4_enumset1(X41,X42,X43,X44,X45,X46) )
      & ( esk1_7(X50,X51,X52,X53,X54,X55,X56) != X50
        | ~ r2_hidden(esk1_7(X50,X51,X52,X53,X54,X55,X56),X56)
        | X56 = k4_enumset1(X50,X51,X52,X53,X54,X55) )
      & ( esk1_7(X50,X51,X52,X53,X54,X55,X56) != X51
        | ~ r2_hidden(esk1_7(X50,X51,X52,X53,X54,X55,X56),X56)
        | X56 = k4_enumset1(X50,X51,X52,X53,X54,X55) )
      & ( esk1_7(X50,X51,X52,X53,X54,X55,X56) != X52
        | ~ r2_hidden(esk1_7(X50,X51,X52,X53,X54,X55,X56),X56)
        | X56 = k4_enumset1(X50,X51,X52,X53,X54,X55) )
      & ( esk1_7(X50,X51,X52,X53,X54,X55,X56) != X53
        | ~ r2_hidden(esk1_7(X50,X51,X52,X53,X54,X55,X56),X56)
        | X56 = k4_enumset1(X50,X51,X52,X53,X54,X55) )
      & ( esk1_7(X50,X51,X52,X53,X54,X55,X56) != X54
        | ~ r2_hidden(esk1_7(X50,X51,X52,X53,X54,X55,X56),X56)
        | X56 = k4_enumset1(X50,X51,X52,X53,X54,X55) )
      & ( esk1_7(X50,X51,X52,X53,X54,X55,X56) != X55
        | ~ r2_hidden(esk1_7(X50,X51,X52,X53,X54,X55,X56),X56)
        | X56 = k4_enumset1(X50,X51,X52,X53,X54,X55) )
      & ( r2_hidden(esk1_7(X50,X51,X52,X53,X54,X55,X56),X56)
        | esk1_7(X50,X51,X52,X53,X54,X55,X56) = X50
        | esk1_7(X50,X51,X52,X53,X54,X55,X56) = X51
        | esk1_7(X50,X51,X52,X53,X54,X55,X56) = X52
        | esk1_7(X50,X51,X52,X53,X54,X55,X56) = X53
        | esk1_7(X50,X51,X52,X53,X54,X55,X56) = X54
        | esk1_7(X50,X51,X52,X53,X54,X55,X56) = X55
        | X56 = k4_enumset1(X50,X51,X52,X53,X54,X55) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_enumset1])])])])])])).

fof(c_0_34,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => r1_tarski(k2_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k2_relat_1(X1),k2_relat_1(X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t27_relat_1])).

fof(c_0_35,plain,(
    ! [X64,X65] :
      ( ~ v1_relat_1(X64)
      | ~ m1_subset_1(X65,k1_zfmisc_1(X64))
      | v1_relat_1(X65) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

cnf(c_0_36,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k4_enumset1(X4,X5,X6,X7,X8,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_39,plain,(
    ! [X66,X67] :
      ( ( r1_tarski(k1_relat_1(X66),k1_relat_1(X67))
        | ~ r1_tarski(X66,X67)
        | ~ v1_relat_1(X67)
        | ~ v1_relat_1(X66) )
      & ( r1_tarski(k2_relat_1(X66),k2_relat_1(X67))
        | ~ r1_tarski(X66,X67)
        | ~ v1_relat_1(X67)
        | ~ v1_relat_1(X66) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

fof(c_0_40,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & ~ r1_tarski(k2_relat_1(k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k2_relat_1(esk2_0),k2_relat_1(esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_34])])])).

cnf(c_0_41,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,plain,
    ( m1_subset_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X4,X4,X5,X6,X7,X8,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_31]),c_0_32])).

fof(c_0_44,plain,(
    ! [X11,X12,X13] :
      ( ~ r1_tarski(X11,X12)
      | ~ r1_tarski(X11,X13)
      | r1_tarski(X11,k3_xboole_0(X12,X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_45,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( v1_relat_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_49,plain,(
    ! [X62,X63] :
      ( ~ r2_hidden(X62,X63)
      | r1_tarski(k1_setfam_1(X63),X62) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X2)
    | X2 != k6_enumset1(X3,X3,X3,X4,X5,X6,X7,X1) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(esk2_0))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( v1_relat_1(k1_setfam_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,X1))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(esk3_0))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_48])).

cnf(c_0_55,plain,
    ( r1_tarski(k1_setfam_1(X2),X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X1)) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,X1))),k2_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_37])])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,X1))),k2_relat_1(esk3_0))
    | ~ r1_tarski(k1_setfam_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,X1)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_53])).

cnf(c_0_60,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)),X6) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k2_relat_1(esk2_0),k2_relat_1(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,X1))),k1_setfam_1(k6_enumset1(k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),X2)))
    | ~ r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,X1))),X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0))),k2_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0))),k1_setfam_1(k6_enumset1(k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_27]),c_0_27]),c_0_28]),c_0_28]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_32]),c_0_32])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:29:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.58  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 0.20/0.58  # and selection function SelectNegativeLiterals.
% 0.20/0.58  #
% 0.20/0.58  # Preprocessing time       : 0.028 s
% 0.20/0.58  
% 0.20/0.58  # Proof found!
% 0.20/0.58  # SZS status Theorem
% 0.20/0.58  # SZS output start CNFRefutation
% 0.20/0.58  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.58  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.58  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.20/0.58  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.58  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.58  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.58  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.20/0.58  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.20/0.58  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.58  fof(d4_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:(X7=k4_enumset1(X1,X2,X3,X4,X5,X6)<=>![X8]:(r2_hidden(X8,X7)<=>~((((((X8!=X1&X8!=X2)&X8!=X3)&X8!=X4)&X8!=X5)&X8!=X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_enumset1)).
% 0.20/0.58  fof(t27_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k2_relat_1(X1),k2_relat_1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_relat_1)).
% 0.20/0.58  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.20/0.58  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 0.20/0.58  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.20/0.58  fof(t4_setfam_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(k1_setfam_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 0.20/0.58  fof(c_0_15, plain, ![X58, X59]:k1_setfam_1(k2_tarski(X58,X59))=k3_xboole_0(X58,X59), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.20/0.58  fof(c_0_16, plain, ![X14, X15]:k1_enumset1(X14,X14,X15)=k2_tarski(X14,X15), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.58  fof(c_0_17, plain, ![X9, X10]:r1_tarski(k3_xboole_0(X9,X10),X9), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.20/0.58  cnf(c_0_18, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.58  cnf(c_0_19, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.58  fof(c_0_20, plain, ![X16, X17, X18]:k2_enumset1(X16,X16,X17,X18)=k1_enumset1(X16,X17,X18), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.58  fof(c_0_21, plain, ![X19, X20, X21, X22]:k3_enumset1(X19,X19,X20,X21,X22)=k2_enumset1(X19,X20,X21,X22), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.58  fof(c_0_22, plain, ![X23, X24, X25, X26, X27]:k4_enumset1(X23,X23,X24,X25,X26,X27)=k3_enumset1(X23,X24,X25,X26,X27), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.58  fof(c_0_23, plain, ![X28, X29, X30, X31, X32, X33]:k5_enumset1(X28,X28,X29,X30,X31,X32,X33)=k4_enumset1(X28,X29,X30,X31,X32,X33), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.20/0.58  fof(c_0_24, plain, ![X34, X35, X36, X37, X38, X39, X40]:k6_enumset1(X34,X34,X35,X36,X37,X38,X39,X40)=k5_enumset1(X34,X35,X36,X37,X38,X39,X40), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.20/0.58  fof(c_0_25, plain, ![X60, X61]:((~m1_subset_1(X60,k1_zfmisc_1(X61))|r1_tarski(X60,X61))&(~r1_tarski(X60,X61)|m1_subset_1(X60,k1_zfmisc_1(X61)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.58  cnf(c_0_26, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.58  cnf(c_0_27, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.58  cnf(c_0_28, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.58  cnf(c_0_29, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.58  cnf(c_0_30, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.58  cnf(c_0_31, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.58  cnf(c_0_32, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.58  fof(c_0_33, plain, ![X41, X42, X43, X44, X45, X46, X47, X48, X49, X50, X51, X52, X53, X54, X55, X56]:(((~r2_hidden(X48,X47)|(X48=X41|X48=X42|X48=X43|X48=X44|X48=X45|X48=X46)|X47!=k4_enumset1(X41,X42,X43,X44,X45,X46))&((((((X49!=X41|r2_hidden(X49,X47)|X47!=k4_enumset1(X41,X42,X43,X44,X45,X46))&(X49!=X42|r2_hidden(X49,X47)|X47!=k4_enumset1(X41,X42,X43,X44,X45,X46)))&(X49!=X43|r2_hidden(X49,X47)|X47!=k4_enumset1(X41,X42,X43,X44,X45,X46)))&(X49!=X44|r2_hidden(X49,X47)|X47!=k4_enumset1(X41,X42,X43,X44,X45,X46)))&(X49!=X45|r2_hidden(X49,X47)|X47!=k4_enumset1(X41,X42,X43,X44,X45,X46)))&(X49!=X46|r2_hidden(X49,X47)|X47!=k4_enumset1(X41,X42,X43,X44,X45,X46))))&(((((((esk1_7(X50,X51,X52,X53,X54,X55,X56)!=X50|~r2_hidden(esk1_7(X50,X51,X52,X53,X54,X55,X56),X56)|X56=k4_enumset1(X50,X51,X52,X53,X54,X55))&(esk1_7(X50,X51,X52,X53,X54,X55,X56)!=X51|~r2_hidden(esk1_7(X50,X51,X52,X53,X54,X55,X56),X56)|X56=k4_enumset1(X50,X51,X52,X53,X54,X55)))&(esk1_7(X50,X51,X52,X53,X54,X55,X56)!=X52|~r2_hidden(esk1_7(X50,X51,X52,X53,X54,X55,X56),X56)|X56=k4_enumset1(X50,X51,X52,X53,X54,X55)))&(esk1_7(X50,X51,X52,X53,X54,X55,X56)!=X53|~r2_hidden(esk1_7(X50,X51,X52,X53,X54,X55,X56),X56)|X56=k4_enumset1(X50,X51,X52,X53,X54,X55)))&(esk1_7(X50,X51,X52,X53,X54,X55,X56)!=X54|~r2_hidden(esk1_7(X50,X51,X52,X53,X54,X55,X56),X56)|X56=k4_enumset1(X50,X51,X52,X53,X54,X55)))&(esk1_7(X50,X51,X52,X53,X54,X55,X56)!=X55|~r2_hidden(esk1_7(X50,X51,X52,X53,X54,X55,X56),X56)|X56=k4_enumset1(X50,X51,X52,X53,X54,X55)))&(r2_hidden(esk1_7(X50,X51,X52,X53,X54,X55,X56),X56)|(esk1_7(X50,X51,X52,X53,X54,X55,X56)=X50|esk1_7(X50,X51,X52,X53,X54,X55,X56)=X51|esk1_7(X50,X51,X52,X53,X54,X55,X56)=X52|esk1_7(X50,X51,X52,X53,X54,X55,X56)=X53|esk1_7(X50,X51,X52,X53,X54,X55,X56)=X54|esk1_7(X50,X51,X52,X53,X54,X55,X56)=X55)|X56=k4_enumset1(X50,X51,X52,X53,X54,X55)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_enumset1])])])])])])).
% 0.20/0.58  fof(c_0_34, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k2_relat_1(X1),k2_relat_1(X2)))))), inference(assume_negation,[status(cth)],[t27_relat_1])).
% 0.20/0.58  fof(c_0_35, plain, ![X64, X65]:(~v1_relat_1(X64)|(~m1_subset_1(X65,k1_zfmisc_1(X64))|v1_relat_1(X65))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.20/0.58  cnf(c_0_36, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.58  cnf(c_0_37, plain, (r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31]), c_0_32])).
% 0.20/0.58  cnf(c_0_38, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k4_enumset1(X4,X5,X6,X7,X8,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.58  fof(c_0_39, plain, ![X66, X67]:((r1_tarski(k1_relat_1(X66),k1_relat_1(X67))|~r1_tarski(X66,X67)|~v1_relat_1(X67)|~v1_relat_1(X66))&(r1_tarski(k2_relat_1(X66),k2_relat_1(X67))|~r1_tarski(X66,X67)|~v1_relat_1(X67)|~v1_relat_1(X66))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.20/0.58  fof(c_0_40, negated_conjecture, (v1_relat_1(esk2_0)&(v1_relat_1(esk3_0)&~r1_tarski(k2_relat_1(k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k2_relat_1(esk2_0),k2_relat_1(esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_34])])])).
% 0.20/0.58  cnf(c_0_41, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.58  cnf(c_0_42, plain, (m1_subset_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.58  cnf(c_0_43, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X4,X4,X5,X6,X7,X8,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_31]), c_0_32])).
% 0.20/0.58  fof(c_0_44, plain, ![X11, X12, X13]:(~r1_tarski(X11,X12)|~r1_tarski(X11,X13)|r1_tarski(X11,k3_xboole_0(X12,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.20/0.58  cnf(c_0_45, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.58  cnf(c_0_46, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.58  cnf(c_0_47, plain, (v1_relat_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.58  cnf(c_0_48, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.58  fof(c_0_49, plain, ![X62, X63]:(~r2_hidden(X62,X63)|r1_tarski(k1_setfam_1(X63),X62)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).
% 0.20/0.58  cnf(c_0_50, plain, (r2_hidden(X1,X2)|X2!=k6_enumset1(X3,X3,X3,X4,X5,X6,X7,X1)), inference(er,[status(thm)],[c_0_43])).
% 0.20/0.58  cnf(c_0_51, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.58  cnf(c_0_52, negated_conjecture, (r1_tarski(k2_relat_1(X1),k2_relat_1(esk2_0))|~v1_relat_1(X1)|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.58  cnf(c_0_53, negated_conjecture, (v1_relat_1(k1_setfam_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,X1)))), inference(spm,[status(thm)],[c_0_47, c_0_46])).
% 0.20/0.58  cnf(c_0_54, negated_conjecture, (r1_tarski(k2_relat_1(X1),k2_relat_1(esk3_0))|~v1_relat_1(X1)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_45, c_0_48])).
% 0.20/0.58  cnf(c_0_55, plain, (r1_tarski(k1_setfam_1(X2),X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.58  cnf(c_0_56, plain, (r2_hidden(X1,k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X1))), inference(er,[status(thm)],[c_0_50])).
% 0.20/0.58  cnf(c_0_57, plain, (r1_tarski(X1,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31]), c_0_32])).
% 0.20/0.58  cnf(c_0_58, negated_conjecture, (r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,X1))),k2_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_37])])).
% 0.20/0.58  cnf(c_0_59, negated_conjecture, (r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,X1))),k2_relat_1(esk3_0))|~r1_tarski(k1_setfam_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,X1)),esk3_0)), inference(spm,[status(thm)],[c_0_54, c_0_53])).
% 0.20/0.58  cnf(c_0_60, plain, (r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)),X6)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.20/0.58  cnf(c_0_61, negated_conjecture, (~r1_tarski(k2_relat_1(k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k2_relat_1(esk2_0),k2_relat_1(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.58  cnf(c_0_62, negated_conjecture, (r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,X1))),k1_setfam_1(k6_enumset1(k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),X2)))|~r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,X1))),X2)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.20/0.58  cnf(c_0_63, negated_conjecture, (r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0))),k2_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.20/0.58  cnf(c_0_64, negated_conjecture, (~r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0))),k1_setfam_1(k6_enumset1(k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_27]), c_0_27]), c_0_28]), c_0_28]), c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_31]), c_0_31]), c_0_32]), c_0_32])).
% 0.20/0.58  cnf(c_0_65, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64]), ['proof']).
% 0.20/0.58  # SZS output end CNFRefutation
% 0.20/0.58  # Proof object total steps             : 66
% 0.20/0.58  # Proof object clause steps            : 35
% 0.20/0.58  # Proof object formula steps           : 31
% 0.20/0.58  # Proof object conjectures             : 15
% 0.20/0.58  # Proof object clause conjectures      : 12
% 0.20/0.58  # Proof object formula conjectures     : 3
% 0.20/0.58  # Proof object initial clauses used    : 17
% 0.20/0.58  # Proof object initial formulas used   : 15
% 0.20/0.58  # Proof object generating inferences   : 12
% 0.20/0.58  # Proof object simplifying inferences  : 31
% 0.20/0.58  # Training examples: 0 positive, 0 negative
% 0.20/0.58  # Parsed axioms                        : 15
% 0.20/0.58  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.58  # Initial clauses                      : 32
% 0.20/0.58  # Removed in clause preprocessing      : 7
% 0.20/0.58  # Initial clauses in saturation        : 25
% 0.20/0.58  # Processed clauses                    : 222
% 0.20/0.58  # ...of these trivial                  : 8
% 0.20/0.58  # ...subsumed                          : 29
% 0.20/0.58  # ...remaining for further processing  : 185
% 0.20/0.58  # Other redundant clauses eliminated   : 82
% 0.20/0.58  # Clauses deleted for lack of memory   : 0
% 0.20/0.58  # Backward-subsumed                    : 0
% 0.20/0.58  # Backward-rewritten                   : 1
% 0.20/0.58  # Generated clauses                    : 2317
% 0.20/0.58  # ...of the previous two non-trivial   : 2137
% 0.20/0.58  # Contextual simplify-reflections      : 8
% 0.20/0.58  # Paramodulations                      : 2220
% 0.20/0.58  # Factorizations                       : 3
% 0.20/0.58  # Equation resolutions                 : 94
% 0.20/0.58  # Propositional unsat checks           : 0
% 0.20/0.58  #    Propositional check models        : 0
% 0.20/0.58  #    Propositional check unsatisfiable : 0
% 0.20/0.58  #    Propositional clauses             : 0
% 0.20/0.58  #    Propositional clauses after purity: 0
% 0.20/0.58  #    Propositional unsat core size     : 0
% 0.20/0.58  #    Propositional preprocessing time  : 0.000
% 0.20/0.58  #    Propositional encoding time       : 0.000
% 0.20/0.58  #    Propositional solver time         : 0.000
% 0.20/0.58  #    Success case prop preproc time    : 0.000
% 0.20/0.58  #    Success case prop encoding time   : 0.000
% 0.20/0.58  #    Success case prop solver time     : 0.000
% 0.20/0.58  # Current number of processed clauses  : 178
% 0.20/0.58  #    Positive orientable unit clauses  : 28
% 0.20/0.58  #    Positive unorientable unit clauses: 0
% 0.20/0.58  #    Negative unit clauses             : 1
% 0.20/0.58  #    Non-unit-clauses                  : 149
% 0.20/0.58  # Current number of unprocessed clauses: 1934
% 0.20/0.58  # ...number of literals in the above   : 30026
% 0.20/0.58  # Current number of archived formulas  : 0
% 0.20/0.58  # Current number of archived clauses   : 8
% 0.20/0.58  # Clause-clause subsumption calls (NU) : 7135
% 0.20/0.58  # Rec. Clause-clause subsumption calls : 1327
% 0.20/0.58  # Non-unit clause-clause subsumptions  : 37
% 0.20/0.58  # Unit Clause-clause subsumption calls : 238
% 0.20/0.58  # Rewrite failures with RHS unbound    : 0
% 0.20/0.58  # BW rewrite match attempts            : 104
% 0.20/0.58  # BW rewrite match successes           : 1
% 0.20/0.58  # Condensation attempts                : 0
% 0.20/0.58  # Condensation successes               : 0
% 0.20/0.58  # Termbank termtop insertions          : 163210
% 0.20/0.58  
% 0.20/0.58  # -------------------------------------------------
% 0.20/0.58  # User time                : 0.226 s
% 0.20/0.58  # System time              : 0.008 s
% 0.20/0.58  # Total time               : 0.234 s
% 0.20/0.58  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
