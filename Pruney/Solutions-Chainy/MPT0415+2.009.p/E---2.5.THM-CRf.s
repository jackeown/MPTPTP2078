%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:39 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 122 expanded)
%              Number of clauses        :   31 (  48 expanded)
%              Number of leaves         :   18 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :  130 ( 202 expanded)
%              Number of equality atoms :   63 ( 125 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal clause size      :   26 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t46_setfam_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ~ ( X2 != k1_xboole_0
          & k7_setfam_1(X1,X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

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

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(d8_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
         => ( X3 = k7_setfam_1(X1,X2)
          <=> ! [X4] :
                ( m1_subset_1(X4,k1_zfmisc_1(X1))
               => ( r2_hidden(X4,X3)
                <=> r2_hidden(k3_subset_1(X1,X4),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(involutiveness_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k7_setfam_1(X1,k7_setfam_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(dt_k1_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(c_0_18,plain,(
    ! [X52,X53] : k1_setfam_1(k2_tarski(X52,X53)) = k3_xboole_0(X52,X53) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_19,plain,(
    ! [X14,X15] : k1_enumset1(X14,X14,X15) = k2_tarski(X14,X15) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_20,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_21,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ~ ( X2 != k1_xboole_0
            & k7_setfam_1(X1,X2) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t46_setfam_1])).

fof(c_0_24,plain,(
    ! [X41,X42] :
      ( ( k4_xboole_0(X41,k1_tarski(X42)) != X41
        | ~ r2_hidden(X42,X41) )
      & ( r2_hidden(X42,X41)
        | k4_xboole_0(X41,k1_tarski(X42)) = X41 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

fof(c_0_25,plain,(
    ! [X13] : k2_tarski(X13,X13) = k1_tarski(X13) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_28,plain,(
    ! [X16,X17,X18] : k2_enumset1(X16,X16,X17,X18) = k1_enumset1(X16,X17,X18) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_29,plain,(
    ! [X19,X20,X21,X22] : k3_enumset1(X19,X19,X20,X21,X22) = k2_enumset1(X19,X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_30,plain,(
    ! [X23,X24,X25,X26,X27] : k4_enumset1(X23,X23,X24,X25,X26,X27) = k3_enumset1(X23,X24,X25,X26,X27) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_31,plain,(
    ! [X28,X29,X30,X31,X32,X33] : k5_enumset1(X28,X28,X29,X30,X31,X32,X33) = k4_enumset1(X28,X29,X30,X31,X32,X33) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_32,plain,(
    ! [X34,X35,X36,X37,X38,X39,X40] : k6_enumset1(X34,X34,X35,X36,X37,X38,X39,X40) = k5_enumset1(X34,X35,X36,X37,X38,X39,X40) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_33,plain,(
    ! [X12] : k4_xboole_0(k1_xboole_0,X12) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

fof(c_0_34,plain,(
    ! [X45,X46,X47,X48] :
      ( ( ~ r2_hidden(X48,X47)
        | r2_hidden(k3_subset_1(X45,X48),X46)
        | ~ m1_subset_1(X48,k1_zfmisc_1(X45))
        | X47 != k7_setfam_1(X45,X46)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k1_zfmisc_1(X45)))
        | ~ m1_subset_1(X46,k1_zfmisc_1(k1_zfmisc_1(X45))) )
      & ( ~ r2_hidden(k3_subset_1(X45,X48),X46)
        | r2_hidden(X48,X47)
        | ~ m1_subset_1(X48,k1_zfmisc_1(X45))
        | X47 != k7_setfam_1(X45,X46)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k1_zfmisc_1(X45)))
        | ~ m1_subset_1(X46,k1_zfmisc_1(k1_zfmisc_1(X45))) )
      & ( m1_subset_1(esk2_3(X45,X46,X47),k1_zfmisc_1(X45))
        | X47 = k7_setfam_1(X45,X46)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k1_zfmisc_1(X45)))
        | ~ m1_subset_1(X46,k1_zfmisc_1(k1_zfmisc_1(X45))) )
      & ( ~ r2_hidden(esk2_3(X45,X46,X47),X47)
        | ~ r2_hidden(k3_subset_1(X45,esk2_3(X45,X46,X47)),X46)
        | X47 = k7_setfam_1(X45,X46)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k1_zfmisc_1(X45)))
        | ~ m1_subset_1(X46,k1_zfmisc_1(k1_zfmisc_1(X45))) )
      & ( r2_hidden(esk2_3(X45,X46,X47),X47)
        | r2_hidden(k3_subset_1(X45,esk2_3(X45,X46,X47)),X46)
        | X47 = k7_setfam_1(X45,X46)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k1_zfmisc_1(X45)))
        | ~ m1_subset_1(X46,k1_zfmisc_1(k1_zfmisc_1(X45))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_setfam_1])])])])])).

fof(c_0_35,plain,(
    ! [X54,X55,X56] :
      ( ~ r2_hidden(X54,X55)
      | ~ m1_subset_1(X55,k1_zfmisc_1(X56))
      | m1_subset_1(X54,X56) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_36,plain,(
    ! [X50,X51] :
      ( ~ m1_subset_1(X51,k1_zfmisc_1(k1_zfmisc_1(X50)))
      | k7_setfam_1(X50,k7_setfam_1(X50,X51)) = X51 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k7_setfam_1])])).

fof(c_0_37,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))
    & esk4_0 != k1_xboole_0
    & k7_setfam_1(esk3_0,esk4_0) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

fof(c_0_38,plain,(
    ! [X44] : m1_subset_1(k1_subset_1(X44),k1_zfmisc_1(X44)) ),
    inference(variable_rename,[status(thm)],[dt_k1_subset_1])).

fof(c_0_39,plain,(
    ! [X43] : k1_subset_1(X43) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,k1_tarski(X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_41,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_43,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_44,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_45,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_46,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_47,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_48,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_49,plain,(
    ! [X8] :
      ( X8 = k1_xboole_0
      | r2_hidden(esk1_1(X8),X8) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_50,plain,
    ( r2_hidden(k3_subset_1(X3,X1),X4)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | X2 != k7_setfam_1(X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_51,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_52,plain,
    ( k7_setfam_1(X2,k7_setfam_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_54,negated_conjecture,
    ( k7_setfam_1(esk3_0,esk4_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_55,plain,
    ( m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_56,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_57,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41]),c_0_22]),c_0_42]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_47]),c_0_47])).

cnf(c_0_58,plain,
    ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_47])).

cnf(c_0_59,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_60,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_61,plain,
    ( r2_hidden(k3_subset_1(X1,X2),X3)
    | ~ m1_subset_1(k7_setfam_1(X1,X3),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X2,k7_setfam_1(X1,X3)) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_50,c_0_51])])).

cnf(c_0_62,negated_conjecture,
    ( k7_setfam_1(esk3_0,k1_xboole_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])).

cnf(c_0_63,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_64,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk1_1(esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( ~ r2_hidden(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_53]),c_0_63])]),c_0_64])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_65,c_0_66]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:33:59 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.13/0.37  # and selection function SelectNegativeLiterals.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.028 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.13/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.37  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.13/0.37  fof(t46_setfam_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>~((X2!=k1_xboole_0&k7_setfam_1(X1,X2)=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_setfam_1)).
% 0.13/0.37  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.13/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.37  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.37  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.13/0.37  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.13/0.37  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.13/0.37  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 0.13/0.37  fof(d8_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(X3=k7_setfam_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>(r2_hidden(X4,X3)<=>r2_hidden(k3_subset_1(X1,X4),X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_setfam_1)).
% 0.13/0.37  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.13/0.37  fof(involutiveness_k7_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k7_setfam_1(X1,k7_setfam_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 0.13/0.37  fof(dt_k1_subset_1, axiom, ![X1]:m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_subset_1)).
% 0.13/0.37  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 0.13/0.37  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.13/0.37  fof(c_0_18, plain, ![X52, X53]:k1_setfam_1(k2_tarski(X52,X53))=k3_xboole_0(X52,X53), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.13/0.37  fof(c_0_19, plain, ![X14, X15]:k1_enumset1(X14,X14,X15)=k2_tarski(X14,X15), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.37  fof(c_0_20, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.13/0.37  cnf(c_0_21, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.37  cnf(c_0_22, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.37  fof(c_0_23, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>~((X2!=k1_xboole_0&k7_setfam_1(X1,X2)=k1_xboole_0)))), inference(assume_negation,[status(cth)],[t46_setfam_1])).
% 0.13/0.37  fof(c_0_24, plain, ![X41, X42]:((k4_xboole_0(X41,k1_tarski(X42))!=X41|~r2_hidden(X42,X41))&(r2_hidden(X42,X41)|k4_xboole_0(X41,k1_tarski(X42))=X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.13/0.37  fof(c_0_25, plain, ![X13]:k2_tarski(X13,X13)=k1_tarski(X13), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.37  cnf(c_0_26, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.37  cnf(c_0_27, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.13/0.37  fof(c_0_28, plain, ![X16, X17, X18]:k2_enumset1(X16,X16,X17,X18)=k1_enumset1(X16,X17,X18), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.37  fof(c_0_29, plain, ![X19, X20, X21, X22]:k3_enumset1(X19,X19,X20,X21,X22)=k2_enumset1(X19,X20,X21,X22), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.37  fof(c_0_30, plain, ![X23, X24, X25, X26, X27]:k4_enumset1(X23,X23,X24,X25,X26,X27)=k3_enumset1(X23,X24,X25,X26,X27), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.13/0.37  fof(c_0_31, plain, ![X28, X29, X30, X31, X32, X33]:k5_enumset1(X28,X28,X29,X30,X31,X32,X33)=k4_enumset1(X28,X29,X30,X31,X32,X33), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.13/0.37  fof(c_0_32, plain, ![X34, X35, X36, X37, X38, X39, X40]:k6_enumset1(X34,X34,X35,X36,X37,X38,X39,X40)=k5_enumset1(X34,X35,X36,X37,X38,X39,X40), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.13/0.37  fof(c_0_33, plain, ![X12]:k4_xboole_0(k1_xboole_0,X12)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.13/0.37  fof(c_0_34, plain, ![X45, X46, X47, X48]:(((~r2_hidden(X48,X47)|r2_hidden(k3_subset_1(X45,X48),X46)|~m1_subset_1(X48,k1_zfmisc_1(X45))|X47!=k7_setfam_1(X45,X46)|~m1_subset_1(X47,k1_zfmisc_1(k1_zfmisc_1(X45)))|~m1_subset_1(X46,k1_zfmisc_1(k1_zfmisc_1(X45))))&(~r2_hidden(k3_subset_1(X45,X48),X46)|r2_hidden(X48,X47)|~m1_subset_1(X48,k1_zfmisc_1(X45))|X47!=k7_setfam_1(X45,X46)|~m1_subset_1(X47,k1_zfmisc_1(k1_zfmisc_1(X45)))|~m1_subset_1(X46,k1_zfmisc_1(k1_zfmisc_1(X45)))))&((m1_subset_1(esk2_3(X45,X46,X47),k1_zfmisc_1(X45))|X47=k7_setfam_1(X45,X46)|~m1_subset_1(X47,k1_zfmisc_1(k1_zfmisc_1(X45)))|~m1_subset_1(X46,k1_zfmisc_1(k1_zfmisc_1(X45))))&((~r2_hidden(esk2_3(X45,X46,X47),X47)|~r2_hidden(k3_subset_1(X45,esk2_3(X45,X46,X47)),X46)|X47=k7_setfam_1(X45,X46)|~m1_subset_1(X47,k1_zfmisc_1(k1_zfmisc_1(X45)))|~m1_subset_1(X46,k1_zfmisc_1(k1_zfmisc_1(X45))))&(r2_hidden(esk2_3(X45,X46,X47),X47)|r2_hidden(k3_subset_1(X45,esk2_3(X45,X46,X47)),X46)|X47=k7_setfam_1(X45,X46)|~m1_subset_1(X47,k1_zfmisc_1(k1_zfmisc_1(X45)))|~m1_subset_1(X46,k1_zfmisc_1(k1_zfmisc_1(X45))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_setfam_1])])])])])).
% 0.13/0.37  fof(c_0_35, plain, ![X54, X55, X56]:(~r2_hidden(X54,X55)|~m1_subset_1(X55,k1_zfmisc_1(X56))|m1_subset_1(X54,X56)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.13/0.37  fof(c_0_36, plain, ![X50, X51]:(~m1_subset_1(X51,k1_zfmisc_1(k1_zfmisc_1(X50)))|k7_setfam_1(X50,k7_setfam_1(X50,X51))=X51), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k7_setfam_1])])).
% 0.13/0.37  fof(c_0_37, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))&(esk4_0!=k1_xboole_0&k7_setfam_1(esk3_0,esk4_0)=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 0.13/0.37  fof(c_0_38, plain, ![X44]:m1_subset_1(k1_subset_1(X44),k1_zfmisc_1(X44)), inference(variable_rename,[status(thm)],[dt_k1_subset_1])).
% 0.13/0.37  fof(c_0_39, plain, ![X43]:k1_subset_1(X43)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 0.13/0.37  cnf(c_0_40, plain, (k4_xboole_0(X1,k1_tarski(X2))!=X1|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.37  cnf(c_0_41, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.37  cnf(c_0_42, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.13/0.37  cnf(c_0_43, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.37  cnf(c_0_44, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.37  cnf(c_0_45, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.37  cnf(c_0_46, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.37  cnf(c_0_47, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.37  cnf(c_0_48, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.37  fof(c_0_49, plain, ![X8]:(X8=k1_xboole_0|r2_hidden(esk1_1(X8),X8)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.13/0.37  cnf(c_0_50, plain, (r2_hidden(k3_subset_1(X3,X1),X4)|~r2_hidden(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X3))|X2!=k7_setfam_1(X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.37  cnf(c_0_51, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.37  cnf(c_0_52, plain, (k7_setfam_1(X2,k7_setfam_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.37  cnf(c_0_53, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.37  cnf(c_0_54, negated_conjecture, (k7_setfam_1(esk3_0,esk4_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.37  cnf(c_0_55, plain, (m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.37  cnf(c_0_56, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.37  cnf(c_0_57, plain, (k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))!=X1|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41]), c_0_22]), c_0_42]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_47]), c_0_47])).
% 0.13/0.37  cnf(c_0_58, plain, (k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_47])).
% 0.13/0.37  cnf(c_0_59, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.37  cnf(c_0_60, plain, (X1=k1_xboole_0|r2_hidden(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.13/0.37  cnf(c_0_61, plain, (r2_hidden(k3_subset_1(X1,X2),X3)|~m1_subset_1(k7_setfam_1(X1,X3),k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))|~r2_hidden(X2,k7_setfam_1(X1,X3))), inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_50, c_0_51])])).
% 0.13/0.37  cnf(c_0_62, negated_conjecture, (k7_setfam_1(esk3_0,k1_xboole_0)=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])).
% 0.13/0.37  cnf(c_0_63, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_55, c_0_56])).
% 0.13/0.37  cnf(c_0_64, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.13/0.37  cnf(c_0_65, negated_conjecture, (r2_hidden(esk1_1(esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.13/0.37  cnf(c_0_66, negated_conjecture, (~r2_hidden(X1,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_53]), c_0_63])]), c_0_64])).
% 0.13/0.37  cnf(c_0_67, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_65, c_0_66]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 68
% 0.13/0.37  # Proof object clause steps            : 31
% 0.13/0.37  # Proof object formula steps           : 37
% 0.13/0.37  # Proof object conjectures             : 10
% 0.13/0.37  # Proof object clause conjectures      : 7
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 20
% 0.13/0.37  # Proof object initial formulas used   : 18
% 0.13/0.37  # Proof object generating inferences   : 4
% 0.13/0.37  # Proof object simplifying inferences  : 30
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 18
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 25
% 0.13/0.37  # Removed in clause preprocessing      : 10
% 0.13/0.37  # Initial clauses in saturation        : 15
% 0.13/0.37  # Processed clauses                    : 74
% 0.13/0.37  # ...of these trivial                  : 1
% 0.13/0.37  # ...subsumed                          : 18
% 0.13/0.37  # ...remaining for further processing  : 55
% 0.13/0.37  # Other redundant clauses eliminated   : 3
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 1
% 0.13/0.37  # Backward-rewritten                   : 1
% 0.13/0.37  # Generated clauses                    : 162
% 0.13/0.37  # ...of the previous two non-trivial   : 129
% 0.13/0.37  # Contextual simplify-reflections      : 1
% 0.13/0.37  # Paramodulations                      : 156
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 3
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 33
% 0.13/0.37  #    Positive orientable unit clauses  : 7
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 3
% 0.13/0.37  #    Non-unit-clauses                  : 23
% 0.13/0.37  # Current number of unprocessed clauses: 80
% 0.13/0.37  # ...number of literals in the above   : 249
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 30
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 172
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 130
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 18
% 0.13/0.37  # Unit Clause-clause subsumption calls : 9
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 1
% 0.13/0.37  # BW rewrite match successes           : 1
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 3607
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.035 s
% 0.13/0.37  # System time              : 0.001 s
% 0.13/0.37  # Total time               : 0.036 s
% 0.13/0.37  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
