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
% DateTime   : Thu Dec  3 10:52:39 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 239 expanded)
%              Number of clauses        :   42 ( 105 expanded)
%              Number of leaves         :   18 (  65 expanded)
%              Depth                    :   14
%              Number of atoms          :  157 ( 509 expanded)
%              Number of equality atoms :   53 ( 140 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(t215_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_xboole_0(k2_relat_1(X1),k2_relat_1(X2))
           => r1_xboole_0(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t215_relat_1)).

fof(t95_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k7_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(t111_relat_1,axiom,(
    ! [X1] : k7_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

fof(t72_xboole_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X4,X2) )
     => X3 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t88_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => k4_xboole_0(k2_xboole_0(X1,X2),X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t27_xboole_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4) )
     => r1_tarski(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_xboole_1)).

fof(t75_xboole_1,axiom,(
    ! [X1,X2] :
      ~ ( ~ r1_xboole_0(X1,X2)
        & r1_xboole_0(k3_xboole_0(X1,X2),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

fof(t21_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(c_0_18,plain,(
    ! [X36,X37] :
      ( ~ v1_relat_1(X36)
      | ~ m1_subset_1(X37,k1_zfmisc_1(X36))
      | v1_relat_1(X37) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_19,plain,(
    ! [X32] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X32)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_xboole_0(k2_relat_1(X1),k2_relat_1(X2))
             => r1_xboole_0(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t215_relat_1])).

cnf(c_0_21,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & r1_xboole_0(k2_relat_1(esk1_0),k2_relat_1(esk2_0))
    & ~ r1_xboole_0(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

fof(c_0_24,plain,(
    ! [X40,X41] :
      ( ( k7_relat_1(X41,X40) != k1_xboole_0
        | r1_xboole_0(k1_relat_1(X41),X40)
        | ~ v1_relat_1(X41) )
      & ( ~ r1_xboole_0(k1_relat_1(X41),X40)
        | k7_relat_1(X41,X40) = k1_xboole_0
        | ~ v1_relat_1(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_relat_1])])])).

fof(c_0_25,plain,(
    ! [X38] : k7_relat_1(k1_xboole_0,X38) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t111_relat_1])).

cnf(c_0_26,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_28,plain,(
    ! [X16,X17,X18,X19] :
      ( k2_xboole_0(X16,X17) != k2_xboole_0(X18,X19)
      | ~ r1_xboole_0(X18,X16)
      | ~ r1_xboole_0(X19,X17)
      | X18 = X17 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t72_xboole_1])])).

fof(c_0_29,plain,(
    ! [X5] : k2_xboole_0(X5,k1_xboole_0) = X5 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_30,plain,
    ( r1_xboole_0(k1_relat_1(X1),X2)
    | k7_relat_1(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( k7_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_33,negated_conjecture,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_34,plain,(
    ! [X28,X29,X30,X31] : k2_zfmisc_1(k3_xboole_0(X28,X29),k3_xboole_0(X30,X31)) = k3_xboole_0(k2_zfmisc_1(X28,X30),k2_zfmisc_1(X29,X31)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

fof(c_0_35,plain,(
    ! [X10,X11] : k4_xboole_0(X10,k4_xboole_0(X10,X11)) = k3_xboole_0(X10,X11) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_36,plain,(
    ! [X22,X23] :
      ( ( ~ r1_xboole_0(X22,X23)
        | k4_xboole_0(X22,X23) = X22 )
      & ( k4_xboole_0(X22,X23) != X22
        | r1_xboole_0(X22,X23) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_37,plain,
    ( X3 = X2
    | k2_xboole_0(X1,X2) != k2_xboole_0(X3,X4)
    | ~ r1_xboole_0(X3,X1)
    | ~ r1_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33])])).

fof(c_0_40,plain,(
    ! [X15] : r1_xboole_0(X15,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_41,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(esk1_0),k2_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_45,plain,(
    ! [X24,X25] :
      ( ~ r1_xboole_0(X24,X25)
      | k4_xboole_0(k2_xboole_0(X24,X25),X25) = X24 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_xboole_1])])).

cnf(c_0_46,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_xboole_0(k2_xboole_0(X1,X2),X1) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])])])).

cnf(c_0_47,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_48,plain,(
    ! [X26,X27] :
      ( ( k2_zfmisc_1(X26,X27) != k1_xboole_0
        | X26 = k1_xboole_0
        | X27 = k1_xboole_0 )
      & ( X26 != k1_xboole_0
        | k2_zfmisc_1(X26,X27) = k1_xboole_0 )
      & ( X27 != k1_xboole_0
        | k2_zfmisc_1(X26,X27) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_49,plain,(
    ! [X6,X7,X8,X9] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X8,X9)
      | r1_tarski(k3_xboole_0(X6,X8),k3_xboole_0(X7,X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_xboole_1])])).

fof(c_0_50,plain,(
    ! [X20,X21] :
      ( r1_xboole_0(X20,X21)
      | ~ r1_xboole_0(k3_xboole_0(X20,X21),X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t75_xboole_1])])])).

cnf(c_0_51,plain,
    ( k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X3,X4))) = k4_xboole_0(k2_zfmisc_1(X1,X3),k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42]),c_0_42]),c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( k4_xboole_0(k2_relat_1(esk1_0),k2_relat_1(esk2_0)) = k2_relat_1(esk1_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_53,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_55,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,plain,
    ( r1_tarski(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_57,plain,(
    ! [X39] :
      ( ~ v1_relat_1(X39)
      | r1_tarski(X39,k2_zfmisc_1(k1_relat_1(X39),k2_relat_1(X39))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).

cnf(c_0_58,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k3_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_59,negated_conjecture,
    ( k4_xboole_0(k2_zfmisc_1(X1,k2_relat_1(esk1_0)),k4_xboole_0(k2_zfmisc_1(X1,k2_relat_1(esk1_0)),k2_zfmisc_1(X2,k2_relat_1(esk2_0)))) = k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k2_relat_1(esk1_0),k2_relat_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_60,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_39]),c_0_54])).

cnf(c_0_61,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_62,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X3)),k4_xboole_0(X2,k4_xboole_0(X2,X4)))
    | ~ r1_tarski(X3,X4)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_42]),c_0_42])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_64,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_58,c_0_42])).

cnf(c_0_65,negated_conjecture,
    ( k4_xboole_0(k2_zfmisc_1(X1,k2_relat_1(esk1_0)),k4_xboole_0(k2_zfmisc_1(X1,k2_relat_1(esk1_0)),k2_zfmisc_1(X2,k2_relat_1(esk2_0)))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_60]),c_0_61])).

fof(c_0_66,plain,(
    ! [X12,X13,X14] :
      ( ~ r1_tarski(X12,X13)
      | ~ r1_xboole_0(X13,X14)
      | r1_xboole_0(X12,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

cnf(c_0_67,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X3,k2_zfmisc_1(k1_relat_1(X2),k2_relat_1(X2)))))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( r1_xboole_0(k2_zfmisc_1(X1,k2_relat_1(esk1_0)),k2_zfmisc_1(X2,k2_relat_1(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_39])])).

cnf(c_0_69,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_70,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)),k4_xboole_0(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)),k2_zfmisc_1(k1_relat_1(X2),k2_relat_1(X2)))))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_63])).

cnf(c_0_71,negated_conjecture,
    ( k4_xboole_0(k2_zfmisc_1(X1,k2_relat_1(esk1_0)),k2_zfmisc_1(X2,k2_relat_1(esk2_0))) = k2_zfmisc_1(X1,k2_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_73,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_39])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_60]),c_0_27]),c_0_72])])).

cnf(c_0_75,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)),X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_76,negated_conjecture,
    ( ~ r1_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_77,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_75]),c_0_76]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:15:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S04DN
% 0.20/0.38  # and selection function SelectNewComplex.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.027 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.20/0.38  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.20/0.38  fof(t215_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_xboole_0(k2_relat_1(X1),k2_relat_1(X2))=>r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t215_relat_1)).
% 0.20/0.38  fof(t95_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(k7_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 0.20/0.38  fof(t111_relat_1, axiom, ![X1]:k7_relat_1(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 0.20/0.38  fof(t72_xboole_1, axiom, ![X1, X2, X3, X4]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)&r1_xboole_0(X3,X1))&r1_xboole_0(X4,X2))=>X3=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_xboole_1)).
% 0.20/0.38  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.20/0.38  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.20/0.38  fof(t123_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 0.20/0.38  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.38  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.20/0.38  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.20/0.38  fof(t88_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>k4_xboole_0(k2_xboole_0(X1,X2),X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_xboole_1)).
% 0.20/0.38  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.20/0.38  fof(t27_xboole_1, axiom, ![X1, X2, X3, X4]:((r1_tarski(X1,X2)&r1_tarski(X3,X4))=>r1_tarski(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_xboole_1)).
% 0.20/0.38  fof(t75_xboole_1, axiom, ![X1, X2]:~((~(r1_xboole_0(X1,X2))&r1_xboole_0(k3_xboole_0(X1,X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_xboole_1)).
% 0.20/0.38  fof(t21_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 0.20/0.38  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.20/0.38  fof(c_0_18, plain, ![X36, X37]:(~v1_relat_1(X36)|(~m1_subset_1(X37,k1_zfmisc_1(X36))|v1_relat_1(X37))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.20/0.38  fof(c_0_19, plain, ![X32]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X32)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.20/0.38  fof(c_0_20, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_xboole_0(k2_relat_1(X1),k2_relat_1(X2))=>r1_xboole_0(X1,X2))))), inference(assume_negation,[status(cth)],[t215_relat_1])).
% 0.20/0.38  cnf(c_0_21, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_22, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  fof(c_0_23, negated_conjecture, (v1_relat_1(esk1_0)&(v1_relat_1(esk2_0)&(r1_xboole_0(k2_relat_1(esk1_0),k2_relat_1(esk2_0))&~r1_xboole_0(esk1_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.20/0.38  fof(c_0_24, plain, ![X40, X41]:((k7_relat_1(X41,X40)!=k1_xboole_0|r1_xboole_0(k1_relat_1(X41),X40)|~v1_relat_1(X41))&(~r1_xboole_0(k1_relat_1(X41),X40)|k7_relat_1(X41,X40)=k1_xboole_0|~v1_relat_1(X41))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_relat_1])])])).
% 0.20/0.38  fof(c_0_25, plain, ![X38]:k7_relat_1(k1_xboole_0,X38)=k1_xboole_0, inference(variable_rename,[status(thm)],[t111_relat_1])).
% 0.20/0.38  cnf(c_0_26, plain, (v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.38  cnf(c_0_27, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.38  fof(c_0_28, plain, ![X16, X17, X18, X19]:(k2_xboole_0(X16,X17)!=k2_xboole_0(X18,X19)|~r1_xboole_0(X18,X16)|~r1_xboole_0(X19,X17)|X18=X17), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t72_xboole_1])])).
% 0.20/0.38  fof(c_0_29, plain, ![X5]:k2_xboole_0(X5,k1_xboole_0)=X5, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.20/0.38  cnf(c_0_30, plain, (r1_xboole_0(k1_relat_1(X1),X2)|k7_relat_1(X1,X2)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.38  cnf(c_0_31, plain, (k7_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.38  cnf(c_0_32, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.20/0.38  cnf(c_0_33, negated_conjecture, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.38  fof(c_0_34, plain, ![X28, X29, X30, X31]:k2_zfmisc_1(k3_xboole_0(X28,X29),k3_xboole_0(X30,X31))=k3_xboole_0(k2_zfmisc_1(X28,X30),k2_zfmisc_1(X29,X31)), inference(variable_rename,[status(thm)],[t123_zfmisc_1])).
% 0.20/0.38  fof(c_0_35, plain, ![X10, X11]:k4_xboole_0(X10,k4_xboole_0(X10,X11))=k3_xboole_0(X10,X11), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.38  fof(c_0_36, plain, ![X22, X23]:((~r1_xboole_0(X22,X23)|k4_xboole_0(X22,X23)=X22)&(k4_xboole_0(X22,X23)!=X22|r1_xboole_0(X22,X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.20/0.38  cnf(c_0_37, plain, (X3=X2|k2_xboole_0(X1,X2)!=k2_xboole_0(X3,X4)|~r1_xboole_0(X3,X1)|~r1_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.38  cnf(c_0_38, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.38  cnf(c_0_39, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33])])).
% 0.20/0.38  fof(c_0_40, plain, ![X15]:r1_xboole_0(X15,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.20/0.38  cnf(c_0_41, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.38  cnf(c_0_42, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.38  cnf(c_0_43, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.38  cnf(c_0_44, negated_conjecture, (r1_xboole_0(k2_relat_1(esk1_0),k2_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.38  fof(c_0_45, plain, ![X24, X25]:(~r1_xboole_0(X24,X25)|k4_xboole_0(k2_xboole_0(X24,X25),X25)=X24), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_xboole_1])])).
% 0.20/0.38  cnf(c_0_46, plain, (k2_xboole_0(X1,X2)=X2|~r1_xboole_0(k2_xboole_0(X1,X2),X1)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])])])).
% 0.20/0.38  cnf(c_0_47, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.38  fof(c_0_48, plain, ![X26, X27]:((k2_zfmisc_1(X26,X27)!=k1_xboole_0|(X26=k1_xboole_0|X27=k1_xboole_0))&((X26!=k1_xboole_0|k2_zfmisc_1(X26,X27)=k1_xboole_0)&(X27!=k1_xboole_0|k2_zfmisc_1(X26,X27)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.20/0.38  fof(c_0_49, plain, ![X6, X7, X8, X9]:(~r1_tarski(X6,X7)|~r1_tarski(X8,X9)|r1_tarski(k3_xboole_0(X6,X8),k3_xboole_0(X7,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_xboole_1])])).
% 0.20/0.38  fof(c_0_50, plain, ![X20, X21]:(r1_xboole_0(X20,X21)|~r1_xboole_0(k3_xboole_0(X20,X21),X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t75_xboole_1])])])).
% 0.20/0.38  cnf(c_0_51, plain, (k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X3,X4)))=k4_xboole_0(k2_zfmisc_1(X1,X3),k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42]), c_0_42]), c_0_42])).
% 0.20/0.38  cnf(c_0_52, negated_conjecture, (k4_xboole_0(k2_relat_1(esk1_0),k2_relat_1(esk2_0))=k2_relat_1(esk1_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.38  cnf(c_0_53, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.38  cnf(c_0_54, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.38  cnf(c_0_55, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.38  cnf(c_0_56, plain, (r1_tarski(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))|~r1_tarski(X1,X2)|~r1_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.38  fof(c_0_57, plain, ![X39]:(~v1_relat_1(X39)|r1_tarski(X39,k2_zfmisc_1(k1_relat_1(X39),k2_relat_1(X39)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).
% 0.20/0.38  cnf(c_0_58, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(k3_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.38  cnf(c_0_59, negated_conjecture, (k4_xboole_0(k2_zfmisc_1(X1,k2_relat_1(esk1_0)),k4_xboole_0(k2_zfmisc_1(X1,k2_relat_1(esk1_0)),k2_zfmisc_1(X2,k2_relat_1(esk2_0))))=k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k2_relat_1(esk1_0),k2_relat_1(esk1_0)))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.20/0.38  cnf(c_0_60, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_39]), c_0_54])).
% 0.20/0.38  cnf(c_0_61, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_55])).
% 0.20/0.38  cnf(c_0_62, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X3)),k4_xboole_0(X2,k4_xboole_0(X2,X4)))|~r1_tarski(X3,X4)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_42]), c_0_42])).
% 0.20/0.38  cnf(c_0_63, plain, (r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.20/0.38  cnf(c_0_64, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[c_0_58, c_0_42])).
% 0.20/0.38  cnf(c_0_65, negated_conjecture, (k4_xboole_0(k2_zfmisc_1(X1,k2_relat_1(esk1_0)),k4_xboole_0(k2_zfmisc_1(X1,k2_relat_1(esk1_0)),k2_zfmisc_1(X2,k2_relat_1(esk2_0))))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_60]), c_0_61])).
% 0.20/0.38  fof(c_0_66, plain, ![X12, X13, X14]:(~r1_tarski(X12,X13)|~r1_xboole_0(X13,X14)|r1_xboole_0(X12,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.20/0.38  cnf(c_0_67, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X3,k2_zfmisc_1(k1_relat_1(X2),k2_relat_1(X2)))))|~v1_relat_1(X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.20/0.38  cnf(c_0_68, negated_conjecture, (r1_xboole_0(k2_zfmisc_1(X1,k2_relat_1(esk1_0)),k2_zfmisc_1(X2,k2_relat_1(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_39])])).
% 0.20/0.38  cnf(c_0_69, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.20/0.38  cnf(c_0_70, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)),k4_xboole_0(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)),k2_zfmisc_1(k1_relat_1(X2),k2_relat_1(X2)))))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_67, c_0_63])).
% 0.20/0.38  cnf(c_0_71, negated_conjecture, (k4_xboole_0(k2_zfmisc_1(X1,k2_relat_1(esk1_0)),k2_zfmisc_1(X2,k2_relat_1(esk2_0)))=k2_zfmisc_1(X1,k2_relat_1(esk1_0))), inference(spm,[status(thm)],[c_0_43, c_0_68])).
% 0.20/0.38  cnf(c_0_72, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.38  cnf(c_0_73, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_69, c_0_39])).
% 0.20/0.38  cnf(c_0_74, negated_conjecture, (r1_tarski(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_60]), c_0_27]), c_0_72])])).
% 0.20/0.38  cnf(c_0_75, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)),X1)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.20/0.38  cnf(c_0_76, negated_conjecture, (~r1_xboole_0(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.38  cnf(c_0_77, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_75]), c_0_76]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 78
% 0.20/0.38  # Proof object clause steps            : 42
% 0.20/0.38  # Proof object formula steps           : 36
% 0.20/0.38  # Proof object conjectures             : 16
% 0.20/0.38  # Proof object clause conjectures      : 13
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 21
% 0.20/0.38  # Proof object initial formulas used   : 18
% 0.20/0.38  # Proof object generating inferences   : 16
% 0.20/0.38  # Proof object simplifying inferences  : 23
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 19
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 27
% 0.20/0.38  # Removed in clause preprocessing      : 1
% 0.20/0.38  # Initial clauses in saturation        : 26
% 0.20/0.38  # Processed clauses                    : 177
% 0.20/0.38  # ...of these trivial                  : 7
% 0.20/0.38  # ...subsumed                          : 30
% 0.20/0.38  # ...remaining for further processing  : 140
% 0.20/0.38  # Other redundant clauses eliminated   : 7
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 4
% 0.20/0.38  # Backward-rewritten                   : 10
% 0.20/0.38  # Generated clauses                    : 633
% 0.20/0.38  # ...of the previous two non-trivial   : 358
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 625
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 8
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 98
% 0.20/0.38  #    Positive orientable unit clauses  : 45
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 1
% 0.20/0.38  #    Non-unit-clauses                  : 52
% 0.20/0.38  # Current number of unprocessed clauses: 209
% 0.20/0.38  # ...number of literals in the above   : 389
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 41
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 278
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 229
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 33
% 0.20/0.38  # Unit Clause-clause subsumption calls : 12
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 39
% 0.20/0.38  # BW rewrite match successes           : 9
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 16448
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.041 s
% 0.20/0.39  # System time              : 0.005 s
% 0.20/0.39  # Total time               : 0.046 s
% 0.20/0.39  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
