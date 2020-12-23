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
% Statistics : Number of formulae       :   82 ( 467 expanded)
%              Number of clauses        :   53 ( 201 expanded)
%              Number of leaves         :   14 ( 128 expanded)
%              Depth                    :   16
%              Number of atoms          :  234 (1121 expanded)
%              Number of equality atoms :  113 ( 646 expanded)
%              Maximal formula depth    :   32 (   4 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d3_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( X6 = k3_enumset1(X1,X2,X3,X4,X5)
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ~ ( X7 != X1
              & X7 != X2
              & X7 != X3
              & X7 != X4
              & X7 != X5 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_enumset1)).

fof(t27_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k2_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k2_relat_1(X1),k2_relat_1(X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_relat_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(t4_setfam_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(k1_setfam_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(c_0_14,plain,(
    ! [X48,X49] : k1_setfam_1(k2_tarski(X48,X49)) = k3_xboole_0(X48,X49) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_15,plain,(
    ! [X13,X14] : k1_enumset1(X13,X13,X14) = k2_tarski(X13,X14) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,plain,(
    ! [X8,X9] : r1_tarski(k3_xboole_0(X8,X9),X8) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_17,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X15,X16,X17] : k2_enumset1(X15,X15,X16,X17) = k1_enumset1(X15,X16,X17) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_20,plain,(
    ! [X18,X19,X20,X21] : k3_enumset1(X18,X18,X19,X20,X21) = k2_enumset1(X18,X19,X20,X21) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_21,plain,(
    ! [X22,X23,X24,X25,X26] : k4_enumset1(X22,X22,X23,X24,X25,X26) = k3_enumset1(X22,X23,X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_22,plain,(
    ! [X27,X28,X29,X30,X31,X32] : k5_enumset1(X27,X27,X28,X29,X30,X31,X32) = k4_enumset1(X27,X28,X29,X30,X31,X32) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_23,plain,(
    ! [X50,X51] :
      ( ( ~ m1_subset_1(X50,k1_zfmisc_1(X51))
        | r1_tarski(X50,X51) )
      & ( ~ r1_tarski(X50,X51)
        | m1_subset_1(X50,k1_zfmisc_1(X51)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_24,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_26,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_30,plain,(
    ! [X33,X34,X35,X36,X37,X38,X39,X40,X41,X42,X43,X44,X45,X46] :
      ( ( ~ r2_hidden(X39,X38)
        | X39 = X33
        | X39 = X34
        | X39 = X35
        | X39 = X36
        | X39 = X37
        | X38 != k3_enumset1(X33,X34,X35,X36,X37) )
      & ( X40 != X33
        | r2_hidden(X40,X38)
        | X38 != k3_enumset1(X33,X34,X35,X36,X37) )
      & ( X40 != X34
        | r2_hidden(X40,X38)
        | X38 != k3_enumset1(X33,X34,X35,X36,X37) )
      & ( X40 != X35
        | r2_hidden(X40,X38)
        | X38 != k3_enumset1(X33,X34,X35,X36,X37) )
      & ( X40 != X36
        | r2_hidden(X40,X38)
        | X38 != k3_enumset1(X33,X34,X35,X36,X37) )
      & ( X40 != X37
        | r2_hidden(X40,X38)
        | X38 != k3_enumset1(X33,X34,X35,X36,X37) )
      & ( esk1_6(X41,X42,X43,X44,X45,X46) != X41
        | ~ r2_hidden(esk1_6(X41,X42,X43,X44,X45,X46),X46)
        | X46 = k3_enumset1(X41,X42,X43,X44,X45) )
      & ( esk1_6(X41,X42,X43,X44,X45,X46) != X42
        | ~ r2_hidden(esk1_6(X41,X42,X43,X44,X45,X46),X46)
        | X46 = k3_enumset1(X41,X42,X43,X44,X45) )
      & ( esk1_6(X41,X42,X43,X44,X45,X46) != X43
        | ~ r2_hidden(esk1_6(X41,X42,X43,X44,X45,X46),X46)
        | X46 = k3_enumset1(X41,X42,X43,X44,X45) )
      & ( esk1_6(X41,X42,X43,X44,X45,X46) != X44
        | ~ r2_hidden(esk1_6(X41,X42,X43,X44,X45,X46),X46)
        | X46 = k3_enumset1(X41,X42,X43,X44,X45) )
      & ( esk1_6(X41,X42,X43,X44,X45,X46) != X45
        | ~ r2_hidden(esk1_6(X41,X42,X43,X44,X45,X46),X46)
        | X46 = k3_enumset1(X41,X42,X43,X44,X45) )
      & ( r2_hidden(esk1_6(X41,X42,X43,X44,X45,X46),X46)
        | esk1_6(X41,X42,X43,X44,X45,X46) = X41
        | esk1_6(X41,X42,X43,X44,X45,X46) = X42
        | esk1_6(X41,X42,X43,X44,X45,X46) = X43
        | esk1_6(X41,X42,X43,X44,X45,X46) = X44
        | esk1_6(X41,X42,X43,X44,X45,X46) = X45
        | X46 = k3_enumset1(X41,X42,X43,X44,X45) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_enumset1])])])])])])).

fof(c_0_31,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => r1_tarski(k2_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k2_relat_1(X1),k2_relat_1(X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t27_relat_1])).

fof(c_0_32,plain,(
    ! [X54,X55] :
      ( ~ v1_relat_1(X54)
      | ~ m1_subset_1(X55,k1_zfmisc_1(X54))
      | v1_relat_1(X55) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

cnf(c_0_33,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( r1_tarski(k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X4,X5,X6,X7,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_36,plain,(
    ! [X56,X57] :
      ( ( r1_tarski(k1_relat_1(X56),k1_relat_1(X57))
        | ~ r1_tarski(X56,X57)
        | ~ v1_relat_1(X57)
        | ~ v1_relat_1(X56) )
      & ( r1_tarski(k2_relat_1(X56),k2_relat_1(X57))
        | ~ r1_tarski(X56,X57)
        | ~ v1_relat_1(X57)
        | ~ v1_relat_1(X56) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

fof(c_0_37,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & ~ r1_tarski(k2_relat_1(k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k2_relat_1(esk2_0),k2_relat_1(esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).

cnf(c_0_38,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( m1_subset_1(k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k5_enumset1(X4,X4,X4,X5,X6,X7,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_28]),c_0_29])).

cnf(c_0_41,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( v1_relat_1(k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_45,plain,(
    ! [X52,X53] :
      ( ~ r2_hidden(X52,X53)
      | r1_tarski(k1_setfam_1(X53),X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | X2 != k5_enumset1(X3,X3,X3,X4,X5,X6,X1) ),
    inference(er,[status(thm)],[c_0_40])).

fof(c_0_47,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_tarski(X10,X11)
      | ~ r1_tarski(X10,X12)
      | r1_tarski(X10,k3_xboole_0(X11,X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(esk2_0))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( v1_relat_1(k1_setfam_1(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,plain,
    ( r1_tarski(k1_setfam_1(X2),X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,k5_enumset1(X2,X2,X2,X3,X4,X5,X1)) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k2_relat_1(k1_setfam_1(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1))),k2_relat_1(esk2_0))
    | ~ r1_tarski(k1_setfam_1(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,plain,
    ( r1_tarski(k1_setfam_1(k5_enumset1(X1,X1,X1,X2,X3,X4,X5)),X5) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k2_relat_1(esk2_0),k2_relat_1(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_56,plain,
    ( r2_hidden(esk1_6(X1,X2,X3,X4,X5,X6),X6)
    | esk1_6(X1,X2,X3,X4,X5,X6) = X1
    | esk1_6(X1,X2,X3,X4,X5,X6) = X2
    | esk1_6(X1,X2,X3,X4,X5,X6) = X3
    | esk1_6(X1,X2,X3,X4,X5,X6) = X4
    | esk1_6(X1,X2,X3,X4,X5,X6) = X5
    | X6 = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,k1_setfam_1(k5_enumset1(X2,X2,X2,X2,X2,X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(k2_relat_1(k1_setfam_1(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0))),k2_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(esk3_0))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_44])).

cnf(c_0_60,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | X1 = X6
    | X1 = X7
    | ~ r2_hidden(X1,X2)
    | X2 != k3_enumset1(X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_61,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k1_setfam_1(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0))),k1_setfam_1(k5_enumset1(k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_27]),c_0_27]),c_0_28]),c_0_28]),c_0_29]),c_0_29])).

cnf(c_0_62,plain,
    ( esk1_6(X1,X2,X3,X4,X5,X6) = X5
    | esk1_6(X1,X2,X3,X4,X5,X6) = X4
    | esk1_6(X1,X2,X3,X4,X5,X6) = X3
    | esk1_6(X1,X2,X3,X4,X5,X6) = X2
    | esk1_6(X1,X2,X3,X4,X5,X6) = X1
    | X6 = k5_enumset1(X1,X1,X1,X2,X3,X4,X5)
    | r2_hidden(esk1_6(X1,X2,X3,X4,X5,X6),X6) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_28]),c_0_29])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(k2_relat_1(k1_setfam_1(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0))),k1_setfam_1(k5_enumset1(k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),X1)))
    | ~ r1_tarski(k2_relat_1(k1_setfam_1(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0))),X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(k2_relat_1(k1_setfam_1(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1))),k2_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_49]),c_0_34])])).

cnf(c_0_65,plain,
    ( X1 = X7
    | X1 = X6
    | X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k5_enumset1(X3,X3,X3,X4,X5,X6,X7)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_28]),c_0_29])).

cnf(c_0_66,negated_conjecture,
    ( esk1_6(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,X1) = esk3_0
    | esk1_6(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,X1) = esk2_0
    | r2_hidden(esk1_6(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,X1),X1)
    | ~ r1_tarski(k2_relat_1(k1_setfam_1(X1)),k1_setfam_1(k5_enumset1(k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(k2_relat_1(k1_setfam_1(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0))),k1_setfam_1(k5_enumset1(k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X4,X5,X6,X2,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_69,plain,
    ( X6 = k3_enumset1(X1,X2,X3,X4,X5)
    | esk1_6(X1,X2,X3,X4,X5,X6) != X4
    | ~ r2_hidden(esk1_6(X1,X2,X3,X4,X5,X6),X6) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_70,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | X1 = X5
    | X1 = X6
    | ~ r2_hidden(X1,k5_enumset1(X6,X6,X6,X5,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( esk1_6(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0)) = esk2_0
    | esk1_6(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0)) = esk3_0
    | r2_hidden(esk1_6(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0)),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_72,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k5_enumset1(X4,X4,X4,X5,X6,X2,X7) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_28]),c_0_29])).

cnf(c_0_73,plain,
    ( X6 = k3_enumset1(X1,X2,X3,X4,X5)
    | esk1_6(X1,X2,X3,X4,X5,X6) != X5
    | ~ r2_hidden(esk1_6(X1,X2,X3,X4,X5,X6),X6) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_74,plain,
    ( X6 = k5_enumset1(X1,X1,X1,X2,X3,X4,X5)
    | esk1_6(X1,X2,X3,X4,X5,X6) != X4
    | ~ r2_hidden(esk1_6(X1,X2,X3,X4,X5,X6),X6) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_28]),c_0_29])).

cnf(c_0_75,negated_conjecture,
    ( esk1_6(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0)) = esk3_0
    | esk1_6(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_76,plain,
    ( r2_hidden(X1,X2)
    | X2 != k5_enumset1(X3,X3,X3,X4,X5,X1,X6) ),
    inference(er,[status(thm)],[c_0_72])).

cnf(c_0_77,plain,
    ( X6 = k5_enumset1(X1,X1,X1,X2,X3,X4,X5)
    | esk1_6(X1,X2,X3,X4,X5,X6) != X5
    | ~ r2_hidden(esk1_6(X1,X2,X3,X4,X5,X6),X6) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_28]),c_0_29])).

cnf(c_0_78,negated_conjecture,
    ( k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0) = k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0)
    | esk1_6(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_51])])).

cnf(c_0_79,plain,
    ( r2_hidden(X1,k5_enumset1(X2,X2,X2,X3,X4,X1,X5)) ),
    inference(er,[status(thm)],[c_0_76])).

cnf(c_0_80,negated_conjecture,
    ( k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0) = k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79])])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_80]),c_0_67])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:55:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  # Version: 2.5pre002
% 0.14/0.36  # No SInE strategy applied
% 0.14/0.36  # Trying AutoSched0 for 299 seconds
% 0.20/0.46  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 0.20/0.46  # and selection function SelectNegativeLiterals.
% 0.20/0.46  #
% 0.20/0.46  # Preprocessing time       : 0.033 s
% 0.20/0.46  
% 0.20/0.46  # Proof found!
% 0.20/0.46  # SZS status Theorem
% 0.20/0.46  # SZS output start CNFRefutation
% 0.20/0.46  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.46  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.46  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.20/0.46  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.46  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.46  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.46  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.20/0.46  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.46  fof(d3_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:(X6=k3_enumset1(X1,X2,X3,X4,X5)<=>![X7]:(r2_hidden(X7,X6)<=>~(((((X7!=X1&X7!=X2)&X7!=X3)&X7!=X4)&X7!=X5)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_enumset1)).
% 0.20/0.46  fof(t27_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k2_relat_1(X1),k2_relat_1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_relat_1)).
% 0.20/0.46  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.20/0.46  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 0.20/0.46  fof(t4_setfam_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(k1_setfam_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 0.20/0.46  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.20/0.46  fof(c_0_14, plain, ![X48, X49]:k1_setfam_1(k2_tarski(X48,X49))=k3_xboole_0(X48,X49), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.20/0.46  fof(c_0_15, plain, ![X13, X14]:k1_enumset1(X13,X13,X14)=k2_tarski(X13,X14), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.46  fof(c_0_16, plain, ![X8, X9]:r1_tarski(k3_xboole_0(X8,X9),X8), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.20/0.46  cnf(c_0_17, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.46  cnf(c_0_18, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.46  fof(c_0_19, plain, ![X15, X16, X17]:k2_enumset1(X15,X15,X16,X17)=k1_enumset1(X15,X16,X17), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.46  fof(c_0_20, plain, ![X18, X19, X20, X21]:k3_enumset1(X18,X18,X19,X20,X21)=k2_enumset1(X18,X19,X20,X21), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.46  fof(c_0_21, plain, ![X22, X23, X24, X25, X26]:k4_enumset1(X22,X22,X23,X24,X25,X26)=k3_enumset1(X22,X23,X24,X25,X26), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.46  fof(c_0_22, plain, ![X27, X28, X29, X30, X31, X32]:k5_enumset1(X27,X27,X28,X29,X30,X31,X32)=k4_enumset1(X27,X28,X29,X30,X31,X32), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.20/0.46  fof(c_0_23, plain, ![X50, X51]:((~m1_subset_1(X50,k1_zfmisc_1(X51))|r1_tarski(X50,X51))&(~r1_tarski(X50,X51)|m1_subset_1(X50,k1_zfmisc_1(X51)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.46  cnf(c_0_24, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.46  cnf(c_0_25, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.46  cnf(c_0_26, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.46  cnf(c_0_27, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.46  cnf(c_0_28, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.46  cnf(c_0_29, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.46  fof(c_0_30, plain, ![X33, X34, X35, X36, X37, X38, X39, X40, X41, X42, X43, X44, X45, X46]:(((~r2_hidden(X39,X38)|(X39=X33|X39=X34|X39=X35|X39=X36|X39=X37)|X38!=k3_enumset1(X33,X34,X35,X36,X37))&(((((X40!=X33|r2_hidden(X40,X38)|X38!=k3_enumset1(X33,X34,X35,X36,X37))&(X40!=X34|r2_hidden(X40,X38)|X38!=k3_enumset1(X33,X34,X35,X36,X37)))&(X40!=X35|r2_hidden(X40,X38)|X38!=k3_enumset1(X33,X34,X35,X36,X37)))&(X40!=X36|r2_hidden(X40,X38)|X38!=k3_enumset1(X33,X34,X35,X36,X37)))&(X40!=X37|r2_hidden(X40,X38)|X38!=k3_enumset1(X33,X34,X35,X36,X37))))&((((((esk1_6(X41,X42,X43,X44,X45,X46)!=X41|~r2_hidden(esk1_6(X41,X42,X43,X44,X45,X46),X46)|X46=k3_enumset1(X41,X42,X43,X44,X45))&(esk1_6(X41,X42,X43,X44,X45,X46)!=X42|~r2_hidden(esk1_6(X41,X42,X43,X44,X45,X46),X46)|X46=k3_enumset1(X41,X42,X43,X44,X45)))&(esk1_6(X41,X42,X43,X44,X45,X46)!=X43|~r2_hidden(esk1_6(X41,X42,X43,X44,X45,X46),X46)|X46=k3_enumset1(X41,X42,X43,X44,X45)))&(esk1_6(X41,X42,X43,X44,X45,X46)!=X44|~r2_hidden(esk1_6(X41,X42,X43,X44,X45,X46),X46)|X46=k3_enumset1(X41,X42,X43,X44,X45)))&(esk1_6(X41,X42,X43,X44,X45,X46)!=X45|~r2_hidden(esk1_6(X41,X42,X43,X44,X45,X46),X46)|X46=k3_enumset1(X41,X42,X43,X44,X45)))&(r2_hidden(esk1_6(X41,X42,X43,X44,X45,X46),X46)|(esk1_6(X41,X42,X43,X44,X45,X46)=X41|esk1_6(X41,X42,X43,X44,X45,X46)=X42|esk1_6(X41,X42,X43,X44,X45,X46)=X43|esk1_6(X41,X42,X43,X44,X45,X46)=X44|esk1_6(X41,X42,X43,X44,X45,X46)=X45)|X46=k3_enumset1(X41,X42,X43,X44,X45)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_enumset1])])])])])])).
% 0.20/0.46  fof(c_0_31, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k2_relat_1(X1),k2_relat_1(X2)))))), inference(assume_negation,[status(cth)],[t27_relat_1])).
% 0.20/0.46  fof(c_0_32, plain, ![X54, X55]:(~v1_relat_1(X54)|(~m1_subset_1(X55,k1_zfmisc_1(X54))|v1_relat_1(X55))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.20/0.46  cnf(c_0_33, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.46  cnf(c_0_34, plain, (r1_tarski(k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29])).
% 0.20/0.46  cnf(c_0_35, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X4,X5,X6,X7,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.46  fof(c_0_36, plain, ![X56, X57]:((r1_tarski(k1_relat_1(X56),k1_relat_1(X57))|~r1_tarski(X56,X57)|~v1_relat_1(X57)|~v1_relat_1(X56))&(r1_tarski(k2_relat_1(X56),k2_relat_1(X57))|~r1_tarski(X56,X57)|~v1_relat_1(X57)|~v1_relat_1(X56))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.20/0.46  fof(c_0_37, negated_conjecture, (v1_relat_1(esk2_0)&(v1_relat_1(esk3_0)&~r1_tarski(k2_relat_1(k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k2_relat_1(esk2_0),k2_relat_1(esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).
% 0.20/0.46  cnf(c_0_38, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.46  cnf(c_0_39, plain, (m1_subset_1(k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.46  cnf(c_0_40, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k5_enumset1(X4,X4,X4,X5,X6,X7,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_28]), c_0_29])).
% 0.20/0.46  cnf(c_0_41, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.46  cnf(c_0_42, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.46  cnf(c_0_43, plain, (v1_relat_1(k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.46  cnf(c_0_44, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.46  fof(c_0_45, plain, ![X52, X53]:(~r2_hidden(X52,X53)|r1_tarski(k1_setfam_1(X53),X52)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).
% 0.20/0.46  cnf(c_0_46, plain, (r2_hidden(X1,X2)|X2!=k5_enumset1(X3,X3,X3,X4,X5,X6,X1)), inference(er,[status(thm)],[c_0_40])).
% 0.20/0.46  fof(c_0_47, plain, ![X10, X11, X12]:(~r1_tarski(X10,X11)|~r1_tarski(X10,X12)|r1_tarski(X10,k3_xboole_0(X11,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.20/0.46  cnf(c_0_48, negated_conjecture, (r1_tarski(k2_relat_1(X1),k2_relat_1(esk2_0))|~v1_relat_1(X1)|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.46  cnf(c_0_49, negated_conjecture, (v1_relat_1(k1_setfam_1(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1)))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.46  cnf(c_0_50, plain, (r1_tarski(k1_setfam_1(X2),X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.46  cnf(c_0_51, plain, (r2_hidden(X1,k5_enumset1(X2,X2,X2,X3,X4,X5,X1))), inference(er,[status(thm)],[c_0_46])).
% 0.20/0.46  cnf(c_0_52, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.46  cnf(c_0_53, negated_conjecture, (r1_tarski(k2_relat_1(k1_setfam_1(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1))),k2_relat_1(esk2_0))|~r1_tarski(k1_setfam_1(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1)),esk2_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.46  cnf(c_0_54, plain, (r1_tarski(k1_setfam_1(k5_enumset1(X1,X1,X1,X2,X3,X4,X5)),X5)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.46  cnf(c_0_55, negated_conjecture, (~r1_tarski(k2_relat_1(k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k2_relat_1(esk2_0),k2_relat_1(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.46  cnf(c_0_56, plain, (r2_hidden(esk1_6(X1,X2,X3,X4,X5,X6),X6)|esk1_6(X1,X2,X3,X4,X5,X6)=X1|esk1_6(X1,X2,X3,X4,X5,X6)=X2|esk1_6(X1,X2,X3,X4,X5,X6)=X3|esk1_6(X1,X2,X3,X4,X5,X6)=X4|esk1_6(X1,X2,X3,X4,X5,X6)=X5|X6=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.46  cnf(c_0_57, plain, (r1_tarski(X1,k1_setfam_1(k5_enumset1(X2,X2,X2,X2,X2,X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29])).
% 0.20/0.46  cnf(c_0_58, negated_conjecture, (r1_tarski(k2_relat_1(k1_setfam_1(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0))),k2_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.20/0.46  cnf(c_0_59, negated_conjecture, (r1_tarski(k2_relat_1(X1),k2_relat_1(esk3_0))|~v1_relat_1(X1)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_41, c_0_44])).
% 0.20/0.46  cnf(c_0_60, plain, (X1=X3|X1=X4|X1=X5|X1=X6|X1=X7|~r2_hidden(X1,X2)|X2!=k3_enumset1(X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.46  cnf(c_0_61, negated_conjecture, (~r1_tarski(k2_relat_1(k1_setfam_1(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0))),k1_setfam_1(k5_enumset1(k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_25]), c_0_25]), c_0_26]), c_0_26]), c_0_27]), c_0_27]), c_0_28]), c_0_28]), c_0_29]), c_0_29])).
% 0.20/0.46  cnf(c_0_62, plain, (esk1_6(X1,X2,X3,X4,X5,X6)=X5|esk1_6(X1,X2,X3,X4,X5,X6)=X4|esk1_6(X1,X2,X3,X4,X5,X6)=X3|esk1_6(X1,X2,X3,X4,X5,X6)=X2|esk1_6(X1,X2,X3,X4,X5,X6)=X1|X6=k5_enumset1(X1,X1,X1,X2,X3,X4,X5)|r2_hidden(esk1_6(X1,X2,X3,X4,X5,X6),X6)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_28]), c_0_29])).
% 0.20/0.46  cnf(c_0_63, negated_conjecture, (r1_tarski(k2_relat_1(k1_setfam_1(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0))),k1_setfam_1(k5_enumset1(k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),X1)))|~r1_tarski(k2_relat_1(k1_setfam_1(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0))),X1)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.20/0.46  cnf(c_0_64, negated_conjecture, (r1_tarski(k2_relat_1(k1_setfam_1(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1))),k2_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_49]), c_0_34])])).
% 0.20/0.46  cnf(c_0_65, plain, (X1=X7|X1=X6|X1=X5|X1=X4|X1=X3|X2!=k5_enumset1(X3,X3,X3,X4,X5,X6,X7)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_28]), c_0_29])).
% 0.20/0.46  cnf(c_0_66, negated_conjecture, (esk1_6(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,X1)=esk3_0|esk1_6(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,X1)=esk2_0|r2_hidden(esk1_6(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,X1),X1)|~r1_tarski(k2_relat_1(k1_setfam_1(X1)),k1_setfam_1(k5_enumset1(k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk3_0))))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.20/0.46  cnf(c_0_67, negated_conjecture, (r1_tarski(k2_relat_1(k1_setfam_1(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0))),k1_setfam_1(k5_enumset1(k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk3_0))))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.20/0.46  cnf(c_0_68, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X4,X5,X6,X2,X7)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.46  cnf(c_0_69, plain, (X6=k3_enumset1(X1,X2,X3,X4,X5)|esk1_6(X1,X2,X3,X4,X5,X6)!=X4|~r2_hidden(esk1_6(X1,X2,X3,X4,X5,X6),X6)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.46  cnf(c_0_70, plain, (X1=X2|X1=X3|X1=X4|X1=X5|X1=X6|~r2_hidden(X1,k5_enumset1(X6,X6,X6,X5,X4,X3,X2))), inference(er,[status(thm)],[c_0_65])).
% 0.20/0.46  cnf(c_0_71, negated_conjecture, (esk1_6(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0))=esk2_0|esk1_6(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0))=esk3_0|r2_hidden(esk1_6(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0)),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.20/0.46  cnf(c_0_72, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k5_enumset1(X4,X4,X4,X5,X6,X2,X7)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_28]), c_0_29])).
% 0.20/0.46  cnf(c_0_73, plain, (X6=k3_enumset1(X1,X2,X3,X4,X5)|esk1_6(X1,X2,X3,X4,X5,X6)!=X5|~r2_hidden(esk1_6(X1,X2,X3,X4,X5,X6),X6)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.46  cnf(c_0_74, plain, (X6=k5_enumset1(X1,X1,X1,X2,X3,X4,X5)|esk1_6(X1,X2,X3,X4,X5,X6)!=X4|~r2_hidden(esk1_6(X1,X2,X3,X4,X5,X6),X6)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_28]), c_0_29])).
% 0.20/0.46  cnf(c_0_75, negated_conjecture, (esk1_6(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0))=esk3_0|esk1_6(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0))=esk2_0), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.20/0.46  cnf(c_0_76, plain, (r2_hidden(X1,X2)|X2!=k5_enumset1(X3,X3,X3,X4,X5,X1,X6)), inference(er,[status(thm)],[c_0_72])).
% 0.20/0.46  cnf(c_0_77, plain, (X6=k5_enumset1(X1,X1,X1,X2,X3,X4,X5)|esk1_6(X1,X2,X3,X4,X5,X6)!=X5|~r2_hidden(esk1_6(X1,X2,X3,X4,X5,X6),X6)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_28]), c_0_29])).
% 0.20/0.46  cnf(c_0_78, negated_conjecture, (k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)=k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0)|esk1_6(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_51])])).
% 0.20/0.46  cnf(c_0_79, plain, (r2_hidden(X1,k5_enumset1(X2,X2,X2,X3,X4,X1,X5))), inference(er,[status(thm)],[c_0_76])).
% 0.20/0.46  cnf(c_0_80, negated_conjecture, (k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)=k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_79])])).
% 0.20/0.46  cnf(c_0_81, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_80]), c_0_67])]), ['proof']).
% 0.20/0.46  # SZS output end CNFRefutation
% 0.20/0.46  # Proof object total steps             : 82
% 0.20/0.46  # Proof object clause steps            : 53
% 0.20/0.46  # Proof object formula steps           : 29
% 0.20/0.46  # Proof object conjectures             : 21
% 0.20/0.46  # Proof object clause conjectures      : 18
% 0.20/0.46  # Proof object formula conjectures     : 3
% 0.20/0.46  # Proof object initial clauses used    : 21
% 0.20/0.46  # Proof object initial formulas used   : 14
% 0.20/0.46  # Proof object generating inferences   : 19
% 0.20/0.46  # Proof object simplifying inferences  : 44
% 0.20/0.46  # Training examples: 0 positive, 0 negative
% 0.20/0.46  # Parsed axioms                        : 14
% 0.20/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.46  # Initial clauses                      : 29
% 0.20/0.46  # Removed in clause preprocessing      : 6
% 0.20/0.46  # Initial clauses in saturation        : 23
% 0.20/0.46  # Processed clauses                    : 151
% 0.20/0.46  # ...of these trivial                  : 7
% 0.20/0.46  # ...subsumed                          : 17
% 0.20/0.46  # ...remaining for further processing  : 127
% 0.20/0.46  # Other redundant clauses eliminated   : 19
% 0.20/0.46  # Clauses deleted for lack of memory   : 0
% 0.20/0.46  # Backward-subsumed                    : 1
% 0.20/0.46  # Backward-rewritten                   : 20
% 0.20/0.46  # Generated clauses                    : 927
% 0.20/0.46  # ...of the previous two non-trivial   : 850
% 0.20/0.46  # Contextual simplify-reflections      : 5
% 0.20/0.46  # Paramodulations                      : 900
% 0.20/0.46  # Factorizations                       : 1
% 0.20/0.46  # Equation resolutions                 : 26
% 0.20/0.46  # Propositional unsat checks           : 0
% 0.20/0.46  #    Propositional check models        : 0
% 0.20/0.46  #    Propositional check unsatisfiable : 0
% 0.20/0.46  #    Propositional clauses             : 0
% 0.20/0.46  #    Propositional clauses after purity: 0
% 0.20/0.46  #    Propositional unsat core size     : 0
% 0.20/0.46  #    Propositional preprocessing time  : 0.000
% 0.20/0.46  #    Propositional encoding time       : 0.000
% 0.20/0.46  #    Propositional solver time         : 0.000
% 0.20/0.46  #    Success case prop preproc time    : 0.000
% 0.20/0.46  #    Success case prop encoding time   : 0.000
% 0.20/0.46  #    Success case prop solver time     : 0.000
% 0.20/0.46  # Current number of processed clauses  : 101
% 0.20/0.46  #    Positive orientable unit clauses  : 18
% 0.20/0.46  #    Positive unorientable unit clauses: 0
% 0.20/0.46  #    Negative unit clauses             : 0
% 0.20/0.46  #    Non-unit-clauses                  : 83
% 0.20/0.46  # Current number of unprocessed clauses: 705
% 0.20/0.46  # ...number of literals in the above   : 8170
% 0.20/0.46  # Current number of archived formulas  : 0
% 0.20/0.46  # Current number of archived clauses   : 27
% 0.20/0.46  # Clause-clause subsumption calls (NU) : 3201
% 0.20/0.46  # Rec. Clause-clause subsumption calls : 453
% 0.20/0.46  # Non-unit clause-clause subsumptions  : 23
% 0.20/0.46  # Unit Clause-clause subsumption calls : 118
% 0.20/0.46  # Rewrite failures with RHS unbound    : 0
% 0.20/0.46  # BW rewrite match attempts            : 31
% 0.20/0.46  # BW rewrite match successes           : 1
% 0.20/0.46  # Condensation attempts                : 0
% 0.20/0.46  # Condensation successes               : 0
% 0.20/0.46  # Termbank termtop insertions          : 54924
% 0.20/0.46  
% 0.20/0.46  # -------------------------------------------------
% 0.20/0.46  # User time                : 0.100 s
% 0.20/0.46  # System time              : 0.008 s
% 0.20/0.46  # Total time               : 0.107 s
% 0.20/0.46  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
