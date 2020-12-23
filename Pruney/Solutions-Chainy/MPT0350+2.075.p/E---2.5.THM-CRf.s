%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:24 EST 2020

% Result     : Theorem 8.58s
% Output     : CNFRefutation 8.58s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 448 expanded)
%              Number of clauses        :   63 ( 202 expanded)
%              Number of leaves         :   24 ( 118 expanded)
%              Depth                    :   13
%              Number of atoms          :  209 ( 822 expanded)
%              Number of equality atoms :  103 ( 427 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t25_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k4_subset_1(X1,X2,k3_subset_1(X1,X2)) = k2_subset_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(t94_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

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

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(t112_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => k4_subset_1(X1,X2,k3_subset_1(X1,X2)) = k2_subset_1(X1) ) ),
    inference(assume_negation,[status(cth)],[t25_subset_1])).

fof(c_0_25,plain,(
    ! [X60,X61,X62,X63,X64,X65] :
      ( ( ~ r2_hidden(X62,X61)
        | r1_tarski(X62,X60)
        | X61 != k1_zfmisc_1(X60) )
      & ( ~ r1_tarski(X63,X60)
        | r2_hidden(X63,X61)
        | X61 != k1_zfmisc_1(X60) )
      & ( ~ r2_hidden(esk2_2(X64,X65),X65)
        | ~ r1_tarski(esk2_2(X64,X65),X64)
        | X65 = k1_zfmisc_1(X64) )
      & ( r2_hidden(esk2_2(X64,X65),X65)
        | r1_tarski(esk2_2(X64,X65),X64)
        | X65 = k1_zfmisc_1(X64) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_26,plain,(
    ! [X69,X70] :
      ( ( ~ m1_subset_1(X70,X69)
        | r2_hidden(X70,X69)
        | v1_xboole_0(X69) )
      & ( ~ r2_hidden(X70,X69)
        | m1_subset_1(X70,X69)
        | v1_xboole_0(X69) )
      & ( ~ m1_subset_1(X70,X69)
        | v1_xboole_0(X70)
        | ~ v1_xboole_0(X69) )
      & ( ~ v1_xboole_0(X70)
        | m1_subset_1(X70,X69)
        | ~ v1_xboole_0(X69) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_27,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))
    & k4_subset_1(esk3_0,esk4_0,k3_subset_1(esk3_0,esk4_0)) != k2_subset_1(esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

fof(c_0_28,plain,(
    ! [X76] : ~ v1_xboole_0(k1_zfmisc_1(X76)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_33,plain,(
    ! [X72,X73] :
      ( ~ m1_subset_1(X73,k1_zfmisc_1(X72))
      | k3_subset_1(X72,X73) = k4_xboole_0(X72,X73) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_34,plain,(
    ! [X19,X20] : k4_xboole_0(X19,X20) = k5_xboole_0(X19,k3_xboole_0(X19,X20)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_35,plain,(
    ! [X24,X25] :
      ( ~ r1_tarski(X24,X25)
      | k3_xboole_0(X24,X25) = X24 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk4_0,k1_zfmisc_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

fof(c_0_38,plain,(
    ! [X8,X9] : k3_xboole_0(X8,X9) = k3_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_39,plain,(
    ! [X67,X68] : k3_tarski(k2_tarski(X67,X68)) = k2_xboole_0(X67,X68) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_40,plain,(
    ! [X33,X34] : k1_enumset1(X33,X33,X34) = k2_tarski(X33,X34) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_41,plain,(
    ! [X27,X28,X29] : k5_xboole_0(k5_xboole_0(X27,X28),X29) = k5_xboole_0(X27,k5_xboole_0(X28,X29)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_42,plain,(
    ! [X30] : k5_xboole_0(X30,X30) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_43,plain,(
    ! [X74,X75] :
      ( ~ m1_subset_1(X75,k1_zfmisc_1(X74))
      | m1_subset_1(k3_subset_1(X74,X75),k1_zfmisc_1(X74)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_44,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_48,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_49,plain,(
    ! [X31,X32] : k2_xboole_0(X31,X32) = k5_xboole_0(k5_xboole_0(X31,X32),k3_xboole_0(X31,X32)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

cnf(c_0_50,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_51,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_52,plain,(
    ! [X35,X36,X37] : k2_enumset1(X35,X35,X36,X37) = k1_enumset1(X35,X36,X37) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_53,plain,(
    ! [X38,X39,X40,X41] : k3_enumset1(X38,X38,X39,X40,X41) = k2_enumset1(X38,X39,X40,X41) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_54,plain,(
    ! [X42,X43,X44,X45,X46] : k4_enumset1(X42,X42,X43,X44,X45,X46) = k3_enumset1(X42,X43,X44,X45,X46) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_55,plain,(
    ! [X47,X48,X49,X50,X51,X52] : k5_enumset1(X47,X47,X48,X49,X50,X51,X52) = k4_enumset1(X47,X48,X49,X50,X51,X52) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_56,plain,(
    ! [X53,X54,X55,X56,X57,X58,X59] : k6_enumset1(X53,X53,X54,X55,X56,X57,X58,X59) = k5_enumset1(X53,X54,X55,X56,X57,X58,X59) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_57,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_58,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_59,plain,(
    ! [X26] : k5_xboole_0(X26,k1_xboole_0) = X26 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_60,plain,(
    ! [X77,X78,X79] :
      ( ~ m1_subset_1(X78,k1_zfmisc_1(X77))
      | ~ m1_subset_1(X79,k1_zfmisc_1(X77))
      | k4_subset_1(X77,X78,X79) = k2_xboole_0(X78,X79) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_61,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_62,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_63,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk4_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])).

cnf(c_0_64,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_65,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_66,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_67,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_68,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_69,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_70,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_71,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_72,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

fof(c_0_73,plain,(
    ! [X10,X11,X12,X13,X14,X15,X16,X17] :
      ( ( r2_hidden(X13,X10)
        | ~ r2_hidden(X13,X12)
        | X12 != k4_xboole_0(X10,X11) )
      & ( ~ r2_hidden(X13,X11)
        | ~ r2_hidden(X13,X12)
        | X12 != k4_xboole_0(X10,X11) )
      & ( ~ r2_hidden(X14,X10)
        | r2_hidden(X14,X11)
        | r2_hidden(X14,X12)
        | X12 != k4_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X15,X16,X17),X17)
        | ~ r2_hidden(esk1_3(X15,X16,X17),X15)
        | r2_hidden(esk1_3(X15,X16,X17),X16)
        | X17 = k4_xboole_0(X15,X16) )
      & ( r2_hidden(esk1_3(X15,X16,X17),X15)
        | r2_hidden(esk1_3(X15,X16,X17),X17)
        | X17 = k4_xboole_0(X15,X16) )
      & ( ~ r2_hidden(esk1_3(X15,X16,X17),X16)
        | r2_hidden(esk1_3(X15,X16,X17),X17)
        | X17 = k4_xboole_0(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_74,plain,(
    ! [X71] : k2_subset_1(X71) = X71 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_75,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk3_0,esk4_0),k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_31])).

cnf(c_0_77,negated_conjecture,
    ( k3_subset_1(esk3_0,esk4_0) = k5_xboole_0(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_31]),c_0_63])).

cnf(c_0_78,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_65]),c_0_66]),c_0_67]),c_0_68]),c_0_69]),c_0_70])).

fof(c_0_79,plain,(
    ! [X21,X22,X23] : k5_xboole_0(k3_xboole_0(X21,X22),k3_xboole_0(X23,X22)) = k3_xboole_0(k5_xboole_0(X21,X23),X22) ),
    inference(variable_rename,[status(thm)],[t112_xboole_1])).

cnf(c_0_80,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_58]),c_0_72])).

cnf(c_0_81,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_82,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_83,negated_conjecture,
    ( k4_subset_1(esk3_0,esk4_0,k3_subset_1(esk3_0,esk4_0)) != k2_subset_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_84,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_85,plain,
    ( k4_subset_1(X2,X1,X3) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_65]),c_0_66]),c_0_67]),c_0_68]),c_0_69]),c_0_70])).

cnf(c_0_86,negated_conjecture,
    ( m1_subset_1(k5_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_87,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_78,c_0_57])).

cnf(c_0_88,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_89,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[c_0_71,c_0_80])).

cnf(c_0_90,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_57])).

cnf(c_0_91,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_81,c_0_45])).

cnf(c_0_92,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_82,c_0_45])).

cnf(c_0_93,negated_conjecture,
    ( k4_subset_1(esk3_0,esk4_0,k3_subset_1(esk3_0,esk4_0)) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_94,negated_conjecture,
    ( k5_xboole_0(X1,k5_xboole_0(esk3_0,k5_xboole_0(esk4_0,k3_xboole_0(X1,k5_xboole_0(esk3_0,esk4_0))))) = k4_subset_1(esk3_0,X1,k5_xboole_0(esk3_0,esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_87]),c_0_57])).

cnf(c_0_95,negated_conjecture,
    ( k3_xboole_0(esk4_0,k5_xboole_0(esk3_0,X1)) = k5_xboole_0(esk4_0,k3_xboole_0(X1,esk4_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_63]),c_0_48])).

cnf(c_0_96,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_72])).

cnf(c_0_97,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_91])).

cnf(c_0_98,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_92])).

cnf(c_0_99,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_100,negated_conjecture,
    ( k4_subset_1(esk3_0,esk4_0,k5_xboole_0(esk3_0,esk4_0)) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_93,c_0_77])).

cnf(c_0_101,negated_conjecture,
    ( k4_subset_1(esk3_0,esk4_0,k5_xboole_0(esk3_0,esk4_0)) = k5_xboole_0(esk4_0,k5_xboole_0(esk3_0,k3_xboole_0(esk4_0,esk4_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_31]),c_0_95]),c_0_89])).

cnf(c_0_102,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_89,c_0_96])).

cnf(c_0_103,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
    | ~ r2_hidden(esk1_3(X1,X2,X1),k5_xboole_0(X3,k3_xboole_0(X3,X1))) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_104,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_99,c_0_45])).

cnf(c_0_105,negated_conjecture,
    ( k5_xboole_0(esk4_0,k5_xboole_0(esk3_0,k3_xboole_0(esk4_0,esk4_0))) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_106,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X2,k5_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_102])).

cnf(c_0_107,negated_conjecture,
    ( k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,X1)) = esk4_0
    | ~ r2_hidden(esk1_3(esk4_0,X1,esk4_0),k5_xboole_0(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_103,c_0_63])).

cnf(c_0_108,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_98]),c_0_98])).

cnf(c_0_109,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk4_0))) != esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_105,c_0_106]),c_0_102])).

cnf(c_0_110,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk4_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_95]),c_0_89])).

cnf(c_0_111,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109,c_0_110]),c_0_58]),c_0_72])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:29:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 8.58/8.77  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 8.58/8.77  # and selection function GSelectMinInfpos.
% 8.58/8.77  #
% 8.58/8.77  # Preprocessing time       : 0.028 s
% 8.58/8.77  # Presaturation interreduction done
% 8.58/8.77  
% 8.58/8.77  # Proof found!
% 8.58/8.77  # SZS status Theorem
% 8.58/8.77  # SZS output start CNFRefutation
% 8.58/8.77  fof(t25_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k3_subset_1(X1,X2))=k2_subset_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 8.58/8.77  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 8.58/8.77  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 8.58/8.77  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 8.58/8.77  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 8.58/8.77  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.58/8.77  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.58/8.77  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.58/8.77  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 8.58/8.77  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 8.58/8.77  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 8.58/8.77  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 8.58/8.77  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 8.58/8.77  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 8.58/8.77  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 8.58/8.77  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 8.58/8.77  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 8.58/8.77  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 8.58/8.77  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 8.58/8.77  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 8.58/8.77  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 8.58/8.77  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 8.58/8.77  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 8.58/8.77  fof(t112_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_xboole_1)).
% 8.58/8.77  fof(c_0_24, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k3_subset_1(X1,X2))=k2_subset_1(X1))), inference(assume_negation,[status(cth)],[t25_subset_1])).
% 8.58/8.77  fof(c_0_25, plain, ![X60, X61, X62, X63, X64, X65]:(((~r2_hidden(X62,X61)|r1_tarski(X62,X60)|X61!=k1_zfmisc_1(X60))&(~r1_tarski(X63,X60)|r2_hidden(X63,X61)|X61!=k1_zfmisc_1(X60)))&((~r2_hidden(esk2_2(X64,X65),X65)|~r1_tarski(esk2_2(X64,X65),X64)|X65=k1_zfmisc_1(X64))&(r2_hidden(esk2_2(X64,X65),X65)|r1_tarski(esk2_2(X64,X65),X64)|X65=k1_zfmisc_1(X64)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 8.58/8.77  fof(c_0_26, plain, ![X69, X70]:(((~m1_subset_1(X70,X69)|r2_hidden(X70,X69)|v1_xboole_0(X69))&(~r2_hidden(X70,X69)|m1_subset_1(X70,X69)|v1_xboole_0(X69)))&((~m1_subset_1(X70,X69)|v1_xboole_0(X70)|~v1_xboole_0(X69))&(~v1_xboole_0(X70)|m1_subset_1(X70,X69)|~v1_xboole_0(X69)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 8.58/8.77  fof(c_0_27, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))&k4_subset_1(esk3_0,esk4_0,k3_subset_1(esk3_0,esk4_0))!=k2_subset_1(esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).
% 8.58/8.77  fof(c_0_28, plain, ![X76]:~v1_xboole_0(k1_zfmisc_1(X76)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 8.58/8.77  cnf(c_0_29, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 8.58/8.77  cnf(c_0_30, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 8.58/8.77  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 8.58/8.77  cnf(c_0_32, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 8.58/8.77  fof(c_0_33, plain, ![X72, X73]:(~m1_subset_1(X73,k1_zfmisc_1(X72))|k3_subset_1(X72,X73)=k4_xboole_0(X72,X73)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 8.58/8.77  fof(c_0_34, plain, ![X19, X20]:k4_xboole_0(X19,X20)=k5_xboole_0(X19,k3_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 8.58/8.77  fof(c_0_35, plain, ![X24, X25]:(~r1_tarski(X24,X25)|k3_xboole_0(X24,X25)=X24), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 8.58/8.77  cnf(c_0_36, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_29])).
% 8.58/8.77  cnf(c_0_37, negated_conjecture, (r2_hidden(esk4_0,k1_zfmisc_1(esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 8.58/8.77  fof(c_0_38, plain, ![X8, X9]:k3_xboole_0(X8,X9)=k3_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 8.58/8.77  fof(c_0_39, plain, ![X67, X68]:k3_tarski(k2_tarski(X67,X68))=k2_xboole_0(X67,X68), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 8.58/8.77  fof(c_0_40, plain, ![X33, X34]:k1_enumset1(X33,X33,X34)=k2_tarski(X33,X34), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 8.58/8.77  fof(c_0_41, plain, ![X27, X28, X29]:k5_xboole_0(k5_xboole_0(X27,X28),X29)=k5_xboole_0(X27,k5_xboole_0(X28,X29)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 8.58/8.77  fof(c_0_42, plain, ![X30]:k5_xboole_0(X30,X30)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 8.58/8.77  fof(c_0_43, plain, ![X74, X75]:(~m1_subset_1(X75,k1_zfmisc_1(X74))|m1_subset_1(k3_subset_1(X74,X75),k1_zfmisc_1(X74))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 8.58/8.77  cnf(c_0_44, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 8.58/8.77  cnf(c_0_45, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 8.58/8.77  cnf(c_0_46, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 8.58/8.77  cnf(c_0_47, negated_conjecture, (r1_tarski(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 8.58/8.77  cnf(c_0_48, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 8.58/8.77  fof(c_0_49, plain, ![X31, X32]:k2_xboole_0(X31,X32)=k5_xboole_0(k5_xboole_0(X31,X32),k3_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 8.58/8.77  cnf(c_0_50, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 8.58/8.77  cnf(c_0_51, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 8.58/8.77  fof(c_0_52, plain, ![X35, X36, X37]:k2_enumset1(X35,X35,X36,X37)=k1_enumset1(X35,X36,X37), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 8.58/8.77  fof(c_0_53, plain, ![X38, X39, X40, X41]:k3_enumset1(X38,X38,X39,X40,X41)=k2_enumset1(X38,X39,X40,X41), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 8.58/8.77  fof(c_0_54, plain, ![X42, X43, X44, X45, X46]:k4_enumset1(X42,X42,X43,X44,X45,X46)=k3_enumset1(X42,X43,X44,X45,X46), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 8.58/8.77  fof(c_0_55, plain, ![X47, X48, X49, X50, X51, X52]:k5_enumset1(X47,X47,X48,X49,X50,X51,X52)=k4_enumset1(X47,X48,X49,X50,X51,X52), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 8.58/8.77  fof(c_0_56, plain, ![X53, X54, X55, X56, X57, X58, X59]:k6_enumset1(X53,X53,X54,X55,X56,X57,X58,X59)=k5_enumset1(X53,X54,X55,X56,X57,X58,X59), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 8.58/8.77  cnf(c_0_57, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 8.58/8.77  cnf(c_0_58, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_42])).
% 8.58/8.77  fof(c_0_59, plain, ![X26]:k5_xboole_0(X26,k1_xboole_0)=X26, inference(variable_rename,[status(thm)],[t5_boole])).
% 8.58/8.77  fof(c_0_60, plain, ![X77, X78, X79]:(~m1_subset_1(X78,k1_zfmisc_1(X77))|~m1_subset_1(X79,k1_zfmisc_1(X77))|k4_subset_1(X77,X78,X79)=k2_xboole_0(X78,X79)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 8.58/8.77  cnf(c_0_61, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 8.58/8.77  cnf(c_0_62, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 8.58/8.77  cnf(c_0_63, negated_conjecture, (k3_xboole_0(esk3_0,esk4_0)=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])).
% 8.58/8.77  cnf(c_0_64, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 8.58/8.77  cnf(c_0_65, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_50, c_0_51])).
% 8.58/8.77  cnf(c_0_66, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 8.58/8.77  cnf(c_0_67, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 8.58/8.77  cnf(c_0_68, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 8.58/8.77  cnf(c_0_69, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 8.58/8.77  cnf(c_0_70, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 8.58/8.77  cnf(c_0_71, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=k5_xboole_0(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 8.58/8.77  cnf(c_0_72, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_59])).
% 8.58/8.77  fof(c_0_73, plain, ![X10, X11, X12, X13, X14, X15, X16, X17]:((((r2_hidden(X13,X10)|~r2_hidden(X13,X12)|X12!=k4_xboole_0(X10,X11))&(~r2_hidden(X13,X11)|~r2_hidden(X13,X12)|X12!=k4_xboole_0(X10,X11)))&(~r2_hidden(X14,X10)|r2_hidden(X14,X11)|r2_hidden(X14,X12)|X12!=k4_xboole_0(X10,X11)))&((~r2_hidden(esk1_3(X15,X16,X17),X17)|(~r2_hidden(esk1_3(X15,X16,X17),X15)|r2_hidden(esk1_3(X15,X16,X17),X16))|X17=k4_xboole_0(X15,X16))&((r2_hidden(esk1_3(X15,X16,X17),X15)|r2_hidden(esk1_3(X15,X16,X17),X17)|X17=k4_xboole_0(X15,X16))&(~r2_hidden(esk1_3(X15,X16,X17),X16)|r2_hidden(esk1_3(X15,X16,X17),X17)|X17=k4_xboole_0(X15,X16))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 8.58/8.77  fof(c_0_74, plain, ![X71]:k2_subset_1(X71)=X71, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 8.58/8.77  cnf(c_0_75, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 8.58/8.77  cnf(c_0_76, negated_conjecture, (m1_subset_1(k3_subset_1(esk3_0,esk4_0),k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_61, c_0_31])).
% 8.58/8.77  cnf(c_0_77, negated_conjecture, (k3_subset_1(esk3_0,esk4_0)=k5_xboole_0(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_31]), c_0_63])).
% 8.58/8.77  cnf(c_0_78, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_65]), c_0_66]), c_0_67]), c_0_68]), c_0_69]), c_0_70])).
% 8.58/8.77  fof(c_0_79, plain, ![X21, X22, X23]:k5_xboole_0(k3_xboole_0(X21,X22),k3_xboole_0(X23,X22))=k3_xboole_0(k5_xboole_0(X21,X23),X22), inference(variable_rename,[status(thm)],[t112_xboole_1])).
% 8.58/8.77  cnf(c_0_80, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_58]), c_0_72])).
% 8.58/8.77  cnf(c_0_81, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 8.58/8.77  cnf(c_0_82, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 8.58/8.77  cnf(c_0_83, negated_conjecture, (k4_subset_1(esk3_0,esk4_0,k3_subset_1(esk3_0,esk4_0))!=k2_subset_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 8.58/8.77  cnf(c_0_84, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_74])).
% 8.58/8.77  cnf(c_0_85, plain, (k4_subset_1(X2,X1,X3)=k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_65]), c_0_66]), c_0_67]), c_0_68]), c_0_69]), c_0_70])).
% 8.58/8.77  cnf(c_0_86, negated_conjecture, (m1_subset_1(k5_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk3_0))), inference(rw,[status(thm)],[c_0_76, c_0_77])).
% 8.58/8.77  cnf(c_0_87, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_78, c_0_57])).
% 8.58/8.77  cnf(c_0_88, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 8.58/8.77  cnf(c_0_89, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[c_0_71, c_0_80])).
% 8.58/8.77  cnf(c_0_90, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_58, c_0_57])).
% 8.58/8.77  cnf(c_0_91, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_81, c_0_45])).
% 8.58/8.77  cnf(c_0_92, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_82, c_0_45])).
% 8.58/8.77  cnf(c_0_93, negated_conjecture, (k4_subset_1(esk3_0,esk4_0,k3_subset_1(esk3_0,esk4_0))!=esk3_0), inference(rw,[status(thm)],[c_0_83, c_0_84])).
% 8.58/8.77  cnf(c_0_94, negated_conjecture, (k5_xboole_0(X1,k5_xboole_0(esk3_0,k5_xboole_0(esk4_0,k3_xboole_0(X1,k5_xboole_0(esk3_0,esk4_0)))))=k4_subset_1(esk3_0,X1,k5_xboole_0(esk3_0,esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_87]), c_0_57])).
% 8.58/8.77  cnf(c_0_95, negated_conjecture, (k3_xboole_0(esk4_0,k5_xboole_0(esk3_0,X1))=k5_xboole_0(esk4_0,k3_xboole_0(X1,esk4_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_63]), c_0_48])).
% 8.58/8.77  cnf(c_0_96, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X1))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_72])).
% 8.58/8.77  cnf(c_0_97, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_91])).
% 8.58/8.77  cnf(c_0_98, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=X1|r2_hidden(esk1_3(X1,X2,X1),X1)), inference(ef,[status(thm)],[c_0_92])).
% 8.58/8.77  cnf(c_0_99, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 8.58/8.77  cnf(c_0_100, negated_conjecture, (k4_subset_1(esk3_0,esk4_0,k5_xboole_0(esk3_0,esk4_0))!=esk3_0), inference(rw,[status(thm)],[c_0_93, c_0_77])).
% 8.58/8.77  cnf(c_0_101, negated_conjecture, (k4_subset_1(esk3_0,esk4_0,k5_xboole_0(esk3_0,esk4_0))=k5_xboole_0(esk4_0,k5_xboole_0(esk3_0,k3_xboole_0(esk4_0,esk4_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_31]), c_0_95]), c_0_89])).
% 8.58/8.77  cnf(c_0_102, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_89, c_0_96])).
% 8.58/8.77  cnf(c_0_103, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=X1|~r2_hidden(esk1_3(X1,X2,X1),k5_xboole_0(X3,k3_xboole_0(X3,X1)))), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 8.58/8.77  cnf(c_0_104, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_99, c_0_45])).
% 8.58/8.77  cnf(c_0_105, negated_conjecture, (k5_xboole_0(esk4_0,k5_xboole_0(esk3_0,k3_xboole_0(esk4_0,esk4_0)))!=esk3_0), inference(rw,[status(thm)],[c_0_100, c_0_101])).
% 8.58/8.77  cnf(c_0_106, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(X2,k5_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_57, c_0_102])).
% 8.58/8.77  cnf(c_0_107, negated_conjecture, (k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,X1))=esk4_0|~r2_hidden(esk1_3(esk4_0,X1,esk4_0),k5_xboole_0(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_103, c_0_63])).
% 8.58/8.77  cnf(c_0_108, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=X1|r2_hidden(esk1_3(X1,X2,X1),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_98]), c_0_98])).
% 8.58/8.77  cnf(c_0_109, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk4_0)))!=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_105, c_0_106]), c_0_102])).
% 8.58/8.77  cnf(c_0_110, negated_conjecture, (k3_xboole_0(esk4_0,esk4_0)=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_95]), c_0_89])).
% 8.58/8.77  cnf(c_0_111, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109, c_0_110]), c_0_58]), c_0_72])]), ['proof']).
% 8.58/8.77  # SZS output end CNFRefutation
% 8.58/8.77  # Proof object total steps             : 112
% 8.58/8.77  # Proof object clause steps            : 63
% 8.58/8.77  # Proof object formula steps           : 49
% 8.58/8.77  # Proof object conjectures             : 21
% 8.58/8.77  # Proof object clause conjectures      : 18
% 8.58/8.77  # Proof object formula conjectures     : 3
% 8.58/8.77  # Proof object initial clauses used    : 27
% 8.58/8.77  # Proof object initial formulas used   : 24
% 8.58/8.77  # Proof object generating inferences   : 19
% 8.58/8.77  # Proof object simplifying inferences  : 44
% 8.58/8.77  # Training examples: 0 positive, 0 negative
% 8.58/8.77  # Parsed axioms                        : 24
% 8.58/8.77  # Removed by relevancy pruning/SinE    : 0
% 8.58/8.77  # Initial clauses                      : 36
% 8.58/8.77  # Removed in clause preprocessing      : 9
% 8.58/8.77  # Initial clauses in saturation        : 27
% 8.58/8.77  # Processed clauses                    : 9805
% 8.58/8.77  # ...of these trivial                  : 296
% 8.58/8.77  # ...subsumed                          : 7964
% 8.58/8.77  # ...remaining for further processing  : 1545
% 8.58/8.77  # Other redundant clauses eliminated   : 5
% 8.58/8.77  # Clauses deleted for lack of memory   : 0
% 8.58/8.77  # Backward-subsumed                    : 38
% 8.58/8.77  # Backward-rewritten                   : 142
% 8.58/8.77  # Generated clauses                    : 276059
% 8.58/8.77  # ...of the previous two non-trivial   : 270414
% 8.58/8.77  # Contextual simplify-reflections      : 2
% 8.58/8.77  # Paramodulations                      : 275992
% 8.58/8.77  # Factorizations                       : 62
% 8.58/8.77  # Equation resolutions                 : 5
% 8.58/8.77  # Propositional unsat checks           : 0
% 8.58/8.77  #    Propositional check models        : 0
% 8.58/8.77  #    Propositional check unsatisfiable : 0
% 8.58/8.77  #    Propositional clauses             : 0
% 8.58/8.77  #    Propositional clauses after purity: 0
% 8.58/8.77  #    Propositional unsat core size     : 0
% 8.58/8.77  #    Propositional preprocessing time  : 0.000
% 8.58/8.77  #    Propositional encoding time       : 0.000
% 8.58/8.77  #    Propositional solver time         : 0.000
% 8.58/8.77  #    Success case prop preproc time    : 0.000
% 8.58/8.77  #    Success case prop encoding time   : 0.000
% 8.58/8.77  #    Success case prop solver time     : 0.000
% 8.58/8.77  # Current number of processed clauses  : 1333
% 8.58/8.77  #    Positive orientable unit clauses  : 144
% 8.58/8.77  #    Positive unorientable unit clauses: 114
% 8.58/8.77  #    Negative unit clauses             : 224
% 8.58/8.77  #    Non-unit-clauses                  : 851
% 8.58/8.77  # Current number of unprocessed clauses: 260096
% 8.58/8.77  # ...number of literals in the above   : 593970
% 8.58/8.77  # Current number of archived formulas  : 0
% 8.58/8.77  # Current number of archived clauses   : 216
% 8.58/8.77  # Clause-clause subsumption calls (NU) : 60858
% 8.58/8.77  # Rec. Clause-clause subsumption calls : 34744
% 8.58/8.77  # Non-unit clause-clause subsumptions  : 2994
% 8.58/8.77  # Unit Clause-clause subsumption calls : 14660
% 8.58/8.77  # Rewrite failures with RHS unbound    : 57803
% 8.58/8.77  # BW rewrite match attempts            : 11754
% 8.58/8.77  # BW rewrite match successes           : 2123
% 8.58/8.77  # Condensation attempts                : 0
% 8.58/8.77  # Condensation successes               : 0
% 8.58/8.77  # Termbank termtop insertions          : 9416314
% 8.58/8.79  
% 8.58/8.79  # -------------------------------------------------
% 8.58/8.79  # User time                : 8.248 s
% 8.58/8.79  # System time              : 0.194 s
% 8.58/8.79  # Total time               : 8.442 s
% 8.58/8.79  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
