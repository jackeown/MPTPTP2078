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
% DateTime   : Thu Dec  3 11:05:41 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 996 expanded)
%              Number of clauses        :   67 ( 379 expanded)
%              Number of leaves         :   17 ( 295 expanded)
%              Depth                    :   12
%              Number of atoms          :  274 (1982 expanded)
%              Number of equality atoms :   88 ( 876 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t66_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,k1_tarski(X2))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,k1_tarski(X2))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
         => r2_relset_1(X1,k1_tarski(X2),X3,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_funct_2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

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

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(t18_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( ! [X5] :
                ( r2_hidden(X5,X1)
               => k1_funct_1(X3,X5) = k1_funct_1(X4,X5) )
           => r2_relset_1(X1,X2,X3,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).

fof(t7_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_hidden(X3,X1)
       => ( X2 = k1_xboole_0
          | r2_hidden(k1_funct_1(X4,X3),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

fof(c_0_17,plain,(
    ! [X8,X9,X10,X11,X12,X13,X14,X15] :
      ( ( r2_hidden(X11,X8)
        | ~ r2_hidden(X11,X10)
        | X10 != k4_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X11,X9)
        | ~ r2_hidden(X11,X10)
        | X10 != k4_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X12,X8)
        | r2_hidden(X12,X9)
        | r2_hidden(X12,X10)
        | X10 != k4_xboole_0(X8,X9) )
      & ( ~ r2_hidden(esk1_3(X13,X14,X15),X15)
        | ~ r2_hidden(esk1_3(X13,X14,X15),X13)
        | r2_hidden(esk1_3(X13,X14,X15),X14)
        | X15 = k4_xboole_0(X13,X14) )
      & ( r2_hidden(esk1_3(X13,X14,X15),X13)
        | r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k4_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk1_3(X13,X14,X15),X14)
        | r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k4_xboole_0(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_18,plain,(
    ! [X19,X20] : k4_xboole_0(X19,X20) = k5_xboole_0(X19,k3_xboole_0(X19,X20)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,k1_tarski(X2))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,k1_tarski(X2))
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
           => r2_relset_1(X1,k1_tarski(X2),X3,X4) ) ) ),
    inference(assume_negation,[status(cth)],[t66_funct_2])).

fof(c_0_20,plain,(
    ! [X17,X18] :
      ( ( r1_tarski(X17,X18)
        | X17 != X18 )
      & ( r1_tarski(X18,X17)
        | X17 != X18 )
      & ( ~ r1_tarski(X17,X18)
        | ~ r1_tarski(X18,X17)
        | X17 = X18 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_21,plain,(
    ! [X21] : r1_tarski(k1_xboole_0,X21) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_22,plain,(
    ! [X58,X59,X60] :
      ( ( r2_hidden(X58,X60)
        | ~ r1_tarski(k2_tarski(X58,X59),X60) )
      & ( r2_hidden(X59,X60)
        | ~ r1_tarski(k2_tarski(X58,X59),X60) )
      & ( ~ r2_hidden(X58,X60)
        | ~ r2_hidden(X59,X60)
        | r1_tarski(k2_tarski(X58,X59),X60) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

fof(c_0_23,plain,(
    ! [X31,X32] : k1_enumset1(X31,X31,X32) = k2_tarski(X31,X32) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_24,plain,(
    ! [X33,X34,X35] : k2_enumset1(X33,X33,X34,X35) = k1_enumset1(X33,X34,X35) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_25,plain,(
    ! [X36,X37,X38,X39] : k3_enumset1(X36,X36,X37,X38,X39) = k2_enumset1(X36,X37,X38,X39) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_26,plain,(
    ! [X40,X41,X42,X43,X44] : k4_enumset1(X40,X40,X41,X42,X43,X44) = k3_enumset1(X40,X41,X42,X43,X44) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_27,plain,(
    ! [X45,X46,X47,X48,X49,X50] : k5_enumset1(X45,X45,X46,X47,X48,X49,X50) = k4_enumset1(X45,X46,X47,X48,X49,X50) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_28,plain,(
    ! [X51,X52,X53,X54,X55,X56,X57] : k6_enumset1(X51,X51,X52,X53,X54,X55,X56,X57) = k5_enumset1(X51,X52,X53,X54,X55,X56,X57) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_31,plain,(
    ! [X22] : k4_xboole_0(X22,k1_xboole_0) = X22 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_32,negated_conjecture,
    ( v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk4_0,k1_tarski(esk5_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_tarski(esk5_0))))
    & v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,esk4_0,k1_tarski(esk5_0))
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_tarski(esk5_0))))
    & ~ r2_relset_1(esk4_0,k1_tarski(esk5_0),esk6_0,esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_33,plain,(
    ! [X30] : k2_tarski(X30,X30) = k1_tarski(X30) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_34,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_35,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_36,plain,
    ( r1_tarski(k2_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_37,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_38,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_39,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_40,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_41,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_42,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_43,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X3,X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_47,plain,(
    ! [X23,X24,X25,X26,X27,X28] :
      ( ( ~ r2_hidden(X25,X24)
        | X25 = X23
        | X24 != k1_tarski(X23) )
      & ( X26 != X23
        | r2_hidden(X26,X24)
        | X24 != k1_tarski(X23) )
      & ( ~ r2_hidden(esk2_2(X27,X28),X28)
        | esk2_2(X27,X28) != X27
        | X28 = k1_tarski(X27) )
      & ( r2_hidden(esk2_2(X27,X28),X28)
        | esk2_2(X27,X28) = X27
        | X28 = k1_tarski(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_48,plain,(
    ! [X67,X68,X69,X70] :
      ( ( r2_hidden(esk3_4(X67,X68,X69,X70),X67)
        | r2_relset_1(X67,X68,X69,X70)
        | ~ v1_funct_1(X70)
        | ~ v1_funct_2(X70,X67,X68)
        | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X67,X68)))
        | ~ v1_funct_1(X69)
        | ~ v1_funct_2(X69,X67,X68)
        | ~ m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(X67,X68))) )
      & ( k1_funct_1(X69,esk3_4(X67,X68,X69,X70)) != k1_funct_1(X70,esk3_4(X67,X68,X69,X70))
        | r2_relset_1(X67,X68,X69,X70)
        | ~ v1_funct_1(X70)
        | ~ v1_funct_2(X70,X67,X68)
        | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X67,X68)))
        | ~ v1_funct_1(X69)
        | ~ v1_funct_2(X69,X67,X68)
        | ~ m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(X67,X68))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_funct_2])])])])])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_tarski(esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_50,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_51,negated_conjecture,
    ( v1_funct_2(esk7_0,esk4_0,k1_tarski(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_52,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_53,plain,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_54,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_55,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_44,c_0_30])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_58,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | esk2_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_59,plain,(
    ! [X72,X73,X74,X75] :
      ( ~ v1_funct_1(X75)
      | ~ v1_funct_2(X75,X72,X73)
      | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X72,X73)))
      | ~ r2_hidden(X74,X72)
      | X73 = k1_xboole_0
      | r2_hidden(k1_funct_1(X75,X74),X73) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).

cnf(c_0_60,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X1)
    | r2_relset_1(X1,X2,X3,X4)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50]),c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_62,negated_conjecture,
    ( v1_funct_2(esk7_0,esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_50]),c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_63,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_tarski(esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_65,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,k1_tarski(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_66,negated_conjecture,
    ( ~ r2_relset_1(esk4_0,k1_tarski(esk5_0),esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_67,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = k1_xboole_0
    | ~ r2_hidden(X2,k1_xboole_0)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_68,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_70,plain,
    ( esk2_2(X1,X2) = X1
    | X2 = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | r2_hidden(esk2_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_50]),c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_71,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_72,plain,
    ( X3 = k1_xboole_0
    | r2_hidden(k1_funct_1(X1,X4),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_73,negated_conjecture,
    ( r2_relset_1(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),X1,esk7_0)
    | r2_hidden(esk3_4(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),X1,esk7_0),esk4_0)
    | ~ v1_funct_2(X1,esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62]),c_0_63])])).

cnf(c_0_74,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_50]),c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_75,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_50]),c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_76,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_77,negated_conjecture,
    ( ~ r2_relset_1(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_50]),c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_78,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_67]),c_0_35])]),c_0_68])).

cnf(c_0_79,plain,
    ( esk2_2(X1,X2) = X1
    | r2_hidden(esk2_2(X1,X2),X2)
    | r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_80,plain,
    ( X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_50]),c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_81,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k1_xboole_0
    | r2_hidden(k1_funct_1(esk7_0,X1),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_61]),c_0_62]),c_0_63])])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk3_4(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0,esk7_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75]),c_0_76])]),c_0_77])).

cnf(c_0_83,plain,
    ( esk2_2(X1,k1_xboole_0) = X1
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_78])).

cnf(c_0_84,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_80])).

cnf(c_0_85,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k1_xboole_0
    | r2_hidden(k1_funct_1(esk7_0,esk3_4(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0,esk7_0)),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_86,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk2_2(X1,X2),X2)
    | esk2_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_87,plain,
    ( esk2_2(X1,k1_xboole_0) = X1
    | ~ r2_hidden(esk2_2(X1,k1_xboole_0),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_79]),c_0_83])).

cnf(c_0_88,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_89,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k1_xboole_0
    | r2_hidden(k1_funct_1(esk6_0,X1),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_74]),c_0_75]),c_0_76])])).

cnf(c_0_90,plain,
    ( r2_relset_1(X2,X3,X1,X4)
    | k1_funct_1(X1,esk3_4(X2,X3,X1,X4)) != k1_funct_1(X4,esk3_4(X2,X3,X1,X4))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_91,negated_conjecture,
    ( k1_funct_1(esk7_0,esk3_4(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0,esk7_0)) = esk5_0
    | k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_92,plain,
    ( X2 = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | esk2_2(X1,X2) != X1
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_50]),c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_93,plain,
    ( esk2_2(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_87,c_0_69])).

cnf(c_0_94,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_95,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k1_xboole_0
    | r2_hidden(k1_funct_1(esk6_0,esk3_4(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0,esk7_0)),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_82])).

cnf(c_0_96,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k1_xboole_0
    | k1_funct_1(esk6_0,esk3_4(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0,esk7_0)) != esk5_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_62]),c_0_75]),c_0_63]),c_0_76]),c_0_61]),c_0_74])]),c_0_77])).

cnf(c_0_97,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k1_xboole_0
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_98,plain,
    ( r2_hidden(X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_57])).

cnf(c_0_99,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_95]),c_0_96])).

cnf(c_0_100,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_97]),c_0_35])]),c_0_68])).

cnf(c_0_101,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_100]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n010.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 10:19:29 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.59  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.18/0.59  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.18/0.59  #
% 0.18/0.59  # Preprocessing time       : 0.030 s
% 0.18/0.59  # Presaturation interreduction done
% 0.18/0.59  
% 0.18/0.59  # Proof found!
% 0.18/0.59  # SZS status Theorem
% 0.18/0.59  # SZS output start CNFRefutation
% 0.18/0.59  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.18/0.59  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.18/0.59  fof(t66_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,k1_tarski(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>r2_relset_1(X1,k1_tarski(X2),X3,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_funct_2)).
% 0.18/0.59  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.18/0.59  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.18/0.59  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.18/0.59  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.18/0.59  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.18/0.59  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.18/0.59  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.18/0.59  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.18/0.59  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.18/0.59  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.18/0.59  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.18/0.59  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.18/0.59  fof(t18_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X5]:(r2_hidden(X5,X1)=>k1_funct_1(X3,X5)=k1_funct_1(X4,X5))=>r2_relset_1(X1,X2,X3,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_2)).
% 0.18/0.59  fof(t7_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_hidden(X3,X1)=>(X2=k1_xboole_0|r2_hidden(k1_funct_1(X4,X3),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 0.18/0.59  fof(c_0_17, plain, ![X8, X9, X10, X11, X12, X13, X14, X15]:((((r2_hidden(X11,X8)|~r2_hidden(X11,X10)|X10!=k4_xboole_0(X8,X9))&(~r2_hidden(X11,X9)|~r2_hidden(X11,X10)|X10!=k4_xboole_0(X8,X9)))&(~r2_hidden(X12,X8)|r2_hidden(X12,X9)|r2_hidden(X12,X10)|X10!=k4_xboole_0(X8,X9)))&((~r2_hidden(esk1_3(X13,X14,X15),X15)|(~r2_hidden(esk1_3(X13,X14,X15),X13)|r2_hidden(esk1_3(X13,X14,X15),X14))|X15=k4_xboole_0(X13,X14))&((r2_hidden(esk1_3(X13,X14,X15),X13)|r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k4_xboole_0(X13,X14))&(~r2_hidden(esk1_3(X13,X14,X15),X14)|r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k4_xboole_0(X13,X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.18/0.59  fof(c_0_18, plain, ![X19, X20]:k4_xboole_0(X19,X20)=k5_xboole_0(X19,k3_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.18/0.59  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,k1_tarski(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>r2_relset_1(X1,k1_tarski(X2),X3,X4)))), inference(assume_negation,[status(cth)],[t66_funct_2])).
% 0.18/0.59  fof(c_0_20, plain, ![X17, X18]:(((r1_tarski(X17,X18)|X17!=X18)&(r1_tarski(X18,X17)|X17!=X18))&(~r1_tarski(X17,X18)|~r1_tarski(X18,X17)|X17=X18)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.18/0.59  fof(c_0_21, plain, ![X21]:r1_tarski(k1_xboole_0,X21), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.18/0.59  fof(c_0_22, plain, ![X58, X59, X60]:(((r2_hidden(X58,X60)|~r1_tarski(k2_tarski(X58,X59),X60))&(r2_hidden(X59,X60)|~r1_tarski(k2_tarski(X58,X59),X60)))&(~r2_hidden(X58,X60)|~r2_hidden(X59,X60)|r1_tarski(k2_tarski(X58,X59),X60))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.18/0.59  fof(c_0_23, plain, ![X31, X32]:k1_enumset1(X31,X31,X32)=k2_tarski(X31,X32), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.18/0.59  fof(c_0_24, plain, ![X33, X34, X35]:k2_enumset1(X33,X33,X34,X35)=k1_enumset1(X33,X34,X35), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.18/0.59  fof(c_0_25, plain, ![X36, X37, X38, X39]:k3_enumset1(X36,X36,X37,X38,X39)=k2_enumset1(X36,X37,X38,X39), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.18/0.59  fof(c_0_26, plain, ![X40, X41, X42, X43, X44]:k4_enumset1(X40,X40,X41,X42,X43,X44)=k3_enumset1(X40,X41,X42,X43,X44), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.18/0.59  fof(c_0_27, plain, ![X45, X46, X47, X48, X49, X50]:k5_enumset1(X45,X45,X46,X47,X48,X49,X50)=k4_enumset1(X45,X46,X47,X48,X49,X50), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.18/0.59  fof(c_0_28, plain, ![X51, X52, X53, X54, X55, X56, X57]:k6_enumset1(X51,X51,X52,X53,X54,X55,X56,X57)=k5_enumset1(X51,X52,X53,X54,X55,X56,X57), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.18/0.59  cnf(c_0_29, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.59  cnf(c_0_30, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.59  fof(c_0_31, plain, ![X22]:k4_xboole_0(X22,k1_xboole_0)=X22, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.18/0.59  fof(c_0_32, negated_conjecture, (((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk4_0,k1_tarski(esk5_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_tarski(esk5_0)))))&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,esk4_0,k1_tarski(esk5_0)))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_tarski(esk5_0)))))&~r2_relset_1(esk4_0,k1_tarski(esk5_0),esk6_0,esk7_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.18/0.59  fof(c_0_33, plain, ![X30]:k2_tarski(X30,X30)=k1_tarski(X30), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.18/0.59  cnf(c_0_34, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.59  cnf(c_0_35, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.59  cnf(c_0_36, plain, (r1_tarski(k2_tarski(X1,X3),X2)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.59  cnf(c_0_37, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.59  cnf(c_0_38, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.59  cnf(c_0_39, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.18/0.59  cnf(c_0_40, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.18/0.59  cnf(c_0_41, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.18/0.59  cnf(c_0_42, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.59  cnf(c_0_43, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.18/0.59  cnf(c_0_44, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.18/0.59  cnf(c_0_45, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X3,X1),X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.59  cnf(c_0_46, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.59  fof(c_0_47, plain, ![X23, X24, X25, X26, X27, X28]:(((~r2_hidden(X25,X24)|X25=X23|X24!=k1_tarski(X23))&(X26!=X23|r2_hidden(X26,X24)|X24!=k1_tarski(X23)))&((~r2_hidden(esk2_2(X27,X28),X28)|esk2_2(X27,X28)!=X27|X28=k1_tarski(X27))&(r2_hidden(esk2_2(X27,X28),X28)|esk2_2(X27,X28)=X27|X28=k1_tarski(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.18/0.59  fof(c_0_48, plain, ![X67, X68, X69, X70]:((r2_hidden(esk3_4(X67,X68,X69,X70),X67)|r2_relset_1(X67,X68,X69,X70)|(~v1_funct_1(X70)|~v1_funct_2(X70,X67,X68)|~m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X67,X68))))|(~v1_funct_1(X69)|~v1_funct_2(X69,X67,X68)|~m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(X67,X68)))))&(k1_funct_1(X69,esk3_4(X67,X68,X69,X70))!=k1_funct_1(X70,esk3_4(X67,X68,X69,X70))|r2_relset_1(X67,X68,X69,X70)|(~v1_funct_1(X70)|~v1_funct_2(X70,X67,X68)|~m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X67,X68))))|(~v1_funct_1(X69)|~v1_funct_2(X69,X67,X68)|~m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(X67,X68)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_funct_2])])])])])).
% 0.18/0.59  cnf(c_0_49, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_tarski(esk5_0))))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.59  cnf(c_0_50, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.18/0.59  cnf(c_0_51, negated_conjecture, (v1_funct_2(esk7_0,esk4_0,k1_tarski(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.59  cnf(c_0_52, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.18/0.59  cnf(c_0_53, plain, (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),X2)|~r2_hidden(X3,X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42])).
% 0.18/0.59  cnf(c_0_54, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_43])).
% 0.18/0.59  cnf(c_0_55, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_44, c_0_30])).
% 0.18/0.59  cnf(c_0_56, plain, (r2_hidden(X1,X2)|~r1_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42])).
% 0.18/0.59  cnf(c_0_57, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_46])).
% 0.18/0.59  cnf(c_0_58, plain, (r2_hidden(esk2_2(X1,X2),X2)|esk2_2(X1,X2)=X1|X2=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.18/0.59  fof(c_0_59, plain, ![X72, X73, X74, X75]:(~v1_funct_1(X75)|~v1_funct_2(X75,X72,X73)|~m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X72,X73)))|(~r2_hidden(X74,X72)|(X73=k1_xboole_0|r2_hidden(k1_funct_1(X75,X74),X73)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).
% 0.18/0.59  cnf(c_0_60, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X1)|r2_relset_1(X1,X2,X3,X4)|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.18/0.59  cnf(c_0_61, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_50]), c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42])).
% 0.18/0.59  cnf(c_0_62, negated_conjecture, (v1_funct_2(esk7_0,esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_50]), c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42])).
% 0.18/0.59  cnf(c_0_63, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.59  cnf(c_0_64, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_tarski(esk5_0))))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.59  cnf(c_0_65, negated_conjecture, (v1_funct_2(esk6_0,esk4_0,k1_tarski(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.59  cnf(c_0_66, negated_conjecture, (~r2_relset_1(esk4_0,k1_tarski(esk5_0),esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.59  cnf(c_0_67, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)=k1_xboole_0|~r2_hidden(X2,k1_xboole_0)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.18/0.59  cnf(c_0_68, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.18/0.59  cnf(c_0_69, plain, (r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.18/0.59  cnf(c_0_70, plain, (esk2_2(X1,X2)=X1|X2=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)|r2_hidden(esk2_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_50]), c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42])).
% 0.18/0.59  cnf(c_0_71, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.18/0.59  cnf(c_0_72, plain, (X3=k1_xboole_0|r2_hidden(k1_funct_1(X1,X4),X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.18/0.59  cnf(c_0_73, negated_conjecture, (r2_relset_1(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),X1,esk7_0)|r2_hidden(esk3_4(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),X1,esk7_0),esk4_0)|~v1_funct_2(X1,esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62]), c_0_63])])).
% 0.18/0.59  cnf(c_0_74, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_50]), c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42])).
% 0.18/0.59  cnf(c_0_75, negated_conjecture, (v1_funct_2(esk6_0,esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_50]), c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42])).
% 0.18/0.59  cnf(c_0_76, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.59  cnf(c_0_77, negated_conjecture, (~r2_relset_1(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0,esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_50]), c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42])).
% 0.18/0.59  cnf(c_0_78, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X2,k1_xboole_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_67]), c_0_35])]), c_0_68])).
% 0.18/0.59  cnf(c_0_79, plain, (esk2_2(X1,X2)=X1|r2_hidden(esk2_2(X1,X2),X2)|r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.18/0.59  cnf(c_0_80, plain, (X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_50]), c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42])).
% 0.18/0.59  cnf(c_0_81, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k1_xboole_0|r2_hidden(k1_funct_1(esk7_0,X1),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))|~r2_hidden(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_61]), c_0_62]), c_0_63])])).
% 0.18/0.59  cnf(c_0_82, negated_conjecture, (r2_hidden(esk3_4(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0,esk7_0),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75]), c_0_76])]), c_0_77])).
% 0.18/0.59  cnf(c_0_83, plain, (esk2_2(X1,k1_xboole_0)=X1|~r2_hidden(X2,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_78])).
% 0.18/0.59  cnf(c_0_84, plain, (X1=X2|~r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_80])).
% 0.18/0.59  cnf(c_0_85, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k1_xboole_0|r2_hidden(k1_funct_1(esk7_0,esk3_4(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0,esk7_0)),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.18/0.59  cnf(c_0_86, plain, (X2=k1_tarski(X1)|~r2_hidden(esk2_2(X1,X2),X2)|esk2_2(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.18/0.59  cnf(c_0_87, plain, (esk2_2(X1,k1_xboole_0)=X1|~r2_hidden(esk2_2(X1,k1_xboole_0),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_79]), c_0_83])).
% 0.18/0.59  cnf(c_0_88, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.59  cnf(c_0_89, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k1_xboole_0|r2_hidden(k1_funct_1(esk6_0,X1),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))|~r2_hidden(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_74]), c_0_75]), c_0_76])])).
% 0.18/0.59  cnf(c_0_90, plain, (r2_relset_1(X2,X3,X1,X4)|k1_funct_1(X1,esk3_4(X2,X3,X1,X4))!=k1_funct_1(X4,esk3_4(X2,X3,X1,X4))|~v1_funct_1(X4)|~v1_funct_2(X4,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.18/0.59  cnf(c_0_91, negated_conjecture, (k1_funct_1(esk7_0,esk3_4(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0,esk7_0))=esk5_0|k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.18/0.59  cnf(c_0_92, plain, (X2=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)|esk2_2(X1,X2)!=X1|~r2_hidden(esk2_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_50]), c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42])).
% 0.18/0.59  cnf(c_0_93, plain, (esk2_2(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_87, c_0_69])).
% 0.18/0.59  cnf(c_0_94, plain, (r2_hidden(X1,X2)|~r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42])).
% 0.18/0.59  cnf(c_0_95, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k1_xboole_0|r2_hidden(k1_funct_1(esk6_0,esk3_4(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0,esk7_0)),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_89, c_0_82])).
% 0.18/0.59  cnf(c_0_96, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k1_xboole_0|k1_funct_1(esk6_0,esk3_4(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0,esk7_0))!=esk5_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_62]), c_0_75]), c_0_63]), c_0_76]), c_0_61]), c_0_74])]), c_0_77])).
% 0.18/0.59  cnf(c_0_97, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)=k1_xboole_0|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 0.18/0.59  cnf(c_0_98, plain, (r2_hidden(X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))), inference(spm,[status(thm)],[c_0_94, c_0_57])).
% 0.18/0.59  cnf(c_0_99, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_95]), c_0_96])).
% 0.18/0.59  cnf(c_0_100, plain, (~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_97]), c_0_35])]), c_0_68])).
% 0.18/0.59  cnf(c_0_101, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_100]), ['proof']).
% 0.18/0.59  # SZS output end CNFRefutation
% 0.18/0.59  # Proof object total steps             : 102
% 0.18/0.59  # Proof object clause steps            : 67
% 0.18/0.59  # Proof object formula steps           : 35
% 0.18/0.59  # Proof object conjectures             : 25
% 0.18/0.59  # Proof object clause conjectures      : 22
% 0.18/0.59  # Proof object formula conjectures     : 3
% 0.18/0.59  # Proof object initial clauses used    : 29
% 0.18/0.59  # Proof object initial formulas used   : 17
% 0.18/0.59  # Proof object generating inferences   : 22
% 0.18/0.59  # Proof object simplifying inferences  : 110
% 0.18/0.59  # Training examples: 0 positive, 0 negative
% 0.18/0.59  # Parsed axioms                        : 20
% 0.18/0.59  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.59  # Initial clauses                      : 40
% 0.18/0.59  # Removed in clause preprocessing      : 8
% 0.18/0.59  # Initial clauses in saturation        : 32
% 0.18/0.59  # Processed clauses                    : 816
% 0.18/0.59  # ...of these trivial                  : 10
% 0.18/0.59  # ...subsumed                          : 397
% 0.18/0.59  # ...remaining for further processing  : 409
% 0.18/0.59  # Other redundant clauses eliminated   : 57
% 0.18/0.59  # Clauses deleted for lack of memory   : 0
% 0.18/0.59  # Backward-subsumed                    : 119
% 0.18/0.59  # Backward-rewritten                   : 69
% 0.18/0.59  # Generated clauses                    : 10418
% 0.18/0.59  # ...of the previous two non-trivial   : 9602
% 0.18/0.59  # Contextual simplify-reflections      : 8
% 0.18/0.59  # Paramodulations                      : 10333
% 0.18/0.59  # Factorizations                       : 27
% 0.18/0.59  # Equation resolutions                 : 58
% 0.18/0.59  # Propositional unsat checks           : 0
% 0.18/0.59  #    Propositional check models        : 0
% 0.18/0.59  #    Propositional check unsatisfiable : 0
% 0.18/0.59  #    Propositional clauses             : 0
% 0.18/0.59  #    Propositional clauses after purity: 0
% 0.18/0.59  #    Propositional unsat core size     : 0
% 0.18/0.59  #    Propositional preprocessing time  : 0.000
% 0.18/0.59  #    Propositional encoding time       : 0.000
% 0.18/0.59  #    Propositional solver time         : 0.000
% 0.18/0.59  #    Success case prop preproc time    : 0.000
% 0.18/0.59  #    Success case prop encoding time   : 0.000
% 0.18/0.59  #    Success case prop solver time     : 0.000
% 0.18/0.59  # Current number of processed clauses  : 182
% 0.18/0.59  #    Positive orientable unit clauses  : 16
% 0.18/0.59  #    Positive unorientable unit clauses: 0
% 0.18/0.59  #    Negative unit clauses             : 1
% 0.18/0.59  #    Non-unit-clauses                  : 165
% 0.18/0.59  # Current number of unprocessed clauses: 8377
% 0.18/0.59  # ...number of literals in the above   : 49875
% 0.18/0.59  # Current number of archived formulas  : 0
% 0.18/0.59  # Current number of archived clauses   : 228
% 0.18/0.59  # Clause-clause subsumption calls (NU) : 8594
% 0.18/0.59  # Rec. Clause-clause subsumption calls : 3004
% 0.18/0.59  # Non-unit clause-clause subsumptions  : 410
% 0.18/0.59  # Unit Clause-clause subsumption calls : 486
% 0.18/0.59  # Rewrite failures with RHS unbound    : 0
% 0.18/0.59  # BW rewrite match attempts            : 26
% 0.18/0.59  # BW rewrite match successes           : 11
% 0.18/0.59  # Condensation attempts                : 0
% 0.18/0.59  # Condensation successes               : 0
% 0.18/0.59  # Termbank termtop insertions          : 244372
% 0.41/0.59  
% 0.41/0.59  # -------------------------------------------------
% 0.41/0.59  # User time                : 0.242 s
% 0.41/0.59  # System time              : 0.010 s
% 0.41/0.59  # Total time               : 0.252 s
% 0.41/0.59  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
