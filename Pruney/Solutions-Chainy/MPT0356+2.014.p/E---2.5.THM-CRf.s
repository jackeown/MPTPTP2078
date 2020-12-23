%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:47 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 333 expanded)
%              Number of clauses        :   60 ( 154 expanded)
%              Number of leaves         :   21 (  87 expanded)
%              Depth                    :   16
%              Number of atoms          :  209 ( 656 expanded)
%              Number of equality atoms :   28 (  91 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(t77_enumset1,axiom,(
    ! [X1,X2] : k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(t85_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k5_enumset1(X1,X1,X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_enumset1)).

fof(t80_zfmisc_1,axiom,(
    ! [X1] : r1_tarski(k1_tarski(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_zfmisc_1)).

fof(t82_enumset1,axiom,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).

fof(t73_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,k2_xboole_0(X2,X3))
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

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

fof(t85_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_xboole_0(X1,k4_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(t86_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

fof(t110_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k5_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).

fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t64_xboole_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4)
        & r1_xboole_0(X2,X4) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t35_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(X2,k3_subset_1(X1,X3))
           => r1_tarski(X3,k3_subset_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

fof(t31_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(X2,X3)
          <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(c_0_21,plain,(
    ! [X37,X38,X39] :
      ( ( r2_hidden(X37,X39)
        | ~ r1_tarski(k2_tarski(X37,X38),X39) )
      & ( r2_hidden(X38,X39)
        | ~ r1_tarski(k2_tarski(X37,X38),X39) )
      & ( ~ r2_hidden(X37,X39)
        | ~ r2_hidden(X38,X39)
        | r1_tarski(k2_tarski(X37,X38),X39) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

fof(c_0_22,plain,(
    ! [X30,X31] : k2_enumset1(X30,X30,X30,X31) = k2_tarski(X30,X31) ),
    inference(variable_rename,[status(thm)],[t77_enumset1])).

fof(c_0_23,plain,(
    ! [X33,X34,X35,X36] : k5_enumset1(X33,X33,X33,X33,X34,X35,X36) = k2_enumset1(X33,X34,X35,X36) ),
    inference(variable_rename,[status(thm)],[t85_enumset1])).

fof(c_0_24,plain,(
    ! [X40] : r1_tarski(k1_tarski(X40),k1_zfmisc_1(X40)) ),
    inference(variable_rename,[status(thm)],[t80_zfmisc_1])).

fof(c_0_25,plain,(
    ! [X32] : k2_enumset1(X32,X32,X32,X32) = k1_tarski(X32) ),
    inference(variable_rename,[status(thm)],[t82_enumset1])).

fof(c_0_26,plain,(
    ! [X19,X20,X21] :
      ( ~ r1_tarski(X19,k2_xboole_0(X20,X21))
      | ~ r1_xboole_0(X19,X21)
      | r1_tarski(X19,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_xboole_1])])).

fof(c_0_27,plain,(
    ! [X22,X23] : r1_tarski(X22,k2_xboole_0(X22,X23)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X3,X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k5_enumset1(X1,X1,X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( r1_tarski(k1_tarski(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( k2_enumset1(X1,X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_35,plain,(
    ! [X18] : r1_xboole_0(X18,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_36,plain,(
    ! [X41,X42] :
      ( ( ~ m1_subset_1(X42,X41)
        | r2_hidden(X42,X41)
        | v1_xboole_0(X41) )
      & ( ~ r2_hidden(X42,X41)
        | m1_subset_1(X42,X41)
        | v1_xboole_0(X41) )
      & ( ~ m1_subset_1(X42,X41)
        | v1_xboole_0(X42)
        | ~ v1_xboole_0(X41) )
      & ( ~ v1_xboole_0(X42)
        | m1_subset_1(X42,X41)
        | ~ v1_xboole_0(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k5_enumset1(X3,X3,X3,X3,X3,X3,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_38,plain,
    ( r1_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32]),c_0_30])).

fof(c_0_39,plain,(
    ! [X45] : ~ v1_xboole_0(k1_zfmisc_1(X45)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_40,plain,(
    ! [X24,X25,X26] :
      ( ~ r1_tarski(X24,X25)
      | r1_xboole_0(X24,k4_xboole_0(X26,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_42,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_43,plain,(
    ! [X43,X44] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(X43))
      | k3_subset_1(X43,X44) = k4_xboole_0(X43,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_44,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_46,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_47,plain,(
    ! [X27,X28,X29] :
      ( ~ r1_tarski(X27,X28)
      | ~ r1_xboole_0(X27,X29)
      | r1_tarski(X27,k4_xboole_0(X28,X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).

cnf(c_0_48,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])).

fof(c_0_52,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(X7,X8)
      | ~ r1_tarski(X9,X8)
      | r1_tarski(k5_xboole_0(X7,X9),X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t110_xboole_1])])).

fof(c_0_53,plain,(
    ! [X5,X6] : k5_xboole_0(X5,X6) = k2_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X6,X5)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_56,plain,
    ( k4_xboole_0(X1,X1) = k3_subset_1(X1,X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_57,plain,
    ( r1_tarski(k5_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_58,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_59,plain,(
    ! [X10,X11] :
      ( ~ r1_tarski(X10,X11)
      | k2_xboole_0(X10,X11) = X11 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_60,plain,(
    ! [X14,X15,X16,X17] :
      ( ~ r1_tarski(X14,X15)
      | ~ r1_tarski(X16,X17)
      | ~ r1_xboole_0(X15,X17)
      | r1_xboole_0(X14,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_xboole_1])])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,k4_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_49])).

cnf(c_0_62,plain,
    ( r1_xboole_0(X1,k3_subset_1(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

fof(c_0_63,plain,(
    ! [X12] : r1_tarski(k1_xboole_0,X12) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_64,plain,
    ( r1_tarski(k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X3,X1)),X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_65,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_66,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4)
    | ~ r1_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_67,plain,
    ( r1_tarski(X1,k4_xboole_0(X1,k3_subset_1(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

fof(c_0_68,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( r1_tarski(X2,k3_subset_1(X1,X3))
             => r1_tarski(X3,k3_subset_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t35_subset_1])).

cnf(c_0_69,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_70,plain,
    ( r1_tarski(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),k2_xboole_0(X1,X3))
    | ~ r1_tarski(X2,k2_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_34])).

cnf(c_0_71,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_65,c_0_49])).

cnf(c_0_72,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X3,k4_xboole_0(X2,k3_subset_1(X2,X2)))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

fof(c_0_73,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))
    & r1_tarski(esk2_0,k3_subset_1(esk1_0,esk3_0))
    & ~ r1_tarski(esk3_0,k3_subset_1(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_68])])])).

fof(c_0_74,plain,(
    ! [X46,X47,X48] :
      ( ( ~ r1_tarski(X47,X48)
        | r1_tarski(k3_subset_1(X46,X48),k3_subset_1(X46,X47))
        | ~ m1_subset_1(X48,k1_zfmisc_1(X46))
        | ~ m1_subset_1(X47,k1_zfmisc_1(X46)) )
      & ( ~ r1_tarski(k3_subset_1(X46,X48),k3_subset_1(X46,X47))
        | r1_tarski(X47,X48)
        | ~ m1_subset_1(X48,k1_zfmisc_1(X46))
        | ~ m1_subset_1(X47,k1_zfmisc_1(X46)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_subset_1])])])])).

cnf(c_0_75,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_65,c_0_69])).

cnf(c_0_76,plain,
    ( r1_tarski(k3_subset_1(X1,X1),k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_34]),c_0_56]),c_0_56]),c_0_71])).

cnf(c_0_77,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k4_xboole_0(X2,k3_subset_1(X2,X2))) ),
    inference(spm,[status(thm)],[c_0_72,c_0_49])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(esk2_0,k3_subset_1(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_80,plain,
    ( r1_tarski(X3,X2)
    | ~ r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

fof(c_0_81,plain,(
    ! [X13] :
      ( ~ r1_tarski(X13,k1_xboole_0)
      | X13 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_82,plain,
    ( r1_tarski(X1,k1_xboole_0)
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_75])).

cnf(c_0_83,plain,
    ( r1_tarski(k3_subset_1(X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_71])).

cnf(c_0_84,plain,
    ( r1_xboole_0(k3_subset_1(X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_55])).

cnf(c_0_85,negated_conjecture,
    ( r1_xboole_0(X1,esk2_0)
    | ~ r1_xboole_0(X2,k3_subset_1(esk1_0,esk3_0))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_66,c_0_78])).

cnf(c_0_86,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk3_0) = k3_subset_1(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_79])).

cnf(c_0_87,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(k3_subset_1(X2,X2),k3_subset_1(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_51])).

cnf(c_0_88,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_89,plain,
    ( r1_tarski(k3_subset_1(X1,X1),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84])])).

cnf(c_0_90,negated_conjecture,
    ( r1_xboole_0(X1,esk2_0)
    | ~ r1_xboole_0(X1,k3_subset_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_49])).

cnf(c_0_91,negated_conjecture,
    ( r1_xboole_0(esk3_0,k3_subset_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_86])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(esk3_0,esk1_0)
    | ~ r1_tarski(k3_subset_1(esk1_0,esk1_0),k3_subset_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_79])).

cnf(c_0_93,plain,
    ( k3_subset_1(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_94,plain,
    ( r1_tarski(X1,k4_xboole_0(k2_xboole_0(X1,X2),X3))
    | ~ r1_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_54,c_0_34])).

cnf(c_0_95,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_96,negated_conjecture,
    ( r1_tarski(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_93]),c_0_69])])).

cnf(c_0_97,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_98,negated_conjecture,
    ( r1_tarski(esk3_0,k4_xboole_0(k2_xboole_0(esk3_0,X1),esk2_0)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_99,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk1_0) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_65,c_0_96])).

cnf(c_0_100,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk2_0) = k3_subset_1(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_97])).

cnf(c_0_101,negated_conjecture,
    ( ~ r1_tarski(esk3_0,k3_subset_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_102,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_100]),c_0_101]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:02:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S002A
% 0.13/0.39  # and selection function SelectNegativeLiterals.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.028 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.13/0.39  fof(t77_enumset1, axiom, ![X1, X2]:k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_enumset1)).
% 0.13/0.39  fof(t85_enumset1, axiom, ![X1, X2, X3, X4]:k5_enumset1(X1,X1,X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_enumset1)).
% 0.13/0.39  fof(t80_zfmisc_1, axiom, ![X1]:r1_tarski(k1_tarski(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_zfmisc_1)).
% 0.13/0.39  fof(t82_enumset1, axiom, ![X1]:k2_enumset1(X1,X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_enumset1)).
% 0.13/0.39  fof(t73_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 0.13/0.39  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.13/0.39  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.13/0.39  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.13/0.39  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.13/0.39  fof(t85_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 0.13/0.39  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.13/0.39  fof(t86_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X1,X3))=>r1_tarski(X1,k4_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 0.13/0.39  fof(t110_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k5_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_xboole_1)).
% 0.13/0.39  fof(d6_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 0.13/0.39  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.13/0.39  fof(t64_xboole_1, axiom, ![X1, X2, X3, X4]:(((r1_tarski(X1,X2)&r1_tarski(X3,X4))&r1_xboole_0(X2,X4))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_xboole_1)).
% 0.13/0.39  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.13/0.39  fof(t35_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X3))=>r1_tarski(X3,k3_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_subset_1)).
% 0.13/0.39  fof(t31_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 0.13/0.39  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.13/0.39  fof(c_0_21, plain, ![X37, X38, X39]:(((r2_hidden(X37,X39)|~r1_tarski(k2_tarski(X37,X38),X39))&(r2_hidden(X38,X39)|~r1_tarski(k2_tarski(X37,X38),X39)))&(~r2_hidden(X37,X39)|~r2_hidden(X38,X39)|r1_tarski(k2_tarski(X37,X38),X39))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.13/0.39  fof(c_0_22, plain, ![X30, X31]:k2_enumset1(X30,X30,X30,X31)=k2_tarski(X30,X31), inference(variable_rename,[status(thm)],[t77_enumset1])).
% 0.13/0.39  fof(c_0_23, plain, ![X33, X34, X35, X36]:k5_enumset1(X33,X33,X33,X33,X34,X35,X36)=k2_enumset1(X33,X34,X35,X36), inference(variable_rename,[status(thm)],[t85_enumset1])).
% 0.13/0.39  fof(c_0_24, plain, ![X40]:r1_tarski(k1_tarski(X40),k1_zfmisc_1(X40)), inference(variable_rename,[status(thm)],[t80_zfmisc_1])).
% 0.13/0.39  fof(c_0_25, plain, ![X32]:k2_enumset1(X32,X32,X32,X32)=k1_tarski(X32), inference(variable_rename,[status(thm)],[t82_enumset1])).
% 0.13/0.39  fof(c_0_26, plain, ![X19, X20, X21]:(~r1_tarski(X19,k2_xboole_0(X20,X21))|~r1_xboole_0(X19,X21)|r1_tarski(X19,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_xboole_1])])).
% 0.13/0.39  fof(c_0_27, plain, ![X22, X23]:r1_tarski(X22,k2_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.13/0.39  cnf(c_0_28, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X3,X1),X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.39  cnf(c_0_29, plain, (k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  cnf(c_0_30, plain, (k5_enumset1(X1,X1,X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.39  cnf(c_0_31, plain, (r1_tarski(k1_tarski(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.39  cnf(c_0_32, plain, (k2_enumset1(X1,X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  cnf(c_0_33, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.39  cnf(c_0_34, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.39  fof(c_0_35, plain, ![X18]:r1_xboole_0(X18,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.13/0.39  fof(c_0_36, plain, ![X41, X42]:(((~m1_subset_1(X42,X41)|r2_hidden(X42,X41)|v1_xboole_0(X41))&(~r2_hidden(X42,X41)|m1_subset_1(X42,X41)|v1_xboole_0(X41)))&((~m1_subset_1(X42,X41)|v1_xboole_0(X42)|~v1_xboole_0(X41))&(~v1_xboole_0(X42)|m1_subset_1(X42,X41)|~v1_xboole_0(X41)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.13/0.39  cnf(c_0_37, plain, (r2_hidden(X1,X2)|~r1_tarski(k5_enumset1(X3,X3,X3,X3,X3,X3,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 0.13/0.39  cnf(c_0_38, plain, (r1_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32]), c_0_30])).
% 0.13/0.39  fof(c_0_39, plain, ![X45]:~v1_xboole_0(k1_zfmisc_1(X45)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.13/0.39  fof(c_0_40, plain, ![X24, X25, X26]:(~r1_tarski(X24,X25)|r1_xboole_0(X24,k4_xboole_0(X26,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).
% 0.13/0.39  cnf(c_0_41, plain, (r1_tarski(X1,X1)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.13/0.39  cnf(c_0_42, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.39  fof(c_0_43, plain, ![X43, X44]:(~m1_subset_1(X44,k1_zfmisc_1(X43))|k3_subset_1(X43,X44)=k4_xboole_0(X43,X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.13/0.39  cnf(c_0_44, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.39  cnf(c_0_45, plain, (r2_hidden(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.13/0.39  cnf(c_0_46, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.39  fof(c_0_47, plain, ![X27, X28, X29]:(~r1_tarski(X27,X28)|~r1_xboole_0(X27,X29)|r1_tarski(X27,k4_xboole_0(X28,X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).
% 0.13/0.39  cnf(c_0_48, plain, (r1_xboole_0(X1,k4_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.39  cnf(c_0_49, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.13/0.39  cnf(c_0_50, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.39  cnf(c_0_51, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])).
% 0.13/0.39  fof(c_0_52, plain, ![X7, X8, X9]:(~r1_tarski(X7,X8)|~r1_tarski(X9,X8)|r1_tarski(k5_xboole_0(X7,X9),X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t110_xboole_1])])).
% 0.13/0.39  fof(c_0_53, plain, ![X5, X6]:k5_xboole_0(X5,X6)=k2_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X6,X5)), inference(variable_rename,[status(thm)],[d6_xboole_0])).
% 0.13/0.39  cnf(c_0_54, plain, (r1_tarski(X1,k4_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.13/0.39  cnf(c_0_55, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.13/0.39  cnf(c_0_56, plain, (k4_xboole_0(X1,X1)=k3_subset_1(X1,X1)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.13/0.39  cnf(c_0_57, plain, (r1_tarski(k5_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.13/0.39  cnf(c_0_58, plain, (k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.13/0.39  fof(c_0_59, plain, ![X10, X11]:(~r1_tarski(X10,X11)|k2_xboole_0(X10,X11)=X11), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.13/0.39  fof(c_0_60, plain, ![X14, X15, X16, X17]:(~r1_tarski(X14,X15)|~r1_tarski(X16,X17)|~r1_xboole_0(X15,X17)|r1_xboole_0(X14,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_xboole_1])])).
% 0.13/0.39  cnf(c_0_61, plain, (r1_tarski(X1,k4_xboole_0(X1,X2))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_54, c_0_49])).
% 0.13/0.39  cnf(c_0_62, plain, (r1_xboole_0(X1,k3_subset_1(X1,X1))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.13/0.39  fof(c_0_63, plain, ![X12]:r1_tarski(k1_xboole_0,X12), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.13/0.39  cnf(c_0_64, plain, (r1_tarski(k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X3,X1)),X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_57, c_0_58])).
% 0.13/0.39  cnf(c_0_65, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.13/0.39  cnf(c_0_66, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X3,X4)|~r1_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.13/0.39  cnf(c_0_67, plain, (r1_tarski(X1,k4_xboole_0(X1,k3_subset_1(X1,X1)))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.13/0.39  fof(c_0_68, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X3))=>r1_tarski(X3,k3_subset_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t35_subset_1])).
% 0.13/0.39  cnf(c_0_69, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.13/0.39  cnf(c_0_70, plain, (r1_tarski(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),k2_xboole_0(X1,X3))|~r1_tarski(X2,k2_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_64, c_0_34])).
% 0.13/0.39  cnf(c_0_71, plain, (k2_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_65, c_0_49])).
% 0.13/0.39  cnf(c_0_72, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X3,k4_xboole_0(X2,k3_subset_1(X2,X2)))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.13/0.39  fof(c_0_73, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))&(r1_tarski(esk2_0,k3_subset_1(esk1_0,esk3_0))&~r1_tarski(esk3_0,k3_subset_1(esk1_0,esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_68])])])).
% 0.13/0.39  fof(c_0_74, plain, ![X46, X47, X48]:((~r1_tarski(X47,X48)|r1_tarski(k3_subset_1(X46,X48),k3_subset_1(X46,X47))|~m1_subset_1(X48,k1_zfmisc_1(X46))|~m1_subset_1(X47,k1_zfmisc_1(X46)))&(~r1_tarski(k3_subset_1(X46,X48),k3_subset_1(X46,X47))|r1_tarski(X47,X48)|~m1_subset_1(X48,k1_zfmisc_1(X46))|~m1_subset_1(X47,k1_zfmisc_1(X46)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_subset_1])])])])).
% 0.13/0.40  cnf(c_0_75, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_65, c_0_69])).
% 0.13/0.40  cnf(c_0_76, plain, (r1_tarski(k3_subset_1(X1,X1),k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_34]), c_0_56]), c_0_56]), c_0_71])).
% 0.13/0.40  cnf(c_0_77, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k4_xboole_0(X2,k3_subset_1(X2,X2)))), inference(spm,[status(thm)],[c_0_72, c_0_49])).
% 0.13/0.40  cnf(c_0_78, negated_conjecture, (r1_tarski(esk2_0,k3_subset_1(esk1_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.13/0.40  cnf(c_0_79, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.13/0.40  cnf(c_0_80, plain, (r1_tarski(X3,X2)|~r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.13/0.40  fof(c_0_81, plain, ![X13]:(~r1_tarski(X13,k1_xboole_0)|X13=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.13/0.40  cnf(c_0_82, plain, (r1_tarski(X1,k1_xboole_0)|~r1_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_33, c_0_75])).
% 0.13/0.40  cnf(c_0_83, plain, (r1_tarski(k3_subset_1(X1,X1),X1)), inference(spm,[status(thm)],[c_0_76, c_0_71])).
% 0.13/0.40  cnf(c_0_84, plain, (r1_xboole_0(k3_subset_1(X1,X1),X1)), inference(spm,[status(thm)],[c_0_77, c_0_55])).
% 0.13/0.40  cnf(c_0_85, negated_conjecture, (r1_xboole_0(X1,esk2_0)|~r1_xboole_0(X2,k3_subset_1(esk1_0,esk3_0))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_66, c_0_78])).
% 0.13/0.40  cnf(c_0_86, negated_conjecture, (k4_xboole_0(esk1_0,esk3_0)=k3_subset_1(esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_50, c_0_79])).
% 0.13/0.40  cnf(c_0_87, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(k3_subset_1(X2,X2),k3_subset_1(X2,X1))), inference(spm,[status(thm)],[c_0_80, c_0_51])).
% 0.13/0.40  cnf(c_0_88, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.13/0.40  cnf(c_0_89, plain, (r1_tarski(k3_subset_1(X1,X1),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84])])).
% 0.13/0.40  cnf(c_0_90, negated_conjecture, (r1_xboole_0(X1,esk2_0)|~r1_xboole_0(X1,k3_subset_1(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_85, c_0_49])).
% 0.13/0.40  cnf(c_0_91, negated_conjecture, (r1_xboole_0(esk3_0,k3_subset_1(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_55, c_0_86])).
% 0.13/0.40  cnf(c_0_92, negated_conjecture, (r1_tarski(esk3_0,esk1_0)|~r1_tarski(k3_subset_1(esk1_0,esk1_0),k3_subset_1(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_87, c_0_79])).
% 0.13/0.40  cnf(c_0_93, plain, (k3_subset_1(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.13/0.40  cnf(c_0_94, plain, (r1_tarski(X1,k4_xboole_0(k2_xboole_0(X1,X2),X3))|~r1_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_54, c_0_34])).
% 0.13/0.40  cnf(c_0_95, negated_conjecture, (r1_xboole_0(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.13/0.40  cnf(c_0_96, negated_conjecture, (r1_tarski(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_93]), c_0_69])])).
% 0.13/0.40  cnf(c_0_97, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.13/0.40  cnf(c_0_98, negated_conjecture, (r1_tarski(esk3_0,k4_xboole_0(k2_xboole_0(esk3_0,X1),esk2_0))), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.13/0.40  cnf(c_0_99, negated_conjecture, (k2_xboole_0(esk3_0,esk1_0)=esk1_0), inference(spm,[status(thm)],[c_0_65, c_0_96])).
% 0.13/0.40  cnf(c_0_100, negated_conjecture, (k4_xboole_0(esk1_0,esk2_0)=k3_subset_1(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_50, c_0_97])).
% 0.13/0.40  cnf(c_0_101, negated_conjecture, (~r1_tarski(esk3_0,k3_subset_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.13/0.40  cnf(c_0_102, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_100]), c_0_101]), ['proof']).
% 0.13/0.40  # SZS output end CNFRefutation
% 0.13/0.40  # Proof object total steps             : 103
% 0.13/0.40  # Proof object clause steps            : 60
% 0.13/0.40  # Proof object formula steps           : 43
% 0.13/0.40  # Proof object conjectures             : 18
% 0.13/0.40  # Proof object clause conjectures      : 15
% 0.13/0.40  # Proof object formula conjectures     : 3
% 0.13/0.40  # Proof object initial clauses used    : 24
% 0.13/0.40  # Proof object initial formulas used   : 21
% 0.13/0.40  # Proof object generating inferences   : 32
% 0.13/0.40  # Proof object simplifying inferences  : 16
% 0.13/0.40  # Training examples: 0 positive, 0 negative
% 0.13/0.40  # Parsed axioms                        : 21
% 0.13/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.40  # Initial clauses                      : 30
% 0.13/0.40  # Removed in clause preprocessing      : 4
% 0.13/0.40  # Initial clauses in saturation        : 26
% 0.13/0.40  # Processed clauses                    : 244
% 0.13/0.40  # ...of these trivial                  : 7
% 0.13/0.40  # ...subsumed                          : 16
% 0.13/0.40  # ...remaining for further processing  : 221
% 0.13/0.40  # Other redundant clauses eliminated   : 0
% 0.13/0.40  # Clauses deleted for lack of memory   : 0
% 0.13/0.40  # Backward-subsumed                    : 0
% 0.13/0.40  # Backward-rewritten                   : 67
% 0.13/0.40  # Generated clauses                    : 1389
% 0.13/0.40  # ...of the previous two non-trivial   : 1183
% 0.13/0.40  # Contextual simplify-reflections      : 0
% 0.13/0.40  # Paramodulations                      : 1389
% 0.13/0.40  # Factorizations                       : 0
% 0.13/0.40  # Equation resolutions                 : 0
% 0.13/0.40  # Propositional unsat checks           : 0
% 0.13/0.40  #    Propositional check models        : 0
% 0.13/0.40  #    Propositional check unsatisfiable : 0
% 0.13/0.40  #    Propositional clauses             : 0
% 0.13/0.40  #    Propositional clauses after purity: 0
% 0.13/0.40  #    Propositional unsat core size     : 0
% 0.13/0.40  #    Propositional preprocessing time  : 0.000
% 0.13/0.40  #    Propositional encoding time       : 0.000
% 0.13/0.40  #    Propositional solver time         : 0.000
% 0.13/0.40  #    Success case prop preproc time    : 0.000
% 0.13/0.40  #    Success case prop encoding time   : 0.000
% 0.13/0.40  #    Success case prop solver time     : 0.000
% 0.13/0.40  # Current number of processed clauses  : 128
% 0.13/0.40  #    Positive orientable unit clauses  : 62
% 0.13/0.40  #    Positive unorientable unit clauses: 0
% 0.13/0.40  #    Negative unit clauses             : 2
% 0.13/0.40  #    Non-unit-clauses                  : 64
% 0.13/0.40  # Current number of unprocessed clauses: 972
% 0.13/0.40  # ...number of literals in the above   : 1697
% 0.13/0.40  # Current number of archived formulas  : 0
% 0.13/0.40  # Current number of archived clauses   : 97
% 0.13/0.40  # Clause-clause subsumption calls (NU) : 724
% 0.13/0.40  # Rec. Clause-clause subsumption calls : 606
% 0.13/0.40  # Non-unit clause-clause subsumptions  : 16
% 0.13/0.40  # Unit Clause-clause subsumption calls : 354
% 0.13/0.40  # Rewrite failures with RHS unbound    : 0
% 0.13/0.40  # BW rewrite match attempts            : 175
% 0.13/0.40  # BW rewrite match successes           : 22
% 0.13/0.40  # Condensation attempts                : 0
% 0.13/0.40  # Condensation successes               : 0
% 0.13/0.40  # Termbank termtop insertions          : 21509
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.050 s
% 0.13/0.40  # System time              : 0.004 s
% 0.13/0.40  # Total time               : 0.054 s
% 0.13/0.40  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
