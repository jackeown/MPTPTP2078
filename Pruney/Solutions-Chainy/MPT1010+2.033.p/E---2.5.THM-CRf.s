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
% DateTime   : Thu Dec  3 11:05:16 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 202 expanded)
%              Number of clauses        :   35 (  76 expanded)
%              Number of leaves         :   17 (  59 expanded)
%              Depth                    :    9
%              Number of atoms          :  247 ( 463 expanded)
%              Number of equality atoms :  132 ( 258 expanded)
%              Maximal formula depth    :   47 (   5 average)
%              Maximal clause size      :   68 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t65_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,k1_tarski(X2))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
     => ( r2_hidden(X3,X1)
       => k1_funct_1(X4,X3) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

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

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(d6_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( X9 = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> ~ ( X10 != X1
              & X10 != X2
              & X10 != X3
              & X10 != X4
              & X10 != X5
              & X10 != X6
              & X10 != X7
              & X10 != X8 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_enumset1)).

fof(d1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => ( v1_funct_2(X3,X1,X2)
          <=> X1 = k1_relset_1(X1,X2,X3) ) )
        & ( X2 = k1_xboole_0
         => ( X1 = k1_xboole_0
            | ( v1_funct_2(X3,X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t172_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k1_relat_1(X2))
         => r2_hidden(k1_funct_1(X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,k1_tarski(X2))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
       => ( r2_hidden(X3,X1)
         => k1_funct_1(X4,X3) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t65_funct_2])).

fof(c_0_18,negated_conjecture,
    ( v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk3_0,k1_tarski(esk4_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_tarski(esk4_0))))
    & r2_hidden(esk5_0,esk3_0)
    & k1_funct_1(esk6_0,esk5_0) != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_19,plain,(
    ! [X19] : k2_tarski(X19,X19) = k1_tarski(X19) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_20,plain,(
    ! [X20,X21] : k1_enumset1(X20,X20,X21) = k2_tarski(X20,X21) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_21,plain,(
    ! [X22,X23,X24] : k2_enumset1(X22,X22,X23,X24) = k1_enumset1(X22,X23,X24) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_22,plain,(
    ! [X25,X26,X27,X28] : k3_enumset1(X25,X25,X26,X27,X28) = k2_enumset1(X25,X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_23,plain,(
    ! [X29,X30,X31,X32,X33] : k4_enumset1(X29,X29,X30,X31,X32,X33) = k3_enumset1(X29,X30,X31,X32,X33) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_24,plain,(
    ! [X34,X35,X36,X37,X38,X39] : k5_enumset1(X34,X34,X35,X36,X37,X38,X39) = k4_enumset1(X34,X35,X36,X37,X38,X39) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_25,plain,(
    ! [X40,X41,X42,X43,X44,X45,X46] : k6_enumset1(X40,X40,X41,X42,X43,X44,X45,X46) = k5_enumset1(X40,X41,X42,X43,X44,X45,X46) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_26,plain,(
    ! [X12,X13,X14,X15,X16,X17] :
      ( ( ~ r2_hidden(X14,X13)
        | X14 = X12
        | X13 != k1_tarski(X12) )
      & ( X15 != X12
        | r2_hidden(X15,X13)
        | X13 != k1_tarski(X12) )
      & ( ~ r2_hidden(esk1_2(X16,X17),X17)
        | esk1_2(X16,X17) != X16
        | X17 = k1_tarski(X16) )
      & ( r2_hidden(esk1_2(X16,X17),X17)
        | esk1_2(X16,X17) = X16
        | X17 = k1_tarski(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_27,plain,(
    ! [X79,X80,X81] :
      ( ~ m1_subset_1(X81,k1_zfmisc_1(k2_zfmisc_1(X79,X80)))
      | k1_relset_1(X79,X80,X81) = k1_relat_1(X81) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_tarski(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_37,plain,(
    ! [X47,X48,X49,X50,X51,X52,X53,X54,X55,X56,X57,X58,X59,X60,X61,X62,X63,X64,X65,X66] :
      ( ( ~ r2_hidden(X56,X55)
        | X56 = X47
        | X56 = X48
        | X56 = X49
        | X56 = X50
        | X56 = X51
        | X56 = X52
        | X56 = X53
        | X56 = X54
        | X55 != k6_enumset1(X47,X48,X49,X50,X51,X52,X53,X54) )
      & ( X57 != X47
        | r2_hidden(X57,X55)
        | X55 != k6_enumset1(X47,X48,X49,X50,X51,X52,X53,X54) )
      & ( X57 != X48
        | r2_hidden(X57,X55)
        | X55 != k6_enumset1(X47,X48,X49,X50,X51,X52,X53,X54) )
      & ( X57 != X49
        | r2_hidden(X57,X55)
        | X55 != k6_enumset1(X47,X48,X49,X50,X51,X52,X53,X54) )
      & ( X57 != X50
        | r2_hidden(X57,X55)
        | X55 != k6_enumset1(X47,X48,X49,X50,X51,X52,X53,X54) )
      & ( X57 != X51
        | r2_hidden(X57,X55)
        | X55 != k6_enumset1(X47,X48,X49,X50,X51,X52,X53,X54) )
      & ( X57 != X52
        | r2_hidden(X57,X55)
        | X55 != k6_enumset1(X47,X48,X49,X50,X51,X52,X53,X54) )
      & ( X57 != X53
        | r2_hidden(X57,X55)
        | X55 != k6_enumset1(X47,X48,X49,X50,X51,X52,X53,X54) )
      & ( X57 != X54
        | r2_hidden(X57,X55)
        | X55 != k6_enumset1(X47,X48,X49,X50,X51,X52,X53,X54) )
      & ( esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66) != X58
        | ~ r2_hidden(esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)
        | X66 = k6_enumset1(X58,X59,X60,X61,X62,X63,X64,X65) )
      & ( esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66) != X59
        | ~ r2_hidden(esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)
        | X66 = k6_enumset1(X58,X59,X60,X61,X62,X63,X64,X65) )
      & ( esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66) != X60
        | ~ r2_hidden(esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)
        | X66 = k6_enumset1(X58,X59,X60,X61,X62,X63,X64,X65) )
      & ( esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66) != X61
        | ~ r2_hidden(esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)
        | X66 = k6_enumset1(X58,X59,X60,X61,X62,X63,X64,X65) )
      & ( esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66) != X62
        | ~ r2_hidden(esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)
        | X66 = k6_enumset1(X58,X59,X60,X61,X62,X63,X64,X65) )
      & ( esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66) != X63
        | ~ r2_hidden(esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)
        | X66 = k6_enumset1(X58,X59,X60,X61,X62,X63,X64,X65) )
      & ( esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66) != X64
        | ~ r2_hidden(esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)
        | X66 = k6_enumset1(X58,X59,X60,X61,X62,X63,X64,X65) )
      & ( esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66) != X65
        | ~ r2_hidden(esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)
        | X66 = k6_enumset1(X58,X59,X60,X61,X62,X63,X64,X65) )
      & ( r2_hidden(esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)
        | esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66) = X58
        | esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66) = X59
        | esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66) = X60
        | esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66) = X61
        | esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66) = X62
        | esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66) = X63
        | esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66) = X64
        | esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66) = X65
        | X66 = k6_enumset1(X58,X59,X60,X61,X62,X63,X64,X65) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).

fof(c_0_38,plain,(
    ! [X82,X83,X84] :
      ( ( ~ v1_funct_2(X84,X82,X83)
        | X82 = k1_relset_1(X82,X83,X84)
        | X83 = k1_xboole_0
        | ~ m1_subset_1(X84,k1_zfmisc_1(k2_zfmisc_1(X82,X83))) )
      & ( X82 != k1_relset_1(X82,X83,X84)
        | v1_funct_2(X84,X82,X83)
        | X83 = k1_xboole_0
        | ~ m1_subset_1(X84,k1_zfmisc_1(k2_zfmisc_1(X82,X83))) )
      & ( ~ v1_funct_2(X84,X82,X83)
        | X82 = k1_relset_1(X82,X83,X84)
        | X82 != k1_xboole_0
        | ~ m1_subset_1(X84,k1_zfmisc_1(k2_zfmisc_1(X82,X83))) )
      & ( X82 != k1_relset_1(X82,X83,X84)
        | v1_funct_2(X84,X82,X83)
        | X82 != k1_xboole_0
        | ~ m1_subset_1(X84,k1_zfmisc_1(k2_zfmisc_1(X82,X83))) )
      & ( ~ v1_funct_2(X84,X82,X83)
        | X84 = k1_xboole_0
        | X82 = k1_xboole_0
        | X83 != k1_xboole_0
        | ~ m1_subset_1(X84,k1_zfmisc_1(k2_zfmisc_1(X82,X83))) )
      & ( X84 != k1_xboole_0
        | v1_funct_2(X84,X82,X83)
        | X82 = k1_xboole_0
        | X83 != k1_xboole_0
        | ~ m1_subset_1(X84,k1_zfmisc_1(k2_zfmisc_1(X82,X83))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_39,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( v1_funct_2(esk6_0,esk3_0,k1_tarski(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_42,plain,(
    ! [X71,X72] :
      ( ~ r2_hidden(X71,X72)
      | ~ r1_tarski(X72,X71) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_43,plain,(
    ! [X11] : r1_tarski(k1_xboole_0,X11) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_44,plain,
    ( X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])).

fof(c_0_45,plain,(
    ! [X68,X69,X70] :
      ( ~ v1_relat_1(X69)
      | ~ v5_relat_1(X69,X68)
      | ~ v1_funct_1(X69)
      | ~ r2_hidden(X70,k1_relat_1(X69))
      | r2_hidden(k1_funct_1(X69,X70),X68) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t172_funct_1])])])).

fof(c_0_46,plain,(
    ! [X76,X77,X78] :
      ( ( v4_relat_1(X78,X76)
        | ~ m1_subset_1(X78,k1_zfmisc_1(k2_zfmisc_1(X76,X77))) )
      & ( v5_relat_1(X78,X77)
        | ~ m1_subset_1(X78,k1_zfmisc_1(k2_zfmisc_1(X76,X77))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_47,plain,(
    ! [X73,X74,X75] :
      ( ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74)))
      | v1_relat_1(X75) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X5,X6,X7,X8,X9,X10,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_49,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_50,negated_conjecture,
    ( k1_relset_1(esk3_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk6_0) = k1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_51,negated_conjecture,
    ( v1_funct_2(esk6_0,esk3_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_52,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_55,plain,
    ( r2_hidden(k1_funct_1(X1,X3),X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_57,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_48])])).

cnf(c_0_59,negated_conjecture,
    ( k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = k1_xboole_0
    | k1_relat_1(esk6_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_40]),c_0_50]),c_0_51])])).

cnf(c_0_60,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_61,plain,
    ( k1_funct_1(X1,X2) = X3
    | ~ v1_funct_1(X1)
    | ~ v5_relat_1(X1,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_62,negated_conjecture,
    ( v5_relat_1(esk6_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_40])).

cnf(c_0_63,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_64,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_40])).

cnf(c_0_65,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk3_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( k1_funct_1(esk6_0,esk5_0) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_67,negated_conjecture,
    ( k1_funct_1(esk6_0,X1) = esk4_0
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63]),c_0_64]),c_0_65])])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:26:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.39  #
% 0.21/0.39  # Preprocessing time       : 0.030 s
% 0.21/0.39  # Presaturation interreduction done
% 0.21/0.39  
% 0.21/0.39  # Proof found!
% 0.21/0.39  # SZS status Theorem
% 0.21/0.39  # SZS output start CNFRefutation
% 0.21/0.39  fof(t65_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>(r2_hidden(X3,X1)=>k1_funct_1(X4,X3)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 0.21/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.21/0.39  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.21/0.39  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.21/0.39  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.21/0.39  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.21/0.39  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.21/0.39  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.21/0.39  fof(d6_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:(X9=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)<=>![X10]:(r2_hidden(X10,X9)<=>~((((((((X10!=X1&X10!=X2)&X10!=X3)&X10!=X4)&X10!=X5)&X10!=X6)&X10!=X7)&X10!=X8)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_enumset1)).
% 0.21/0.39  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.21/0.39  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.21/0.39  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.21/0.39  fof(t172_funct_1, axiom, ![X1, X2]:(((v1_relat_1(X2)&v5_relat_1(X2,X1))&v1_funct_1(X2))=>![X3]:(r2_hidden(X3,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 0.21/0.39  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.21/0.39  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.21/0.39  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>(r2_hidden(X3,X1)=>k1_funct_1(X4,X3)=X2))), inference(assume_negation,[status(cth)],[t65_funct_2])).
% 0.21/0.39  fof(c_0_18, negated_conjecture, (((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk3_0,k1_tarski(esk4_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_tarski(esk4_0)))))&(r2_hidden(esk5_0,esk3_0)&k1_funct_1(esk6_0,esk5_0)!=esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.21/0.39  fof(c_0_19, plain, ![X19]:k2_tarski(X19,X19)=k1_tarski(X19), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.39  fof(c_0_20, plain, ![X20, X21]:k1_enumset1(X20,X20,X21)=k2_tarski(X20,X21), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.39  fof(c_0_21, plain, ![X22, X23, X24]:k2_enumset1(X22,X22,X23,X24)=k1_enumset1(X22,X23,X24), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.21/0.39  fof(c_0_22, plain, ![X25, X26, X27, X28]:k3_enumset1(X25,X25,X26,X27,X28)=k2_enumset1(X25,X26,X27,X28), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.21/0.39  fof(c_0_23, plain, ![X29, X30, X31, X32, X33]:k4_enumset1(X29,X29,X30,X31,X32,X33)=k3_enumset1(X29,X30,X31,X32,X33), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.21/0.39  fof(c_0_24, plain, ![X34, X35, X36, X37, X38, X39]:k5_enumset1(X34,X34,X35,X36,X37,X38,X39)=k4_enumset1(X34,X35,X36,X37,X38,X39), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.21/0.39  fof(c_0_25, plain, ![X40, X41, X42, X43, X44, X45, X46]:k6_enumset1(X40,X40,X41,X42,X43,X44,X45,X46)=k5_enumset1(X40,X41,X42,X43,X44,X45,X46), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.21/0.39  fof(c_0_26, plain, ![X12, X13, X14, X15, X16, X17]:(((~r2_hidden(X14,X13)|X14=X12|X13!=k1_tarski(X12))&(X15!=X12|r2_hidden(X15,X13)|X13!=k1_tarski(X12)))&((~r2_hidden(esk1_2(X16,X17),X17)|esk1_2(X16,X17)!=X16|X17=k1_tarski(X16))&(r2_hidden(esk1_2(X16,X17),X17)|esk1_2(X16,X17)=X16|X17=k1_tarski(X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.21/0.39  fof(c_0_27, plain, ![X79, X80, X81]:(~m1_subset_1(X81,k1_zfmisc_1(k2_zfmisc_1(X79,X80)))|k1_relset_1(X79,X80,X81)=k1_relat_1(X81)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.21/0.39  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_tarski(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.39  cnf(c_0_29, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.39  cnf(c_0_30, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.39  cnf(c_0_31, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.39  cnf(c_0_32, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.39  cnf(c_0_33, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.39  cnf(c_0_34, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.39  cnf(c_0_35, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.39  cnf(c_0_36, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.39  fof(c_0_37, plain, ![X47, X48, X49, X50, X51, X52, X53, X54, X55, X56, X57, X58, X59, X60, X61, X62, X63, X64, X65, X66]:(((~r2_hidden(X56,X55)|(X56=X47|X56=X48|X56=X49|X56=X50|X56=X51|X56=X52|X56=X53|X56=X54)|X55!=k6_enumset1(X47,X48,X49,X50,X51,X52,X53,X54))&((((((((X57!=X47|r2_hidden(X57,X55)|X55!=k6_enumset1(X47,X48,X49,X50,X51,X52,X53,X54))&(X57!=X48|r2_hidden(X57,X55)|X55!=k6_enumset1(X47,X48,X49,X50,X51,X52,X53,X54)))&(X57!=X49|r2_hidden(X57,X55)|X55!=k6_enumset1(X47,X48,X49,X50,X51,X52,X53,X54)))&(X57!=X50|r2_hidden(X57,X55)|X55!=k6_enumset1(X47,X48,X49,X50,X51,X52,X53,X54)))&(X57!=X51|r2_hidden(X57,X55)|X55!=k6_enumset1(X47,X48,X49,X50,X51,X52,X53,X54)))&(X57!=X52|r2_hidden(X57,X55)|X55!=k6_enumset1(X47,X48,X49,X50,X51,X52,X53,X54)))&(X57!=X53|r2_hidden(X57,X55)|X55!=k6_enumset1(X47,X48,X49,X50,X51,X52,X53,X54)))&(X57!=X54|r2_hidden(X57,X55)|X55!=k6_enumset1(X47,X48,X49,X50,X51,X52,X53,X54))))&(((((((((esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66)!=X58|~r2_hidden(esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)|X66=k6_enumset1(X58,X59,X60,X61,X62,X63,X64,X65))&(esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66)!=X59|~r2_hidden(esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)|X66=k6_enumset1(X58,X59,X60,X61,X62,X63,X64,X65)))&(esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66)!=X60|~r2_hidden(esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)|X66=k6_enumset1(X58,X59,X60,X61,X62,X63,X64,X65)))&(esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66)!=X61|~r2_hidden(esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)|X66=k6_enumset1(X58,X59,X60,X61,X62,X63,X64,X65)))&(esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66)!=X62|~r2_hidden(esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)|X66=k6_enumset1(X58,X59,X60,X61,X62,X63,X64,X65)))&(esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66)!=X63|~r2_hidden(esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)|X66=k6_enumset1(X58,X59,X60,X61,X62,X63,X64,X65)))&(esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66)!=X64|~r2_hidden(esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)|X66=k6_enumset1(X58,X59,X60,X61,X62,X63,X64,X65)))&(esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66)!=X65|~r2_hidden(esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)|X66=k6_enumset1(X58,X59,X60,X61,X62,X63,X64,X65)))&(r2_hidden(esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)|(esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66)=X58|esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66)=X59|esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66)=X60|esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66)=X61|esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66)=X62|esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66)=X63|esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66)=X64|esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66)=X65)|X66=k6_enumset1(X58,X59,X60,X61,X62,X63,X64,X65)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).
% 0.21/0.39  fof(c_0_38, plain, ![X82, X83, X84]:((((~v1_funct_2(X84,X82,X83)|X82=k1_relset_1(X82,X83,X84)|X83=k1_xboole_0|~m1_subset_1(X84,k1_zfmisc_1(k2_zfmisc_1(X82,X83))))&(X82!=k1_relset_1(X82,X83,X84)|v1_funct_2(X84,X82,X83)|X83=k1_xboole_0|~m1_subset_1(X84,k1_zfmisc_1(k2_zfmisc_1(X82,X83)))))&((~v1_funct_2(X84,X82,X83)|X82=k1_relset_1(X82,X83,X84)|X82!=k1_xboole_0|~m1_subset_1(X84,k1_zfmisc_1(k2_zfmisc_1(X82,X83))))&(X82!=k1_relset_1(X82,X83,X84)|v1_funct_2(X84,X82,X83)|X82!=k1_xboole_0|~m1_subset_1(X84,k1_zfmisc_1(k2_zfmisc_1(X82,X83))))))&((~v1_funct_2(X84,X82,X83)|X84=k1_xboole_0|X82=k1_xboole_0|X83!=k1_xboole_0|~m1_subset_1(X84,k1_zfmisc_1(k2_zfmisc_1(X82,X83))))&(X84!=k1_xboole_0|v1_funct_2(X84,X82,X83)|X82=k1_xboole_0|X83!=k1_xboole_0|~m1_subset_1(X84,k1_zfmisc_1(k2_zfmisc_1(X82,X83)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.21/0.39  cnf(c_0_39, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.39  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.21/0.39  cnf(c_0_41, negated_conjecture, (v1_funct_2(esk6_0,esk3_0,k1_tarski(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.39  fof(c_0_42, plain, ![X71, X72]:(~r2_hidden(X71,X72)|~r1_tarski(X72,X71)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.21/0.39  fof(c_0_43, plain, ![X11]:r1_tarski(k1_xboole_0,X11), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.21/0.39  cnf(c_0_44, plain, (X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_29]), c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.21/0.39  fof(c_0_45, plain, ![X68, X69, X70]:(~v1_relat_1(X69)|~v5_relat_1(X69,X68)|~v1_funct_1(X69)|(~r2_hidden(X70,k1_relat_1(X69))|r2_hidden(k1_funct_1(X69,X70),X68))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t172_funct_1])])])).
% 0.21/0.39  fof(c_0_46, plain, ![X76, X77, X78]:((v4_relat_1(X78,X76)|~m1_subset_1(X78,k1_zfmisc_1(k2_zfmisc_1(X76,X77))))&(v5_relat_1(X78,X77)|~m1_subset_1(X78,k1_zfmisc_1(k2_zfmisc_1(X76,X77))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.21/0.39  fof(c_0_47, plain, ![X73, X74, X75]:(~m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74)))|v1_relat_1(X75)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.21/0.39  cnf(c_0_48, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X5,X6,X7,X8,X9,X10,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.21/0.39  cnf(c_0_49, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.21/0.39  cnf(c_0_50, negated_conjecture, (k1_relset_1(esk3_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk6_0)=k1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.21/0.39  cnf(c_0_51, negated_conjecture, (v1_funct_2(esk6_0,esk3_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_29]), c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.21/0.39  cnf(c_0_52, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.39  cnf(c_0_53, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.21/0.39  cnf(c_0_54, plain, (X1=X2|~r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_44])).
% 0.21/0.39  cnf(c_0_55, plain, (r2_hidden(k1_funct_1(X1,X3),X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~v1_funct_1(X1)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.21/0.39  cnf(c_0_56, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.21/0.39  cnf(c_0_57, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.21/0.39  cnf(c_0_58, plain, (r2_hidden(X1,k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_48])])).
% 0.21/0.39  cnf(c_0_59, negated_conjecture, (k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=k1_xboole_0|k1_relat_1(esk6_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_40]), c_0_50]), c_0_51])])).
% 0.21/0.39  cnf(c_0_60, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.21/0.39  cnf(c_0_61, plain, (k1_funct_1(X1,X2)=X3|~v1_funct_1(X1)|~v5_relat_1(X1,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.21/0.39  cnf(c_0_62, negated_conjecture, (v5_relat_1(esk6_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_56, c_0_40])).
% 0.21/0.39  cnf(c_0_63, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.39  cnf(c_0_64, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_57, c_0_40])).
% 0.21/0.39  cnf(c_0_65, negated_conjecture, (k1_relat_1(esk6_0)=esk3_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])).
% 0.21/0.39  cnf(c_0_66, negated_conjecture, (k1_funct_1(esk6_0,esk5_0)!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.39  cnf(c_0_67, negated_conjecture, (k1_funct_1(esk6_0,X1)=esk4_0|~r2_hidden(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63]), c_0_64]), c_0_65])])).
% 0.21/0.39  cnf(c_0_68, negated_conjecture, (r2_hidden(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.39  cnf(c_0_69, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68])]), ['proof']).
% 0.21/0.39  # SZS output end CNFRefutation
% 0.21/0.39  # Proof object total steps             : 70
% 0.21/0.39  # Proof object clause steps            : 35
% 0.21/0.39  # Proof object formula steps           : 35
% 0.21/0.39  # Proof object conjectures             : 17
% 0.21/0.39  # Proof object clause conjectures      : 14
% 0.21/0.39  # Proof object formula conjectures     : 3
% 0.21/0.39  # Proof object initial clauses used    : 21
% 0.21/0.39  # Proof object initial formulas used   : 17
% 0.21/0.39  # Proof object generating inferences   : 9
% 0.21/0.39  # Proof object simplifying inferences  : 34
% 0.21/0.39  # Training examples: 0 positive, 0 negative
% 0.21/0.39  # Parsed axioms                        : 17
% 0.21/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.39  # Initial clauses                      : 47
% 0.21/0.39  # Removed in clause preprocessing      : 7
% 0.21/0.39  # Initial clauses in saturation        : 40
% 0.21/0.39  # Processed clauses                    : 172
% 0.21/0.39  # ...of these trivial                  : 3
% 0.21/0.39  # ...subsumed                          : 31
% 0.21/0.39  # ...remaining for further processing  : 138
% 0.21/0.39  # Other redundant clauses eliminated   : 47
% 0.21/0.39  # Clauses deleted for lack of memory   : 0
% 0.21/0.39  # Backward-subsumed                    : 11
% 0.21/0.39  # Backward-rewritten                   : 4
% 0.21/0.39  # Generated clauses                    : 366
% 0.21/0.39  # ...of the previous two non-trivial   : 313
% 0.21/0.39  # Contextual simplify-reflections      : 3
% 0.21/0.39  # Paramodulations                      : 326
% 0.21/0.39  # Factorizations                       : 3
% 0.21/0.39  # Equation resolutions                 : 47
% 0.21/0.39  # Propositional unsat checks           : 0
% 0.21/0.39  #    Propositional check models        : 0
% 0.21/0.39  #    Propositional check unsatisfiable : 0
% 0.21/0.39  #    Propositional clauses             : 0
% 0.21/0.39  #    Propositional clauses after purity: 0
% 0.21/0.39  #    Propositional unsat core size     : 0
% 0.21/0.39  #    Propositional preprocessing time  : 0.000
% 0.21/0.39  #    Propositional encoding time       : 0.000
% 0.21/0.39  #    Propositional solver time         : 0.000
% 0.21/0.39  #    Success case prop preproc time    : 0.000
% 0.21/0.39  #    Success case prop encoding time   : 0.000
% 0.21/0.39  #    Success case prop solver time     : 0.000
% 0.21/0.39  # Current number of processed clauses  : 69
% 0.21/0.39  #    Positive orientable unit clauses  : 19
% 0.21/0.39  #    Positive unorientable unit clauses: 0
% 0.21/0.39  #    Negative unit clauses             : 2
% 0.21/0.39  #    Non-unit-clauses                  : 48
% 0.21/0.39  # Current number of unprocessed clauses: 209
% 0.21/0.39  # ...number of literals in the above   : 1370
% 0.21/0.39  # Current number of archived formulas  : 0
% 0.21/0.39  # Current number of archived clauses   : 61
% 0.21/0.39  # Clause-clause subsumption calls (NU) : 653
% 0.21/0.39  # Rec. Clause-clause subsumption calls : 324
% 0.21/0.39  # Non-unit clause-clause subsumptions  : 37
% 0.21/0.39  # Unit Clause-clause subsumption calls : 7
% 0.21/0.39  # Rewrite failures with RHS unbound    : 0
% 0.21/0.39  # BW rewrite match attempts            : 75
% 0.21/0.39  # BW rewrite match successes           : 3
% 0.21/0.39  # Condensation attempts                : 0
% 0.21/0.39  # Condensation successes               : 0
% 0.21/0.39  # Termbank termtop insertions          : 9709
% 0.21/0.39  
% 0.21/0.39  # -------------------------------------------------
% 0.21/0.39  # User time                : 0.046 s
% 0.21/0.39  # System time              : 0.003 s
% 0.21/0.39  # Total time               : 0.049 s
% 0.21/0.39  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
