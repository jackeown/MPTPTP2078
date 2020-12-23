%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:05:15 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 206 expanded)
%              Number of clauses        :   37 (  78 expanded)
%              Number of leaves         :   18 (  60 expanded)
%              Depth                    :    9
%              Number of atoms          :  261 ( 477 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

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

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t202_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1) )
     => ! [X3] :
          ( r2_hidden(X3,k2_relat_1(X2))
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t202_relat_1)).

fof(t12_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => r2_hidden(k1_funct_1(X2,X1),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_enumset1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,k1_tarski(X2))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
       => ( r2_hidden(X3,X1)
         => k1_funct_1(X4,X3) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t65_funct_2])).

fof(c_0_19,negated_conjecture,
    ( v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk3_0,k1_tarski(esk4_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_tarski(esk4_0))))
    & r2_hidden(esk5_0,esk3_0)
    & k1_funct_1(esk6_0,esk5_0) != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_20,plain,(
    ! [X19] : k2_tarski(X19,X19) = k1_tarski(X19) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_21,plain,(
    ! [X20,X21] : k1_enumset1(X20,X20,X21) = k2_tarski(X20,X21) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_22,plain,(
    ! [X22,X23,X24] : k2_enumset1(X22,X22,X23,X24) = k1_enumset1(X22,X23,X24) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_23,plain,(
    ! [X25,X26,X27,X28] : k3_enumset1(X25,X25,X26,X27,X28) = k2_enumset1(X25,X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_24,plain,(
    ! [X29,X30,X31,X32,X33] : k4_enumset1(X29,X29,X30,X31,X32,X33) = k3_enumset1(X29,X30,X31,X32,X33) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_25,plain,(
    ! [X34,X35,X36,X37,X38,X39] : k5_enumset1(X34,X34,X35,X36,X37,X38,X39) = k4_enumset1(X34,X35,X36,X37,X38,X39) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_26,plain,(
    ! [X40,X41,X42,X43,X44,X45,X46] : k6_enumset1(X40,X40,X41,X42,X43,X44,X45,X46) = k5_enumset1(X40,X41,X42,X43,X44,X45,X46) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_27,plain,(
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

fof(c_0_28,plain,(
    ! [X81,X82,X83] :
      ( ~ m1_subset_1(X83,k1_zfmisc_1(k2_zfmisc_1(X81,X82)))
      | k1_relset_1(X81,X82,X83) = k1_relat_1(X83) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_tarski(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_38,plain,(
    ! [X68,X69,X70] :
      ( ~ v1_relat_1(X69)
      | ~ v5_relat_1(X69,X68)
      | ~ r2_hidden(X70,k2_relat_1(X69))
      | r2_hidden(X70,X68) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t202_relat_1])])])).

fof(c_0_39,plain,(
    ! [X71,X72] :
      ( ~ v1_relat_1(X72)
      | ~ v1_funct_1(X72)
      | ~ r2_hidden(X71,k1_relat_1(X72))
      | r2_hidden(k1_funct_1(X72,X71),k2_relat_1(X72)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_1])])).

fof(c_0_40,plain,(
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

fof(c_0_41,plain,(
    ! [X84,X85,X86] :
      ( ( ~ v1_funct_2(X86,X84,X85)
        | X84 = k1_relset_1(X84,X85,X86)
        | X85 = k1_xboole_0
        | ~ m1_subset_1(X86,k1_zfmisc_1(k2_zfmisc_1(X84,X85))) )
      & ( X84 != k1_relset_1(X84,X85,X86)
        | v1_funct_2(X86,X84,X85)
        | X85 = k1_xboole_0
        | ~ m1_subset_1(X86,k1_zfmisc_1(k2_zfmisc_1(X84,X85))) )
      & ( ~ v1_funct_2(X86,X84,X85)
        | X84 = k1_relset_1(X84,X85,X86)
        | X84 != k1_xboole_0
        | ~ m1_subset_1(X86,k1_zfmisc_1(k2_zfmisc_1(X84,X85))) )
      & ( X84 != k1_relset_1(X84,X85,X86)
        | v1_funct_2(X86,X84,X85)
        | X84 != k1_xboole_0
        | ~ m1_subset_1(X86,k1_zfmisc_1(k2_zfmisc_1(X84,X85))) )
      & ( ~ v1_funct_2(X86,X84,X85)
        | X86 = k1_xboole_0
        | X84 = k1_xboole_0
        | X85 != k1_xboole_0
        | ~ m1_subset_1(X86,k1_zfmisc_1(k2_zfmisc_1(X84,X85))) )
      & ( X86 != k1_xboole_0
        | v1_funct_2(X86,X84,X85)
        | X84 = k1_xboole_0
        | X85 != k1_xboole_0
        | ~ m1_subset_1(X86,k1_zfmisc_1(k2_zfmisc_1(X84,X85))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_42,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_2(esk6_0,esk3_0,k1_tarski(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_45,plain,(
    ! [X73,X74] :
      ( ~ r2_hidden(X73,X74)
      | ~ r1_tarski(X74,X73) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_46,plain,(
    ! [X11] : r1_tarski(k1_xboole_0,X11) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_47,plain,
    ( X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36])).

cnf(c_0_48,plain,
    ( r2_hidden(X3,X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ r2_hidden(X3,k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_50,plain,(
    ! [X78,X79,X80] :
      ( ( v4_relat_1(X80,X78)
        | ~ m1_subset_1(X80,k1_zfmisc_1(k2_zfmisc_1(X78,X79))) )
      & ( v5_relat_1(X80,X79)
        | ~ m1_subset_1(X80,k1_zfmisc_1(k2_zfmisc_1(X78,X79))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_51,plain,(
    ! [X75,X76,X77] :
      ( ~ m1_subset_1(X77,k1_zfmisc_1(k2_zfmisc_1(X75,X76)))
      | v1_relat_1(X77) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X5,X6,X7,X8,X9,X10,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_53,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_54,negated_conjecture,
    ( k1_relset_1(esk3_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk6_0) = k1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_55,negated_conjecture,
    ( v1_funct_2(esk6_0,esk3_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36])).

cnf(c_0_56,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_57,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_58,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_59,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | ~ v1_funct_1(X1)
    | ~ v5_relat_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_60,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_61,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_52])])).

cnf(c_0_63,negated_conjecture,
    ( k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = k1_xboole_0
    | k1_relat_1(esk6_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_43]),c_0_54]),c_0_55])])).

cnf(c_0_64,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_65,plain,
    ( k1_funct_1(X1,X2) = X3
    | ~ v1_funct_1(X1)
    | ~ v5_relat_1(X1,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( v5_relat_1(esk6_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_43])).

cnf(c_0_67,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_68,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_43])).

cnf(c_0_69,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk3_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( k1_funct_1(esk6_0,esk5_0) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_71,negated_conjecture,
    ( k1_funct_1(esk6_0,X1) = esk4_0
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_68]),c_0_69])])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:03:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.029 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t65_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>(r2_hidden(X3,X1)=>k1_funct_1(X4,X3)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 0.13/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.38  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.13/0.38  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.13/0.38  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.13/0.38  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.13/0.38  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.13/0.38  fof(t202_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v5_relat_1(X2,X1))=>![X3]:(r2_hidden(X3,k2_relat_1(X2))=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t202_relat_1)).
% 0.13/0.38  fof(t12_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r2_hidden(X1,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X1),k2_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 0.13/0.38  fof(d6_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:(X9=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)<=>![X10]:(r2_hidden(X10,X9)<=>~((((((((X10!=X1&X10!=X2)&X10!=X3)&X10!=X4)&X10!=X5)&X10!=X6)&X10!=X7)&X10!=X8)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_enumset1)).
% 0.13/0.38  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.13/0.38  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.13/0.38  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.13/0.38  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.13/0.38  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.13/0.38  fof(c_0_18, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>(r2_hidden(X3,X1)=>k1_funct_1(X4,X3)=X2))), inference(assume_negation,[status(cth)],[t65_funct_2])).
% 0.13/0.38  fof(c_0_19, negated_conjecture, (((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk3_0,k1_tarski(esk4_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_tarski(esk4_0)))))&(r2_hidden(esk5_0,esk3_0)&k1_funct_1(esk6_0,esk5_0)!=esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.13/0.38  fof(c_0_20, plain, ![X19]:k2_tarski(X19,X19)=k1_tarski(X19), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.38  fof(c_0_21, plain, ![X20, X21]:k1_enumset1(X20,X20,X21)=k2_tarski(X20,X21), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.38  fof(c_0_22, plain, ![X22, X23, X24]:k2_enumset1(X22,X22,X23,X24)=k1_enumset1(X22,X23,X24), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.38  fof(c_0_23, plain, ![X25, X26, X27, X28]:k3_enumset1(X25,X25,X26,X27,X28)=k2_enumset1(X25,X26,X27,X28), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.38  fof(c_0_24, plain, ![X29, X30, X31, X32, X33]:k4_enumset1(X29,X29,X30,X31,X32,X33)=k3_enumset1(X29,X30,X31,X32,X33), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.13/0.38  fof(c_0_25, plain, ![X34, X35, X36, X37, X38, X39]:k5_enumset1(X34,X34,X35,X36,X37,X38,X39)=k4_enumset1(X34,X35,X36,X37,X38,X39), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.13/0.38  fof(c_0_26, plain, ![X40, X41, X42, X43, X44, X45, X46]:k6_enumset1(X40,X40,X41,X42,X43,X44,X45,X46)=k5_enumset1(X40,X41,X42,X43,X44,X45,X46), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.13/0.38  fof(c_0_27, plain, ![X12, X13, X14, X15, X16, X17]:(((~r2_hidden(X14,X13)|X14=X12|X13!=k1_tarski(X12))&(X15!=X12|r2_hidden(X15,X13)|X13!=k1_tarski(X12)))&((~r2_hidden(esk1_2(X16,X17),X17)|esk1_2(X16,X17)!=X16|X17=k1_tarski(X16))&(r2_hidden(esk1_2(X16,X17),X17)|esk1_2(X16,X17)=X16|X17=k1_tarski(X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.13/0.38  fof(c_0_28, plain, ![X81, X82, X83]:(~m1_subset_1(X83,k1_zfmisc_1(k2_zfmisc_1(X81,X82)))|k1_relset_1(X81,X82,X83)=k1_relat_1(X83)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_tarski(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_30, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_31, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_32, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_33, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_34, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.38  cnf(c_0_35, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.38  cnf(c_0_36, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.38  cnf(c_0_37, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.38  fof(c_0_38, plain, ![X68, X69, X70]:(~v1_relat_1(X69)|~v5_relat_1(X69,X68)|(~r2_hidden(X70,k2_relat_1(X69))|r2_hidden(X70,X68))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t202_relat_1])])])).
% 0.13/0.38  fof(c_0_39, plain, ![X71, X72]:(~v1_relat_1(X72)|~v1_funct_1(X72)|(~r2_hidden(X71,k1_relat_1(X72))|r2_hidden(k1_funct_1(X72,X71),k2_relat_1(X72)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_1])])).
% 0.13/0.38  fof(c_0_40, plain, ![X47, X48, X49, X50, X51, X52, X53, X54, X55, X56, X57, X58, X59, X60, X61, X62, X63, X64, X65, X66]:(((~r2_hidden(X56,X55)|(X56=X47|X56=X48|X56=X49|X56=X50|X56=X51|X56=X52|X56=X53|X56=X54)|X55!=k6_enumset1(X47,X48,X49,X50,X51,X52,X53,X54))&((((((((X57!=X47|r2_hidden(X57,X55)|X55!=k6_enumset1(X47,X48,X49,X50,X51,X52,X53,X54))&(X57!=X48|r2_hidden(X57,X55)|X55!=k6_enumset1(X47,X48,X49,X50,X51,X52,X53,X54)))&(X57!=X49|r2_hidden(X57,X55)|X55!=k6_enumset1(X47,X48,X49,X50,X51,X52,X53,X54)))&(X57!=X50|r2_hidden(X57,X55)|X55!=k6_enumset1(X47,X48,X49,X50,X51,X52,X53,X54)))&(X57!=X51|r2_hidden(X57,X55)|X55!=k6_enumset1(X47,X48,X49,X50,X51,X52,X53,X54)))&(X57!=X52|r2_hidden(X57,X55)|X55!=k6_enumset1(X47,X48,X49,X50,X51,X52,X53,X54)))&(X57!=X53|r2_hidden(X57,X55)|X55!=k6_enumset1(X47,X48,X49,X50,X51,X52,X53,X54)))&(X57!=X54|r2_hidden(X57,X55)|X55!=k6_enumset1(X47,X48,X49,X50,X51,X52,X53,X54))))&(((((((((esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66)!=X58|~r2_hidden(esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)|X66=k6_enumset1(X58,X59,X60,X61,X62,X63,X64,X65))&(esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66)!=X59|~r2_hidden(esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)|X66=k6_enumset1(X58,X59,X60,X61,X62,X63,X64,X65)))&(esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66)!=X60|~r2_hidden(esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)|X66=k6_enumset1(X58,X59,X60,X61,X62,X63,X64,X65)))&(esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66)!=X61|~r2_hidden(esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)|X66=k6_enumset1(X58,X59,X60,X61,X62,X63,X64,X65)))&(esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66)!=X62|~r2_hidden(esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)|X66=k6_enumset1(X58,X59,X60,X61,X62,X63,X64,X65)))&(esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66)!=X63|~r2_hidden(esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)|X66=k6_enumset1(X58,X59,X60,X61,X62,X63,X64,X65)))&(esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66)!=X64|~r2_hidden(esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)|X66=k6_enumset1(X58,X59,X60,X61,X62,X63,X64,X65)))&(esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66)!=X65|~r2_hidden(esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)|X66=k6_enumset1(X58,X59,X60,X61,X62,X63,X64,X65)))&(r2_hidden(esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66),X66)|(esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66)=X58|esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66)=X59|esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66)=X60|esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66)=X61|esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66)=X62|esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66)=X63|esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66)=X64|esk2_9(X58,X59,X60,X61,X62,X63,X64,X65,X66)=X65)|X66=k6_enumset1(X58,X59,X60,X61,X62,X63,X64,X65)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).
% 0.13/0.38  fof(c_0_41, plain, ![X84, X85, X86]:((((~v1_funct_2(X86,X84,X85)|X84=k1_relset_1(X84,X85,X86)|X85=k1_xboole_0|~m1_subset_1(X86,k1_zfmisc_1(k2_zfmisc_1(X84,X85))))&(X84!=k1_relset_1(X84,X85,X86)|v1_funct_2(X86,X84,X85)|X85=k1_xboole_0|~m1_subset_1(X86,k1_zfmisc_1(k2_zfmisc_1(X84,X85)))))&((~v1_funct_2(X86,X84,X85)|X84=k1_relset_1(X84,X85,X86)|X84!=k1_xboole_0|~m1_subset_1(X86,k1_zfmisc_1(k2_zfmisc_1(X84,X85))))&(X84!=k1_relset_1(X84,X85,X86)|v1_funct_2(X86,X84,X85)|X84!=k1_xboole_0|~m1_subset_1(X86,k1_zfmisc_1(k2_zfmisc_1(X84,X85))))))&((~v1_funct_2(X86,X84,X85)|X86=k1_xboole_0|X84=k1_xboole_0|X85!=k1_xboole_0|~m1_subset_1(X86,k1_zfmisc_1(k2_zfmisc_1(X84,X85))))&(X86!=k1_xboole_0|v1_funct_2(X86,X84,X85)|X84=k1_xboole_0|X85!=k1_xboole_0|~m1_subset_1(X86,k1_zfmisc_1(k2_zfmisc_1(X84,X85)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.13/0.38  cnf(c_0_42, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.38  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35]), c_0_36])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (v1_funct_2(esk6_0,esk3_0,k1_tarski(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  fof(c_0_45, plain, ![X73, X74]:(~r2_hidden(X73,X74)|~r1_tarski(X74,X73)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.13/0.38  fof(c_0_46, plain, ![X11]:r1_tarski(k1_xboole_0,X11), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.13/0.38  cnf(c_0_47, plain, (X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35]), c_0_36])).
% 0.13/0.38  cnf(c_0_48, plain, (r2_hidden(X3,X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~r2_hidden(X3,k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.38  cnf(c_0_49, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.38  fof(c_0_50, plain, ![X78, X79, X80]:((v4_relat_1(X80,X78)|~m1_subset_1(X80,k1_zfmisc_1(k2_zfmisc_1(X78,X79))))&(v5_relat_1(X80,X79)|~m1_subset_1(X80,k1_zfmisc_1(k2_zfmisc_1(X78,X79))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.13/0.38  fof(c_0_51, plain, ![X75, X76, X77]:(~m1_subset_1(X77,k1_zfmisc_1(k2_zfmisc_1(X75,X76)))|v1_relat_1(X77)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.13/0.38  cnf(c_0_52, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X5,X6,X7,X8,X9,X10,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.38  cnf(c_0_53, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.13/0.38  cnf(c_0_54, negated_conjecture, (k1_relset_1(esk3_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk6_0)=k1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.13/0.38  cnf(c_0_55, negated_conjecture, (v1_funct_2(esk6_0,esk3_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35]), c_0_36])).
% 0.13/0.38  cnf(c_0_56, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.13/0.38  cnf(c_0_57, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.13/0.38  cnf(c_0_58, plain, (X1=X2|~r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_47])).
% 0.13/0.38  cnf(c_0_59, plain, (r2_hidden(k1_funct_1(X1,X2),X3)|~v1_funct_1(X1)|~v5_relat_1(X1,X3)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.13/0.38  cnf(c_0_60, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.13/0.38  cnf(c_0_61, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.13/0.38  cnf(c_0_62, plain, (r2_hidden(X1,k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_52])])).
% 0.13/0.38  cnf(c_0_63, negated_conjecture, (k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=k1_xboole_0|k1_relat_1(esk6_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_43]), c_0_54]), c_0_55])])).
% 0.13/0.38  cnf(c_0_64, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.13/0.38  cnf(c_0_65, plain, (k1_funct_1(X1,X2)=X3|~v1_funct_1(X1)|~v5_relat_1(X1,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.13/0.38  cnf(c_0_66, negated_conjecture, (v5_relat_1(esk6_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_60, c_0_43])).
% 0.13/0.38  cnf(c_0_67, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_68, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_61, c_0_43])).
% 0.13/0.38  cnf(c_0_69, negated_conjecture, (k1_relat_1(esk6_0)=esk3_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])).
% 0.13/0.38  cnf(c_0_70, negated_conjecture, (k1_funct_1(esk6_0,esk5_0)!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_71, negated_conjecture, (k1_funct_1(esk6_0,X1)=esk4_0|~r2_hidden(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), c_0_68]), c_0_69])])).
% 0.13/0.38  cnf(c_0_72, negated_conjecture, (r2_hidden(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_73, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 74
% 0.13/0.38  # Proof object clause steps            : 37
% 0.13/0.38  # Proof object formula steps           : 37
% 0.13/0.38  # Proof object conjectures             : 17
% 0.13/0.38  # Proof object clause conjectures      : 14
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 22
% 0.13/0.38  # Proof object initial formulas used   : 18
% 0.13/0.38  # Proof object generating inferences   : 10
% 0.13/0.38  # Proof object simplifying inferences  : 34
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 18
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 48
% 0.13/0.38  # Removed in clause preprocessing      : 7
% 0.13/0.38  # Initial clauses in saturation        : 41
% 0.13/0.38  # Processed clauses                    : 194
% 0.13/0.38  # ...of these trivial                  : 4
% 0.13/0.38  # ...subsumed                          : 36
% 0.13/0.38  # ...remaining for further processing  : 154
% 0.13/0.38  # Other redundant clauses eliminated   : 34
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 15
% 0.13/0.38  # Backward-rewritten                   : 11
% 0.13/0.38  # Generated clauses                    : 297
% 0.13/0.38  # ...of the previous two non-trivial   : 258
% 0.13/0.38  # Contextual simplify-reflections      : 6
% 0.13/0.38  # Paramodulations                      : 273
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 34
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 73
% 0.13/0.38  #    Positive orientable unit clauses  : 20
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 2
% 0.13/0.38  #    Non-unit-clauses                  : 51
% 0.13/0.38  # Current number of unprocessed clauses: 115
% 0.13/0.38  # ...number of literals in the above   : 646
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 73
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 676
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 304
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 47
% 0.13/0.38  # Unit Clause-clause subsumption calls : 42
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 75
% 0.13/0.38  # BW rewrite match successes           : 4
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 8660
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.043 s
% 0.13/0.38  # System time              : 0.005 s
% 0.13/0.38  # Total time               : 0.048 s
% 0.13/0.38  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
