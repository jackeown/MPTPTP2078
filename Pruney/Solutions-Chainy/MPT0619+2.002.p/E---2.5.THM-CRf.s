%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:51 EST 2020

% Result     : Theorem 0.92s
% Output     : CNFRefutation 0.92s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 806 expanded)
%              Number of clauses        :   63 ( 310 expanded)
%              Number of leaves         :   19 ( 228 expanded)
%              Depth                    :   14
%              Number of atoms          :  288 (1662 expanded)
%              Number of equality atoms :  113 ( 964 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t14_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( k1_relat_1(X2) = k1_tarski(X1)
       => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(d16_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

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

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(d5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( X2 = k2_relat_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                  & X3 = k1_funct_1(X1,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(t41_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_tarski(X2)
        & X1 != k1_xboole_0
        & ! [X3] :
            ~ ( r2_hidden(X3,X1)
              & X3 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(t205_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k1_relat_1(X2))
      <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(t128_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),X4))
    <=> ( X1 = X3
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t21_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( k1_relat_1(X2) = k1_tarski(X1)
         => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t14_funct_1])).

fof(c_0_20,plain,(
    ! [X46,X47] :
      ( ~ v1_relat_1(X46)
      | k11_relat_1(X46,X47) = k9_relat_1(X46,k1_tarski(X47)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).

fof(c_0_21,plain,(
    ! [X15] : k2_tarski(X15,X15) = k1_tarski(X15) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_22,plain,(
    ! [X16,X17] : k1_enumset1(X16,X16,X17) = k2_tarski(X16,X17) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_23,plain,(
    ! [X18,X19,X20] : k2_enumset1(X18,X18,X19,X20) = k1_enumset1(X18,X19,X20) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_24,plain,(
    ! [X21,X22,X23,X24] : k3_enumset1(X21,X21,X22,X23,X24) = k2_enumset1(X21,X22,X23,X24) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_25,plain,(
    ! [X25,X26,X27,X28,X29] : k4_enumset1(X25,X25,X26,X27,X28,X29) = k3_enumset1(X25,X26,X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_26,plain,(
    ! [X30,X31,X32,X33,X34,X35] : k5_enumset1(X30,X30,X31,X32,X33,X34,X35) = k4_enumset1(X30,X31,X32,X33,X34,X35) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_27,plain,(
    ! [X40,X41,X42] :
      ( ( r2_hidden(X40,X42)
        | ~ r1_tarski(k2_tarski(X40,X41),X42) )
      & ( r2_hidden(X41,X42)
        | ~ r1_tarski(k2_tarski(X40,X41),X42) )
      & ( ~ r2_hidden(X40,X42)
        | ~ r2_hidden(X41,X42)
        | r1_tarski(k2_tarski(X40,X41),X42) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

fof(c_0_28,negated_conjecture,
    ( v1_relat_1(esk8_0)
    & v1_funct_1(esk8_0)
    & k1_relat_1(esk8_0) = k1_tarski(esk7_0)
    & k2_relat_1(esk8_0) != k1_tarski(k1_funct_1(esk8_0,esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

cnf(c_0_29,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_36,plain,(
    ! [X48] :
      ( ~ v1_relat_1(X48)
      | k9_relat_1(X48,k1_relat_1(X48)) = k2_relat_1(X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X3,X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( k1_relat_1(esk8_0) = k1_tarski(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_39,plain,(
    ! [X13,X14] :
      ( ( r1_tarski(X13,X14)
        | X13 != X14 )
      & ( r1_tarski(X14,X13)
        | X13 != X14 )
      & ( ~ r1_tarski(X13,X14)
        | ~ r1_tarski(X14,X13)
        | X13 = X14 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_40,plain,(
    ! [X54] :
      ( ~ v1_relat_1(X54)
      | k10_relat_1(X54,k2_relat_1(X54)) = k1_relat_1(X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

fof(c_0_41,plain,(
    ! [X58,X59,X60,X62,X63,X64,X66] :
      ( ( r2_hidden(esk4_3(X58,X59,X60),k1_relat_1(X58))
        | ~ r2_hidden(X60,X59)
        | X59 != k2_relat_1(X58)
        | ~ v1_relat_1(X58)
        | ~ v1_funct_1(X58) )
      & ( X60 = k1_funct_1(X58,esk4_3(X58,X59,X60))
        | ~ r2_hidden(X60,X59)
        | X59 != k2_relat_1(X58)
        | ~ v1_relat_1(X58)
        | ~ v1_funct_1(X58) )
      & ( ~ r2_hidden(X63,k1_relat_1(X58))
        | X62 != k1_funct_1(X58,X63)
        | r2_hidden(X62,X59)
        | X59 != k2_relat_1(X58)
        | ~ v1_relat_1(X58)
        | ~ v1_funct_1(X58) )
      & ( ~ r2_hidden(esk5_2(X58,X64),X64)
        | ~ r2_hidden(X66,k1_relat_1(X58))
        | esk5_2(X58,X64) != k1_funct_1(X58,X66)
        | X64 = k2_relat_1(X58)
        | ~ v1_relat_1(X58)
        | ~ v1_funct_1(X58) )
      & ( r2_hidden(esk6_2(X58,X64),k1_relat_1(X58))
        | r2_hidden(esk5_2(X58,X64),X64)
        | X64 = k2_relat_1(X58)
        | ~ v1_relat_1(X58)
        | ~ v1_funct_1(X58) )
      & ( esk5_2(X58,X64) = k1_funct_1(X58,esk6_2(X58,X64))
        | r2_hidden(esk5_2(X58,X64),X64)
        | X64 = k2_relat_1(X58)
        | ~ v1_relat_1(X58)
        | ~ v1_funct_1(X58) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_42,plain,(
    ! [X43,X44] :
      ( ( r2_hidden(esk2_2(X43,X44),X43)
        | X43 = k1_tarski(X44)
        | X43 = k1_xboole_0 )
      & ( esk2_2(X43,X44) != X44
        | X43 = k1_tarski(X44)
        | X43 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_zfmisc_1])])])])).

cnf(c_0_43,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_45,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k5_enumset1(X3,X3,X3,X3,X3,X3,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_47,negated_conjecture,
    ( k1_relat_1(esk8_0) = k5_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_49,plain,(
    ! [X49,X50,X51,X53] :
      ( ( r2_hidden(esk3_3(X49,X50,X51),k2_relat_1(X51))
        | ~ r2_hidden(X49,k10_relat_1(X51,X50))
        | ~ v1_relat_1(X51) )
      & ( r2_hidden(k4_tarski(X49,esk3_3(X49,X50,X51)),X51)
        | ~ r2_hidden(X49,k10_relat_1(X51,X50))
        | ~ v1_relat_1(X51) )
      & ( r2_hidden(esk3_3(X49,X50,X51),X50)
        | ~ r2_hidden(X49,k10_relat_1(X51,X50))
        | ~ v1_relat_1(X51) )
      & ( ~ r2_hidden(X53,k2_relat_1(X51))
        | ~ r2_hidden(k4_tarski(X49,X53),X51)
        | ~ r2_hidden(X53,X50)
        | r2_hidden(X49,k10_relat_1(X51,X50))
        | ~ v1_relat_1(X51) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

cnf(c_0_50,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_51,plain,(
    ! [X55,X56] :
      ( ( ~ r2_hidden(X55,k1_relat_1(X56))
        | k11_relat_1(X56,X55) != k1_xboole_0
        | ~ v1_relat_1(X56) )
      & ( k11_relat_1(X56,X55) = k1_xboole_0
        | r2_hidden(X55,k1_relat_1(X56))
        | ~ v1_relat_1(X56) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t205_relat_1])])])).

cnf(c_0_52,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_53,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | X1 = k1_tarski(X2)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_54,negated_conjecture,
    ( k9_relat_1(esk8_0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) = k11_relat_1(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_55,negated_conjecture,
    ( k9_relat_1(esk8_0,k1_relat_1(esk8_0)) = k2_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_44])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk7_0,X1)
    | ~ r1_tarski(k1_relat_1(esk8_0),X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_58,plain,
    ( X1 = k1_funct_1(X2,esk4_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_59,plain,(
    ! [X36,X37,X38,X39] :
      ( ( X36 = X38
        | ~ r2_hidden(k4_tarski(X36,X37),k2_zfmisc_1(k1_tarski(X38),X39)) )
      & ( r2_hidden(X37,X39)
        | ~ r2_hidden(k4_tarski(X36,X37),k2_zfmisc_1(k1_tarski(X38),X39)) )
      & ( X36 != X38
        | ~ r2_hidden(X37,X39)
        | r2_hidden(k4_tarski(X36,X37),k2_zfmisc_1(k1_tarski(X38),X39)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t128_zfmisc_1])])])).

fof(c_0_60,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_61,plain,(
    ! [X57] :
      ( ~ v1_relat_1(X57)
      | r1_tarski(X57,k2_zfmisc_1(k1_relat_1(X57),k2_relat_1(X57))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).

cnf(c_0_62,plain,
    ( r2_hidden(k4_tarski(X1,esk3_3(X1,X2,X3)),X3)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_63,negated_conjecture,
    ( k10_relat_1(esk8_0,k2_relat_1(esk8_0)) = k1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_44])).

cnf(c_0_64,plain,
    ( k11_relat_1(X1,X2) = k1_xboole_0
    | r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_65,plain,
    ( r2_hidden(esk4_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_66,plain,
    ( X1 = k1_xboole_0
    | X1 = k5_enumset1(X2,X2,X2,X2,X2,X2,X2)
    | r2_hidden(esk2_2(X1,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_67,plain,
    ( ~ r2_hidden(X1,k1_relat_1(X2))
    | k11_relat_1(X2,X1) != k1_xboole_0
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_68,negated_conjecture,
    ( k11_relat_1(esk8_0,esk7_0) = k2_relat_1(esk8_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_47]),c_0_55])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk7_0,k1_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_70,plain,
    ( k1_funct_1(X1,esk4_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_58])).

cnf(c_0_71,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_tarski(X2),X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_72,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk3_3(X1,k2_relat_1(esk8_0),esk8_0)),esk8_0)
    | ~ r2_hidden(X1,k1_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_44])])).

cnf(c_0_75,negated_conjecture,
    ( k11_relat_1(esk8_0,X1) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_44])).

cnf(c_0_76,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_77,plain,
    ( k2_relat_1(X1) = k5_enumset1(X2,X2,X2,X2,X2,X2,X2)
    | k2_relat_1(X1) = k1_xboole_0
    | r2_hidden(esk4_3(X1,k2_relat_1(X1),esk2_2(k2_relat_1(X1),X2)),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_78,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_79,negated_conjecture,
    ( k2_relat_1(esk8_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_44]),c_0_69])])).

cnf(c_0_80,negated_conjecture,
    ( k2_relat_1(esk8_0) != k1_tarski(k1_funct_1(esk8_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_81,plain,
    ( k1_funct_1(X1,esk4_3(X1,k2_relat_1(X1),esk2_2(k2_relat_1(X1),X2))) = esk2_2(k2_relat_1(X1),X2)
    | k2_relat_1(X1) = k5_enumset1(X2,X2,X2,X2,X2,X2,X2)
    | k2_relat_1(X1) = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_66])).

cnf(c_0_82,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k5_enumset1(X2,X2,X2,X2,X2,X2,X2),X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_83,plain,
    ( r2_hidden(X1,k2_zfmisc_1(k1_relat_1(X2),k2_relat_1(X2)))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_84,negated_conjecture,
    ( k11_relat_1(esk8_0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(X1,esk3_3(X1,k2_relat_1(esk8_0),esk8_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_85,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_76])])).

cnf(c_0_86,negated_conjecture,
    ( k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = k2_relat_1(esk8_0)
    | r2_hidden(esk4_3(esk8_0,k2_relat_1(esk8_0),esk2_2(k2_relat_1(esk8_0),X1)),k1_relat_1(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_44])]),c_0_79])).

cnf(c_0_87,negated_conjecture,
    ( k2_relat_1(esk8_0) != k5_enumset1(k1_funct_1(esk8_0,esk7_0),k1_funct_1(esk8_0,esk7_0),k1_funct_1(esk8_0,esk7_0),k1_funct_1(esk8_0,esk7_0),k1_funct_1(esk8_0,esk7_0),k1_funct_1(esk8_0,esk7_0),k1_funct_1(esk8_0,esk7_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_88,negated_conjecture,
    ( k1_funct_1(esk8_0,esk4_3(esk8_0,k2_relat_1(esk8_0),esk2_2(k2_relat_1(esk8_0),X1))) = esk2_2(k2_relat_1(esk8_0),X1)
    | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = k2_relat_1(esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_78]),c_0_44])]),c_0_79])).

cnf(c_0_89,negated_conjecture,
    ( X1 = esk7_0
    | ~ r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_relat_1(esk8_0),X3)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_47])).

cnf(c_0_90,negated_conjecture,
    ( k11_relat_1(esk8_0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(X1,esk3_3(X1,k2_relat_1(esk8_0),esk8_0)),k2_zfmisc_1(k1_relat_1(esk8_0),k2_relat_1(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_44])])).

cnf(c_0_91,negated_conjecture,
    ( k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = k2_relat_1(esk8_0)
    | r2_hidden(k1_funct_1(esk8_0,esk4_3(esk8_0,k2_relat_1(esk8_0),esk2_2(k2_relat_1(esk8_0),X1))),k2_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_78]),c_0_44])])).

cnf(c_0_92,negated_conjecture,
    ( k1_funct_1(esk8_0,esk4_3(esk8_0,k2_relat_1(esk8_0),esk2_2(k2_relat_1(esk8_0),k1_funct_1(esk8_0,esk7_0)))) = esk2_2(k2_relat_1(esk8_0),k1_funct_1(esk8_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_93,negated_conjecture,
    ( k11_relat_1(esk8_0,X1) = k1_xboole_0
    | X1 = esk7_0 ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_94,negated_conjecture,
    ( r2_hidden(esk2_2(k2_relat_1(esk8_0),k1_funct_1(esk8_0,esk7_0)),k2_relat_1(esk8_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_87])).

cnf(c_0_95,negated_conjecture,
    ( X1 = esk7_0
    | ~ r2_hidden(X1,k1_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_93]),c_0_44])])).

cnf(c_0_96,negated_conjecture,
    ( r2_hidden(esk4_3(esk8_0,k2_relat_1(esk8_0),esk2_2(k2_relat_1(esk8_0),k1_funct_1(esk8_0,esk7_0))),k1_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_94]),c_0_78]),c_0_44])])).

cnf(c_0_97,plain,
    ( X1 = k1_tarski(X2)
    | X1 = k1_xboole_0
    | esk2_2(X1,X2) != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_98,negated_conjecture,
    ( esk4_3(esk8_0,k2_relat_1(esk8_0),esk2_2(k2_relat_1(esk8_0),k1_funct_1(esk8_0,esk7_0))) = esk7_0 ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_99,plain,
    ( X1 = k1_xboole_0
    | X1 = k5_enumset1(X2,X2,X2,X2,X2,X2,X2)
    | esk2_2(X1,X2) != X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97,c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_100,negated_conjecture,
    ( esk2_2(k2_relat_1(esk8_0),k1_funct_1(esk8_0,esk7_0)) = k1_funct_1(esk8_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_92,c_0_98])).

cnf(c_0_101,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_87]),c_0_79]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:37:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.92/1.08  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.92/1.08  # and selection function SelectCQArNTNpEqFirst.
% 0.92/1.08  #
% 0.92/1.08  # Preprocessing time       : 0.042 s
% 0.92/1.08  # Presaturation interreduction done
% 0.92/1.08  
% 0.92/1.08  # Proof found!
% 0.92/1.08  # SZS status Theorem
% 0.92/1.08  # SZS output start CNFRefutation
% 0.92/1.08  fof(t14_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 0.92/1.08  fof(d16_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 0.92/1.08  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.92/1.08  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.92/1.08  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.92/1.08  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.92/1.08  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.92/1.08  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.92/1.08  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.92/1.08  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 0.92/1.08  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.92/1.08  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 0.92/1.08  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 0.92/1.08  fof(t41_zfmisc_1, axiom, ![X1, X2]:~(((X1!=k1_tarski(X2)&X1!=k1_xboole_0)&![X3]:~((r2_hidden(X3,X1)&X3!=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 0.92/1.08  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 0.92/1.08  fof(t205_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 0.92/1.08  fof(t128_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),X4))<=>(X1=X3&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 0.92/1.08  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.92/1.08  fof(t21_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 0.92/1.08  fof(c_0_19, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1))))), inference(assume_negation,[status(cth)],[t14_funct_1])).
% 0.92/1.08  fof(c_0_20, plain, ![X46, X47]:(~v1_relat_1(X46)|k11_relat_1(X46,X47)=k9_relat_1(X46,k1_tarski(X47))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).
% 0.92/1.08  fof(c_0_21, plain, ![X15]:k2_tarski(X15,X15)=k1_tarski(X15), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.92/1.08  fof(c_0_22, plain, ![X16, X17]:k1_enumset1(X16,X16,X17)=k2_tarski(X16,X17), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.92/1.08  fof(c_0_23, plain, ![X18, X19, X20]:k2_enumset1(X18,X18,X19,X20)=k1_enumset1(X18,X19,X20), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.92/1.08  fof(c_0_24, plain, ![X21, X22, X23, X24]:k3_enumset1(X21,X21,X22,X23,X24)=k2_enumset1(X21,X22,X23,X24), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.92/1.08  fof(c_0_25, plain, ![X25, X26, X27, X28, X29]:k4_enumset1(X25,X25,X26,X27,X28,X29)=k3_enumset1(X25,X26,X27,X28,X29), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.92/1.08  fof(c_0_26, plain, ![X30, X31, X32, X33, X34, X35]:k5_enumset1(X30,X30,X31,X32,X33,X34,X35)=k4_enumset1(X30,X31,X32,X33,X34,X35), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.92/1.08  fof(c_0_27, plain, ![X40, X41, X42]:(((r2_hidden(X40,X42)|~r1_tarski(k2_tarski(X40,X41),X42))&(r2_hidden(X41,X42)|~r1_tarski(k2_tarski(X40,X41),X42)))&(~r2_hidden(X40,X42)|~r2_hidden(X41,X42)|r1_tarski(k2_tarski(X40,X41),X42))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.92/1.08  fof(c_0_28, negated_conjecture, ((v1_relat_1(esk8_0)&v1_funct_1(esk8_0))&(k1_relat_1(esk8_0)=k1_tarski(esk7_0)&k2_relat_1(esk8_0)!=k1_tarski(k1_funct_1(esk8_0,esk7_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.92/1.08  cnf(c_0_29, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.92/1.08  cnf(c_0_30, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.92/1.08  cnf(c_0_31, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.92/1.08  cnf(c_0_32, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.92/1.08  cnf(c_0_33, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.92/1.08  cnf(c_0_34, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.92/1.08  cnf(c_0_35, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.92/1.08  fof(c_0_36, plain, ![X48]:(~v1_relat_1(X48)|k9_relat_1(X48,k1_relat_1(X48))=k2_relat_1(X48)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.92/1.08  cnf(c_0_37, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X3,X1),X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.92/1.08  cnf(c_0_38, negated_conjecture, (k1_relat_1(esk8_0)=k1_tarski(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.92/1.08  fof(c_0_39, plain, ![X13, X14]:(((r1_tarski(X13,X14)|X13!=X14)&(r1_tarski(X14,X13)|X13!=X14))&(~r1_tarski(X13,X14)|~r1_tarski(X14,X13)|X13=X14)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.92/1.08  fof(c_0_40, plain, ![X54]:(~v1_relat_1(X54)|k10_relat_1(X54,k2_relat_1(X54))=k1_relat_1(X54)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.92/1.08  fof(c_0_41, plain, ![X58, X59, X60, X62, X63, X64, X66]:((((r2_hidden(esk4_3(X58,X59,X60),k1_relat_1(X58))|~r2_hidden(X60,X59)|X59!=k2_relat_1(X58)|(~v1_relat_1(X58)|~v1_funct_1(X58)))&(X60=k1_funct_1(X58,esk4_3(X58,X59,X60))|~r2_hidden(X60,X59)|X59!=k2_relat_1(X58)|(~v1_relat_1(X58)|~v1_funct_1(X58))))&(~r2_hidden(X63,k1_relat_1(X58))|X62!=k1_funct_1(X58,X63)|r2_hidden(X62,X59)|X59!=k2_relat_1(X58)|(~v1_relat_1(X58)|~v1_funct_1(X58))))&((~r2_hidden(esk5_2(X58,X64),X64)|(~r2_hidden(X66,k1_relat_1(X58))|esk5_2(X58,X64)!=k1_funct_1(X58,X66))|X64=k2_relat_1(X58)|(~v1_relat_1(X58)|~v1_funct_1(X58)))&((r2_hidden(esk6_2(X58,X64),k1_relat_1(X58))|r2_hidden(esk5_2(X58,X64),X64)|X64=k2_relat_1(X58)|(~v1_relat_1(X58)|~v1_funct_1(X58)))&(esk5_2(X58,X64)=k1_funct_1(X58,esk6_2(X58,X64))|r2_hidden(esk5_2(X58,X64),X64)|X64=k2_relat_1(X58)|(~v1_relat_1(X58)|~v1_funct_1(X58)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.92/1.08  fof(c_0_42, plain, ![X43, X44]:((r2_hidden(esk2_2(X43,X44),X43)|(X43=k1_tarski(X44)|X43=k1_xboole_0))&(esk2_2(X43,X44)!=X44|(X43=k1_tarski(X44)|X43=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_zfmisc_1])])])])).
% 0.92/1.08  cnf(c_0_43, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.92/1.08  cnf(c_0_44, negated_conjecture, (v1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.92/1.08  cnf(c_0_45, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.92/1.08  cnf(c_0_46, plain, (r2_hidden(X1,X2)|~r1_tarski(k5_enumset1(X3,X3,X3,X3,X3,X3,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.92/1.08  cnf(c_0_47, negated_conjecture, (k1_relat_1(esk8_0)=k5_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.92/1.08  cnf(c_0_48, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.92/1.08  fof(c_0_49, plain, ![X49, X50, X51, X53]:((((r2_hidden(esk3_3(X49,X50,X51),k2_relat_1(X51))|~r2_hidden(X49,k10_relat_1(X51,X50))|~v1_relat_1(X51))&(r2_hidden(k4_tarski(X49,esk3_3(X49,X50,X51)),X51)|~r2_hidden(X49,k10_relat_1(X51,X50))|~v1_relat_1(X51)))&(r2_hidden(esk3_3(X49,X50,X51),X50)|~r2_hidden(X49,k10_relat_1(X51,X50))|~v1_relat_1(X51)))&(~r2_hidden(X53,k2_relat_1(X51))|~r2_hidden(k4_tarski(X49,X53),X51)|~r2_hidden(X53,X50)|r2_hidden(X49,k10_relat_1(X51,X50))|~v1_relat_1(X51))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.92/1.08  cnf(c_0_50, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.92/1.08  fof(c_0_51, plain, ![X55, X56]:((~r2_hidden(X55,k1_relat_1(X56))|k11_relat_1(X56,X55)!=k1_xboole_0|~v1_relat_1(X56))&(k11_relat_1(X56,X55)=k1_xboole_0|r2_hidden(X55,k1_relat_1(X56))|~v1_relat_1(X56))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t205_relat_1])])])).
% 0.92/1.08  cnf(c_0_52, plain, (r2_hidden(esk4_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.92/1.08  cnf(c_0_53, plain, (r2_hidden(esk2_2(X1,X2),X1)|X1=k1_tarski(X2)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.92/1.08  cnf(c_0_54, negated_conjecture, (k9_relat_1(esk8_0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))=k11_relat_1(esk8_0,X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.92/1.08  cnf(c_0_55, negated_conjecture, (k9_relat_1(esk8_0,k1_relat_1(esk8_0))=k2_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_45, c_0_44])).
% 0.92/1.08  cnf(c_0_56, negated_conjecture, (r2_hidden(esk7_0,X1)|~r1_tarski(k1_relat_1(esk8_0),X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.92/1.08  cnf(c_0_57, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_48])).
% 0.92/1.08  cnf(c_0_58, plain, (X1=k1_funct_1(X2,esk4_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.92/1.08  fof(c_0_59, plain, ![X36, X37, X38, X39]:(((X36=X38|~r2_hidden(k4_tarski(X36,X37),k2_zfmisc_1(k1_tarski(X38),X39)))&(r2_hidden(X37,X39)|~r2_hidden(k4_tarski(X36,X37),k2_zfmisc_1(k1_tarski(X38),X39))))&(X36!=X38|~r2_hidden(X37,X39)|r2_hidden(k4_tarski(X36,X37),k2_zfmisc_1(k1_tarski(X38),X39)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t128_zfmisc_1])])])).
% 0.92/1.08  fof(c_0_60, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.92/1.08  fof(c_0_61, plain, ![X57]:(~v1_relat_1(X57)|r1_tarski(X57,k2_zfmisc_1(k1_relat_1(X57),k2_relat_1(X57)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).
% 0.92/1.08  cnf(c_0_62, plain, (r2_hidden(k4_tarski(X1,esk3_3(X1,X2,X3)),X3)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.92/1.08  cnf(c_0_63, negated_conjecture, (k10_relat_1(esk8_0,k2_relat_1(esk8_0))=k1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_50, c_0_44])).
% 0.92/1.08  cnf(c_0_64, plain, (k11_relat_1(X1,X2)=k1_xboole_0|r2_hidden(X2,k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.92/1.08  cnf(c_0_65, plain, (r2_hidden(esk4_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_52])).
% 0.92/1.08  cnf(c_0_66, plain, (X1=k1_xboole_0|X1=k5_enumset1(X2,X2,X2,X2,X2,X2,X2)|r2_hidden(esk2_2(X1,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.92/1.08  cnf(c_0_67, plain, (~r2_hidden(X1,k1_relat_1(X2))|k11_relat_1(X2,X1)!=k1_xboole_0|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.92/1.08  cnf(c_0_68, negated_conjecture, (k11_relat_1(esk8_0,esk7_0)=k2_relat_1(esk8_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_47]), c_0_55])).
% 0.92/1.08  cnf(c_0_69, negated_conjecture, (r2_hidden(esk7_0,k1_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.92/1.08  cnf(c_0_70, plain, (k1_funct_1(X1,esk4_3(X1,k2_relat_1(X1),X2))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_58])).
% 0.92/1.08  cnf(c_0_71, plain, (X1=X2|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_tarski(X2),X4))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.92/1.08  cnf(c_0_72, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.92/1.08  cnf(c_0_73, plain, (r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.92/1.08  cnf(c_0_74, negated_conjecture, (r2_hidden(k4_tarski(X1,esk3_3(X1,k2_relat_1(esk8_0),esk8_0)),esk8_0)|~r2_hidden(X1,k1_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_44])])).
% 0.92/1.08  cnf(c_0_75, negated_conjecture, (k11_relat_1(esk8_0,X1)=k1_xboole_0|r2_hidden(X1,k1_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_64, c_0_44])).
% 0.92/1.08  cnf(c_0_76, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.92/1.08  cnf(c_0_77, plain, (k2_relat_1(X1)=k5_enumset1(X2,X2,X2,X2,X2,X2,X2)|k2_relat_1(X1)=k1_xboole_0|r2_hidden(esk4_3(X1,k2_relat_1(X1),esk2_2(k2_relat_1(X1),X2)),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.92/1.08  cnf(c_0_78, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.92/1.08  cnf(c_0_79, negated_conjecture, (k2_relat_1(esk8_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_44]), c_0_69])])).
% 0.92/1.08  cnf(c_0_80, negated_conjecture, (k2_relat_1(esk8_0)!=k1_tarski(k1_funct_1(esk8_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.92/1.08  cnf(c_0_81, plain, (k1_funct_1(X1,esk4_3(X1,k2_relat_1(X1),esk2_2(k2_relat_1(X1),X2)))=esk2_2(k2_relat_1(X1),X2)|k2_relat_1(X1)=k5_enumset1(X2,X2,X2,X2,X2,X2,X2)|k2_relat_1(X1)=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_70, c_0_66])).
% 0.92/1.08  cnf(c_0_82, plain, (X1=X2|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k5_enumset1(X2,X2,X2,X2,X2,X2,X2),X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.92/1.08  cnf(c_0_83, plain, (r2_hidden(X1,k2_zfmisc_1(k1_relat_1(X2),k2_relat_1(X2)))|~v1_relat_1(X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.92/1.08  cnf(c_0_84, negated_conjecture, (k11_relat_1(esk8_0,X1)=k1_xboole_0|r2_hidden(k4_tarski(X1,esk3_3(X1,k2_relat_1(esk8_0),esk8_0)),esk8_0)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.92/1.08  cnf(c_0_85, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_76])])).
% 0.92/1.08  cnf(c_0_86, negated_conjecture, (k5_enumset1(X1,X1,X1,X1,X1,X1,X1)=k2_relat_1(esk8_0)|r2_hidden(esk4_3(esk8_0,k2_relat_1(esk8_0),esk2_2(k2_relat_1(esk8_0),X1)),k1_relat_1(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_44])]), c_0_79])).
% 0.92/1.08  cnf(c_0_87, negated_conjecture, (k2_relat_1(esk8_0)!=k5_enumset1(k1_funct_1(esk8_0,esk7_0),k1_funct_1(esk8_0,esk7_0),k1_funct_1(esk8_0,esk7_0),k1_funct_1(esk8_0,esk7_0),k1_funct_1(esk8_0,esk7_0),k1_funct_1(esk8_0,esk7_0),k1_funct_1(esk8_0,esk7_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.92/1.08  cnf(c_0_88, negated_conjecture, (k1_funct_1(esk8_0,esk4_3(esk8_0,k2_relat_1(esk8_0),esk2_2(k2_relat_1(esk8_0),X1)))=esk2_2(k2_relat_1(esk8_0),X1)|k5_enumset1(X1,X1,X1,X1,X1,X1,X1)=k2_relat_1(esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_78]), c_0_44])]), c_0_79])).
% 0.92/1.08  cnf(c_0_89, negated_conjecture, (X1=esk7_0|~r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_relat_1(esk8_0),X3))), inference(spm,[status(thm)],[c_0_82, c_0_47])).
% 0.92/1.08  cnf(c_0_90, negated_conjecture, (k11_relat_1(esk8_0,X1)=k1_xboole_0|r2_hidden(k4_tarski(X1,esk3_3(X1,k2_relat_1(esk8_0),esk8_0)),k2_zfmisc_1(k1_relat_1(esk8_0),k2_relat_1(esk8_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_44])])).
% 0.92/1.08  cnf(c_0_91, negated_conjecture, (k5_enumset1(X1,X1,X1,X1,X1,X1,X1)=k2_relat_1(esk8_0)|r2_hidden(k1_funct_1(esk8_0,esk4_3(esk8_0,k2_relat_1(esk8_0),esk2_2(k2_relat_1(esk8_0),X1))),k2_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_78]), c_0_44])])).
% 0.92/1.08  cnf(c_0_92, negated_conjecture, (k1_funct_1(esk8_0,esk4_3(esk8_0,k2_relat_1(esk8_0),esk2_2(k2_relat_1(esk8_0),k1_funct_1(esk8_0,esk7_0))))=esk2_2(k2_relat_1(esk8_0),k1_funct_1(esk8_0,esk7_0))), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.92/1.08  cnf(c_0_93, negated_conjecture, (k11_relat_1(esk8_0,X1)=k1_xboole_0|X1=esk7_0), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.92/1.08  cnf(c_0_94, negated_conjecture, (r2_hidden(esk2_2(k2_relat_1(esk8_0),k1_funct_1(esk8_0,esk7_0)),k2_relat_1(esk8_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_87])).
% 0.92/1.08  cnf(c_0_95, negated_conjecture, (X1=esk7_0|~r2_hidden(X1,k1_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_93]), c_0_44])])).
% 0.92/1.08  cnf(c_0_96, negated_conjecture, (r2_hidden(esk4_3(esk8_0,k2_relat_1(esk8_0),esk2_2(k2_relat_1(esk8_0),k1_funct_1(esk8_0,esk7_0))),k1_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_94]), c_0_78]), c_0_44])])).
% 0.92/1.08  cnf(c_0_97, plain, (X1=k1_tarski(X2)|X1=k1_xboole_0|esk2_2(X1,X2)!=X2), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.92/1.08  cnf(c_0_98, negated_conjecture, (esk4_3(esk8_0,k2_relat_1(esk8_0),esk2_2(k2_relat_1(esk8_0),k1_funct_1(esk8_0,esk7_0)))=esk7_0), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 0.92/1.08  cnf(c_0_99, plain, (X1=k1_xboole_0|X1=k5_enumset1(X2,X2,X2,X2,X2,X2,X2)|esk2_2(X1,X2)!=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97, c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.92/1.08  cnf(c_0_100, negated_conjecture, (esk2_2(k2_relat_1(esk8_0),k1_funct_1(esk8_0,esk7_0))=k1_funct_1(esk8_0,esk7_0)), inference(rw,[status(thm)],[c_0_92, c_0_98])).
% 0.92/1.08  cnf(c_0_101, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_87]), c_0_79]), ['proof']).
% 0.92/1.08  # SZS output end CNFRefutation
% 0.92/1.08  # Proof object total steps             : 102
% 0.92/1.08  # Proof object clause steps            : 63
% 0.92/1.08  # Proof object formula steps           : 39
% 0.92/1.08  # Proof object conjectures             : 32
% 0.92/1.08  # Proof object clause conjectures      : 29
% 0.92/1.08  # Proof object formula conjectures     : 3
% 0.92/1.08  # Proof object initial clauses used    : 26
% 0.92/1.08  # Proof object initial formulas used   : 19
% 0.92/1.08  # Proof object generating inferences   : 25
% 0.92/1.08  # Proof object simplifying inferences  : 72
% 0.92/1.08  # Training examples: 0 positive, 0 negative
% 0.92/1.08  # Parsed axioms                        : 19
% 0.92/1.08  # Removed by relevancy pruning/SinE    : 0
% 0.92/1.08  # Initial clauses                      : 40
% 0.92/1.08  # Removed in clause preprocessing      : 6
% 0.92/1.08  # Initial clauses in saturation        : 34
% 0.92/1.08  # Processed clauses                    : 1762
% 0.92/1.08  # ...of these trivial                  : 11
% 0.92/1.08  # ...subsumed                          : 379
% 0.92/1.08  # ...remaining for further processing  : 1372
% 0.92/1.08  # Other redundant clauses eliminated   : 7
% 0.92/1.08  # Clauses deleted for lack of memory   : 0
% 0.92/1.08  # Backward-subsumed                    : 6
% 0.92/1.08  # Backward-rewritten                   : 486
% 0.92/1.08  # Generated clauses                    : 38480
% 0.92/1.08  # ...of the previous two non-trivial   : 38184
% 0.92/1.08  # Contextual simplify-reflections      : 0
% 0.92/1.08  # Paramodulations                      : 38454
% 0.92/1.08  # Factorizations                       : 20
% 0.92/1.08  # Equation resolutions                 : 7
% 0.92/1.08  # Propositional unsat checks           : 0
% 0.92/1.08  #    Propositional check models        : 0
% 0.92/1.08  #    Propositional check unsatisfiable : 0
% 0.92/1.08  #    Propositional clauses             : 0
% 0.92/1.08  #    Propositional clauses after purity: 0
% 0.92/1.08  #    Propositional unsat core size     : 0
% 0.92/1.08  #    Propositional preprocessing time  : 0.000
% 0.92/1.08  #    Propositional encoding time       : 0.000
% 0.92/1.08  #    Propositional solver time         : 0.000
% 0.92/1.08  #    Success case prop preproc time    : 0.000
% 0.92/1.08  #    Success case prop encoding time   : 0.000
% 0.92/1.08  #    Success case prop solver time     : 0.000
% 0.92/1.08  # Current number of processed clauses  : 841
% 0.92/1.08  #    Positive orientable unit clauses  : 29
% 0.92/1.08  #    Positive unorientable unit clauses: 0
% 0.92/1.08  #    Negative unit clauses             : 3
% 0.92/1.08  #    Non-unit-clauses                  : 809
% 0.92/1.08  # Current number of unprocessed clauses: 36219
% 0.92/1.08  # ...number of literals in the above   : 126176
% 0.92/1.08  # Current number of archived formulas  : 0
% 0.92/1.08  # Current number of archived clauses   : 531
% 0.92/1.08  # Clause-clause subsumption calls (NU) : 144312
% 0.92/1.08  # Rec. Clause-clause subsumption calls : 80675
% 0.92/1.08  # Non-unit clause-clause subsumptions  : 383
% 0.92/1.08  # Unit Clause-clause subsumption calls : 2313
% 0.92/1.08  # Rewrite failures with RHS unbound    : 0
% 0.92/1.08  # BW rewrite match attempts            : 258
% 0.92/1.08  # BW rewrite match successes           : 7
% 0.92/1.08  # Condensation attempts                : 0
% 0.92/1.08  # Condensation successes               : 0
% 0.92/1.08  # Termbank termtop insertions          : 2581242
% 0.92/1.08  
% 0.92/1.08  # -------------------------------------------------
% 0.92/1.08  # User time                : 0.704 s
% 0.92/1.08  # System time              : 0.036 s
% 0.92/1.08  # Total time               : 0.740 s
% 0.92/1.08  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
