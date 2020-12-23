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
% DateTime   : Thu Dec  3 10:52:14 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 246 expanded)
%              Number of clauses        :   42 (  99 expanded)
%              Number of leaves         :   20 (  68 expanded)
%              Depth                    :   13
%              Number of atoms          :  158 ( 451 expanded)
%              Number of equality atoms :   61 ( 222 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t205_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k1_relat_1(X2))
      <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(l27_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,X2)
     => r1_xboole_0(k1_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

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

fof(t21_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(d16_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(t187_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_xboole_0(X2,k1_relat_1(X1))
         => k7_relat_1(X1,X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t55_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r1_xboole_0(k2_tarski(X1,X2),X3)
        & r2_hidden(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t95_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k7_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X1,k1_relat_1(X2))
        <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t205_relat_1])).

fof(c_0_21,plain,(
    ! [X43,X44] :
      ( ~ v1_relat_1(X44)
      | k2_relat_1(k7_relat_1(X44,X43)) = k9_relat_1(X44,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_22,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & ( ~ r2_hidden(esk3_0,k1_relat_1(esk4_0))
      | k11_relat_1(esk4_0,esk3_0) = k1_xboole_0 )
    & ( r2_hidden(esk3_0,k1_relat_1(esk4_0))
      | k11_relat_1(esk4_0,esk3_0) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

fof(c_0_23,plain,(
    ! [X32,X33] :
      ( r2_hidden(X32,X33)
      | r1_xboole_0(k1_tarski(X32),X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).

fof(c_0_24,plain,(
    ! [X17] : k2_tarski(X17,X17) = k1_tarski(X17) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_25,plain,(
    ! [X18,X19] : k1_enumset1(X18,X18,X19) = k2_tarski(X18,X19) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_26,plain,(
    ! [X20,X21,X22] : k2_enumset1(X20,X20,X21,X22) = k1_enumset1(X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_27,plain,(
    ! [X23,X24,X25,X26] : k3_enumset1(X23,X23,X24,X25,X26) = k2_enumset1(X23,X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_28,plain,(
    ! [X27,X28,X29,X30,X31] : k4_enumset1(X27,X27,X28,X29,X30,X31) = k3_enumset1(X27,X28,X29,X30,X31) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_29,plain,(
    ! [X47] :
      ( ~ v1_relat_1(X47)
      | r1_tarski(X47,k2_zfmisc_1(k1_relat_1(X47),k2_relat_1(X47))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).

cnf(c_0_30,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_32,plain,(
    ! [X39,X40] :
      ( ~ v1_relat_1(X39)
      | k11_relat_1(X39,X40) = k9_relat_1(X39,k1_tarski(X40)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).

fof(c_0_33,plain,(
    ! [X45,X46] :
      ( ~ v1_relat_1(X45)
      | ~ r1_xboole_0(X46,k1_relat_1(X45))
      | k7_relat_1(X45,X46) = k1_xboole_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t187_relat_1])])])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk4_0,X1)) = k9_relat_1(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_42,plain,(
    ! [X41,X42] :
      ( ~ v1_relat_1(X41)
      | v1_relat_1(k7_relat_1(X41,X42)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_43,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( k7_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(k7_relat_1(esk4_0,X1),k2_zfmisc_1(k1_relat_1(k7_relat_1(esk4_0,X1)),k9_relat_1(esk4_0,X1)))
    | ~ v1_relat_1(k7_relat_1(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k4_enumset1(X2,X2,X2,X2,X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_49,negated_conjecture,
    ( k11_relat_1(esk4_0,esk3_0) = k1_xboole_0
    | ~ r2_hidden(esk3_0,k1_relat_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_50,plain,
    ( k7_relat_1(X1,k4_enumset1(X2,X2,X2,X2,X2,X2)) = k1_xboole_0
    | r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

fof(c_0_51,plain,(
    ! [X34,X35] :
      ( ( k2_zfmisc_1(X34,X35) != k1_xboole_0
        | X34 = k1_xboole_0
        | X35 = k1_xboole_0 )
      & ( X34 != k1_xboole_0
        | k2_zfmisc_1(X34,X35) = k1_xboole_0 )
      & ( X35 != k1_xboole_0
        | k2_zfmisc_1(X34,X35) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_52,plain,(
    ! [X36,X37,X38] :
      ( ~ r1_xboole_0(k2_tarski(X36,X37),X38)
      | ~ r2_hidden(X36,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_zfmisc_1])])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k7_relat_1(esk4_0,X1),k2_zfmisc_1(k1_relat_1(k7_relat_1(esk4_0,X1)),k9_relat_1(esk4_0,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_31])])).

cnf(c_0_54,negated_conjecture,
    ( k9_relat_1(esk4_0,k4_enumset1(X1,X1,X1,X1,X1,X1)) = k11_relat_1(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_31])).

cnf(c_0_55,negated_conjecture,
    ( k7_relat_1(esk4_0,k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) = k1_xboole_0
    | k11_relat_1(esk4_0,esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_31])])).

cnf(c_0_56,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_57,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_58,plain,
    ( ~ r1_xboole_0(k2_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_59,plain,(
    ! [X16] : r1_xboole_0(X16,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_60,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(k7_relat_1(esk4_0,k4_enumset1(X1,X1,X1,X1,X1,X1)),k2_zfmisc_1(k1_relat_1(k7_relat_1(esk4_0,k4_enumset1(X1,X1,X1,X1,X1,X1))),k11_relat_1(esk4_0,X1))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( k11_relat_1(esk4_0,esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_55]),c_0_56]),c_0_54])])).

cnf(c_0_63,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_57])).

cnf(c_0_64,plain,
    ( ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_65,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_66,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(k7_relat_1(esk4_0,k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])).

cnf(c_0_68,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

fof(c_0_69,plain,(
    ! [X14] :
      ( X14 = k1_xboole_0
      | r2_hidden(esk2_1(X14),X14) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_70,plain,(
    ! [X48,X49] :
      ( ( k7_relat_1(X49,X48) != k1_xboole_0
        | r1_xboole_0(k1_relat_1(X49),X48)
        | ~ v1_relat_1(X49) )
      & ( ~ r1_xboole_0(k1_relat_1(X49),X48)
        | k7_relat_1(X49,X48) = k1_xboole_0
        | ~ v1_relat_1(X49) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_relat_1])])])).

cnf(c_0_71,negated_conjecture,
    ( ~ r2_hidden(X1,k7_relat_1(esk4_0,k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68])).

cnf(c_0_72,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

fof(c_0_73,plain,(
    ! [X12,X13] :
      ( ~ r1_xboole_0(X12,X13)
      | r1_xboole_0(X13,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_74,plain,
    ( r1_xboole_0(k1_relat_1(X1),X2)
    | k7_relat_1(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_75,negated_conjecture,
    ( k7_relat_1(esk4_0,k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_76,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_77,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(esk4_0),k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_31])])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk3_0,k1_relat_1(esk4_0))
    | k11_relat_1(esk4_0,esk3_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_79,negated_conjecture,
    ( r1_xboole_0(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(esk3_0,k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_62])])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_79]),c_0_80])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:22:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.43  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.20/0.43  # and selection function SelectCQArNTNpEqFirst.
% 0.20/0.43  #
% 0.20/0.43  # Preprocessing time       : 0.050 s
% 0.20/0.43  # Presaturation interreduction done
% 0.20/0.43  
% 0.20/0.43  # Proof found!
% 0.20/0.43  # SZS status Theorem
% 0.20/0.43  # SZS output start CNFRefutation
% 0.20/0.43  fof(t205_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 0.20/0.43  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.20/0.43  fof(l27_zfmisc_1, axiom, ![X1, X2]:(~(r2_hidden(X1,X2))=>r1_xboole_0(k1_tarski(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 0.20/0.43  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.43  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.43  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.43  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.43  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.43  fof(t21_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 0.20/0.43  fof(d16_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 0.20/0.43  fof(t187_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_xboole_0(X2,k1_relat_1(X1))=>k7_relat_1(X1,X2)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 0.20/0.43  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.20/0.43  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.20/0.43  fof(t55_zfmisc_1, axiom, ![X1, X2, X3]:~((r1_xboole_0(k2_tarski(X1,X2),X3)&r2_hidden(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 0.20/0.43  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.20/0.43  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.20/0.43  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.43  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.20/0.43  fof(t95_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(k7_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 0.20/0.43  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.20/0.43  fof(c_0_20, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t205_relat_1])).
% 0.20/0.43  fof(c_0_21, plain, ![X43, X44]:(~v1_relat_1(X44)|k2_relat_1(k7_relat_1(X44,X43))=k9_relat_1(X44,X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.20/0.43  fof(c_0_22, negated_conjecture, (v1_relat_1(esk4_0)&((~r2_hidden(esk3_0,k1_relat_1(esk4_0))|k11_relat_1(esk4_0,esk3_0)=k1_xboole_0)&(r2_hidden(esk3_0,k1_relat_1(esk4_0))|k11_relat_1(esk4_0,esk3_0)!=k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.20/0.43  fof(c_0_23, plain, ![X32, X33]:(r2_hidden(X32,X33)|r1_xboole_0(k1_tarski(X32),X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).
% 0.20/0.43  fof(c_0_24, plain, ![X17]:k2_tarski(X17,X17)=k1_tarski(X17), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.43  fof(c_0_25, plain, ![X18, X19]:k1_enumset1(X18,X18,X19)=k2_tarski(X18,X19), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.43  fof(c_0_26, plain, ![X20, X21, X22]:k2_enumset1(X20,X20,X21,X22)=k1_enumset1(X20,X21,X22), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.43  fof(c_0_27, plain, ![X23, X24, X25, X26]:k3_enumset1(X23,X23,X24,X25,X26)=k2_enumset1(X23,X24,X25,X26), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.43  fof(c_0_28, plain, ![X27, X28, X29, X30, X31]:k4_enumset1(X27,X27,X28,X29,X30,X31)=k3_enumset1(X27,X28,X29,X30,X31), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.43  fof(c_0_29, plain, ![X47]:(~v1_relat_1(X47)|r1_tarski(X47,k2_zfmisc_1(k1_relat_1(X47),k2_relat_1(X47)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).
% 0.20/0.43  cnf(c_0_30, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.43  cnf(c_0_31, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.43  fof(c_0_32, plain, ![X39, X40]:(~v1_relat_1(X39)|k11_relat_1(X39,X40)=k9_relat_1(X39,k1_tarski(X40))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).
% 0.20/0.43  fof(c_0_33, plain, ![X45, X46]:(~v1_relat_1(X45)|(~r1_xboole_0(X46,k1_relat_1(X45))|k7_relat_1(X45,X46)=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t187_relat_1])])])).
% 0.20/0.43  cnf(c_0_34, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.43  cnf(c_0_35, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.43  cnf(c_0_36, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.43  cnf(c_0_37, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.43  cnf(c_0_38, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.43  cnf(c_0_39, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.43  cnf(c_0_40, plain, (r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.43  cnf(c_0_41, negated_conjecture, (k2_relat_1(k7_relat_1(esk4_0,X1))=k9_relat_1(esk4_0,X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.43  fof(c_0_42, plain, ![X41, X42]:(~v1_relat_1(X41)|v1_relat_1(k7_relat_1(X41,X42))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.20/0.43  cnf(c_0_43, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.43  cnf(c_0_44, plain, (k7_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.43  cnf(c_0_45, plain, (r2_hidden(X1,X2)|r1_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.20/0.43  cnf(c_0_46, negated_conjecture, (r1_tarski(k7_relat_1(esk4_0,X1),k2_zfmisc_1(k1_relat_1(k7_relat_1(esk4_0,X1)),k9_relat_1(esk4_0,X1)))|~v1_relat_1(k7_relat_1(esk4_0,X1))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.43  cnf(c_0_47, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.43  cnf(c_0_48, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k4_enumset1(X2,X2,X2,X2,X2,X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.20/0.43  cnf(c_0_49, negated_conjecture, (k11_relat_1(esk4_0,esk3_0)=k1_xboole_0|~r2_hidden(esk3_0,k1_relat_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.43  cnf(c_0_50, plain, (k7_relat_1(X1,k4_enumset1(X2,X2,X2,X2,X2,X2))=k1_xboole_0|r2_hidden(X2,k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.43  fof(c_0_51, plain, ![X34, X35]:((k2_zfmisc_1(X34,X35)!=k1_xboole_0|(X34=k1_xboole_0|X35=k1_xboole_0))&((X34!=k1_xboole_0|k2_zfmisc_1(X34,X35)=k1_xboole_0)&(X35!=k1_xboole_0|k2_zfmisc_1(X34,X35)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.20/0.43  fof(c_0_52, plain, ![X36, X37, X38]:(~r1_xboole_0(k2_tarski(X36,X37),X38)|~r2_hidden(X36,X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_zfmisc_1])])).
% 0.20/0.43  cnf(c_0_53, negated_conjecture, (r1_tarski(k7_relat_1(esk4_0,X1),k2_zfmisc_1(k1_relat_1(k7_relat_1(esk4_0,X1)),k9_relat_1(esk4_0,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_31])])).
% 0.20/0.43  cnf(c_0_54, negated_conjecture, (k9_relat_1(esk4_0,k4_enumset1(X1,X1,X1,X1,X1,X1))=k11_relat_1(esk4_0,X1)), inference(spm,[status(thm)],[c_0_48, c_0_31])).
% 0.20/0.43  cnf(c_0_55, negated_conjecture, (k7_relat_1(esk4_0,k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))=k1_xboole_0|k11_relat_1(esk4_0,esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_31])])).
% 0.20/0.43  cnf(c_0_56, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.20/0.43  cnf(c_0_57, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.43  cnf(c_0_58, plain, (~r1_xboole_0(k2_tarski(X1,X2),X3)|~r2_hidden(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.43  fof(c_0_59, plain, ![X16]:r1_xboole_0(X16,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.20/0.43  fof(c_0_60, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.43  cnf(c_0_61, negated_conjecture, (r1_tarski(k7_relat_1(esk4_0,k4_enumset1(X1,X1,X1,X1,X1,X1)),k2_zfmisc_1(k1_relat_1(k7_relat_1(esk4_0,k4_enumset1(X1,X1,X1,X1,X1,X1))),k11_relat_1(esk4_0,X1)))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.20/0.43  cnf(c_0_62, negated_conjecture, (k11_relat_1(esk4_0,esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_55]), c_0_56]), c_0_54])])).
% 0.20/0.43  cnf(c_0_63, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_57])).
% 0.20/0.43  cnf(c_0_64, plain, (~r2_hidden(X1,X3)|~r1_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X2),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.20/0.43  cnf(c_0_65, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.43  cnf(c_0_66, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.43  cnf(c_0_67, negated_conjecture, (r1_tarski(k7_relat_1(esk4_0,k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63])).
% 0.20/0.43  cnf(c_0_68, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.20/0.43  fof(c_0_69, plain, ![X14]:(X14=k1_xboole_0|r2_hidden(esk2_1(X14),X14)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.20/0.43  fof(c_0_70, plain, ![X48, X49]:((k7_relat_1(X49,X48)!=k1_xboole_0|r1_xboole_0(k1_relat_1(X49),X48)|~v1_relat_1(X49))&(~r1_xboole_0(k1_relat_1(X49),X48)|k7_relat_1(X49,X48)=k1_xboole_0|~v1_relat_1(X49))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_relat_1])])])).
% 0.20/0.43  cnf(c_0_71, negated_conjecture, (~r2_hidden(X1,k7_relat_1(esk4_0,k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68])).
% 0.20/0.43  cnf(c_0_72, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.20/0.43  fof(c_0_73, plain, ![X12, X13]:(~r1_xboole_0(X12,X13)|r1_xboole_0(X13,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.20/0.43  cnf(c_0_74, plain, (r1_xboole_0(k1_relat_1(X1),X2)|k7_relat_1(X1,X2)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.20/0.43  cnf(c_0_75, negated_conjecture, (k7_relat_1(esk4_0,k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.20/0.43  cnf(c_0_76, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.20/0.43  cnf(c_0_77, negated_conjecture, (r1_xboole_0(k1_relat_1(esk4_0),k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_31])])).
% 0.20/0.43  cnf(c_0_78, negated_conjecture, (r2_hidden(esk3_0,k1_relat_1(esk4_0))|k11_relat_1(esk4_0,esk3_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.43  cnf(c_0_79, negated_conjecture, (r1_xboole_0(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.20/0.43  cnf(c_0_80, negated_conjecture, (r2_hidden(esk3_0,k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_62])])).
% 0.20/0.43  cnf(c_0_81, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_79]), c_0_80])]), ['proof']).
% 0.20/0.43  # SZS output end CNFRefutation
% 0.20/0.43  # Proof object total steps             : 82
% 0.20/0.43  # Proof object clause steps            : 42
% 0.20/0.43  # Proof object formula steps           : 40
% 0.20/0.43  # Proof object conjectures             : 20
% 0.20/0.43  # Proof object clause conjectures      : 17
% 0.20/0.43  # Proof object formula conjectures     : 3
% 0.20/0.43  # Proof object initial clauses used    : 22
% 0.20/0.43  # Proof object initial formulas used   : 20
% 0.20/0.43  # Proof object generating inferences   : 15
% 0.20/0.43  # Proof object simplifying inferences  : 30
% 0.20/0.43  # Training examples: 0 positive, 0 negative
% 0.20/0.43  # Parsed axioms                        : 20
% 0.20/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.43  # Initial clauses                      : 28
% 0.20/0.43  # Removed in clause preprocessing      : 5
% 0.20/0.43  # Initial clauses in saturation        : 23
% 0.20/0.43  # Processed clauses                    : 299
% 0.20/0.43  # ...of these trivial                  : 3
% 0.20/0.43  # ...subsumed                          : 127
% 0.20/0.43  # ...remaining for further processing  : 169
% 0.20/0.43  # Other redundant clauses eliminated   : 2
% 0.20/0.43  # Clauses deleted for lack of memory   : 0
% 0.20/0.43  # Backward-subsumed                    : 9
% 0.20/0.43  # Backward-rewritten                   : 10
% 0.20/0.43  # Generated clauses                    : 684
% 0.20/0.43  # ...of the previous two non-trivial   : 582
% 0.20/0.43  # Contextual simplify-reflections      : 0
% 0.20/0.43  # Paramodulations                      : 624
% 0.20/0.43  # Factorizations                       : 58
% 0.20/0.43  # Equation resolutions                 : 2
% 0.20/0.43  # Propositional unsat checks           : 0
% 0.20/0.43  #    Propositional check models        : 0
% 0.20/0.43  #    Propositional check unsatisfiable : 0
% 0.20/0.43  #    Propositional clauses             : 0
% 0.20/0.43  #    Propositional clauses after purity: 0
% 0.20/0.43  #    Propositional unsat core size     : 0
% 0.20/0.43  #    Propositional preprocessing time  : 0.000
% 0.20/0.43  #    Propositional encoding time       : 0.000
% 0.20/0.43  #    Propositional solver time         : 0.000
% 0.20/0.43  #    Success case prop preproc time    : 0.000
% 0.20/0.43  #    Success case prop encoding time   : 0.000
% 0.20/0.43  #    Success case prop solver time     : 0.000
% 0.20/0.43  # Current number of processed clauses  : 125
% 0.20/0.43  #    Positive orientable unit clauses  : 33
% 0.20/0.43  #    Positive unorientable unit clauses: 0
% 0.20/0.43  #    Negative unit clauses             : 1
% 0.20/0.43  #    Non-unit-clauses                  : 91
% 0.20/0.43  # Current number of unprocessed clauses: 312
% 0.20/0.43  # ...number of literals in the above   : 1297
% 0.20/0.43  # Current number of archived formulas  : 0
% 0.20/0.43  # Current number of archived clauses   : 47
% 0.20/0.43  # Clause-clause subsumption calls (NU) : 2879
% 0.20/0.43  # Rec. Clause-clause subsumption calls : 1157
% 0.20/0.43  # Non-unit clause-clause subsumptions  : 133
% 0.20/0.43  # Unit Clause-clause subsumption calls : 38
% 0.20/0.43  # Rewrite failures with RHS unbound    : 0
% 0.20/0.43  # BW rewrite match attempts            : 20
% 0.20/0.43  # BW rewrite match successes           : 6
% 0.20/0.43  # Condensation attempts                : 0
% 0.20/0.43  # Condensation successes               : 0
% 0.20/0.43  # Termbank termtop insertions          : 15113
% 0.20/0.44  
% 0.20/0.44  # -------------------------------------------------
% 0.20/0.44  # User time                : 0.086 s
% 0.20/0.44  # System time              : 0.004 s
% 0.20/0.44  # Total time               : 0.091 s
% 0.20/0.44  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
