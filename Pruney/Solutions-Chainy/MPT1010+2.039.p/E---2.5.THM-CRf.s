%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:05:16 EST 2020

% Result     : Theorem 0.60s
% Output     : CNFRefutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 817 expanded)
%              Number of clauses        :   66 ( 318 expanded)
%              Number of leaves         :   23 ( 241 expanded)
%              Depth                    :   15
%              Number of atoms          :  271 (1400 expanded)
%              Number of equality atoms :  120 ( 800 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   1 average)

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

fof(t202_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1) )
     => ! [X3] :
          ( r2_hidden(X3,k2_relat_1(X2))
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t202_relat_1)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

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

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t20_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    <=> X1 != X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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

fof(t12_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => r2_hidden(k1_funct_1(X2,X1),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,k1_tarski(X2))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
       => ( r2_hidden(X3,X1)
         => k1_funct_1(X4,X3) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t65_funct_2])).

fof(c_0_24,negated_conjecture,
    ( v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk3_0,k1_tarski(esk4_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_tarski(esk4_0))))
    & r2_hidden(esk5_0,esk3_0)
    & k1_funct_1(esk6_0,esk5_0) != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

fof(c_0_25,plain,(
    ! [X27] : k2_tarski(X27,X27) = k1_tarski(X27) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_26,plain,(
    ! [X28,X29] : k1_enumset1(X28,X28,X29) = k2_tarski(X28,X29) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_27,plain,(
    ! [X30,X31,X32] : k2_enumset1(X30,X30,X31,X32) = k1_enumset1(X30,X31,X32) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_28,plain,(
    ! [X33,X34,X35,X36] : k3_enumset1(X33,X33,X34,X35,X36) = k2_enumset1(X33,X34,X35,X36) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_29,plain,(
    ! [X37,X38,X39,X40,X41] : k4_enumset1(X37,X37,X38,X39,X40,X41) = k3_enumset1(X37,X38,X39,X40,X41) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_30,plain,(
    ! [X42,X43,X44,X45,X46,X47] : k5_enumset1(X42,X42,X43,X44,X45,X46,X47) = k4_enumset1(X42,X43,X44,X45,X46,X47) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_31,plain,(
    ! [X48,X49,X50,X51,X52,X53,X54] : k6_enumset1(X48,X48,X49,X50,X51,X52,X53,X54) = k5_enumset1(X48,X49,X50,X51,X52,X53,X54) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_32,plain,(
    ! [X57,X58,X59] :
      ( ~ v1_relat_1(X58)
      | ~ v5_relat_1(X58,X57)
      | ~ r2_hidden(X59,k2_relat_1(X58))
      | r2_hidden(X59,X57) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t202_relat_1])])])).

fof(c_0_33,plain,(
    ! [X11,X12] :
      ( ( ~ r2_hidden(esk1_2(X11,X12),X11)
        | ~ r2_hidden(esk1_2(X11,X12),X12)
        | X11 = X12 )
      & ( r2_hidden(esk1_2(X11,X12),X11)
        | r2_hidden(esk1_2(X11,X12),X12)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

fof(c_0_34,plain,(
    ! [X67,X68,X69] :
      ( ( v4_relat_1(X69,X67)
        | ~ m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(X67,X68))) )
      & ( v5_relat_1(X69,X68)
        | ~ m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(X67,X68))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_tarski(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_43,plain,(
    ! [X64,X65,X66] :
      ( ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65)))
      | v1_relat_1(X66) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_44,plain,(
    ! [X20,X21,X22,X23,X24,X25] :
      ( ( ~ r2_hidden(X22,X21)
        | X22 = X20
        | X21 != k1_tarski(X20) )
      & ( X23 != X20
        | r2_hidden(X23,X21)
        | X21 != k1_tarski(X20) )
      & ( ~ r2_hidden(esk2_2(X24,X25),X25)
        | esk2_2(X24,X25) != X24
        | X25 = k1_tarski(X24) )
      & ( r2_hidden(esk2_2(X24,X25),X25)
        | esk2_2(X24,X25) = X24
        | X25 = k1_tarski(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_45,plain,
    ( r2_hidden(X3,X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ r2_hidden(X3,k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_46,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(esk1_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_47,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_49,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_50,plain,(
    ! [X17] : k4_xboole_0(X17,k1_xboole_0) = X17 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_51,plain,(
    ! [X14,X15] : k4_xboole_0(X14,X15) = k5_xboole_0(X14,k3_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_52,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,plain,
    ( k2_relat_1(X1) = X2
    | r2_hidden(esk1_2(k2_relat_1(X1),X2),X2)
    | r2_hidden(esk1_2(k2_relat_1(X1),X2),X3)
    | ~ v5_relat_1(X1,X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( v5_relat_1(esk6_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_48])).

fof(c_0_56,plain,(
    ! [X55,X56] :
      ( ( k4_xboole_0(k1_tarski(X55),k1_tarski(X56)) != k1_tarski(X55)
        | X55 != X56 )
      & ( X55 = X56
        | k4_xboole_0(k1_tarski(X55),k1_tarski(X56)) = k1_tarski(X55) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).

fof(c_0_57,plain,(
    ! [X18,X19] : k4_xboole_0(X18,k4_xboole_0(X18,X19)) = k3_xboole_0(X18,X19) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_58,plain,(
    ! [X8,X9,X10] :
      ( ( ~ r2_hidden(X8,X9)
        | ~ r2_hidden(X8,X10)
        | ~ r2_hidden(X8,k5_xboole_0(X9,X10)) )
      & ( r2_hidden(X8,X9)
        | r2_hidden(X8,X10)
        | ~ r2_hidden(X8,k5_xboole_0(X9,X10)) )
      & ( ~ r2_hidden(X8,X9)
        | r2_hidden(X8,X10)
        | r2_hidden(X8,k5_xboole_0(X9,X10)) )
      & ( ~ r2_hidden(X8,X10)
        | r2_hidden(X8,X9)
        | r2_hidden(X8,k5_xboole_0(X9,X10)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

cnf(c_0_59,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_60,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_61,plain,(
    ! [X62,X63] :
      ( ~ r2_hidden(X62,X63)
      | ~ r1_tarski(X63,X62) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_62,plain,(
    ! [X16] : r1_tarski(k1_xboole_0,X16) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_63,plain,
    ( X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_64,negated_conjecture,
    ( k2_relat_1(esk6_0) = X1
    | r2_hidden(esk1_2(k2_relat_1(esk6_0),X1),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))
    | r2_hidden(esk1_2(k2_relat_1(esk6_0),X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_66,plain,
    ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) != k1_tarski(X1)
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_67,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_68,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_69,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_70,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_71,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_72,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_63])).

cnf(c_0_73,negated_conjecture,
    ( k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = k2_relat_1(esk6_0)
    | r2_hidden(esk1_2(k2_relat_1(esk6_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(ef,[status(thm)],[c_0_64])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_75,plain,
    ( X1 != X2
    | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_60]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_42]),c_0_42])).

cnf(c_0_76,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_60]),c_0_60])).

cnf(c_0_77,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,k5_xboole_0(X3,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_78,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,k1_xboole_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_79,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_80,plain,
    ( X1 = X2
    | ~ r2_hidden(esk1_2(X1,X2),X1)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_81,negated_conjecture,
    ( esk1_2(k2_relat_1(esk6_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) = esk4_0
    | k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = k2_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_82,plain,
    ( r2_hidden(X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_74])])).

cnf(c_0_83,negated_conjecture,
    ( esk1_2(k2_relat_1(esk6_0),X1) = esk4_0
    | k2_relat_1(esk6_0) = X1
    | r2_hidden(esk1_2(k2_relat_1(esk6_0),X1),X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_64])).

fof(c_0_84,plain,(
    ! [X70,X71,X72] :
      ( ~ m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X70,X71)))
      | k1_relset_1(X70,X71,X72) = k1_relat_1(X72) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_85,plain,
    ( k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(er,[status(thm)],[c_0_75])).

cnf(c_0_86,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k3_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_69])).

cnf(c_0_87,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_69]),c_0_78])).

cnf(c_0_88,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk1_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_79,c_0_46])).

cnf(c_0_89,negated_conjecture,
    ( k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = k2_relat_1(esk6_0)
    | ~ r2_hidden(esk4_0,k2_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82])])).

cnf(c_0_90,negated_conjecture,
    ( esk1_2(k2_relat_1(esk6_0),k1_xboole_0) = esk4_0
    | k2_relat_1(esk6_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_79,c_0_83])).

fof(c_0_91,plain,(
    ! [X73,X74,X75] :
      ( ( ~ v1_funct_2(X75,X73,X74)
        | X73 = k1_relset_1(X73,X74,X75)
        | X74 = k1_xboole_0
        | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74))) )
      & ( X73 != k1_relset_1(X73,X74,X75)
        | v1_funct_2(X75,X73,X74)
        | X74 = k1_xboole_0
        | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74))) )
      & ( ~ v1_funct_2(X75,X73,X74)
        | X73 = k1_relset_1(X73,X74,X75)
        | X73 != k1_xboole_0
        | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74))) )
      & ( X73 != k1_relset_1(X73,X74,X75)
        | v1_funct_2(X75,X73,X74)
        | X73 != k1_xboole_0
        | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74))) )
      & ( ~ v1_funct_2(X75,X73,X74)
        | X75 = k1_xboole_0
        | X73 = k1_xboole_0
        | X74 != k1_xboole_0
        | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74))) )
      & ( X75 != k1_xboole_0
        | v1_funct_2(X75,X73,X74)
        | X73 = k1_xboole_0
        | X74 != k1_xboole_0
        | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_92,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_93,negated_conjecture,
    ( v1_funct_2(esk6_0,esk3_0,k1_tarski(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_94,plain,
    ( k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_xboole_0) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_95,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_96,negated_conjecture,
    ( X1 = esk4_0
    | ~ r2_hidden(esk4_0,k2_relat_1(esk6_0))
    | ~ r2_hidden(X1,k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_89])).

cnf(c_0_97,negated_conjecture,
    ( k2_relat_1(esk6_0) = k1_xboole_0
    | r2_hidden(esk4_0,k2_relat_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_90]),c_0_79])).

fof(c_0_98,plain,(
    ! [X60,X61] :
      ( ~ v1_relat_1(X61)
      | ~ v1_funct_1(X61)
      | ~ r2_hidden(X60,k1_relat_1(X61))
      | r2_hidden(k1_funct_1(X61,X60),k2_relat_1(X61)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_1])])).

cnf(c_0_99,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_100,negated_conjecture,
    ( k1_relset_1(esk3_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk6_0) = k1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_92,c_0_48])).

cnf(c_0_101,negated_conjecture,
    ( v1_funct_2(esk6_0,esk3_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_102,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_103,negated_conjecture,
    ( k2_relat_1(esk6_0) = k1_xboole_0
    | X1 = esk4_0
    | ~ r2_hidden(X1,k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_104,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_105,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_106,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk3_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_48]),c_0_100]),c_0_101])]),c_0_102])).

cnf(c_0_107,negated_conjecture,
    ( k1_funct_1(esk6_0,esk5_0) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_108,negated_conjecture,
    ( k1_funct_1(esk6_0,X1) = esk4_0
    | k2_relat_1(esk6_0) = k1_xboole_0
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_105]),c_0_55]),c_0_106])])).

cnf(c_0_109,negated_conjecture,
    ( r2_hidden(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_110,negated_conjecture,
    ( k2_relat_1(esk6_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_109])])).

cnf(c_0_111,negated_conjecture,
    ( ~ r2_hidden(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_110]),c_0_105]),c_0_55]),c_0_106])]),c_0_79])).

cnf(c_0_112,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_109,c_0_111]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:03:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.60/0.85  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.60/0.85  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.60/0.85  #
% 0.60/0.85  # Preprocessing time       : 0.029 s
% 0.60/0.85  
% 0.60/0.85  # Proof found!
% 0.60/0.85  # SZS status Theorem
% 0.60/0.85  # SZS output start CNFRefutation
% 0.60/0.85  fof(t65_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>(r2_hidden(X3,X1)=>k1_funct_1(X4,X3)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 0.60/0.85  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.60/0.85  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.60/0.85  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.60/0.85  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.60/0.85  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.60/0.85  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.60/0.85  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.60/0.85  fof(t202_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v5_relat_1(X2,X1))=>![X3]:(r2_hidden(X3,k2_relat_1(X2))=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t202_relat_1)).
% 0.60/0.85  fof(t2_tarski, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)<=>r2_hidden(X3,X2))=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 0.60/0.85  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.60/0.85  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.60/0.85  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.60/0.85  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.60/0.85  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.60/0.85  fof(t20_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 0.60/0.85  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.60/0.85  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 0.60/0.85  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.60/0.85  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.60/0.85  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.60/0.85  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.60/0.85  fof(t12_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r2_hidden(X1,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X1),k2_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 0.60/0.85  fof(c_0_23, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>(r2_hidden(X3,X1)=>k1_funct_1(X4,X3)=X2))), inference(assume_negation,[status(cth)],[t65_funct_2])).
% 0.60/0.85  fof(c_0_24, negated_conjecture, (((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk3_0,k1_tarski(esk4_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_tarski(esk4_0)))))&(r2_hidden(esk5_0,esk3_0)&k1_funct_1(esk6_0,esk5_0)!=esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 0.60/0.85  fof(c_0_25, plain, ![X27]:k2_tarski(X27,X27)=k1_tarski(X27), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.60/0.85  fof(c_0_26, plain, ![X28, X29]:k1_enumset1(X28,X28,X29)=k2_tarski(X28,X29), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.60/0.85  fof(c_0_27, plain, ![X30, X31, X32]:k2_enumset1(X30,X30,X31,X32)=k1_enumset1(X30,X31,X32), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.60/0.85  fof(c_0_28, plain, ![X33, X34, X35, X36]:k3_enumset1(X33,X33,X34,X35,X36)=k2_enumset1(X33,X34,X35,X36), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.60/0.85  fof(c_0_29, plain, ![X37, X38, X39, X40, X41]:k4_enumset1(X37,X37,X38,X39,X40,X41)=k3_enumset1(X37,X38,X39,X40,X41), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.60/0.85  fof(c_0_30, plain, ![X42, X43, X44, X45, X46, X47]:k5_enumset1(X42,X42,X43,X44,X45,X46,X47)=k4_enumset1(X42,X43,X44,X45,X46,X47), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.60/0.85  fof(c_0_31, plain, ![X48, X49, X50, X51, X52, X53, X54]:k6_enumset1(X48,X48,X49,X50,X51,X52,X53,X54)=k5_enumset1(X48,X49,X50,X51,X52,X53,X54), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.60/0.85  fof(c_0_32, plain, ![X57, X58, X59]:(~v1_relat_1(X58)|~v5_relat_1(X58,X57)|(~r2_hidden(X59,k2_relat_1(X58))|r2_hidden(X59,X57))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t202_relat_1])])])).
% 0.60/0.85  fof(c_0_33, plain, ![X11, X12]:((~r2_hidden(esk1_2(X11,X12),X11)|~r2_hidden(esk1_2(X11,X12),X12)|X11=X12)&(r2_hidden(esk1_2(X11,X12),X11)|r2_hidden(esk1_2(X11,X12),X12)|X11=X12)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).
% 0.60/0.85  fof(c_0_34, plain, ![X67, X68, X69]:((v4_relat_1(X69,X67)|~m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(X67,X68))))&(v5_relat_1(X69,X68)|~m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(X67,X68))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.60/0.85  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_tarski(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.60/0.85  cnf(c_0_36, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.60/0.85  cnf(c_0_37, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.60/0.85  cnf(c_0_38, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.60/0.85  cnf(c_0_39, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.60/0.85  cnf(c_0_40, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.60/0.85  cnf(c_0_41, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.60/0.85  cnf(c_0_42, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.60/0.85  fof(c_0_43, plain, ![X64, X65, X66]:(~m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65)))|v1_relat_1(X66)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.60/0.85  fof(c_0_44, plain, ![X20, X21, X22, X23, X24, X25]:(((~r2_hidden(X22,X21)|X22=X20|X21!=k1_tarski(X20))&(X23!=X20|r2_hidden(X23,X21)|X21!=k1_tarski(X20)))&((~r2_hidden(esk2_2(X24,X25),X25)|esk2_2(X24,X25)!=X24|X25=k1_tarski(X24))&(r2_hidden(esk2_2(X24,X25),X25)|esk2_2(X24,X25)=X24|X25=k1_tarski(X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.60/0.85  cnf(c_0_45, plain, (r2_hidden(X3,X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~r2_hidden(X3,k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.60/0.85  cnf(c_0_46, plain, (r2_hidden(esk1_2(X1,X2),X1)|r2_hidden(esk1_2(X1,X2),X2)|X1=X2), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.60/0.85  cnf(c_0_47, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.60/0.85  cnf(c_0_48, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42])).
% 0.60/0.85  cnf(c_0_49, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.60/0.85  fof(c_0_50, plain, ![X17]:k4_xboole_0(X17,k1_xboole_0)=X17, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.60/0.85  fof(c_0_51, plain, ![X14, X15]:k4_xboole_0(X14,X15)=k5_xboole_0(X14,k3_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.60/0.85  cnf(c_0_52, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.60/0.85  cnf(c_0_53, plain, (k2_relat_1(X1)=X2|r2_hidden(esk1_2(k2_relat_1(X1),X2),X2)|r2_hidden(esk1_2(k2_relat_1(X1),X2),X3)|~v5_relat_1(X1,X3)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.60/0.85  cnf(c_0_54, negated_conjecture, (v5_relat_1(esk6_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.60/0.85  cnf(c_0_55, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_49, c_0_48])).
% 0.60/0.85  fof(c_0_56, plain, ![X55, X56]:((k4_xboole_0(k1_tarski(X55),k1_tarski(X56))!=k1_tarski(X55)|X55!=X56)&(X55=X56|k4_xboole_0(k1_tarski(X55),k1_tarski(X56))=k1_tarski(X55))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).
% 0.60/0.85  fof(c_0_57, plain, ![X18, X19]:k4_xboole_0(X18,k4_xboole_0(X18,X19))=k3_xboole_0(X18,X19), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.60/0.85  fof(c_0_58, plain, ![X8, X9, X10]:(((~r2_hidden(X8,X9)|~r2_hidden(X8,X10)|~r2_hidden(X8,k5_xboole_0(X9,X10)))&(r2_hidden(X8,X9)|r2_hidden(X8,X10)|~r2_hidden(X8,k5_xboole_0(X9,X10))))&((~r2_hidden(X8,X9)|r2_hidden(X8,X10)|r2_hidden(X8,k5_xboole_0(X9,X10)))&(~r2_hidden(X8,X10)|r2_hidden(X8,X9)|r2_hidden(X8,k5_xboole_0(X9,X10))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 0.60/0.85  cnf(c_0_59, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.60/0.85  cnf(c_0_60, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.60/0.85  fof(c_0_61, plain, ![X62, X63]:(~r2_hidden(X62,X63)|~r1_tarski(X63,X62)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.60/0.85  fof(c_0_62, plain, ![X16]:r1_tarski(k1_xboole_0,X16), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.60/0.85  cnf(c_0_63, plain, (X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42])).
% 0.60/0.85  cnf(c_0_64, negated_conjecture, (k2_relat_1(esk6_0)=X1|r2_hidden(esk1_2(k2_relat_1(esk6_0),X1),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))|r2_hidden(esk1_2(k2_relat_1(esk6_0),X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])])).
% 0.60/0.85  cnf(c_0_65, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.60/0.85  cnf(c_0_66, plain, (k4_xboole_0(k1_tarski(X1),k1_tarski(X2))!=k1_tarski(X1)|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.60/0.85  cnf(c_0_67, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.60/0.85  cnf(c_0_68, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.60/0.85  cnf(c_0_69, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_59, c_0_60])).
% 0.60/0.85  cnf(c_0_70, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.60/0.85  cnf(c_0_71, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.60/0.85  cnf(c_0_72, plain, (X1=X2|~r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_63])).
% 0.60/0.85  cnf(c_0_73, negated_conjecture, (k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=k2_relat_1(esk6_0)|r2_hidden(esk1_2(k2_relat_1(esk6_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))), inference(ef,[status(thm)],[c_0_64])).
% 0.60/0.85  cnf(c_0_74, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42])).
% 0.60/0.85  cnf(c_0_75, plain, (X1!=X2|k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))!=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_60]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_42]), c_0_42])).
% 0.60/0.85  cnf(c_0_76, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_60]), c_0_60])).
% 0.60/0.85  cnf(c_0_77, plain, (r2_hidden(X1,X3)|r2_hidden(X1,k5_xboole_0(X3,X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.60/0.85  cnf(c_0_78, plain, (~r2_hidden(X1,k3_xboole_0(X2,k1_xboole_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.60/0.85  cnf(c_0_79, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.60/0.85  cnf(c_0_80, plain, (X1=X2|~r2_hidden(esk1_2(X1,X2),X1)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.60/0.85  cnf(c_0_81, negated_conjecture, (esk1_2(k2_relat_1(esk6_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))=esk4_0|k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=k2_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.60/0.85  cnf(c_0_82, plain, (r2_hidden(X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_74])])).
% 0.60/0.85  cnf(c_0_83, negated_conjecture, (esk1_2(k2_relat_1(esk6_0),X1)=esk4_0|k2_relat_1(esk6_0)=X1|r2_hidden(esk1_2(k2_relat_1(esk6_0),X1),X1)), inference(spm,[status(thm)],[c_0_72, c_0_64])).
% 0.60/0.85  fof(c_0_84, plain, ![X70, X71, X72]:(~m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X70,X71)))|k1_relset_1(X70,X71,X72)=k1_relat_1(X72)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.60/0.85  cnf(c_0_85, plain, (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))!=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)), inference(er,[status(thm)],[c_0_75])).
% 0.60/0.85  cnf(c_0_86, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k3_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_76, c_0_69])).
% 0.60/0.85  cnf(c_0_87, plain, (~r2_hidden(X1,k3_xboole_0(X2,k1_xboole_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_69]), c_0_78])).
% 0.60/0.85  cnf(c_0_88, plain, (k1_xboole_0=X1|r2_hidden(esk1_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_79, c_0_46])).
% 0.60/0.85  cnf(c_0_89, negated_conjecture, (k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=k2_relat_1(esk6_0)|~r2_hidden(esk4_0,k2_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_82])])).
% 0.60/0.85  cnf(c_0_90, negated_conjecture, (esk1_2(k2_relat_1(esk6_0),k1_xboole_0)=esk4_0|k2_relat_1(esk6_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_79, c_0_83])).
% 0.60/0.85  fof(c_0_91, plain, ![X73, X74, X75]:((((~v1_funct_2(X75,X73,X74)|X73=k1_relset_1(X73,X74,X75)|X74=k1_xboole_0|~m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74))))&(X73!=k1_relset_1(X73,X74,X75)|v1_funct_2(X75,X73,X74)|X74=k1_xboole_0|~m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74)))))&((~v1_funct_2(X75,X73,X74)|X73=k1_relset_1(X73,X74,X75)|X73!=k1_xboole_0|~m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74))))&(X73!=k1_relset_1(X73,X74,X75)|v1_funct_2(X75,X73,X74)|X73!=k1_xboole_0|~m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74))))))&((~v1_funct_2(X75,X73,X74)|X75=k1_xboole_0|X73=k1_xboole_0|X74!=k1_xboole_0|~m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74))))&(X75!=k1_xboole_0|v1_funct_2(X75,X73,X74)|X73=k1_xboole_0|X74!=k1_xboole_0|~m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.60/0.85  cnf(c_0_92, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.60/0.85  cnf(c_0_93, negated_conjecture, (v1_funct_2(esk6_0,esk3_0,k1_tarski(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.60/0.85  cnf(c_0_94, plain, (k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_xboole_0)!=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)), inference(rw,[status(thm)],[c_0_85, c_0_86])).
% 0.60/0.85  cnf(c_0_95, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.60/0.85  cnf(c_0_96, negated_conjecture, (X1=esk4_0|~r2_hidden(esk4_0,k2_relat_1(esk6_0))|~r2_hidden(X1,k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_72, c_0_89])).
% 0.60/0.85  cnf(c_0_97, negated_conjecture, (k2_relat_1(esk6_0)=k1_xboole_0|r2_hidden(esk4_0,k2_relat_1(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_90]), c_0_79])).
% 0.60/0.85  fof(c_0_98, plain, ![X60, X61]:(~v1_relat_1(X61)|~v1_funct_1(X61)|(~r2_hidden(X60,k1_relat_1(X61))|r2_hidden(k1_funct_1(X61,X60),k2_relat_1(X61)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_1])])).
% 0.60/0.85  cnf(c_0_99, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_91])).
% 0.60/0.85  cnf(c_0_100, negated_conjecture, (k1_relset_1(esk3_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk6_0)=k1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_92, c_0_48])).
% 0.60/0.85  cnf(c_0_101, negated_conjecture, (v1_funct_2(esk6_0,esk3_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42])).
% 0.60/0.85  cnf(c_0_102, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_94, c_0_95])).
% 0.60/0.85  cnf(c_0_103, negated_conjecture, (k2_relat_1(esk6_0)=k1_xboole_0|X1=esk4_0|~r2_hidden(X1,k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 0.60/0.85  cnf(c_0_104, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_98])).
% 0.60/0.85  cnf(c_0_105, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.60/0.85  cnf(c_0_106, negated_conjecture, (k1_relat_1(esk6_0)=esk3_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_48]), c_0_100]), c_0_101])]), c_0_102])).
% 0.60/0.85  cnf(c_0_107, negated_conjecture, (k1_funct_1(esk6_0,esk5_0)!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.60/0.85  cnf(c_0_108, negated_conjecture, (k1_funct_1(esk6_0,X1)=esk4_0|k2_relat_1(esk6_0)=k1_xboole_0|~r2_hidden(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_105]), c_0_55]), c_0_106])])).
% 0.60/0.85  cnf(c_0_109, negated_conjecture, (r2_hidden(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.60/0.85  cnf(c_0_110, negated_conjecture, (k2_relat_1(esk6_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_109])])).
% 0.60/0.85  cnf(c_0_111, negated_conjecture, (~r2_hidden(X1,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_110]), c_0_105]), c_0_55]), c_0_106])]), c_0_79])).
% 0.60/0.85  cnf(c_0_112, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_109, c_0_111]), ['proof']).
% 0.60/0.85  # SZS output end CNFRefutation
% 0.60/0.85  # Proof object total steps             : 113
% 0.60/0.85  # Proof object clause steps            : 66
% 0.60/0.85  # Proof object formula steps           : 47
% 0.60/0.85  # Proof object conjectures             : 27
% 0.60/0.85  # Proof object clause conjectures      : 24
% 0.60/0.85  # Proof object formula conjectures     : 3
% 0.60/0.85  # Proof object initial clauses used    : 30
% 0.60/0.85  # Proof object initial formulas used   : 23
% 0.60/0.85  # Proof object generating inferences   : 23
% 0.60/0.85  # Proof object simplifying inferences  : 86
% 0.60/0.85  # Training examples: 0 positive, 0 negative
% 0.60/0.85  # Parsed axioms                        : 23
% 0.60/0.85  # Removed by relevancy pruning/SinE    : 0
% 0.60/0.85  # Initial clauses                      : 41
% 0.60/0.85  # Removed in clause preprocessing      : 8
% 0.60/0.85  # Initial clauses in saturation        : 33
% 0.60/0.85  # Processed clauses                    : 1535
% 0.60/0.85  # ...of these trivial                  : 13
% 0.60/0.85  # ...subsumed                          : 1056
% 0.60/0.85  # ...remaining for further processing  : 466
% 0.60/0.85  # Other redundant clauses eliminated   : 108
% 0.60/0.85  # Clauses deleted for lack of memory   : 0
% 0.60/0.85  # Backward-subsumed                    : 39
% 0.60/0.85  # Backward-rewritten                   : 119
% 0.60/0.85  # Generated clauses                    : 21989
% 0.60/0.85  # ...of the previous two non-trivial   : 20928
% 0.60/0.85  # Contextual simplify-reflections      : 12
% 0.60/0.85  # Paramodulations                      : 21749
% 0.60/0.85  # Factorizations                       : 128
% 0.60/0.85  # Equation resolutions                 : 109
% 0.60/0.85  # Propositional unsat checks           : 0
% 0.60/0.85  #    Propositional check models        : 0
% 0.60/0.85  #    Propositional check unsatisfiable : 0
% 0.60/0.85  #    Propositional clauses             : 0
% 0.60/0.85  #    Propositional clauses after purity: 0
% 0.60/0.85  #    Propositional unsat core size     : 0
% 0.60/0.85  #    Propositional preprocessing time  : 0.000
% 0.60/0.85  #    Propositional encoding time       : 0.000
% 0.60/0.85  #    Propositional solver time         : 0.000
% 0.60/0.85  #    Success case prop preproc time    : 0.000
% 0.60/0.85  #    Success case prop encoding time   : 0.000
% 0.60/0.85  #    Success case prop solver time     : 0.000
% 0.60/0.85  # Current number of processed clauses  : 296
% 0.60/0.85  #    Positive orientable unit clauses  : 23
% 0.60/0.85  #    Positive unorientable unit clauses: 0
% 0.60/0.85  #    Negative unit clauses             : 4
% 0.60/0.85  #    Non-unit-clauses                  : 269
% 0.60/0.85  # Current number of unprocessed clauses: 19129
% 0.60/0.85  # ...number of literals in the above   : 131436
% 0.60/0.85  # Current number of archived formulas  : 0
% 0.60/0.85  # Current number of archived clauses   : 171
% 0.60/0.85  # Clause-clause subsumption calls (NU) : 14028
% 0.60/0.85  # Rec. Clause-clause subsumption calls : 4856
% 0.60/0.85  # Non-unit clause-clause subsumptions  : 966
% 0.60/0.85  # Unit Clause-clause subsumption calls : 325
% 0.60/0.85  # Rewrite failures with RHS unbound    : 0
% 0.60/0.85  # BW rewrite match attempts            : 51
% 0.60/0.85  # BW rewrite match successes           : 36
% 0.60/0.85  # Condensation attempts                : 0
% 0.60/0.85  # Condensation successes               : 0
% 0.60/0.85  # Termbank termtop insertions          : 573618
% 0.60/0.85  
% 0.60/0.85  # -------------------------------------------------
% 0.60/0.85  # User time                : 0.486 s
% 0.60/0.85  # System time              : 0.018 s
% 0.60/0.85  # Total time               : 0.504 s
% 0.60/0.85  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
