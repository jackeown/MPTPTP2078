%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:05:35 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 414 expanded)
%              Number of clauses        :   58 ( 178 expanded)
%              Number of leaves         :   22 ( 114 expanded)
%              Depth                    :   14
%              Number of atoms          :  317 ( 981 expanded)
%              Number of equality atoms :  158 ( 560 expanded)
%              Maximal formula depth    :   37 (   5 average)
%              Maximal clause size      :   52 (   2 average)
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

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

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

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(t35_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0 )
    <=> k3_zfmisc_1(X1,X2,X3) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

fof(t54_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4) = k4_zfmisc_1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_mcart_1)).

fof(d4_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(d4_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] :
      ( X7 = k4_enumset1(X1,X2,X3,X4,X5,X6)
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ~ ( X8 != X1
              & X8 != X2
              & X8 != X3
              & X8 != X4
              & X8 != X5
              & X8 != X6 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_enumset1)).

fof(t7_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_hidden(X3,X1)
       => ( X2 = k1_xboole_0
          | r2_hidden(k1_funct_1(X4,X3),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

fof(t12_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))
     => ( k1_mcart_1(X1) = X2
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,k1_tarski(X2))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
       => ( r2_hidden(X3,X1)
         => k1_funct_1(X4,X3) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t65_funct_2])).

fof(c_0_23,plain,(
    ! [X61,X62,X63,X64,X65,X66] :
      ( ( ~ r2_hidden(X63,X62)
        | r1_tarski(X63,X61)
        | X62 != k1_zfmisc_1(X61) )
      & ( ~ r1_tarski(X64,X61)
        | r2_hidden(X64,X62)
        | X62 != k1_zfmisc_1(X61) )
      & ( ~ r2_hidden(esk4_2(X65,X66),X66)
        | ~ r1_tarski(esk4_2(X65,X66),X65)
        | X66 = k1_zfmisc_1(X65) )
      & ( r2_hidden(esk4_2(X65,X66),X66)
        | r1_tarski(esk4_2(X65,X66),X65)
        | X66 = k1_zfmisc_1(X65) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_24,negated_conjecture,
    ( v1_funct_1(esk9_0)
    & v1_funct_2(esk9_0,esk6_0,k1_tarski(esk7_0))
    & m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_tarski(esk7_0))))
    & r2_hidden(esk8_0,esk6_0)
    & k1_funct_1(esk9_0,esk8_0) != esk7_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).

fof(c_0_25,plain,(
    ! [X33] : k2_tarski(X33,X33) = k1_tarski(X33) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_26,plain,(
    ! [X34,X35] : k1_enumset1(X34,X34,X35) = k2_tarski(X34,X35) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_27,plain,(
    ! [X36,X37,X38] : k2_enumset1(X36,X36,X37,X38) = k1_enumset1(X36,X37,X38) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_28,plain,(
    ! [X39,X40,X41,X42] : k3_enumset1(X39,X39,X40,X41,X42) = k2_enumset1(X39,X40,X41,X42) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_29,plain,(
    ! [X43,X44,X45,X46,X47] : k4_enumset1(X43,X43,X44,X45,X46,X47) = k3_enumset1(X43,X44,X45,X46,X47) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_30,plain,(
    ! [X48,X49,X50,X51,X52,X53] : k5_enumset1(X48,X48,X49,X50,X51,X52,X53) = k4_enumset1(X48,X49,X50,X51,X52,X53) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_31,plain,(
    ! [X54,X55,X56,X57,X58,X59,X60] : k6_enumset1(X54,X54,X55,X56,X57,X58,X59,X60) = k5_enumset1(X54,X55,X56,X57,X58,X59,X60) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_32,plain,(
    ! [X22,X23] :
      ( ~ r1_tarski(X22,X23)
      | k3_xboole_0(X22,X23) = X22 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_34,plain,(
    ! [X86,X87] :
      ( ~ m1_subset_1(X86,X87)
      | v1_xboole_0(X87)
      | r2_hidden(X86,X87) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_tarski(esk7_0)))) ),
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
    ! [X85] : ~ v1_xboole_0(k1_zfmisc_1(X85)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_44,plain,(
    ! [X98,X99,X100] :
      ( ( X98 = k1_xboole_0
        | X99 = k1_xboole_0
        | X100 = k1_xboole_0
        | k3_zfmisc_1(X98,X99,X100) != k1_xboole_0 )
      & ( X98 != k1_xboole_0
        | k3_zfmisc_1(X98,X99,X100) = k1_xboole_0 )
      & ( X99 != k1_xboole_0
        | k3_zfmisc_1(X98,X99,X100) = k1_xboole_0 )
      & ( X100 != k1_xboole_0
        | k3_zfmisc_1(X98,X99,X100) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_mcart_1])])])).

fof(c_0_45,plain,(
    ! [X101,X102,X103,X104] : k3_zfmisc_1(k2_zfmisc_1(X101,X102),X103,X104) = k4_zfmisc_1(X101,X102,X103,X104) ),
    inference(variable_rename,[status(thm)],[t54_mcart_1])).

fof(c_0_46,plain,(
    ! [X88,X89,X90,X91] : k4_zfmisc_1(X88,X89,X90,X91) = k2_zfmisc_1(k3_zfmisc_1(X88,X89,X90),X91) ),
    inference(variable_rename,[status(thm)],[d4_zfmisc_1])).

fof(c_0_47,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( r2_hidden(X16,X13)
        | ~ r2_hidden(X16,X15)
        | X15 != k3_xboole_0(X13,X14) )
      & ( r2_hidden(X16,X14)
        | ~ r2_hidden(X16,X15)
        | X15 != k3_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X13)
        | ~ r2_hidden(X17,X14)
        | r2_hidden(X17,X15)
        | X15 != k3_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X20)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X18)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X19)
        | X20 = k3_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X18)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k3_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X19)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k3_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_48,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_50,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_52,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,plain,
    ( k3_zfmisc_1(X2,X1,X3) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_54,plain,
    ( k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4) = k4_zfmisc_1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_55,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_56,plain,
    ( k3_zfmisc_1(X2,X3,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_57,plain,(
    ! [X24,X25,X26,X27,X28,X29,X30,X31] :
      ( ( ~ r2_hidden(X27,X26)
        | X27 = X24
        | X27 = X25
        | X26 != k2_tarski(X24,X25) )
      & ( X28 != X24
        | r2_hidden(X28,X26)
        | X26 != k2_tarski(X24,X25) )
      & ( X28 != X25
        | r2_hidden(X28,X26)
        | X26 != k2_tarski(X24,X25) )
      & ( esk3_3(X29,X30,X31) != X29
        | ~ r2_hidden(esk3_3(X29,X30,X31),X31)
        | X31 = k2_tarski(X29,X30) )
      & ( esk3_3(X29,X30,X31) != X30
        | ~ r2_hidden(esk3_3(X29,X30,X31),X31)
        | X31 = k2_tarski(X29,X30) )
      & ( r2_hidden(esk3_3(X29,X30,X31),X31)
        | esk3_3(X29,X30,X31) = X29
        | esk3_3(X29,X30,X31) = X30
        | X31 = k2_tarski(X29,X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_59,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

fof(c_0_61,plain,(
    ! [X92,X93,X94] :
      ( ( r2_hidden(k1_mcart_1(X92),X93)
        | ~ r2_hidden(X92,k2_zfmisc_1(X93,X94)) )
      & ( r2_hidden(k2_mcart_1(X92),X94)
        | ~ r2_hidden(X92,k2_zfmisc_1(X93,X94)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_62,plain,
    ( k3_zfmisc_1(X1,k1_xboole_0,X2) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_53])).

cnf(c_0_63,plain,
    ( k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(rw,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_64,plain,
    ( k3_zfmisc_1(X1,X2,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_56])).

cnf(c_0_65,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_58])).

cnf(c_0_67,negated_conjecture,
    ( k3_xboole_0(esk9_0,k2_zfmisc_1(esk6_0,k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0))) = esk9_0 ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_68,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_69,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])).

cnf(c_0_70,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk6_0,k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)))
    | ~ r2_hidden(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_72,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_73,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(k2_mcart_1(X1),k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0))
    | ~ r2_hidden(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_71])).

fof(c_0_75,plain,(
    ! [X68,X69,X70,X71,X72,X73,X74,X75,X76,X77,X78,X79,X80,X81,X82,X83] :
      ( ( ~ r2_hidden(X75,X74)
        | X75 = X68
        | X75 = X69
        | X75 = X70
        | X75 = X71
        | X75 = X72
        | X75 = X73
        | X74 != k4_enumset1(X68,X69,X70,X71,X72,X73) )
      & ( X76 != X68
        | r2_hidden(X76,X74)
        | X74 != k4_enumset1(X68,X69,X70,X71,X72,X73) )
      & ( X76 != X69
        | r2_hidden(X76,X74)
        | X74 != k4_enumset1(X68,X69,X70,X71,X72,X73) )
      & ( X76 != X70
        | r2_hidden(X76,X74)
        | X74 != k4_enumset1(X68,X69,X70,X71,X72,X73) )
      & ( X76 != X71
        | r2_hidden(X76,X74)
        | X74 != k4_enumset1(X68,X69,X70,X71,X72,X73) )
      & ( X76 != X72
        | r2_hidden(X76,X74)
        | X74 != k4_enumset1(X68,X69,X70,X71,X72,X73) )
      & ( X76 != X73
        | r2_hidden(X76,X74)
        | X74 != k4_enumset1(X68,X69,X70,X71,X72,X73) )
      & ( esk5_7(X77,X78,X79,X80,X81,X82,X83) != X77
        | ~ r2_hidden(esk5_7(X77,X78,X79,X80,X81,X82,X83),X83)
        | X83 = k4_enumset1(X77,X78,X79,X80,X81,X82) )
      & ( esk5_7(X77,X78,X79,X80,X81,X82,X83) != X78
        | ~ r2_hidden(esk5_7(X77,X78,X79,X80,X81,X82,X83),X83)
        | X83 = k4_enumset1(X77,X78,X79,X80,X81,X82) )
      & ( esk5_7(X77,X78,X79,X80,X81,X82,X83) != X79
        | ~ r2_hidden(esk5_7(X77,X78,X79,X80,X81,X82,X83),X83)
        | X83 = k4_enumset1(X77,X78,X79,X80,X81,X82) )
      & ( esk5_7(X77,X78,X79,X80,X81,X82,X83) != X80
        | ~ r2_hidden(esk5_7(X77,X78,X79,X80,X81,X82,X83),X83)
        | X83 = k4_enumset1(X77,X78,X79,X80,X81,X82) )
      & ( esk5_7(X77,X78,X79,X80,X81,X82,X83) != X81
        | ~ r2_hidden(esk5_7(X77,X78,X79,X80,X81,X82,X83),X83)
        | X83 = k4_enumset1(X77,X78,X79,X80,X81,X82) )
      & ( esk5_7(X77,X78,X79,X80,X81,X82,X83) != X82
        | ~ r2_hidden(esk5_7(X77,X78,X79,X80,X81,X82,X83),X83)
        | X83 = k4_enumset1(X77,X78,X79,X80,X81,X82) )
      & ( r2_hidden(esk5_7(X77,X78,X79,X80,X81,X82,X83),X83)
        | esk5_7(X77,X78,X79,X80,X81,X82,X83) = X77
        | esk5_7(X77,X78,X79,X80,X81,X82,X83) = X78
        | esk5_7(X77,X78,X79,X80,X81,X82,X83) = X79
        | esk5_7(X77,X78,X79,X80,X81,X82,X83) = X80
        | esk5_7(X77,X78,X79,X80,X81,X82,X83) = X81
        | esk5_7(X77,X78,X79,X80,X81,X82,X83) = X82
        | X83 = k4_enumset1(X77,X78,X79,X80,X81,X82) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_enumset1])])])])])])).

fof(c_0_76,plain,(
    ! [X105,X106,X107,X108] :
      ( ~ v1_funct_1(X108)
      | ~ v1_funct_2(X108,X105,X106)
      | ~ m1_subset_1(X108,k1_zfmisc_1(k2_zfmisc_1(X105,X106)))
      | ~ r2_hidden(X107,X105)
      | X106 = k1_xboole_0
      | r2_hidden(k1_funct_1(X108,X107),X106) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).

cnf(c_0_77,negated_conjecture,
    ( v1_funct_2(esk9_0,esk6_0,k1_tarski(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_78,plain,(
    ! [X95,X96,X97] :
      ( ( k1_mcart_1(X95) = X96
        | ~ r2_hidden(X95,k2_zfmisc_1(k1_tarski(X96),X97)) )
      & ( r2_hidden(k2_mcart_1(X95),X97)
        | ~ r2_hidden(X95,k2_zfmisc_1(k1_tarski(X96),X97)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_mcart_1])])])).

cnf(c_0_79,plain,
    ( r2_hidden(k2_mcart_1(k2_mcart_1(X1)),X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_72])).

cnf(c_0_80,negated_conjecture,
    ( k2_mcart_1(X1) = esk7_0
    | ~ r2_hidden(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

fof(c_0_81,plain,(
    ! [X9,X10,X11] :
      ( ( ~ v1_xboole_0(X9)
        | ~ r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_1(X11),X11)
        | v1_xboole_0(X11) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_82,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k4_enumset1(X4,X5,X6,X7,X8,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_83,plain,
    ( X3 = k1_xboole_0
    | r2_hidden(k1_funct_1(X1,X4),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_84,negated_conjecture,
    ( v1_funct_2(esk9_0,esk6_0,k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_85,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_86,plain,
    ( k1_mcart_1(X1) = X2
    | ~ r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(esk7_0,X1)
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_72])).

cnf(c_0_88,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_89,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X4,X4,X5,X6,X7,X8,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_41]),c_0_42])).

cnf(c_0_90,negated_conjecture,
    ( k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0) = k1_xboole_0
    | r2_hidden(k1_funct_1(esk9_0,X1),k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_51]),c_0_84]),c_0_85])])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(esk8_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_92,plain,
    ( k1_mcart_1(X1) = X2
    | ~ r2_hidden(X1,k2_zfmisc_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(esk7_0,X1)
    | v1_xboole_0(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_94,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_95,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_89])])).

cnf(c_0_96,negated_conjecture,
    ( k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0) = k1_xboole_0
    | r2_hidden(k1_funct_1(esk9_0,esk8_0),k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_97,negated_conjecture,
    ( k1_funct_1(esk9_0,esk8_0) != esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_98,negated_conjecture,
    ( k1_mcart_1(esk7_0) = X1
    | v1_xboole_0(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_99,plain,
    ( ~ v1_xboole_0(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_100,negated_conjecture,
    ( k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_96]),c_0_97])).

cnf(c_0_101,negated_conjecture,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_98])).

cnf(c_0_102,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_101])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:54:02 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.030 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t65_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>(r2_hidden(X3,X1)=>k1_funct_1(X4,X3)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 0.13/0.38  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.13/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.38  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.13/0.38  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.13/0.38  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.13/0.38  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.13/0.38  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.13/0.38  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.13/0.38  fof(t35_mcart_1, axiom, ![X1, X2, X3]:(((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)<=>k3_zfmisc_1(X1,X2,X3)!=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_mcart_1)).
% 0.13/0.38  fof(t54_mcart_1, axiom, ![X1, X2, X3, X4]:k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4)=k4_zfmisc_1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_mcart_1)).
% 0.13/0.38  fof(d4_zfmisc_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 0.13/0.38  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.13/0.38  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.13/0.38  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.13/0.38  fof(d4_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:(X7=k4_enumset1(X1,X2,X3,X4,X5,X6)<=>![X8]:(r2_hidden(X8,X7)<=>~((((((X8!=X1&X8!=X2)&X8!=X3)&X8!=X4)&X8!=X5)&X8!=X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_enumset1)).
% 0.13/0.38  fof(t7_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_hidden(X3,X1)=>(X2=k1_xboole_0|r2_hidden(k1_funct_1(X4,X3),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 0.13/0.38  fof(t12_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))=>(k1_mcart_1(X1)=X2&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_mcart_1)).
% 0.13/0.38  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.13/0.38  fof(c_0_22, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>(r2_hidden(X3,X1)=>k1_funct_1(X4,X3)=X2))), inference(assume_negation,[status(cth)],[t65_funct_2])).
% 0.13/0.38  fof(c_0_23, plain, ![X61, X62, X63, X64, X65, X66]:(((~r2_hidden(X63,X62)|r1_tarski(X63,X61)|X62!=k1_zfmisc_1(X61))&(~r1_tarski(X64,X61)|r2_hidden(X64,X62)|X62!=k1_zfmisc_1(X61)))&((~r2_hidden(esk4_2(X65,X66),X66)|~r1_tarski(esk4_2(X65,X66),X65)|X66=k1_zfmisc_1(X65))&(r2_hidden(esk4_2(X65,X66),X66)|r1_tarski(esk4_2(X65,X66),X65)|X66=k1_zfmisc_1(X65)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.13/0.38  fof(c_0_24, negated_conjecture, (((v1_funct_1(esk9_0)&v1_funct_2(esk9_0,esk6_0,k1_tarski(esk7_0)))&m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_tarski(esk7_0)))))&(r2_hidden(esk8_0,esk6_0)&k1_funct_1(esk9_0,esk8_0)!=esk7_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).
% 0.13/0.38  fof(c_0_25, plain, ![X33]:k2_tarski(X33,X33)=k1_tarski(X33), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.38  fof(c_0_26, plain, ![X34, X35]:k1_enumset1(X34,X34,X35)=k2_tarski(X34,X35), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.38  fof(c_0_27, plain, ![X36, X37, X38]:k2_enumset1(X36,X36,X37,X38)=k1_enumset1(X36,X37,X38), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.38  fof(c_0_28, plain, ![X39, X40, X41, X42]:k3_enumset1(X39,X39,X40,X41,X42)=k2_enumset1(X39,X40,X41,X42), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.38  fof(c_0_29, plain, ![X43, X44, X45, X46, X47]:k4_enumset1(X43,X43,X44,X45,X46,X47)=k3_enumset1(X43,X44,X45,X46,X47), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.13/0.38  fof(c_0_30, plain, ![X48, X49, X50, X51, X52, X53]:k5_enumset1(X48,X48,X49,X50,X51,X52,X53)=k4_enumset1(X48,X49,X50,X51,X52,X53), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.13/0.38  fof(c_0_31, plain, ![X54, X55, X56, X57, X58, X59, X60]:k6_enumset1(X54,X54,X55,X56,X57,X58,X59,X60)=k5_enumset1(X54,X55,X56,X57,X58,X59,X60), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.13/0.38  fof(c_0_32, plain, ![X22, X23]:(~r1_tarski(X22,X23)|k3_xboole_0(X22,X23)=X22), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.13/0.38  cnf(c_0_33, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  fof(c_0_34, plain, ![X86, X87]:(~m1_subset_1(X86,X87)|(v1_xboole_0(X87)|r2_hidden(X86,X87))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_tarski(esk7_0))))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.38  cnf(c_0_36, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.38  cnf(c_0_37, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.38  cnf(c_0_38, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.38  cnf(c_0_39, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.38  cnf(c_0_40, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.38  cnf(c_0_41, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.38  cnf(c_0_42, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.38  fof(c_0_43, plain, ![X85]:~v1_xboole_0(k1_zfmisc_1(X85)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.13/0.38  fof(c_0_44, plain, ![X98, X99, X100]:((X98=k1_xboole_0|X99=k1_xboole_0|X100=k1_xboole_0|k3_zfmisc_1(X98,X99,X100)!=k1_xboole_0)&(((X98!=k1_xboole_0|k3_zfmisc_1(X98,X99,X100)=k1_xboole_0)&(X99!=k1_xboole_0|k3_zfmisc_1(X98,X99,X100)=k1_xboole_0))&(X100!=k1_xboole_0|k3_zfmisc_1(X98,X99,X100)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_mcart_1])])])).
% 0.13/0.38  fof(c_0_45, plain, ![X101, X102, X103, X104]:k3_zfmisc_1(k2_zfmisc_1(X101,X102),X103,X104)=k4_zfmisc_1(X101,X102,X103,X104), inference(variable_rename,[status(thm)],[t54_mcart_1])).
% 0.13/0.38  fof(c_0_46, plain, ![X88, X89, X90, X91]:k4_zfmisc_1(X88,X89,X90,X91)=k2_zfmisc_1(k3_zfmisc_1(X88,X89,X90),X91), inference(variable_rename,[status(thm)],[d4_zfmisc_1])).
% 0.13/0.38  fof(c_0_47, plain, ![X13, X14, X15, X16, X17, X18, X19, X20]:((((r2_hidden(X16,X13)|~r2_hidden(X16,X15)|X15!=k3_xboole_0(X13,X14))&(r2_hidden(X16,X14)|~r2_hidden(X16,X15)|X15!=k3_xboole_0(X13,X14)))&(~r2_hidden(X17,X13)|~r2_hidden(X17,X14)|r2_hidden(X17,X15)|X15!=k3_xboole_0(X13,X14)))&((~r2_hidden(esk2_3(X18,X19,X20),X20)|(~r2_hidden(esk2_3(X18,X19,X20),X18)|~r2_hidden(esk2_3(X18,X19,X20),X19))|X20=k3_xboole_0(X18,X19))&((r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k3_xboole_0(X18,X19))&(r2_hidden(esk2_3(X18,X19,X20),X19)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k3_xboole_0(X18,X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.13/0.38  cnf(c_0_48, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.38  cnf(c_0_49, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_33])).
% 0.13/0.38  cnf(c_0_50, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42])).
% 0.13/0.38  cnf(c_0_52, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.38  cnf(c_0_53, plain, (k3_zfmisc_1(X2,X1,X3)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.38  cnf(c_0_54, plain, (k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4)=k4_zfmisc_1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.13/0.38  cnf(c_0_55, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.13/0.38  cnf(c_0_56, plain, (k3_zfmisc_1(X2,X3,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.38  fof(c_0_57, plain, ![X24, X25, X26, X27, X28, X29, X30, X31]:(((~r2_hidden(X27,X26)|(X27=X24|X27=X25)|X26!=k2_tarski(X24,X25))&((X28!=X24|r2_hidden(X28,X26)|X26!=k2_tarski(X24,X25))&(X28!=X25|r2_hidden(X28,X26)|X26!=k2_tarski(X24,X25))))&(((esk3_3(X29,X30,X31)!=X29|~r2_hidden(esk3_3(X29,X30,X31),X31)|X31=k2_tarski(X29,X30))&(esk3_3(X29,X30,X31)!=X30|~r2_hidden(esk3_3(X29,X30,X31),X31)|X31=k2_tarski(X29,X30)))&(r2_hidden(esk3_3(X29,X30,X31),X31)|(esk3_3(X29,X30,X31)=X29|esk3_3(X29,X30,X31)=X30)|X31=k2_tarski(X29,X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.13/0.38  cnf(c_0_58, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.13/0.38  cnf(c_0_59, plain, (k3_xboole_0(X1,X2)=X1|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.13/0.38  cnf(c_0_60, negated_conjecture, (r2_hidden(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0))))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])).
% 0.13/0.38  fof(c_0_61, plain, ![X92, X93, X94]:((r2_hidden(k1_mcart_1(X92),X93)|~r2_hidden(X92,k2_zfmisc_1(X93,X94)))&(r2_hidden(k2_mcart_1(X92),X94)|~r2_hidden(X92,k2_zfmisc_1(X93,X94)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.13/0.38  cnf(c_0_62, plain, (k3_zfmisc_1(X1,k1_xboole_0,X2)=k1_xboole_0), inference(er,[status(thm)],[c_0_53])).
% 0.13/0.38  cnf(c_0_63, plain, (k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)), inference(rw,[status(thm)],[c_0_54, c_0_55])).
% 0.13/0.38  cnf(c_0_64, plain, (k3_zfmisc_1(X1,X2,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_56])).
% 0.13/0.38  cnf(c_0_65, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.13/0.38  cnf(c_0_66, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_58])).
% 0.13/0.38  cnf(c_0_67, negated_conjecture, (k3_xboole_0(esk9_0,k2_zfmisc_1(esk6_0,k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)))=esk9_0), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.13/0.38  cnf(c_0_68, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.13/0.38  cnf(c_0_69, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])).
% 0.13/0.38  cnf(c_0_70, plain, (X1=X4|X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42])).
% 0.13/0.38  cnf(c_0_71, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(esk6_0,k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)))|~r2_hidden(X1,esk9_0)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.13/0.38  cnf(c_0_72, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.13/0.38  cnf(c_0_73, plain, (X1=X2|X1=X3|~r2_hidden(X1,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2))), inference(er,[status(thm)],[c_0_70])).
% 0.13/0.38  cnf(c_0_74, negated_conjecture, (r2_hidden(k2_mcart_1(X1),k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0))|~r2_hidden(X1,esk9_0)), inference(spm,[status(thm)],[c_0_68, c_0_71])).
% 0.13/0.38  fof(c_0_75, plain, ![X68, X69, X70, X71, X72, X73, X74, X75, X76, X77, X78, X79, X80, X81, X82, X83]:(((~r2_hidden(X75,X74)|(X75=X68|X75=X69|X75=X70|X75=X71|X75=X72|X75=X73)|X74!=k4_enumset1(X68,X69,X70,X71,X72,X73))&((((((X76!=X68|r2_hidden(X76,X74)|X74!=k4_enumset1(X68,X69,X70,X71,X72,X73))&(X76!=X69|r2_hidden(X76,X74)|X74!=k4_enumset1(X68,X69,X70,X71,X72,X73)))&(X76!=X70|r2_hidden(X76,X74)|X74!=k4_enumset1(X68,X69,X70,X71,X72,X73)))&(X76!=X71|r2_hidden(X76,X74)|X74!=k4_enumset1(X68,X69,X70,X71,X72,X73)))&(X76!=X72|r2_hidden(X76,X74)|X74!=k4_enumset1(X68,X69,X70,X71,X72,X73)))&(X76!=X73|r2_hidden(X76,X74)|X74!=k4_enumset1(X68,X69,X70,X71,X72,X73))))&(((((((esk5_7(X77,X78,X79,X80,X81,X82,X83)!=X77|~r2_hidden(esk5_7(X77,X78,X79,X80,X81,X82,X83),X83)|X83=k4_enumset1(X77,X78,X79,X80,X81,X82))&(esk5_7(X77,X78,X79,X80,X81,X82,X83)!=X78|~r2_hidden(esk5_7(X77,X78,X79,X80,X81,X82,X83),X83)|X83=k4_enumset1(X77,X78,X79,X80,X81,X82)))&(esk5_7(X77,X78,X79,X80,X81,X82,X83)!=X79|~r2_hidden(esk5_7(X77,X78,X79,X80,X81,X82,X83),X83)|X83=k4_enumset1(X77,X78,X79,X80,X81,X82)))&(esk5_7(X77,X78,X79,X80,X81,X82,X83)!=X80|~r2_hidden(esk5_7(X77,X78,X79,X80,X81,X82,X83),X83)|X83=k4_enumset1(X77,X78,X79,X80,X81,X82)))&(esk5_7(X77,X78,X79,X80,X81,X82,X83)!=X81|~r2_hidden(esk5_7(X77,X78,X79,X80,X81,X82,X83),X83)|X83=k4_enumset1(X77,X78,X79,X80,X81,X82)))&(esk5_7(X77,X78,X79,X80,X81,X82,X83)!=X82|~r2_hidden(esk5_7(X77,X78,X79,X80,X81,X82,X83),X83)|X83=k4_enumset1(X77,X78,X79,X80,X81,X82)))&(r2_hidden(esk5_7(X77,X78,X79,X80,X81,X82,X83),X83)|(esk5_7(X77,X78,X79,X80,X81,X82,X83)=X77|esk5_7(X77,X78,X79,X80,X81,X82,X83)=X78|esk5_7(X77,X78,X79,X80,X81,X82,X83)=X79|esk5_7(X77,X78,X79,X80,X81,X82,X83)=X80|esk5_7(X77,X78,X79,X80,X81,X82,X83)=X81|esk5_7(X77,X78,X79,X80,X81,X82,X83)=X82)|X83=k4_enumset1(X77,X78,X79,X80,X81,X82)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_enumset1])])])])])])).
% 0.13/0.38  fof(c_0_76, plain, ![X105, X106, X107, X108]:(~v1_funct_1(X108)|~v1_funct_2(X108,X105,X106)|~m1_subset_1(X108,k1_zfmisc_1(k2_zfmisc_1(X105,X106)))|(~r2_hidden(X107,X105)|(X106=k1_xboole_0|r2_hidden(k1_funct_1(X108,X107),X106)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).
% 0.13/0.38  cnf(c_0_77, negated_conjecture, (v1_funct_2(esk9_0,esk6_0,k1_tarski(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.38  fof(c_0_78, plain, ![X95, X96, X97]:((k1_mcart_1(X95)=X96|~r2_hidden(X95,k2_zfmisc_1(k1_tarski(X96),X97)))&(r2_hidden(k2_mcart_1(X95),X97)|~r2_hidden(X95,k2_zfmisc_1(k1_tarski(X96),X97)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_mcart_1])])])).
% 0.13/0.38  cnf(c_0_79, plain, (r2_hidden(k2_mcart_1(k2_mcart_1(X1)),X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_68, c_0_72])).
% 0.13/0.38  cnf(c_0_80, negated_conjecture, (k2_mcart_1(X1)=esk7_0|~r2_hidden(X1,esk9_0)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.13/0.38  fof(c_0_81, plain, ![X9, X10, X11]:((~v1_xboole_0(X9)|~r2_hidden(X10,X9))&(r2_hidden(esk1_1(X11),X11)|v1_xboole_0(X11))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.13/0.38  cnf(c_0_82, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k4_enumset1(X4,X5,X6,X7,X8,X2)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.13/0.38  cnf(c_0_83, plain, (X3=k1_xboole_0|r2_hidden(k1_funct_1(X1,X4),X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.13/0.38  cnf(c_0_84, negated_conjecture, (v1_funct_2(esk9_0,esk6_0,k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42])).
% 0.13/0.38  cnf(c_0_85, negated_conjecture, (v1_funct_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.38  cnf(c_0_86, plain, (k1_mcart_1(X1)=X2|~r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.13/0.38  cnf(c_0_87, negated_conjecture, (r2_hidden(esk7_0,X1)|~r2_hidden(X2,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_72])).
% 0.13/0.38  cnf(c_0_88, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.13/0.38  cnf(c_0_89, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X4,X4,X5,X6,X7,X8,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_41]), c_0_42])).
% 0.13/0.38  cnf(c_0_90, negated_conjecture, (k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)=k1_xboole_0|r2_hidden(k1_funct_1(esk9_0,X1),k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0))|~r2_hidden(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_51]), c_0_84]), c_0_85])])).
% 0.13/0.38  cnf(c_0_91, negated_conjecture, (r2_hidden(esk8_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.38  cnf(c_0_92, plain, (k1_mcart_1(X1)=X2|~r2_hidden(X1,k2_zfmisc_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42])).
% 0.13/0.38  cnf(c_0_93, negated_conjecture, (r2_hidden(esk7_0,X1)|v1_xboole_0(k1_xboole_0)), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.13/0.38  cnf(c_0_94, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.13/0.38  cnf(c_0_95, plain, (r2_hidden(X1,k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_89])])).
% 0.13/0.38  cnf(c_0_96, negated_conjecture, (k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)=k1_xboole_0|r2_hidden(k1_funct_1(esk9_0,esk8_0),k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0))), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.13/0.38  cnf(c_0_97, negated_conjecture, (k1_funct_1(esk9_0,esk8_0)!=esk7_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.38  cnf(c_0_98, negated_conjecture, (k1_mcart_1(esk7_0)=X1|v1_xboole_0(k1_xboole_0)), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 0.13/0.38  cnf(c_0_99, plain, (~v1_xboole_0(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6))), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.13/0.38  cnf(c_0_100, negated_conjecture, (k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_96]), c_0_97])).
% 0.13/0.38  cnf(c_0_101, negated_conjecture, (v1_xboole_0(k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_98])).
% 0.13/0.38  cnf(c_0_102, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_101])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 103
% 0.13/0.38  # Proof object clause steps            : 58
% 0.13/0.38  # Proof object formula steps           : 45
% 0.13/0.38  # Proof object conjectures             : 23
% 0.13/0.38  # Proof object clause conjectures      : 20
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 28
% 0.13/0.38  # Proof object initial formulas used   : 22
% 0.13/0.38  # Proof object generating inferences   : 18
% 0.13/0.38  # Proof object simplifying inferences  : 47
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 22
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 58
% 0.13/0.38  # Removed in clause preprocessing      : 8
% 0.13/0.38  # Initial clauses in saturation        : 50
% 0.13/0.38  # Processed clauses                    : 194
% 0.13/0.38  # ...of these trivial                  : 1
% 0.13/0.38  # ...subsumed                          : 49
% 0.13/0.38  # ...remaining for further processing  : 144
% 0.13/0.38  # Other redundant clauses eliminated   : 26
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 6
% 0.13/0.38  # Backward-rewritten                   : 12
% 0.13/0.38  # Generated clauses                    : 392
% 0.13/0.38  # ...of the previous two non-trivial   : 366
% 0.13/0.38  # Contextual simplify-reflections      : 4
% 0.13/0.38  # Paramodulations                      : 372
% 0.13/0.38  # Factorizations                       : 2
% 0.13/0.38  # Equation resolutions                 : 26
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
% 0.13/0.38  # Current number of processed clauses  : 61
% 0.13/0.38  #    Positive orientable unit clauses  : 18
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 4
% 0.13/0.38  #    Non-unit-clauses                  : 39
% 0.13/0.38  # Current number of unprocessed clauses: 154
% 0.13/0.38  # ...number of literals in the above   : 439
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 73
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 1413
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 1010
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 49
% 0.13/0.38  # Unit Clause-clause subsumption calls : 35
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 40
% 0.13/0.38  # BW rewrite match successes           : 3
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 7417
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.037 s
% 0.13/0.38  # System time              : 0.007 s
% 0.13/0.38  # Total time               : 0.044 s
% 0.13/0.38  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
