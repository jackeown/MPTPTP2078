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
% DateTime   : Thu Dec  3 10:45:17 EST 2020

% Result     : Theorem 0.37s
% Output     : CNFRefutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  117 (4811 expanded)
%              Number of clauses        :   72 (2277 expanded)
%              Number of leaves         :   22 (1248 expanded)
%              Depth                    :   18
%              Number of atoms          :  218 (10643 expanded)
%              Number of equality atoms :  105 (5247 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(t25_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k4_subset_1(X1,X2,k3_subset_1(X1,X2)) = k2_subset_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(dt_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k7_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(t94_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(commutativity_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k4_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

fof(c_0_22,plain,(
    ! [X29,X30,X31,X32,X33,X34,X35,X36] :
      ( ( r2_hidden(X32,X29)
        | ~ r2_hidden(X32,X31)
        | X31 != k4_xboole_0(X29,X30) )
      & ( ~ r2_hidden(X32,X30)
        | ~ r2_hidden(X32,X31)
        | X31 != k4_xboole_0(X29,X30) )
      & ( ~ r2_hidden(X33,X29)
        | r2_hidden(X33,X30)
        | r2_hidden(X33,X31)
        | X31 != k4_xboole_0(X29,X30) )
      & ( ~ r2_hidden(esk3_3(X34,X35,X36),X36)
        | ~ r2_hidden(esk3_3(X34,X35,X36),X34)
        | r2_hidden(esk3_3(X34,X35,X36),X35)
        | X36 = k4_xboole_0(X34,X35) )
      & ( r2_hidden(esk3_3(X34,X35,X36),X34)
        | r2_hidden(esk3_3(X34,X35,X36),X36)
        | X36 = k4_xboole_0(X34,X35) )
      & ( ~ r2_hidden(esk3_3(X34,X35,X36),X35)
        | r2_hidden(esk3_3(X34,X35,X36),X36)
        | X36 = k4_xboole_0(X34,X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_23,plain,(
    ! [X45,X46] : k4_xboole_0(X45,X46) = k5_xboole_0(X45,k3_xboole_0(X45,X46)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_26,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_27,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_28,plain,(
    ! [X87] : k5_xboole_0(X87,k1_xboole_0) = X87 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_29,plain,(
    ! [X9,X10] : k5_xboole_0(X9,X10) = k5_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

fof(c_0_30,plain,(
    ! [X20,X21,X22,X23,X24,X25,X26,X27] :
      ( ( r2_hidden(X23,X20)
        | ~ r2_hidden(X23,X22)
        | X22 != k3_xboole_0(X20,X21) )
      & ( r2_hidden(X23,X21)
        | ~ r2_hidden(X23,X22)
        | X22 != k3_xboole_0(X20,X21) )
      & ( ~ r2_hidden(X24,X20)
        | ~ r2_hidden(X24,X21)
        | r2_hidden(X24,X22)
        | X22 != k3_xboole_0(X20,X21) )
      & ( ~ r2_hidden(esk2_3(X25,X26,X27),X27)
        | ~ r2_hidden(esk2_3(X25,X26,X27),X25)
        | ~ r2_hidden(esk2_3(X25,X26,X27),X26)
        | X27 = k3_xboole_0(X25,X26) )
      & ( r2_hidden(esk2_3(X25,X26,X27),X25)
        | r2_hidden(esk2_3(X25,X26,X27),X27)
        | X27 = k3_xboole_0(X25,X26) )
      & ( r2_hidden(esk2_3(X25,X26,X27),X26)
        | r2_hidden(esk2_3(X25,X26,X27),X27)
        | X27 = k3_xboole_0(X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_36,plain,(
    ! [X70,X71] : k4_xboole_0(X70,k4_xboole_0(X70,X71)) = k3_xboole_0(X70,X71) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_37,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X3,X2)))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_35])).

fof(c_0_40,plain,(
    ! [X41] :
      ( X41 = k1_xboole_0
      | r2_hidden(esk4_1(X41),X41) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_41,plain,(
    ! [X117,X118,X119] :
      ( ~ m1_subset_1(X118,k1_zfmisc_1(X117))
      | k7_subset_1(X117,X118,X119) = k4_xboole_0(X118,X119) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_42,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => k4_subset_1(X1,X2,k3_subset_1(X1,X2)) = k2_subset_1(X1) ) ),
    inference(assume_negation,[status(cth)],[t25_subset_1])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_45,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk4_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_47,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))
    & k4_subset_1(esk5_0,esk6_0,k3_subset_1(esk5_0,esk6_0)) != k2_subset_1(esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_42])])])).

cnf(c_0_48,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_25]),c_0_25])).

cnf(c_0_49,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

fof(c_0_50,plain,(
    ! [X108,X109,X110] :
      ( ~ m1_subset_1(X109,k1_zfmisc_1(X108))
      | m1_subset_1(k7_subset_1(X108,X109,X110),k1_zfmisc_1(X108)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_subset_1])])).

cnf(c_0_51,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k3_xboole_0(X1,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_46,c_0_25])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_53,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_33])).

fof(c_0_54,plain,(
    ! [X111,X112,X113] :
      ( ~ m1_subset_1(X112,k1_zfmisc_1(X111))
      | ~ r2_hidden(X113,X112)
      | r2_hidden(X113,X111) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_55,plain,(
    ! [X104,X105] :
      ( ~ m1_subset_1(X105,k1_zfmisc_1(X104))
      | k3_subset_1(X104,X105) = k4_xboole_0(X104,X105) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_56,plain,
    ( m1_subset_1(k7_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( k7_subset_1(esk5_0,esk6_0,X1) = k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,X1)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_58,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_53]),c_0_49]),c_0_33])).

cnf(c_0_59,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_60,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,X1)),k1_zfmisc_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_52])])).

cnf(c_0_62,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_53,c_0_58])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,k7_subset_1(X2,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_56])).

fof(c_0_64,plain,(
    ! [X58,X59] : k2_xboole_0(X58,k3_xboole_0(X58,X59)) = X58 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

fof(c_0_65,plain,(
    ! [X95,X96] : k2_xboole_0(X95,X96) = k5_xboole_0(X95,k4_xboole_0(X96,X95)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_66,plain,(
    ! [X72,X73,X74] : k3_xboole_0(X72,k4_xboole_0(X73,X74)) = k4_xboole_0(k3_xboole_0(X72,X73),X74) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

fof(c_0_67,plain,(
    ! [X106,X107] :
      ( ~ m1_subset_1(X107,k1_zfmisc_1(X106))
      | m1_subset_1(k3_subset_1(X106,X107),k1_zfmisc_1(X106)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_68,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_60,c_0_25])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(esk5_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_58]),c_0_62])).

fof(c_0_70,plain,(
    ! [X93,X94] : k2_xboole_0(X93,X94) = k5_xboole_0(k5_xboole_0(X93,X94),k3_xboole_0(X93,X94)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,k7_subset_1(esk5_0,esk6_0,X2)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_52])).

fof(c_0_72,plain,(
    ! [X54,X55,X56] : k3_xboole_0(k3_xboole_0(X54,X55),X56) = k3_xboole_0(X54,k3_xboole_0(X55,X56)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

cnf(c_0_73,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_74,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_75,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_76,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_77,negated_conjecture,
    ( k3_subset_1(esk5_0,k1_xboole_0) = esk5_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_49]),c_0_33])).

cnf(c_0_78,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_79,negated_conjecture,
    ( k7_subset_1(esk5_0,esk6_0,X1) = k1_xboole_0
    | r2_hidden(esk4_1(k7_subset_1(esk5_0,esk6_0,X1)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_45])).

cnf(c_0_80,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_81,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_74]),c_0_25])).

cnf(c_0_82,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_25]),c_0_25])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_69])])).

cnf(c_0_84,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_74]),c_0_25])).

cnf(c_0_85,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r2_hidden(esk4_1(k5_xboole_0(X1,k3_xboole_0(X1,X2))),X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_45])).

cnf(c_0_86,negated_conjecture,
    ( k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,X1)) = k1_xboole_0
    | r2_hidden(esk4_1(k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,X1))),esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_57]),c_0_57])).

cnf(c_0_87,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_80,c_0_58])).

fof(c_0_88,plain,(
    ! [X103] : k2_subset_1(X103) = X103 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_89,plain,(
    ! [X114,X115,X116] :
      ( ~ m1_subset_1(X115,k1_zfmisc_1(X114))
      | ~ m1_subset_1(X116,k1_zfmisc_1(X114))
      | k4_subset_1(X114,X115,X116) = k2_xboole_0(X115,X116) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_90,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X1)))) = X1 ),
    inference(rw,[status(thm)],[c_0_81,c_0_80])).

cnf(c_0_91,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X3))) = k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_82,c_0_80])).

fof(c_0_92,plain,(
    ! [X100,X101,X102] :
      ( ~ m1_subset_1(X101,k1_zfmisc_1(X100))
      | ~ m1_subset_1(X102,k1_zfmisc_1(X100))
      | k4_subset_1(X100,X101,X102) = k4_subset_1(X100,X102,X101) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k4_subset_1])])).

cnf(c_0_93,negated_conjecture,
    ( k7_subset_1(esk5_0,esk5_0,X1) = k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_83])).

cnf(c_0_94,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_84,c_0_34])).

cnf(c_0_95,negated_conjecture,
    ( k5_xboole_0(esk6_0,k3_xboole_0(esk5_0,esk6_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_32])).

cnf(c_0_96,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_87,c_0_32])).

cnf(c_0_97,negated_conjecture,
    ( k4_subset_1(esk5_0,esk6_0,k3_subset_1(esk5_0,esk6_0)) != k2_subset_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_98,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_99,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_100,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = X1 ),
    inference(rw,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_101,plain,
    ( k4_subset_1(X2,X1,X3) = k4_subset_1(X2,X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_102,negated_conjecture,
    ( m1_subset_1(k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,X1)),k1_zfmisc_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_93]),c_0_83])])).

cnf(c_0_103,negated_conjecture,
    ( k3_xboole_0(esk5_0,esk6_0) = esk6_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_96]),c_0_33]),c_0_80]),c_0_58]),c_0_62]),c_0_33])).

cnf(c_0_104,negated_conjecture,
    ( k4_subset_1(esk5_0,esk6_0,k3_subset_1(esk5_0,esk6_0)) != esk5_0 ),
    inference(rw,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_105,negated_conjecture,
    ( k3_subset_1(esk5_0,esk6_0) = k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_52])).

cnf(c_0_106,plain,
    ( k4_subset_1(X2,X1,X3) = k5_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_74]),c_0_25])).

cnf(c_0_107,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_100]),c_0_58]),c_0_62])).

cnf(c_0_108,negated_conjecture,
    ( k4_subset_1(esk5_0,X1,esk6_0) = k4_subset_1(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_101,c_0_52])).

cnf(c_0_109,negated_conjecture,
    ( m1_subset_1(k5_xboole_0(esk5_0,esk6_0),k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_110,negated_conjecture,
    ( k4_subset_1(esk5_0,esk6_0,k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,esk6_0))) != esk5_0 ),
    inference(rw,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_111,negated_conjecture,
    ( k5_xboole_0(X1,k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,X1))) = k4_subset_1(esk5_0,X1,esk6_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_106,c_0_52])).

cnf(c_0_112,negated_conjecture,
    ( k3_xboole_0(esk6_0,k5_xboole_0(esk5_0,esk6_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_107,c_0_103])).

cnf(c_0_113,negated_conjecture,
    ( k5_xboole_0(esk6_0,k5_xboole_0(esk5_0,esk6_0)) = esk5_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_103]),c_0_32]),c_0_103]),c_0_62]),c_0_33])).

cnf(c_0_114,negated_conjecture,
    ( k4_subset_1(esk5_0,k5_xboole_0(esk5_0,esk6_0),esk6_0) = k4_subset_1(esk5_0,esk6_0,k5_xboole_0(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_115,negated_conjecture,
    ( k4_subset_1(esk5_0,esk6_0,k5_xboole_0(esk5_0,esk6_0)) != esk5_0 ),
    inference(rw,[status(thm)],[c_0_110,c_0_103])).

cnf(c_0_116,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_109]),c_0_112]),c_0_33]),c_0_34]),c_0_113]),c_0_114]),c_0_115]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:12:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 0.37/0.54  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S032I
% 0.37/0.54  # and selection function SelectUnlessUniqMax.
% 0.37/0.54  #
% 0.37/0.54  # Preprocessing time       : 0.030 s
% 0.37/0.54  # Presaturation interreduction done
% 0.37/0.54  
% 0.37/0.54  # Proof found!
% 0.37/0.54  # SZS status Theorem
% 0.37/0.54  # SZS output start CNFRefutation
% 0.37/0.54  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.37/0.54  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.37/0.54  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.37/0.54  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.37/0.54  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.37/0.54  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.37/0.54  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.37/0.54  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.37/0.54  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.37/0.54  fof(t25_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k3_subset_1(X1,X2))=k2_subset_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 0.37/0.54  fof(dt_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k7_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 0.37/0.54  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.37/0.54  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.37/0.54  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 0.37/0.54  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.37/0.54  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.37/0.54  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.37/0.54  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 0.37/0.54  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 0.37/0.54  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.37/0.54  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.37/0.54  fof(commutativity_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k4_subset_1(X1,X3,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k4_subset_1)).
% 0.37/0.54  fof(c_0_22, plain, ![X29, X30, X31, X32, X33, X34, X35, X36]:((((r2_hidden(X32,X29)|~r2_hidden(X32,X31)|X31!=k4_xboole_0(X29,X30))&(~r2_hidden(X32,X30)|~r2_hidden(X32,X31)|X31!=k4_xboole_0(X29,X30)))&(~r2_hidden(X33,X29)|r2_hidden(X33,X30)|r2_hidden(X33,X31)|X31!=k4_xboole_0(X29,X30)))&((~r2_hidden(esk3_3(X34,X35,X36),X36)|(~r2_hidden(esk3_3(X34,X35,X36),X34)|r2_hidden(esk3_3(X34,X35,X36),X35))|X36=k4_xboole_0(X34,X35))&((r2_hidden(esk3_3(X34,X35,X36),X34)|r2_hidden(esk3_3(X34,X35,X36),X36)|X36=k4_xboole_0(X34,X35))&(~r2_hidden(esk3_3(X34,X35,X36),X35)|r2_hidden(esk3_3(X34,X35,X36),X36)|X36=k4_xboole_0(X34,X35))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.37/0.54  fof(c_0_23, plain, ![X45, X46]:k4_xboole_0(X45,X46)=k5_xboole_0(X45,k3_xboole_0(X45,X46)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.37/0.54  cnf(c_0_24, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.37/0.54  cnf(c_0_25, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.37/0.54  cnf(c_0_26, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.37/0.54  fof(c_0_27, plain, ![X7, X8]:k3_xboole_0(X7,X8)=k3_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.37/0.54  fof(c_0_28, plain, ![X87]:k5_xboole_0(X87,k1_xboole_0)=X87, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.37/0.54  fof(c_0_29, plain, ![X9, X10]:k5_xboole_0(X9,X10)=k5_xboole_0(X10,X9), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.37/0.54  fof(c_0_30, plain, ![X20, X21, X22, X23, X24, X25, X26, X27]:((((r2_hidden(X23,X20)|~r2_hidden(X23,X22)|X22!=k3_xboole_0(X20,X21))&(r2_hidden(X23,X21)|~r2_hidden(X23,X22)|X22!=k3_xboole_0(X20,X21)))&(~r2_hidden(X24,X20)|~r2_hidden(X24,X21)|r2_hidden(X24,X22)|X22!=k3_xboole_0(X20,X21)))&((~r2_hidden(esk2_3(X25,X26,X27),X27)|(~r2_hidden(esk2_3(X25,X26,X27),X25)|~r2_hidden(esk2_3(X25,X26,X27),X26))|X27=k3_xboole_0(X25,X26))&((r2_hidden(esk2_3(X25,X26,X27),X25)|r2_hidden(esk2_3(X25,X26,X27),X27)|X27=k3_xboole_0(X25,X26))&(r2_hidden(esk2_3(X25,X26,X27),X26)|r2_hidden(esk2_3(X25,X26,X27),X27)|X27=k3_xboole_0(X25,X26))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.37/0.54  cnf(c_0_31, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_26])).
% 0.37/0.54  cnf(c_0_32, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.37/0.54  cnf(c_0_33, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.37/0.54  cnf(c_0_34, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.37/0.54  cnf(c_0_35, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.37/0.54  fof(c_0_36, plain, ![X70, X71]:k4_xboole_0(X70,k4_xboole_0(X70,X71))=k3_xboole_0(X70,X71), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.37/0.54  cnf(c_0_37, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X3,X2)))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.37/0.54  cnf(c_0_38, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.37/0.54  cnf(c_0_39, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_35])).
% 0.37/0.54  fof(c_0_40, plain, ![X41]:(X41=k1_xboole_0|r2_hidden(esk4_1(X41),X41)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.37/0.54  fof(c_0_41, plain, ![X117, X118, X119]:(~m1_subset_1(X118,k1_zfmisc_1(X117))|k7_subset_1(X117,X118,X119)=k4_xboole_0(X118,X119)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.37/0.54  fof(c_0_42, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k3_subset_1(X1,X2))=k2_subset_1(X1))), inference(assume_negation,[status(cth)],[t25_subset_1])).
% 0.37/0.54  cnf(c_0_43, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.37/0.54  cnf(c_0_44, plain, (~r2_hidden(X1,k3_xboole_0(X2,k1_xboole_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])).
% 0.37/0.54  cnf(c_0_45, plain, (X1=k1_xboole_0|r2_hidden(esk4_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.37/0.54  cnf(c_0_46, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.37/0.54  fof(c_0_47, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))&k4_subset_1(esk5_0,esk6_0,k3_subset_1(esk5_0,esk6_0))!=k2_subset_1(esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_42])])])).
% 0.37/0.54  cnf(c_0_48, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_25]), c_0_25])).
% 0.37/0.54  cnf(c_0_49, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.37/0.54  fof(c_0_50, plain, ![X108, X109, X110]:(~m1_subset_1(X109,k1_zfmisc_1(X108))|m1_subset_1(k7_subset_1(X108,X109,X110),k1_zfmisc_1(X108))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_subset_1])])).
% 0.37/0.54  cnf(c_0_51, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k3_xboole_0(X1,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_46, c_0_25])).
% 0.37/0.54  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.37/0.54  cnf(c_0_53, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_33])).
% 0.37/0.54  fof(c_0_54, plain, ![X111, X112, X113]:(~m1_subset_1(X112,k1_zfmisc_1(X111))|(~r2_hidden(X113,X112)|r2_hidden(X113,X111))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.37/0.54  fof(c_0_55, plain, ![X104, X105]:(~m1_subset_1(X105,k1_zfmisc_1(X104))|k3_subset_1(X104,X105)=k4_xboole_0(X104,X105)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.37/0.54  cnf(c_0_56, plain, (m1_subset_1(k7_subset_1(X2,X1,X3),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.37/0.54  cnf(c_0_57, negated_conjecture, (k7_subset_1(esk5_0,esk6_0,X1)=k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,X1))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.37/0.54  cnf(c_0_58, plain, (k3_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_53]), c_0_49]), c_0_33])).
% 0.37/0.54  cnf(c_0_59, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.37/0.54  cnf(c_0_60, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.37/0.54  cnf(c_0_61, negated_conjecture, (m1_subset_1(k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,X1)),k1_zfmisc_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_52])])).
% 0.37/0.54  cnf(c_0_62, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_53, c_0_58])).
% 0.37/0.54  cnf(c_0_63, plain, (r2_hidden(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r2_hidden(X1,k7_subset_1(X2,X3,X4))), inference(spm,[status(thm)],[c_0_59, c_0_56])).
% 0.37/0.54  fof(c_0_64, plain, ![X58, X59]:k2_xboole_0(X58,k3_xboole_0(X58,X59))=X58, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 0.37/0.54  fof(c_0_65, plain, ![X95, X96]:k2_xboole_0(X95,X96)=k5_xboole_0(X95,k4_xboole_0(X96,X95)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.37/0.54  fof(c_0_66, plain, ![X72, X73, X74]:k3_xboole_0(X72,k4_xboole_0(X73,X74))=k4_xboole_0(k3_xboole_0(X72,X73),X74), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.37/0.54  fof(c_0_67, plain, ![X106, X107]:(~m1_subset_1(X107,k1_zfmisc_1(X106))|m1_subset_1(k3_subset_1(X106,X107),k1_zfmisc_1(X106))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.37/0.54  cnf(c_0_68, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_60, c_0_25])).
% 0.37/0.54  cnf(c_0_69, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(esk5_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_58]), c_0_62])).
% 0.37/0.54  fof(c_0_70, plain, ![X93, X94]:k2_xboole_0(X93,X94)=k5_xboole_0(k5_xboole_0(X93,X94),k3_xboole_0(X93,X94)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 0.37/0.54  cnf(c_0_71, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,k7_subset_1(esk5_0,esk6_0,X2))), inference(spm,[status(thm)],[c_0_63, c_0_52])).
% 0.37/0.54  fof(c_0_72, plain, ![X54, X55, X56]:k3_xboole_0(k3_xboole_0(X54,X55),X56)=k3_xboole_0(X54,k3_xboole_0(X55,X56)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 0.37/0.54  cnf(c_0_73, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.37/0.54  cnf(c_0_74, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.37/0.54  cnf(c_0_75, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.37/0.54  cnf(c_0_76, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.37/0.54  cnf(c_0_77, negated_conjecture, (k3_subset_1(esk5_0,k1_xboole_0)=esk5_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_49]), c_0_33])).
% 0.37/0.54  cnf(c_0_78, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.37/0.54  cnf(c_0_79, negated_conjecture, (k7_subset_1(esk5_0,esk6_0,X1)=k1_xboole_0|r2_hidden(esk4_1(k7_subset_1(esk5_0,esk6_0,X1)),esk5_0)), inference(spm,[status(thm)],[c_0_71, c_0_45])).
% 0.37/0.54  cnf(c_0_80, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.37/0.54  cnf(c_0_81, plain, (k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_74]), c_0_25])).
% 0.37/0.54  cnf(c_0_82, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_25]), c_0_25])).
% 0.37/0.54  cnf(c_0_83, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_69])])).
% 0.37/0.54  cnf(c_0_84, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_74]), c_0_25])).
% 0.37/0.54  cnf(c_0_85, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|~r2_hidden(esk4_1(k5_xboole_0(X1,k3_xboole_0(X1,X2))),X2)), inference(spm,[status(thm)],[c_0_31, c_0_45])).
% 0.37/0.54  cnf(c_0_86, negated_conjecture, (k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,X1))=k1_xboole_0|r2_hidden(esk4_1(k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,X1))),esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_57]), c_0_57])).
% 0.37/0.54  cnf(c_0_87, plain, (k3_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_80, c_0_58])).
% 0.37/0.54  fof(c_0_88, plain, ![X103]:k2_subset_1(X103)=X103, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.37/0.54  fof(c_0_89, plain, ![X114, X115, X116]:(~m1_subset_1(X115,k1_zfmisc_1(X114))|~m1_subset_1(X116,k1_zfmisc_1(X114))|k4_subset_1(X114,X115,X116)=k2_xboole_0(X115,X116)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.37/0.54  cnf(c_0_90, plain, (k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X1))))=X1), inference(rw,[status(thm)],[c_0_81, c_0_80])).
% 0.37/0.54  cnf(c_0_91, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X3)))=k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_82, c_0_80])).
% 0.37/0.54  fof(c_0_92, plain, ![X100, X101, X102]:(~m1_subset_1(X101,k1_zfmisc_1(X100))|~m1_subset_1(X102,k1_zfmisc_1(X100))|k4_subset_1(X100,X101,X102)=k4_subset_1(X100,X102,X101)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k4_subset_1])])).
% 0.37/0.54  cnf(c_0_93, negated_conjecture, (k7_subset_1(esk5_0,esk5_0,X1)=k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,X1))), inference(spm,[status(thm)],[c_0_51, c_0_83])).
% 0.37/0.54  cnf(c_0_94, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_84, c_0_34])).
% 0.37/0.54  cnf(c_0_95, negated_conjecture, (k5_xboole_0(esk6_0,k3_xboole_0(esk5_0,esk6_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_32])).
% 0.37/0.54  cnf(c_0_96, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_87, c_0_32])).
% 0.37/0.54  cnf(c_0_97, negated_conjecture, (k4_subset_1(esk5_0,esk6_0,k3_subset_1(esk5_0,esk6_0))!=k2_subset_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.37/0.54  cnf(c_0_98, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.37/0.54  cnf(c_0_99, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_89])).
% 0.37/0.54  cnf(c_0_100, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))=X1), inference(rw,[status(thm)],[c_0_90, c_0_91])).
% 0.37/0.54  cnf(c_0_101, plain, (k4_subset_1(X2,X1,X3)=k4_subset_1(X2,X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_92])).
% 0.37/0.54  cnf(c_0_102, negated_conjecture, (m1_subset_1(k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,X1)),k1_zfmisc_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_93]), c_0_83])])).
% 0.37/0.54  cnf(c_0_103, negated_conjecture, (k3_xboole_0(esk5_0,esk6_0)=esk6_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_96]), c_0_33]), c_0_80]), c_0_58]), c_0_62]), c_0_33])).
% 0.37/0.54  cnf(c_0_104, negated_conjecture, (k4_subset_1(esk5_0,esk6_0,k3_subset_1(esk5_0,esk6_0))!=esk5_0), inference(rw,[status(thm)],[c_0_97, c_0_98])).
% 0.37/0.54  cnf(c_0_105, negated_conjecture, (k3_subset_1(esk5_0,esk6_0)=k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_68, c_0_52])).
% 0.37/0.54  cnf(c_0_106, plain, (k4_subset_1(X2,X1,X3)=k5_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X1)))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_99, c_0_74]), c_0_25])).
% 0.37/0.54  cnf(c_0_107, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_100]), c_0_58]), c_0_62])).
% 0.37/0.54  cnf(c_0_108, negated_conjecture, (k4_subset_1(esk5_0,X1,esk6_0)=k4_subset_1(esk5_0,esk6_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_101, c_0_52])).
% 0.37/0.54  cnf(c_0_109, negated_conjecture, (m1_subset_1(k5_xboole_0(esk5_0,esk6_0),k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_102, c_0_103])).
% 0.37/0.54  cnf(c_0_110, negated_conjecture, (k4_subset_1(esk5_0,esk6_0,k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,esk6_0)))!=esk5_0), inference(rw,[status(thm)],[c_0_104, c_0_105])).
% 0.37/0.54  cnf(c_0_111, negated_conjecture, (k5_xboole_0(X1,k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,X1)))=k4_subset_1(esk5_0,X1,esk6_0)|~m1_subset_1(X1,k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_106, c_0_52])).
% 0.37/0.54  cnf(c_0_112, negated_conjecture, (k3_xboole_0(esk6_0,k5_xboole_0(esk5_0,esk6_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_107, c_0_103])).
% 0.37/0.54  cnf(c_0_113, negated_conjecture, (k5_xboole_0(esk6_0,k5_xboole_0(esk5_0,esk6_0))=esk5_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_103]), c_0_32]), c_0_103]), c_0_62]), c_0_33])).
% 0.37/0.54  cnf(c_0_114, negated_conjecture, (k4_subset_1(esk5_0,k5_xboole_0(esk5_0,esk6_0),esk6_0)=k4_subset_1(esk5_0,esk6_0,k5_xboole_0(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_108, c_0_109])).
% 0.37/0.54  cnf(c_0_115, negated_conjecture, (k4_subset_1(esk5_0,esk6_0,k5_xboole_0(esk5_0,esk6_0))!=esk5_0), inference(rw,[status(thm)],[c_0_110, c_0_103])).
% 0.37/0.54  cnf(c_0_116, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_109]), c_0_112]), c_0_33]), c_0_34]), c_0_113]), c_0_114]), c_0_115]), ['proof']).
% 0.37/0.54  # SZS output end CNFRefutation
% 0.37/0.54  # Proof object total steps             : 117
% 0.37/0.54  # Proof object clause steps            : 72
% 0.37/0.54  # Proof object formula steps           : 45
% 0.37/0.54  # Proof object conjectures             : 28
% 0.37/0.54  # Proof object clause conjectures      : 25
% 0.37/0.54  # Proof object formula conjectures     : 3
% 0.37/0.54  # Proof object initial clauses used    : 23
% 0.37/0.54  # Proof object initial formulas used   : 22
% 0.37/0.54  # Proof object generating inferences   : 30
% 0.37/0.54  # Proof object simplifying inferences  : 57
% 0.37/0.54  # Training examples: 0 positive, 0 negative
% 0.37/0.54  # Parsed axioms                        : 44
% 0.37/0.54  # Removed by relevancy pruning/SinE    : 0
% 0.37/0.54  # Initial clauses                      : 61
% 0.37/0.54  # Removed in clause preprocessing      : 3
% 0.37/0.54  # Initial clauses in saturation        : 58
% 0.37/0.54  # Processed clauses                    : 1456
% 0.37/0.54  # ...of these trivial                  : 147
% 0.37/0.54  # ...subsumed                          : 890
% 0.37/0.54  # ...remaining for further processing  : 419
% 0.37/0.54  # Other redundant clauses eliminated   : 9
% 0.37/0.54  # Clauses deleted for lack of memory   : 0
% 0.37/0.54  # Backward-subsumed                    : 2
% 0.37/0.54  # Backward-rewritten                   : 66
% 0.37/0.54  # Generated clauses                    : 10334
% 0.37/0.54  # ...of the previous two non-trivial   : 7981
% 0.37/0.54  # Contextual simplify-reflections      : 2
% 0.37/0.54  # Paramodulations                      : 10313
% 0.37/0.54  # Factorizations                       : 12
% 0.37/0.54  # Equation resolutions                 : 9
% 0.37/0.54  # Propositional unsat checks           : 0
% 0.37/0.54  #    Propositional check models        : 0
% 0.37/0.54  #    Propositional check unsatisfiable : 0
% 0.37/0.54  #    Propositional clauses             : 0
% 0.37/0.54  #    Propositional clauses after purity: 0
% 0.37/0.54  #    Propositional unsat core size     : 0
% 0.37/0.54  #    Propositional preprocessing time  : 0.000
% 0.37/0.54  #    Propositional encoding time       : 0.000
% 0.37/0.54  #    Propositional solver time         : 0.000
% 0.37/0.54  #    Success case prop preproc time    : 0.000
% 0.37/0.54  #    Success case prop encoding time   : 0.000
% 0.37/0.54  #    Success case prop solver time     : 0.000
% 0.37/0.54  # Current number of processed clauses  : 285
% 0.37/0.54  #    Positive orientable unit clauses  : 127
% 0.37/0.54  #    Positive unorientable unit clauses: 9
% 0.37/0.54  #    Negative unit clauses             : 5
% 0.37/0.54  #    Non-unit-clauses                  : 144
% 0.37/0.54  # Current number of unprocessed clauses: 6504
% 0.37/0.54  # ...number of literals in the above   : 9509
% 0.37/0.54  # Current number of archived formulas  : 0
% 0.37/0.54  # Current number of archived clauses   : 128
% 0.37/0.54  # Clause-clause subsumption calls (NU) : 5201
% 0.37/0.54  # Rec. Clause-clause subsumption calls : 4009
% 0.37/0.54  # Non-unit clause-clause subsumptions  : 343
% 0.37/0.54  # Unit Clause-clause subsumption calls : 644
% 0.37/0.54  # Rewrite failures with RHS unbound    : 0
% 0.37/0.54  # BW rewrite match attempts            : 552
% 0.37/0.54  # BW rewrite match successes           : 178
% 0.37/0.54  # Condensation attempts                : 0
% 0.37/0.54  # Condensation successes               : 0
% 0.37/0.54  # Termbank termtop insertions          : 195199
% 0.37/0.54  
% 0.37/0.54  # -------------------------------------------------
% 0.37/0.54  # User time                : 0.186 s
% 0.37/0.54  # System time              : 0.008 s
% 0.37/0.54  # Total time               : 0.193 s
% 0.37/0.54  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
