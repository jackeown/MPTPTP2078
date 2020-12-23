%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0550+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:48 EST 2020

% Result     : Theorem 0.39s
% Output     : CNFRefutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 234 expanded)
%              Number of clauses        :   50 ( 119 expanded)
%              Number of leaves         :   11 (  61 expanded)
%              Depth                    :   16
%              Number of atoms          :  191 ( 607 expanded)
%              Number of equality atoms :   30 (  82 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(t152_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ~ ( X1 != k1_xboole_0
          & r1_tarski(X1,k1_relat_1(X2))
          & k9_relat_1(X2,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(c_0_11,plain,(
    ! [X33,X34,X35] :
      ( ~ r2_hidden(X33,X34)
      | ~ m1_subset_1(X34,k1_zfmisc_1(X35))
      | ~ v1_xboole_0(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_12,plain,(
    ! [X31,X32] :
      ( ( ~ m1_subset_1(X31,k1_zfmisc_1(X32))
        | r1_tarski(X31,X32) )
      & ( ~ r1_tarski(X31,X32)
        | m1_subset_1(X31,k1_zfmisc_1(X32)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_13,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,plain,(
    ! [X29,X30] :
      ( ~ m1_subset_1(X29,X30)
      | v1_xboole_0(X30)
      | r2_hidden(X29,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_16,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X3)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_18,plain,(
    ! [X22] : m1_subset_1(esk5_1(X22),X22) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_19,plain,(
    ! [X11,X12,X13,X15,X16,X17,X18,X20] :
      ( ( ~ r2_hidden(X13,X12)
        | r2_hidden(k4_tarski(X13,esk2_3(X11,X12,X13)),X11)
        | X12 != k1_relat_1(X11) )
      & ( ~ r2_hidden(k4_tarski(X15,X16),X11)
        | r2_hidden(X15,X12)
        | X12 != k1_relat_1(X11) )
      & ( ~ r2_hidden(esk3_2(X17,X18),X18)
        | ~ r2_hidden(k4_tarski(esk3_2(X17,X18),X20),X17)
        | X18 = k1_relat_1(X17) )
      & ( r2_hidden(esk3_2(X17,X18),X18)
        | r2_hidden(k4_tarski(esk3_2(X17,X18),esk4_2(X17,X18)),X17)
        | X18 = k1_relat_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_20,plain,(
    ! [X37,X38] :
      ( ~ v1_xboole_0(X37)
      | X37 = X38
      | ~ v1_xboole_0(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_21,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1)
    | ~ v1_xboole_0(X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( m1_subset_1(esk5_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_27,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( r1_tarski(esk5_1(k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_22])).

cnf(c_0_29,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,esk5_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_13,c_0_22])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( X1 = o_0_0_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( v1_xboole_0(esk5_1(k1_zfmisc_1(X1)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k1_relat_1(esk5_1(k1_zfmisc_1(X1)))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,plain,
    ( esk5_1(k1_zfmisc_1(X1)) = o_0_0_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_35,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_36,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k1_relat_1(o_0_0_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_37,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_38,plain,
    ( r1_tarski(k1_relat_1(o_0_0_xboole_0),X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_39,plain,(
    ! [X24,X25,X26,X28] :
      ( ( r2_hidden(esk6_3(X24,X25,X26),k1_relat_1(X26))
        | ~ r2_hidden(X24,k9_relat_1(X26,X25))
        | ~ v1_relat_1(X26) )
      & ( r2_hidden(k4_tarski(esk6_3(X24,X25,X26),X24),X26)
        | ~ r2_hidden(X24,k9_relat_1(X26,X25))
        | ~ v1_relat_1(X26) )
      & ( r2_hidden(esk6_3(X24,X25,X26),X25)
        | ~ r2_hidden(X24,k9_relat_1(X26,X25))
        | ~ v1_relat_1(X26) )
      & ( ~ r2_hidden(X28,k1_relat_1(X26))
        | ~ r2_hidden(k4_tarski(X28,X24),X26)
        | ~ r2_hidden(X28,X25)
        | r2_hidden(X24,k9_relat_1(X26,X25))
        | ~ v1_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

fof(c_0_40,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ~ ( X1 != k1_xboole_0
            & r1_tarski(X1,k1_relat_1(X2))
            & k9_relat_1(X2,X1) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t152_relat_1])).

fof(c_0_41,plain,(
    ! [X36] :
      ( ~ v1_xboole_0(X36)
      | X36 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_42,plain,
    ( r1_tarski(k1_relat_1(o_0_0_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_26])).

cnf(c_0_43,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,o_0_0_xboole_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_34])).

cnf(c_0_44,plain,
    ( r2_hidden(X3,k9_relat_1(X2,X4))
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_45,negated_conjecture,
    ( v1_relat_1(esk8_0)
    & esk7_0 != k1_xboole_0
    & r1_tarski(esk7_0,k1_relat_1(esk8_0))
    & k9_relat_1(esk8_0,esk7_0) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_40])])])).

cnf(c_0_46,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_48,plain,
    ( v1_xboole_0(k1_relat_1(o_0_0_xboole_0))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_42])).

cnf(c_0_49,plain,
    ( r1_tarski(o_0_0_xboole_0,X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_43,c_0_37])).

cnf(c_0_50,plain,
    ( r2_hidden(esk2_3(X1,k1_relat_1(X1),X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_44,c_0_30])).

cnf(c_0_51,negated_conjecture,
    ( k9_relat_1(esk8_0,esk7_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_26])).

cnf(c_0_53,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(esk7_0,k1_relat_1(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_56,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)
    | X2 = k1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_57,plain,
    ( v1_xboole_0(k1_relat_1(o_0_0_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_26])).

cnf(c_0_58,plain,
    ( r1_tarski(o_0_0_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_26])).

cnf(c_0_59,plain,
    ( ~ v1_relat_1(X1)
    | ~ v1_xboole_0(X2)
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | ~ r2_hidden(X3,X4)
    | ~ r1_tarski(k9_relat_1(X1,X4),X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_50])).

cnf(c_0_60,negated_conjecture,
    ( k9_relat_1(esk8_0,esk7_0) = o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(esk8_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_63,plain,
    ( X1 = k1_relat_1(X2)
    | r2_hidden(esk3_2(X2,X1),k1_relat_1(X2))
    | r2_hidden(esk3_2(X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_64,plain,
    ( k1_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_57])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,o_0_0_xboole_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_58])).

cnf(c_0_66,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_67,negated_conjecture,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,esk7_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_58])]),c_0_62])).

cnf(c_0_68,plain,
    ( X1 = o_0_0_xboole_0
    | r2_hidden(esk3_2(o_0_0_xboole_0,X1),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( esk7_0 != o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[c_0_66,c_0_52])).

cnf(c_0_70,negated_conjecture,
    ( ~ v1_xboole_0(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])).

cnf(c_0_71,plain,
    ( $false ),
    inference(sr,[status(thm)],[c_0_26,c_0_70]),
    [proof]).

%------------------------------------------------------------------------------
