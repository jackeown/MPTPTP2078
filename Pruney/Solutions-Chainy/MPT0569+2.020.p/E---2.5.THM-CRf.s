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
% DateTime   : Thu Dec  3 10:51:35 EST 2020

% Result     : Theorem 1.02s
% Output     : CNFRefutation 1.02s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 239 expanded)
%              Number of clauses        :   41 ( 116 expanded)
%              Number of leaves         :    8 (  61 expanded)
%              Depth                    :   13
%              Number of atoms          :  202 ( 908 expanded)
%              Number of equality atoms :   61 ( 273 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(t173_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k10_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(d14_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k10_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(k4_tarski(X4,X5),X1)
                  & r2_hidden(X5,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

fof(c_0_8,plain,(
    ! [X14,X15] : ~ r2_hidden(X14,k2_zfmisc_1(X14,X15)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

fof(c_0_9,plain,(
    ! [X12,X13] :
      ( ( k2_zfmisc_1(X12,X13) != k1_xboole_0
        | X12 = k1_xboole_0
        | X13 = k1_xboole_0 )
      & ( X12 != k1_xboole_0
        | k2_zfmisc_1(X12,X13) = k1_xboole_0 )
      & ( X13 != k1_xboole_0
        | k2_zfmisc_1(X12,X13) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_10,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X28,X29,X30,X32,X33,X34,X35,X37] :
      ( ( ~ r2_hidden(X30,X29)
        | r2_hidden(k4_tarski(esk5_3(X28,X29,X30),X30),X28)
        | X29 != k2_relat_1(X28) )
      & ( ~ r2_hidden(k4_tarski(X33,X32),X28)
        | r2_hidden(X32,X29)
        | X29 != k2_relat_1(X28) )
      & ( ~ r2_hidden(esk6_2(X34,X35),X35)
        | ~ r2_hidden(k4_tarski(X37,esk6_2(X34,X35)),X34)
        | X35 = k2_relat_1(X34) )
      & ( r2_hidden(esk6_2(X34,X35),X35)
        | r2_hidden(k4_tarski(esk7_2(X34,X35),esk6_2(X34,X35)),X34)
        | X35 = k2_relat_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

fof(c_0_13,plain,(
    ! [X6,X7,X9,X10,X11] :
      ( ( r2_hidden(esk1_2(X6,X7),X6)
        | r1_xboole_0(X6,X7) )
      & ( r2_hidden(esk1_2(X6,X7),X7)
        | r1_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X11,X9)
        | ~ r2_hidden(X11,X10)
        | ~ r1_xboole_0(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_14,plain,(
    ! [X39,X40,X41,X43] :
      ( ( r2_hidden(esk8_3(X39,X40,X41),k2_relat_1(X41))
        | ~ r2_hidden(X39,k10_relat_1(X41,X40))
        | ~ v1_relat_1(X41) )
      & ( r2_hidden(k4_tarski(X39,esk8_3(X39,X40,X41)),X41)
        | ~ r2_hidden(X39,k10_relat_1(X41,X40))
        | ~ v1_relat_1(X41) )
      & ( r2_hidden(esk8_3(X39,X40,X41),X40)
        | ~ r2_hidden(X39,k10_relat_1(X41,X40))
        | ~ v1_relat_1(X41) )
      & ( ~ r2_hidden(X43,k2_relat_1(X41))
        | ~ r2_hidden(k4_tarski(X39,X43),X41)
        | ~ r2_hidden(X43,X40)
        | r2_hidden(X39,k10_relat_1(X41,X40))
        | ~ v1_relat_1(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

cnf(c_0_15,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(esk6_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk7_2(X1,X2),esk6_2(X1,X2)),X1)
    | X2 = k2_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r2_hidden(esk8_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(esk5_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk6_2(k1_xboole_0,X1),X1)
    | X2 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( k10_relat_1(X2,X1) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t173_relat_1])).

cnf(c_0_23,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(esk8_3(X2,X3,X1),X4)
    | ~ r2_hidden(X2,k10_relat_1(X1,X3))
    | ~ r1_xboole_0(X4,X3) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,plain,
    ( r2_hidden(esk8_3(X1,X2,X3),k2_relat_1(X3))
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,plain,
    ( X1 != k1_xboole_0
    | X2 != k1_xboole_0
    | ~ r2_hidden(X3,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_20]),c_0_17])).

cnf(c_0_26,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,plain,
    ( X1 != k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X3,k10_relat_1(X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_19])).

cnf(c_0_28,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk6_2(k1_xboole_0,X1),X1) ),
    inference(er,[status(thm)],[c_0_21])).

fof(c_0_29,negated_conjecture,
    ( v1_relat_1(esk10_0)
    & ( k10_relat_1(esk10_0,esk9_0) != k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(esk10_0),esk9_0) )
    & ( k10_relat_1(esk10_0,esk9_0) = k1_xboole_0
      | r1_xboole_0(k2_relat_1(esk10_0),esk9_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).

fof(c_0_30,plain,(
    ! [X16,X17,X18,X19,X21,X22,X23,X24,X26] :
      ( ( r2_hidden(k4_tarski(X19,esk2_4(X16,X17,X18,X19)),X16)
        | ~ r2_hidden(X19,X18)
        | X18 != k10_relat_1(X16,X17)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(esk2_4(X16,X17,X18,X19),X17)
        | ~ r2_hidden(X19,X18)
        | X18 != k10_relat_1(X16,X17)
        | ~ v1_relat_1(X16) )
      & ( ~ r2_hidden(k4_tarski(X21,X22),X16)
        | ~ r2_hidden(X22,X17)
        | r2_hidden(X21,X18)
        | X18 != k10_relat_1(X16,X17)
        | ~ v1_relat_1(X16) )
      & ( ~ r2_hidden(esk3_3(X16,X23,X24),X24)
        | ~ r2_hidden(k4_tarski(esk3_3(X16,X23,X24),X26),X16)
        | ~ r2_hidden(X26,X23)
        | X24 = k10_relat_1(X16,X23)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(k4_tarski(esk3_3(X16,X23,X24),esk4_3(X16,X23,X24)),X16)
        | r2_hidden(esk3_3(X16,X23,X24),X24)
        | X24 = k10_relat_1(X16,X23)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(esk4_3(X16,X23,X24),X23)
        | r2_hidden(esk3_3(X16,X23,X24),X24)
        | X24 = k10_relat_1(X16,X23)
        | ~ v1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

cnf(c_0_31,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k10_relat_1(X1,X3))
    | ~ r1_xboole_0(k2_relat_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,plain,
    ( r1_xboole_0(X1,X2)
    | X3 != k1_xboole_0
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,plain,
    ( k10_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | X2 != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X5 != k10_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(esk6_2(k1_xboole_0,X1),X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_28])).

cnf(c_0_37,plain,
    ( r1_xboole_0(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r1_xboole_0(k2_relat_1(X2),X3) ),
    inference(spm,[status(thm)],[c_0_31,c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( k10_relat_1(esk10_0,esk9_0) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(esk10_0),esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( r1_xboole_0(X1,X2)
    | X2 != k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( k10_relat_1(esk10_0,k1_xboole_0) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,plain,
    ( r1_xboole_0(X1,k1_xboole_0)
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_15,c_0_26])).

cnf(c_0_42,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X4)
    | X4 != k10_relat_1(X1,X5)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,X5)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_20])).

cnf(c_0_43,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_28])).

cnf(c_0_44,negated_conjecture,
    ( r1_xboole_0(X1,k10_relat_1(esk10_0,esk9_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_34])]),c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( k10_relat_1(esk10_0,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_46,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_47,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),k10_relat_1(X1,X4))
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,X4)
    | ~ r2_hidden(X3,X2) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( k10_relat_1(esk10_0,esk9_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_45]),c_0_34]),c_0_46])])).

cnf(c_0_50,negated_conjecture,
    ( X1 != k2_relat_1(esk10_0)
    | ~ r2_hidden(X2,esk9_0)
    | ~ r2_hidden(X2,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_34])]),c_0_49])).

cnf(c_0_51,negated_conjecture,
    ( k10_relat_1(esk10_0,esk9_0) != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(esk10_0),esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_52,negated_conjecture,
    ( r1_xboole_0(X1,esk9_0)
    | X2 != k2_relat_1(esk10_0)
    | ~ r2_hidden(esk1_2(X1,esk9_0),X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_26])).

cnf(c_0_53,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_54,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(esk10_0),esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_48])])).

cnf(c_0_55,negated_conjecture,
    ( r1_xboole_0(X1,esk9_0)
    | X1 != k2_relat_1(esk10_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_54,c_0_55]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:46:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 1.02/1.19  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 1.02/1.19  # and selection function SelectMaxLComplexAvoidPosPred.
% 1.02/1.19  #
% 1.02/1.19  # Preprocessing time       : 0.029 s
% 1.02/1.19  # Presaturation interreduction done
% 1.02/1.19  
% 1.02/1.19  # Proof found!
% 1.02/1.19  # SZS status Theorem
% 1.02/1.19  # SZS output start CNFRefutation
% 1.02/1.19  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.02/1.19  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.02/1.19  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 1.02/1.19  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.02/1.19  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 1.02/1.19  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.02/1.19  fof(t173_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 1.02/1.19  fof(d14_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X4,X5),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 1.02/1.19  fof(c_0_8, plain, ![X14, X15]:~r2_hidden(X14,k2_zfmisc_1(X14,X15)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 1.02/1.19  fof(c_0_9, plain, ![X12, X13]:((k2_zfmisc_1(X12,X13)!=k1_xboole_0|(X12=k1_xboole_0|X13=k1_xboole_0))&((X12!=k1_xboole_0|k2_zfmisc_1(X12,X13)=k1_xboole_0)&(X13!=k1_xboole_0|k2_zfmisc_1(X12,X13)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 1.02/1.19  cnf(c_0_10, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.02/1.19  cnf(c_0_11, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.02/1.19  fof(c_0_12, plain, ![X28, X29, X30, X32, X33, X34, X35, X37]:(((~r2_hidden(X30,X29)|r2_hidden(k4_tarski(esk5_3(X28,X29,X30),X30),X28)|X29!=k2_relat_1(X28))&(~r2_hidden(k4_tarski(X33,X32),X28)|r2_hidden(X32,X29)|X29!=k2_relat_1(X28)))&((~r2_hidden(esk6_2(X34,X35),X35)|~r2_hidden(k4_tarski(X37,esk6_2(X34,X35)),X34)|X35=k2_relat_1(X34))&(r2_hidden(esk6_2(X34,X35),X35)|r2_hidden(k4_tarski(esk7_2(X34,X35),esk6_2(X34,X35)),X34)|X35=k2_relat_1(X34)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 1.02/1.19  fof(c_0_13, plain, ![X6, X7, X9, X10, X11]:(((r2_hidden(esk1_2(X6,X7),X6)|r1_xboole_0(X6,X7))&(r2_hidden(esk1_2(X6,X7),X7)|r1_xboole_0(X6,X7)))&(~r2_hidden(X11,X9)|~r2_hidden(X11,X10)|~r1_xboole_0(X9,X10))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 1.02/1.19  fof(c_0_14, plain, ![X39, X40, X41, X43]:((((r2_hidden(esk8_3(X39,X40,X41),k2_relat_1(X41))|~r2_hidden(X39,k10_relat_1(X41,X40))|~v1_relat_1(X41))&(r2_hidden(k4_tarski(X39,esk8_3(X39,X40,X41)),X41)|~r2_hidden(X39,k10_relat_1(X41,X40))|~v1_relat_1(X41)))&(r2_hidden(esk8_3(X39,X40,X41),X40)|~r2_hidden(X39,k10_relat_1(X41,X40))|~v1_relat_1(X41)))&(~r2_hidden(X43,k2_relat_1(X41))|~r2_hidden(k4_tarski(X39,X43),X41)|~r2_hidden(X43,X40)|r2_hidden(X39,k10_relat_1(X41,X40))|~v1_relat_1(X41))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 1.02/1.19  cnf(c_0_15, plain, (X1!=k1_xboole_0|~r2_hidden(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 1.02/1.19  cnf(c_0_16, plain, (r2_hidden(esk6_2(X1,X2),X2)|r2_hidden(k4_tarski(esk7_2(X1,X2),esk6_2(X1,X2)),X1)|X2=k2_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.02/1.19  cnf(c_0_17, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 1.02/1.19  cnf(c_0_18, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.02/1.19  cnf(c_0_19, plain, (r2_hidden(esk8_3(X1,X2,X3),X2)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.02/1.19  cnf(c_0_20, plain, (r2_hidden(k4_tarski(esk5_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.02/1.19  cnf(c_0_21, plain, (X1=k1_xboole_0|r2_hidden(esk6_2(k1_xboole_0,X1),X1)|X2!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])).
% 1.02/1.19  fof(c_0_22, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1)))), inference(assume_negation,[status(cth)],[t173_relat_1])).
% 1.02/1.19  cnf(c_0_23, plain, (~v1_relat_1(X1)|~r2_hidden(esk8_3(X2,X3,X1),X4)|~r2_hidden(X2,k10_relat_1(X1,X3))|~r1_xboole_0(X4,X3)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 1.02/1.19  cnf(c_0_24, plain, (r2_hidden(esk8_3(X1,X2,X3),k2_relat_1(X3))|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.02/1.19  cnf(c_0_25, plain, (X1!=k1_xboole_0|X2!=k1_xboole_0|~r2_hidden(X3,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_20]), c_0_17])).
% 1.02/1.19  cnf(c_0_26, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.02/1.19  cnf(c_0_27, plain, (X1!=k1_xboole_0|~v1_relat_1(X2)|~r2_hidden(X3,k10_relat_1(X2,k1_xboole_0))), inference(spm,[status(thm)],[c_0_15, c_0_19])).
% 1.02/1.19  cnf(c_0_28, plain, (X1=k1_xboole_0|r2_hidden(esk6_2(k1_xboole_0,X1),X1)), inference(er,[status(thm)],[c_0_21])).
% 1.02/1.19  fof(c_0_29, negated_conjecture, (v1_relat_1(esk10_0)&((k10_relat_1(esk10_0,esk9_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk10_0),esk9_0))&(k10_relat_1(esk10_0,esk9_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk10_0),esk9_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).
% 1.02/1.19  fof(c_0_30, plain, ![X16, X17, X18, X19, X21, X22, X23, X24, X26]:((((r2_hidden(k4_tarski(X19,esk2_4(X16,X17,X18,X19)),X16)|~r2_hidden(X19,X18)|X18!=k10_relat_1(X16,X17)|~v1_relat_1(X16))&(r2_hidden(esk2_4(X16,X17,X18,X19),X17)|~r2_hidden(X19,X18)|X18!=k10_relat_1(X16,X17)|~v1_relat_1(X16)))&(~r2_hidden(k4_tarski(X21,X22),X16)|~r2_hidden(X22,X17)|r2_hidden(X21,X18)|X18!=k10_relat_1(X16,X17)|~v1_relat_1(X16)))&((~r2_hidden(esk3_3(X16,X23,X24),X24)|(~r2_hidden(k4_tarski(esk3_3(X16,X23,X24),X26),X16)|~r2_hidden(X26,X23))|X24=k10_relat_1(X16,X23)|~v1_relat_1(X16))&((r2_hidden(k4_tarski(esk3_3(X16,X23,X24),esk4_3(X16,X23,X24)),X16)|r2_hidden(esk3_3(X16,X23,X24),X24)|X24=k10_relat_1(X16,X23)|~v1_relat_1(X16))&(r2_hidden(esk4_3(X16,X23,X24),X23)|r2_hidden(esk3_3(X16,X23,X24),X24)|X24=k10_relat_1(X16,X23)|~v1_relat_1(X16))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).
% 1.02/1.19  cnf(c_0_31, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k10_relat_1(X1,X3))|~r1_xboole_0(k2_relat_1(X1),X3)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 1.02/1.19  cnf(c_0_32, plain, (r1_xboole_0(X1,X2)|X3!=k1_xboole_0|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 1.02/1.19  cnf(c_0_33, plain, (k10_relat_1(X1,k1_xboole_0)=k1_xboole_0|X2!=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 1.02/1.19  cnf(c_0_34, negated_conjecture, (v1_relat_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.02/1.19  cnf(c_0_35, plain, (r2_hidden(X1,X5)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X2,X4)|X5!=k10_relat_1(X3,X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.02/1.19  cnf(c_0_36, plain, (X1=k1_xboole_0|~r2_hidden(esk6_2(k1_xboole_0,X1),X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_18, c_0_28])).
% 1.02/1.19  cnf(c_0_37, plain, (r1_xboole_0(X1,k10_relat_1(X2,X3))|~v1_relat_1(X2)|~r1_xboole_0(k2_relat_1(X2),X3)), inference(spm,[status(thm)],[c_0_31, c_0_26])).
% 1.02/1.19  cnf(c_0_38, negated_conjecture, (k10_relat_1(esk10_0,esk9_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk10_0),esk9_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.02/1.19  cnf(c_0_39, plain, (r1_xboole_0(X1,X2)|X2!=k1_xboole_0), inference(er,[status(thm)],[c_0_32])).
% 1.02/1.19  cnf(c_0_40, negated_conjecture, (k10_relat_1(esk10_0,k1_xboole_0)=k1_xboole_0|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 1.02/1.19  cnf(c_0_41, plain, (r1_xboole_0(X1,k1_xboole_0)|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_15, c_0_26])).
% 1.02/1.19  cnf(c_0_42, plain, (r2_hidden(esk5_3(X1,X2,X3),X4)|X4!=k10_relat_1(X1,X5)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~r2_hidden(X3,X5)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_35, c_0_20])).
% 1.02/1.19  cnf(c_0_43, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_36, c_0_28])).
% 1.02/1.19  cnf(c_0_44, negated_conjecture, (r1_xboole_0(X1,k10_relat_1(esk10_0,esk9_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_34])]), c_0_39])).
% 1.02/1.19  cnf(c_0_45, negated_conjecture, (k10_relat_1(esk10_0,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_40])).
% 1.02/1.19  cnf(c_0_46, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(er,[status(thm)],[c_0_41])).
% 1.02/1.19  cnf(c_0_47, plain, (r2_hidden(esk5_3(X1,X2,X3),k10_relat_1(X1,X4))|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~r2_hidden(X3,X4)|~r2_hidden(X3,X2)), inference(er,[status(thm)],[c_0_42])).
% 1.02/1.19  cnf(c_0_48, negated_conjecture, (k10_relat_1(esk10_0,esk9_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 1.02/1.19  cnf(c_0_49, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_45]), c_0_34]), c_0_46])])).
% 1.02/1.19  cnf(c_0_50, negated_conjecture, (X1!=k2_relat_1(esk10_0)|~r2_hidden(X2,esk9_0)|~r2_hidden(X2,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_34])]), c_0_49])).
% 1.02/1.19  cnf(c_0_51, negated_conjecture, (k10_relat_1(esk10_0,esk9_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk10_0),esk9_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.02/1.19  cnf(c_0_52, negated_conjecture, (r1_xboole_0(X1,esk9_0)|X2!=k2_relat_1(esk10_0)|~r2_hidden(esk1_2(X1,esk9_0),X2)), inference(spm,[status(thm)],[c_0_50, c_0_26])).
% 1.02/1.19  cnf(c_0_53, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.02/1.19  cnf(c_0_54, negated_conjecture, (~r1_xboole_0(k2_relat_1(esk10_0),esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_48])])).
% 1.02/1.19  cnf(c_0_55, negated_conjecture, (r1_xboole_0(X1,esk9_0)|X1!=k2_relat_1(esk10_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 1.02/1.19  cnf(c_0_56, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_54, c_0_55]), ['proof']).
% 1.02/1.19  # SZS output end CNFRefutation
% 1.02/1.19  # Proof object total steps             : 57
% 1.02/1.19  # Proof object clause steps            : 41
% 1.02/1.19  # Proof object formula steps           : 16
% 1.02/1.19  # Proof object conjectures             : 16
% 1.02/1.19  # Proof object clause conjectures      : 13
% 1.02/1.19  # Proof object formula conjectures     : 3
% 1.02/1.19  # Proof object initial clauses used    : 14
% 1.02/1.19  # Proof object initial formulas used   : 8
% 1.02/1.19  # Proof object generating inferences   : 26
% 1.02/1.19  # Proof object simplifying inferences  : 13
% 1.02/1.19  # Training examples: 0 positive, 0 negative
% 1.02/1.19  # Parsed axioms                        : 8
% 1.02/1.19  # Removed by relevancy pruning/SinE    : 0
% 1.02/1.19  # Initial clauses                      : 26
% 1.02/1.19  # Removed in clause preprocessing      : 0
% 1.02/1.19  # Initial clauses in saturation        : 26
% 1.02/1.19  # Processed clauses                    : 10968
% 1.02/1.19  # ...of these trivial                  : 48
% 1.02/1.19  # ...subsumed                          : 9777
% 1.02/1.19  # ...remaining for further processing  : 1143
% 1.02/1.19  # Other redundant clauses eliminated   : 0
% 1.02/1.19  # Clauses deleted for lack of memory   : 0
% 1.02/1.19  # Backward-subsumed                    : 80
% 1.02/1.19  # Backward-rewritten                   : 10
% 1.02/1.19  # Generated clauses                    : 71989
% 1.02/1.19  # ...of the previous two non-trivial   : 66428
% 1.02/1.19  # Contextual simplify-reflections      : 23
% 1.02/1.19  # Paramodulations                      : 71707
% 1.02/1.19  # Factorizations                       : 2
% 1.02/1.19  # Equation resolutions                 : 280
% 1.02/1.19  # Propositional unsat checks           : 0
% 1.02/1.19  #    Propositional check models        : 0
% 1.02/1.19  #    Propositional check unsatisfiable : 0
% 1.02/1.19  #    Propositional clauses             : 0
% 1.02/1.19  #    Propositional clauses after purity: 0
% 1.02/1.19  #    Propositional unsat core size     : 0
% 1.02/1.19  #    Propositional preprocessing time  : 0.000
% 1.02/1.19  #    Propositional encoding time       : 0.000
% 1.02/1.19  #    Propositional solver time         : 0.000
% 1.02/1.19  #    Success case prop preproc time    : 0.000
% 1.02/1.19  #    Success case prop encoding time   : 0.000
% 1.02/1.19  #    Success case prop solver time     : 0.000
% 1.02/1.19  # Current number of processed clauses  : 1027
% 1.02/1.19  #    Positive orientable unit clauses  : 7
% 1.02/1.19  #    Positive unorientable unit clauses: 0
% 1.02/1.19  #    Negative unit clauses             : 7
% 1.02/1.19  #    Non-unit-clauses                  : 1013
% 1.02/1.19  # Current number of unprocessed clauses: 55255
% 1.02/1.19  # ...number of literals in the above   : 317683
% 1.02/1.19  # Current number of archived formulas  : 0
% 1.02/1.19  # Current number of archived clauses   : 116
% 1.02/1.19  # Clause-clause subsumption calls (NU) : 424607
% 1.02/1.19  # Rec. Clause-clause subsumption calls : 137660
% 1.02/1.19  # Non-unit clause-clause subsumptions  : 6248
% 1.02/1.19  # Unit Clause-clause subsumption calls : 339
% 1.02/1.19  # Rewrite failures with RHS unbound    : 0
% 1.02/1.19  # BW rewrite match attempts            : 4
% 1.02/1.19  # BW rewrite match successes           : 4
% 1.02/1.19  # Condensation attempts                : 0
% 1.02/1.19  # Condensation successes               : 0
% 1.02/1.19  # Termbank termtop insertions          : 1170434
% 1.02/1.19  
% 1.02/1.19  # -------------------------------------------------
% 1.02/1.19  # User time                : 0.817 s
% 1.02/1.19  # System time              : 0.034 s
% 1.02/1.19  # Total time               : 0.851 s
% 1.02/1.19  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
