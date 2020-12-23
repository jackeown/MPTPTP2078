%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:36 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 191 expanded)
%              Number of clauses        :   44 (  96 expanded)
%              Number of leaves         :    9 (  44 expanded)
%              Depth                    :   14
%              Number of atoms          :  200 ( 606 expanded)
%              Number of equality atoms :   60 ( 243 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(t168_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,X1) = k10_relat_1(X2,k3_xboole_0(k2_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

fof(t173_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k10_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(c_0_9,plain,(
    ! [X34,X35] :
      ( ( k2_zfmisc_1(X34,X35) != k1_xboole_0
        | X34 = k1_xboole_0
        | X35 = k1_xboole_0 )
      & ( X34 != k1_xboole_0
        | k2_zfmisc_1(X34,X35) = k1_xboole_0 )
      & ( X35 != k1_xboole_0
        | k2_zfmisc_1(X34,X35) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_10,plain,(
    ! [X36,X37] : ~ r2_hidden(X36,k2_zfmisc_1(X36,X37)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_11,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X23,X24] :
      ( ( ~ r2_hidden(esk3_2(X23,X24),X23)
        | ~ r2_hidden(esk3_2(X23,X24),X24)
        | X23 = X24 )
      & ( r2_hidden(esk3_2(X23,X24),X23)
        | r2_hidden(esk3_2(X23,X24),X24)
        | X23 = X24 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

fof(c_0_15,plain,(
    ! [X26,X27,X29,X30,X31] :
      ( ( r1_xboole_0(X26,X27)
        | r2_hidden(esk4_2(X26,X27),k3_xboole_0(X26,X27)) )
      & ( ~ r2_hidden(X31,k3_xboole_0(X29,X30))
        | ~ r1_xboole_0(X29,X30) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r2_hidden(esk3_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X40,X41,X42,X44,X45,X46,X47,X49] :
      ( ( ~ r2_hidden(X42,X41)
        | r2_hidden(k4_tarski(esk5_3(X40,X41,X42),X42),X40)
        | X41 != k2_relat_1(X40) )
      & ( ~ r2_hidden(k4_tarski(X45,X44),X40)
        | r2_hidden(X44,X41)
        | X41 != k2_relat_1(X40) )
      & ( ~ r2_hidden(esk6_2(X46,X47),X47)
        | ~ r2_hidden(k4_tarski(X49,esk6_2(X46,X47)),X46)
        | X47 = k2_relat_1(X46) )
      & ( r2_hidden(esk6_2(X46,X47),X47)
        | r2_hidden(k4_tarski(esk7_2(X46,X47),esk6_2(X46,X47)),X46)
        | X47 = k2_relat_1(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

fof(c_0_19,plain,(
    ! [X56,X57] :
      ( ~ v1_relat_1(X57)
      | k10_relat_1(X57,X56) = k10_relat_1(X57,k3_xboole_0(k2_relat_1(X57),X56)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_relat_1])])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk3_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( k10_relat_1(X2,X1) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t173_relat_1])).

fof(c_0_23,plain,(
    ! [X51,X52,X53,X55] :
      ( ( r2_hidden(esk8_3(X51,X52,X53),k2_relat_1(X53))
        | ~ r2_hidden(X51,k10_relat_1(X53,X52))
        | ~ v1_relat_1(X53) )
      & ( r2_hidden(k4_tarski(X51,esk8_3(X51,X52,X53)),X53)
        | ~ r2_hidden(X51,k10_relat_1(X53,X52))
        | ~ v1_relat_1(X53) )
      & ( r2_hidden(esk8_3(X51,X52,X53),X52)
        | ~ r2_hidden(X51,k10_relat_1(X53,X52))
        | ~ v1_relat_1(X53) )
      & ( ~ r2_hidden(X55,k2_relat_1(X53))
        | ~ r2_hidden(k4_tarski(X51,X55),X53)
        | ~ r2_hidden(X55,X52)
        | r2_hidden(X51,k10_relat_1(X53,X52))
        | ~ v1_relat_1(X53) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

cnf(c_0_24,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k10_relat_1(X1,X2) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_27,negated_conjecture,
    ( v1_relat_1(esk10_0)
    & ( k10_relat_1(esk10_0,esk9_0) != k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(esk10_0),esk9_0) )
    & ( k10_relat_1(esk10_0,esk9_0) = k1_xboole_0
      | r1_xboole_0(k2_relat_1(esk10_0),esk9_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).

cnf(c_0_28,plain,
    ( r2_hidden(X3,k10_relat_1(X2,X4))
    | ~ r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(esk5_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_31,plain,
    ( k10_relat_1(X1,k1_xboole_0) = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( k10_relat_1(esk10_0,esk9_0) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(esk10_0),esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_34,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(csr,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,plain,
    ( r2_hidden(k4_tarski(esk5_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( k10_relat_1(esk10_0,esk9_0) = k10_relat_1(esk10_0,k1_xboole_0)
    | k10_relat_1(esk10_0,esk9_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( r2_hidden(esk5_3(X1,k2_relat_1(X1),X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( k10_relat_1(esk10_0,esk9_0) = k1_xboole_0
    | k10_relat_1(esk10_0,k1_xboole_0) != k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_37])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_43,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk4_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_45,plain,
    ( r2_hidden(esk6_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk7_2(X1,X2),esk6_2(X1,X2)),X1)
    | X2 = k2_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_46,negated_conjecture,
    ( k10_relat_1(esk10_0,k1_xboole_0) != k1_xboole_0
    | ~ r2_hidden(X1,k2_relat_1(esk10_0))
    | ~ r2_hidden(X1,esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_33])]),c_0_16])).

cnf(c_0_47,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk4_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,plain,
    ( r2_hidden(esk8_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_49,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk3_2(k1_xboole_0,k3_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_21])).

cnf(c_0_50,plain,
    ( X1 = k2_relat_1(k1_xboole_0)
    | r2_hidden(esk6_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(esk10_0),X1)
    | k10_relat_1(esk10_0,k1_xboole_0) != k1_xboole_0
    | ~ r2_hidden(esk4_2(k2_relat_1(esk10_0),X1),esk9_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk4_2(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_43])).

cnf(c_0_53,plain,
    ( r2_hidden(esk8_3(X1,k3_xboole_0(k2_relat_1(X2),X3),X2),k3_xboole_0(k2_relat_1(X2),X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k10_relat_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_25])).

cnf(c_0_54,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_49])).

cnf(c_0_55,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( k10_relat_1(esk10_0,esk9_0) != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(esk10_0),esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_57,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(esk10_0),esk9_0)
    | k10_relat_1(esk10_0,k1_xboole_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_58,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k10_relat_1(X1,k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_16])).

cnf(c_0_59,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk6_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[c_0_50,c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( k10_relat_1(esk10_0,k1_xboole_0) != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_41])).

cnf(c_0_61,plain,
    ( k10_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_33])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n023.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:55:05 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.57  # AutoSched0-Mode selected heuristic U_____100_C09_12_F1_SE_CS_SP_PS_S5PRR_RG_ND_S04AN
% 0.18/0.57  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.18/0.57  #
% 0.18/0.57  # Preprocessing time       : 0.029 s
% 0.18/0.57  # Presaturation interreduction done
% 0.18/0.57  
% 0.18/0.57  # Proof found!
% 0.18/0.57  # SZS status Theorem
% 0.18/0.57  # SZS output start CNFRefutation
% 0.18/0.57  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.18/0.57  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.18/0.57  fof(t2_tarski, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)<=>r2_hidden(X3,X2))=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 0.18/0.57  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.18/0.57  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 0.18/0.57  fof(t168_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k10_relat_1(X2,X1)=k10_relat_1(X2,k3_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 0.18/0.57  fof(t173_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 0.18/0.57  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 0.18/0.57  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.18/0.57  fof(c_0_9, plain, ![X34, X35]:((k2_zfmisc_1(X34,X35)!=k1_xboole_0|(X34=k1_xboole_0|X35=k1_xboole_0))&((X34!=k1_xboole_0|k2_zfmisc_1(X34,X35)=k1_xboole_0)&(X35!=k1_xboole_0|k2_zfmisc_1(X34,X35)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.18/0.57  fof(c_0_10, plain, ![X36, X37]:~r2_hidden(X36,k2_zfmisc_1(X36,X37)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.18/0.57  cnf(c_0_11, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.57  cnf(c_0_12, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.57  cnf(c_0_13, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_11])).
% 0.18/0.57  fof(c_0_14, plain, ![X23, X24]:((~r2_hidden(esk3_2(X23,X24),X23)|~r2_hidden(esk3_2(X23,X24),X24)|X23=X24)&(r2_hidden(esk3_2(X23,X24),X23)|r2_hidden(esk3_2(X23,X24),X24)|X23=X24)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).
% 0.18/0.57  fof(c_0_15, plain, ![X26, X27, X29, X30, X31]:((r1_xboole_0(X26,X27)|r2_hidden(esk4_2(X26,X27),k3_xboole_0(X26,X27)))&(~r2_hidden(X31,k3_xboole_0(X29,X30))|~r1_xboole_0(X29,X30))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.18/0.57  cnf(c_0_16, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.18/0.57  cnf(c_0_17, plain, (r2_hidden(esk3_2(X1,X2),X1)|r2_hidden(esk3_2(X1,X2),X2)|X1=X2), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.57  fof(c_0_18, plain, ![X40, X41, X42, X44, X45, X46, X47, X49]:(((~r2_hidden(X42,X41)|r2_hidden(k4_tarski(esk5_3(X40,X41,X42),X42),X40)|X41!=k2_relat_1(X40))&(~r2_hidden(k4_tarski(X45,X44),X40)|r2_hidden(X44,X41)|X41!=k2_relat_1(X40)))&((~r2_hidden(esk6_2(X46,X47),X47)|~r2_hidden(k4_tarski(X49,esk6_2(X46,X47)),X46)|X47=k2_relat_1(X46))&(r2_hidden(esk6_2(X46,X47),X47)|r2_hidden(k4_tarski(esk7_2(X46,X47),esk6_2(X46,X47)),X46)|X47=k2_relat_1(X46)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.18/0.57  fof(c_0_19, plain, ![X56, X57]:(~v1_relat_1(X57)|k10_relat_1(X57,X56)=k10_relat_1(X57,k3_xboole_0(k2_relat_1(X57),X56))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_relat_1])])).
% 0.18/0.57  cnf(c_0_20, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.57  cnf(c_0_21, plain, (k1_xboole_0=X1|r2_hidden(esk3_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.18/0.57  fof(c_0_22, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1)))), inference(assume_negation,[status(cth)],[t173_relat_1])).
% 0.18/0.57  fof(c_0_23, plain, ![X51, X52, X53, X55]:((((r2_hidden(esk8_3(X51,X52,X53),k2_relat_1(X53))|~r2_hidden(X51,k10_relat_1(X53,X52))|~v1_relat_1(X53))&(r2_hidden(k4_tarski(X51,esk8_3(X51,X52,X53)),X53)|~r2_hidden(X51,k10_relat_1(X53,X52))|~v1_relat_1(X53)))&(r2_hidden(esk8_3(X51,X52,X53),X52)|~r2_hidden(X51,k10_relat_1(X53,X52))|~v1_relat_1(X53)))&(~r2_hidden(X55,k2_relat_1(X53))|~r2_hidden(k4_tarski(X51,X55),X53)|~r2_hidden(X55,X52)|r2_hidden(X51,k10_relat_1(X53,X52))|~v1_relat_1(X53))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.18/0.57  cnf(c_0_24, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.57  cnf(c_0_25, plain, (k10_relat_1(X1,X2)=k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.57  cnf(c_0_26, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.18/0.57  fof(c_0_27, negated_conjecture, (v1_relat_1(esk10_0)&((k10_relat_1(esk10_0,esk9_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk10_0),esk9_0))&(k10_relat_1(esk10_0,esk9_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk10_0),esk9_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).
% 0.18/0.57  cnf(c_0_28, plain, (r2_hidden(X3,k10_relat_1(X2,X4))|~r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,X4)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.57  cnf(c_0_29, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)), inference(er,[status(thm)],[c_0_24])).
% 0.18/0.57  cnf(c_0_30, plain, (r2_hidden(k4_tarski(esk5_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.57  cnf(c_0_31, plain, (k10_relat_1(X1,k1_xboole_0)=k10_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_xboole_0(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.18/0.57  cnf(c_0_32, negated_conjecture, (k10_relat_1(esk10_0,esk9_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk10_0),esk9_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.18/0.57  cnf(c_0_33, negated_conjecture, (v1_relat_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.18/0.57  fof(c_0_34, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6))&(r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k3_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k3_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))&(r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.18/0.57  cnf(c_0_35, plain, (r2_hidden(X1,k10_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X4),X2)|~r2_hidden(X4,X3)), inference(csr,[status(thm)],[c_0_28, c_0_29])).
% 0.18/0.57  cnf(c_0_36, plain, (r2_hidden(k4_tarski(esk5_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_30])).
% 0.18/0.57  cnf(c_0_37, negated_conjecture, (k10_relat_1(esk10_0,esk9_0)=k10_relat_1(esk10_0,k1_xboole_0)|k10_relat_1(esk10_0,esk9_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])])).
% 0.18/0.57  cnf(c_0_38, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.57  cnf(c_0_39, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.57  cnf(c_0_40, plain, (r2_hidden(esk5_3(X1,k2_relat_1(X1),X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.18/0.57  cnf(c_0_41, negated_conjecture, (k10_relat_1(esk10_0,esk9_0)=k1_xboole_0|k10_relat_1(esk10_0,k1_xboole_0)!=k1_xboole_0), inference(ef,[status(thm)],[c_0_37])).
% 0.18/0.57  cnf(c_0_42, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_38])).
% 0.18/0.57  cnf(c_0_43, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk4_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.57  cnf(c_0_44, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_39])).
% 0.18/0.57  cnf(c_0_45, plain, (r2_hidden(esk6_2(X1,X2),X2)|r2_hidden(k4_tarski(esk7_2(X1,X2),esk6_2(X1,X2)),X1)|X2=k2_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.57  cnf(c_0_46, negated_conjecture, (k10_relat_1(esk10_0,k1_xboole_0)!=k1_xboole_0|~r2_hidden(X1,k2_relat_1(esk10_0))|~r2_hidden(X1,esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_33])]), c_0_16])).
% 0.18/0.57  cnf(c_0_47, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk4_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.18/0.57  cnf(c_0_48, plain, (r2_hidden(esk8_3(X1,X2,X3),X2)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.57  cnf(c_0_49, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|r2_hidden(esk3_2(k1_xboole_0,k3_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_44, c_0_21])).
% 0.18/0.57  cnf(c_0_50, plain, (X1=k2_relat_1(k1_xboole_0)|r2_hidden(esk6_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_16, c_0_45])).
% 0.18/0.57  cnf(c_0_51, negated_conjecture, (r1_xboole_0(k2_relat_1(esk10_0),X1)|k10_relat_1(esk10_0,k1_xboole_0)!=k1_xboole_0|~r2_hidden(esk4_2(k2_relat_1(esk10_0),X1),esk9_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.18/0.57  cnf(c_0_52, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk4_2(X1,X2),X2)), inference(spm,[status(thm)],[c_0_44, c_0_43])).
% 0.18/0.57  cnf(c_0_53, plain, (r2_hidden(esk8_3(X1,k3_xboole_0(k2_relat_1(X2),X3),X2),k3_xboole_0(k2_relat_1(X2),X3))|~v1_relat_1(X2)|~r2_hidden(X1,k10_relat_1(X2,X3))), inference(spm,[status(thm)],[c_0_48, c_0_25])).
% 0.18/0.57  cnf(c_0_54, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_16, c_0_49])).
% 0.18/0.57  cnf(c_0_55, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_16, c_0_50])).
% 0.18/0.57  cnf(c_0_56, negated_conjecture, (k10_relat_1(esk10_0,esk9_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk10_0),esk9_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.18/0.57  cnf(c_0_57, negated_conjecture, (r1_xboole_0(k2_relat_1(esk10_0),esk9_0)|k10_relat_1(esk10_0,k1_xboole_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.18/0.57  cnf(c_0_58, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k10_relat_1(X1,k1_xboole_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_16])).
% 0.18/0.57  cnf(c_0_59, plain, (X1=k1_xboole_0|r2_hidden(esk6_2(k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[c_0_50, c_0_55])).
% 0.18/0.57  cnf(c_0_60, negated_conjecture, (k10_relat_1(esk10_0,k1_xboole_0)!=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_41])).
% 0.18/0.57  cnf(c_0_61, plain, (k10_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.18/0.57  cnf(c_0_62, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_33])]), ['proof']).
% 0.18/0.57  # SZS output end CNFRefutation
% 0.18/0.57  # Proof object total steps             : 63
% 0.18/0.57  # Proof object clause steps            : 44
% 0.18/0.57  # Proof object formula steps           : 19
% 0.18/0.57  # Proof object conjectures             : 13
% 0.18/0.57  # Proof object clause conjectures      : 10
% 0.18/0.57  # Proof object formula conjectures     : 3
% 0.18/0.57  # Proof object initial clauses used    : 16
% 0.18/0.57  # Proof object initial formulas used   : 9
% 0.18/0.57  # Proof object generating inferences   : 21
% 0.18/0.57  # Proof object simplifying inferences  : 16
% 0.18/0.57  # Training examples: 0 positive, 0 negative
% 0.18/0.57  # Parsed axioms                        : 12
% 0.18/0.57  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.57  # Initial clauses                      : 34
% 0.18/0.57  # Removed in clause preprocessing      : 0
% 0.18/0.57  # Initial clauses in saturation        : 34
% 0.18/0.57  # Processed clauses                    : 2983
% 0.18/0.57  # ...of these trivial                  : 7
% 0.18/0.57  # ...subsumed                          : 2451
% 0.18/0.57  # ...remaining for further processing  : 525
% 0.18/0.57  # Other redundant clauses eliminated   : 10
% 0.18/0.57  # Clauses deleted for lack of memory   : 0
% 0.18/0.57  # Backward-subsumed                    : 10
% 0.18/0.57  # Backward-rewritten                   : 9
% 0.18/0.57  # Generated clauses                    : 16163
% 0.18/0.57  # ...of the previous two non-trivial   : 14055
% 0.18/0.57  # Contextual simplify-reflections      : 2
% 0.18/0.57  # Paramodulations                      : 16086
% 0.18/0.57  # Factorizations                       : 67
% 0.18/0.57  # Equation resolutions                 : 10
% 0.18/0.57  # Propositional unsat checks           : 0
% 0.18/0.57  #    Propositional check models        : 0
% 0.18/0.57  #    Propositional check unsatisfiable : 0
% 0.18/0.57  #    Propositional clauses             : 0
% 0.18/0.57  #    Propositional clauses after purity: 0
% 0.18/0.57  #    Propositional unsat core size     : 0
% 0.18/0.57  #    Propositional preprocessing time  : 0.000
% 0.18/0.57  #    Propositional encoding time       : 0.000
% 0.18/0.57  #    Propositional solver time         : 0.000
% 0.18/0.57  #    Success case prop preproc time    : 0.000
% 0.18/0.57  #    Success case prop encoding time   : 0.000
% 0.18/0.57  #    Success case prop solver time     : 0.000
% 0.18/0.57  # Current number of processed clauses  : 462
% 0.18/0.57  #    Positive orientable unit clauses  : 24
% 0.18/0.57  #    Positive unorientable unit clauses: 0
% 0.18/0.57  #    Negative unit clauses             : 4
% 0.18/0.57  #    Non-unit-clauses                  : 434
% 0.18/0.57  # Current number of unprocessed clauses: 11104
% 0.18/0.57  # ...number of literals in the above   : 35550
% 0.18/0.57  # Current number of archived formulas  : 0
% 0.18/0.57  # Current number of archived clauses   : 53
% 0.18/0.57  # Clause-clause subsumption calls (NU) : 46672
% 0.18/0.57  # Rec. Clause-clause subsumption calls : 28212
% 0.18/0.57  # Non-unit clause-clause subsumptions  : 2043
% 0.18/0.57  # Unit Clause-clause subsumption calls : 112
% 0.18/0.57  # Rewrite failures with RHS unbound    : 0
% 0.18/0.57  # BW rewrite match attempts            : 35
% 0.18/0.57  # BW rewrite match successes           : 7
% 0.18/0.57  # Condensation attempts                : 0
% 0.18/0.57  # Condensation successes               : 0
% 0.18/0.57  # Termbank termtop insertions          : 252944
% 0.18/0.57  
% 0.18/0.57  # -------------------------------------------------
% 0.18/0.57  # User time                : 0.220 s
% 0.18/0.57  # System time              : 0.016 s
% 0.18/0.57  # Total time               : 0.236 s
% 0.18/0.57  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
