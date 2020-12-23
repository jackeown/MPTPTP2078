%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:41 EST 2020

% Result     : Theorem 0.72s
% Output     : CNFRefutation 0.72s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 117 expanded)
%              Number of clauses        :   37 (  53 expanded)
%              Number of leaves         :   11 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :  184 ( 375 expanded)
%              Number of equality atoms :   45 ( 118 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t174_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ~ ( X1 != k1_xboole_0
          & r1_tarski(X1,k2_relat_1(X2))
          & k10_relat_1(X2,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(t20_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(X2,k2_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(c_0_11,plain,(
    ! [X14,X15] :
      ( ( k2_zfmisc_1(X14,X15) != k1_xboole_0
        | X14 = k1_xboole_0
        | X15 = k1_xboole_0 )
      & ( X14 != k1_xboole_0
        | k2_zfmisc_1(X14,X15) = k1_xboole_0 )
      & ( X15 != k1_xboole_0
        | k2_zfmisc_1(X14,X15) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_12,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_13,plain,(
    ! [X16,X17] : ~ r2_hidden(X16,k2_zfmisc_1(X16,X17)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_14,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ~ ( X1 != k1_xboole_0
            & r1_tarski(X1,k2_relat_1(X2))
            & k10_relat_1(X2,X1) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t174_relat_1])).

fof(c_0_17,plain,(
    ! [X33,X34] :
      ( ~ v1_relat_1(X34)
      | ~ r1_tarski(k1_relat_1(X34),X33)
      | k7_relat_1(X34,X33) = X34 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_19,plain,(
    ! [X25,X26,X27,X29] :
      ( ( r2_hidden(esk3_3(X25,X26,X27),k2_relat_1(X27))
        | ~ r2_hidden(X25,k10_relat_1(X27,X26))
        | ~ v1_relat_1(X27) )
      & ( r2_hidden(k4_tarski(X25,esk3_3(X25,X26,X27)),X27)
        | ~ r2_hidden(X25,k10_relat_1(X27,X26))
        | ~ v1_relat_1(X27) )
      & ( r2_hidden(esk3_3(X25,X26,X27),X26)
        | ~ r2_hidden(X25,k10_relat_1(X27,X26))
        | ~ v1_relat_1(X27) )
      & ( ~ r2_hidden(X29,k2_relat_1(X27))
        | ~ r2_hidden(k4_tarski(X25,X29),X27)
        | ~ r2_hidden(X29,X26)
        | r2_hidden(X25,k10_relat_1(X27,X26))
        | ~ v1_relat_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

fof(c_0_20,plain,(
    ! [X30,X31,X32] :
      ( ( r2_hidden(X30,k1_relat_1(X32))
        | ~ r2_hidden(k4_tarski(X30,X31),X32)
        | ~ v1_relat_1(X32) )
      & ( r2_hidden(X31,k2_relat_1(X32))
        | ~ r2_hidden(k4_tarski(X30,X31),X32)
        | ~ v1_relat_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_25,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X24)
      | k2_relat_1(k7_relat_1(X24,X23)) = k9_relat_1(X24,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_26,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & esk4_0 != k1_xboole_0
    & r1_tarski(esk4_0,k2_relat_1(esk5_0))
    & k10_relat_1(esk5_0,esk4_0) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

cnf(c_0_27,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( r2_hidden(X3,k10_relat_1(X2,X4))
    | ~ r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_32,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_33,plain,(
    ! [X13] :
      ( ~ r1_tarski(X13,k1_xboole_0)
      | X13 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_34,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(csr,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,plain,
    ( r2_hidden(esk1_2(X1,k1_xboole_0),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_40,plain,(
    ! [X18,X19,X20,X22] :
      ( ( r2_hidden(esk2_3(X18,X19,X20),k1_relat_1(X20))
        | ~ r2_hidden(X18,k9_relat_1(X20,X19))
        | ~ v1_relat_1(X20) )
      & ( r2_hidden(k4_tarski(esk2_3(X18,X19,X20),X18),X20)
        | ~ r2_hidden(X18,k9_relat_1(X20,X19))
        | ~ v1_relat_1(X20) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X19)
        | ~ r2_hidden(X18,k9_relat_1(X20,X19))
        | ~ v1_relat_1(X20) )
      & ( ~ r2_hidden(X22,k1_relat_1(X20))
        | ~ r2_hidden(k4_tarski(X22,X18),X20)
        | ~ r2_hidden(X22,X19)
        | r2_hidden(X18,k9_relat_1(X20,X19))
        | ~ v1_relat_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

cnf(c_0_41,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk5_0,X1)) = k9_relat_1(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( k7_relat_1(esk5_0,k1_relat_1(esk5_0)) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_35])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,esk1_2(X3,k1_xboole_0)),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_2(X1,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_24])).

cnf(c_0_45,plain,
    ( r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( k9_relat_1(esk5_0,k1_relat_1(esk5_0)) = k2_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X2,esk1_2(X1,k1_xboole_0)),X3) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_3(X1,k1_relat_1(esk5_0),esk5_0),X1),esk5_0)
    | ~ r2_hidden(X1,k2_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_35])])).

cnf(c_0_49,negated_conjecture,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_3(esk1_2(X1,k1_xboole_0),k1_relat_1(esk5_0),esk5_0),k10_relat_1(esk5_0,X1))
    | ~ r2_hidden(esk1_2(X1,k1_xboole_0),k2_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_35])])).

cnf(c_0_50,negated_conjecture,
    ( k10_relat_1(esk5_0,esk4_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_51,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(esk4_0,k2_relat_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_53,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_54,negated_conjecture,
    ( ~ r2_hidden(esk1_2(esk4_0,k1_xboole_0),k2_relat_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_31])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(X1,k2_relat_1(esk5_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_52])).

cnf(c_0_56,plain,
    ( X1 = X2
    | r2_hidden(esk1_2(X2,X1),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_24])).

cnf(c_0_57,negated_conjecture,
    ( ~ r2_hidden(esk1_2(esk4_0,k1_xboole_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_58,plain,
    ( X1 = X2
    | r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(esk1_2(X2,X1),X2) ),
    inference(spm,[status(thm)],[c_0_56,c_0_24])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_51]),c_0_31]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:04:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.72/0.92  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.72/0.92  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.72/0.92  #
% 0.72/0.92  # Preprocessing time       : 0.044 s
% 0.72/0.92  # Presaturation interreduction done
% 0.72/0.92  
% 0.72/0.92  # Proof found!
% 0.72/0.92  # SZS status Theorem
% 0.72/0.92  # SZS output start CNFRefutation
% 0.72/0.92  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.72/0.92  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.72/0.92  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.72/0.92  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.72/0.92  fof(t174_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>~(((X1!=k1_xboole_0&r1_tarski(X1,k2_relat_1(X2)))&k10_relat_1(X2,X1)=k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_relat_1)).
% 0.72/0.92  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 0.72/0.92  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 0.72/0.92  fof(t20_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(X2,k2_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 0.72/0.92  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.72/0.92  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.72/0.92  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 0.72/0.92  fof(c_0_11, plain, ![X14, X15]:((k2_zfmisc_1(X14,X15)!=k1_xboole_0|(X14=k1_xboole_0|X15=k1_xboole_0))&((X14!=k1_xboole_0|k2_zfmisc_1(X14,X15)=k1_xboole_0)&(X15!=k1_xboole_0|k2_zfmisc_1(X14,X15)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.72/0.92  fof(c_0_12, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.72/0.92  fof(c_0_13, plain, ![X16, X17]:~r2_hidden(X16,k2_zfmisc_1(X16,X17)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.72/0.92  cnf(c_0_14, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.72/0.92  fof(c_0_15, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.72/0.92  fof(c_0_16, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>~(((X1!=k1_xboole_0&r1_tarski(X1,k2_relat_1(X2)))&k10_relat_1(X2,X1)=k1_xboole_0)))), inference(assume_negation,[status(cth)],[t174_relat_1])).
% 0.72/0.92  fof(c_0_17, plain, ![X33, X34]:(~v1_relat_1(X34)|(~r1_tarski(k1_relat_1(X34),X33)|k7_relat_1(X34,X33)=X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 0.72/0.92  cnf(c_0_18, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.72/0.92  fof(c_0_19, plain, ![X25, X26, X27, X29]:((((r2_hidden(esk3_3(X25,X26,X27),k2_relat_1(X27))|~r2_hidden(X25,k10_relat_1(X27,X26))|~v1_relat_1(X27))&(r2_hidden(k4_tarski(X25,esk3_3(X25,X26,X27)),X27)|~r2_hidden(X25,k10_relat_1(X27,X26))|~v1_relat_1(X27)))&(r2_hidden(esk3_3(X25,X26,X27),X26)|~r2_hidden(X25,k10_relat_1(X27,X26))|~v1_relat_1(X27)))&(~r2_hidden(X29,k2_relat_1(X27))|~r2_hidden(k4_tarski(X25,X29),X27)|~r2_hidden(X29,X26)|r2_hidden(X25,k10_relat_1(X27,X26))|~v1_relat_1(X27))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.72/0.92  fof(c_0_20, plain, ![X30, X31, X32]:((r2_hidden(X30,k1_relat_1(X32))|~r2_hidden(k4_tarski(X30,X31),X32)|~v1_relat_1(X32))&(r2_hidden(X31,k2_relat_1(X32))|~r2_hidden(k4_tarski(X30,X31),X32)|~v1_relat_1(X32))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).
% 0.72/0.92  cnf(c_0_21, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.72/0.92  cnf(c_0_22, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_14])).
% 0.72/0.92  cnf(c_0_23, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.72/0.92  cnf(c_0_24, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.72/0.92  fof(c_0_25, plain, ![X23, X24]:(~v1_relat_1(X24)|k2_relat_1(k7_relat_1(X24,X23))=k9_relat_1(X24,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.72/0.92  fof(c_0_26, negated_conjecture, (v1_relat_1(esk5_0)&((esk4_0!=k1_xboole_0&r1_tarski(esk4_0,k2_relat_1(esk5_0)))&k10_relat_1(esk5_0,esk4_0)=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.72/0.92  cnf(c_0_27, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.72/0.92  cnf(c_0_28, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_18])).
% 0.72/0.92  cnf(c_0_29, plain, (r2_hidden(X3,k10_relat_1(X2,X4))|~r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,X4)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.72/0.92  cnf(c_0_30, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.72/0.92  cnf(c_0_31, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.72/0.92  cnf(c_0_32, plain, (r2_hidden(esk1_2(X1,X2),X1)|r2_hidden(X3,X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.72/0.92  fof(c_0_33, plain, ![X13]:(~r1_tarski(X13,k1_xboole_0)|X13=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.72/0.92  cnf(c_0_34, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.72/0.92  cnf(c_0_35, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.72/0.92  cnf(c_0_36, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.72/0.92  cnf(c_0_37, plain, (r2_hidden(X1,k10_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X4),X2)|~r2_hidden(X4,X3)), inference(csr,[status(thm)],[c_0_29, c_0_30])).
% 0.72/0.92  cnf(c_0_38, plain, (r2_hidden(esk1_2(X1,k1_xboole_0),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.72/0.92  cnf(c_0_39, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.72/0.92  fof(c_0_40, plain, ![X18, X19, X20, X22]:((((r2_hidden(esk2_3(X18,X19,X20),k1_relat_1(X20))|~r2_hidden(X18,k9_relat_1(X20,X19))|~v1_relat_1(X20))&(r2_hidden(k4_tarski(esk2_3(X18,X19,X20),X18),X20)|~r2_hidden(X18,k9_relat_1(X20,X19))|~v1_relat_1(X20)))&(r2_hidden(esk2_3(X18,X19,X20),X19)|~r2_hidden(X18,k9_relat_1(X20,X19))|~v1_relat_1(X20)))&(~r2_hidden(X22,k1_relat_1(X20))|~r2_hidden(k4_tarski(X22,X18),X20)|~r2_hidden(X22,X19)|r2_hidden(X18,k9_relat_1(X20,X19))|~v1_relat_1(X20))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.72/0.92  cnf(c_0_41, negated_conjecture, (k2_relat_1(k7_relat_1(esk5_0,X1))=k9_relat_1(esk5_0,X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.72/0.92  cnf(c_0_42, negated_conjecture, (k7_relat_1(esk5_0,k1_relat_1(esk5_0))=esk5_0), inference(spm,[status(thm)],[c_0_36, c_0_35])).
% 0.72/0.92  cnf(c_0_43, plain, (r2_hidden(X1,k10_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,esk1_2(X3,k1_xboole_0)),X2)|~r2_hidden(X4,X3)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.72/0.92  cnf(c_0_44, plain, (X1=k1_xboole_0|r2_hidden(esk1_2(X1,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_39, c_0_24])).
% 0.72/0.92  cnf(c_0_45, plain, (r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.72/0.92  cnf(c_0_46, negated_conjecture, (k9_relat_1(esk5_0,k1_relat_1(esk5_0))=k2_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.72/0.92  cnf(c_0_47, plain, (X1=k1_xboole_0|r2_hidden(X2,k10_relat_1(X3,X1))|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X2,esk1_2(X1,k1_xboole_0)),X3)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.72/0.92  cnf(c_0_48, negated_conjecture, (r2_hidden(k4_tarski(esk2_3(X1,k1_relat_1(esk5_0),esk5_0),X1),esk5_0)|~r2_hidden(X1,k2_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_35])])).
% 0.72/0.92  cnf(c_0_49, negated_conjecture, (X1=k1_xboole_0|r2_hidden(esk2_3(esk1_2(X1,k1_xboole_0),k1_relat_1(esk5_0),esk5_0),k10_relat_1(esk5_0,X1))|~r2_hidden(esk1_2(X1,k1_xboole_0),k2_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_35])])).
% 0.72/0.92  cnf(c_0_50, negated_conjecture, (k10_relat_1(esk5_0,esk4_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.72/0.92  cnf(c_0_51, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.72/0.92  cnf(c_0_52, negated_conjecture, (r1_tarski(esk4_0,k2_relat_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.72/0.92  cnf(c_0_53, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.72/0.92  cnf(c_0_54, negated_conjecture, (~r2_hidden(esk1_2(esk4_0,k1_xboole_0),k2_relat_1(esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), c_0_31])).
% 0.72/0.92  cnf(c_0_55, negated_conjecture, (r2_hidden(X1,k2_relat_1(esk5_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_23, c_0_52])).
% 0.72/0.92  cnf(c_0_56, plain, (X1=X2|r2_hidden(esk1_2(X2,X1),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_53, c_0_24])).
% 0.72/0.92  cnf(c_0_57, negated_conjecture, (~r2_hidden(esk1_2(esk4_0,k1_xboole_0),esk4_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.72/0.92  cnf(c_0_58, plain, (X1=X2|r2_hidden(esk1_2(X1,X2),X1)|r2_hidden(esk1_2(X2,X1),X2)), inference(spm,[status(thm)],[c_0_56, c_0_24])).
% 0.72/0.92  cnf(c_0_59, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_51]), c_0_31]), ['proof']).
% 0.72/0.92  # SZS output end CNFRefutation
% 0.72/0.92  # Proof object total steps             : 60
% 0.72/0.92  # Proof object clause steps            : 37
% 0.72/0.92  # Proof object formula steps           : 23
% 0.72/0.92  # Proof object conjectures             : 16
% 0.72/0.92  # Proof object clause conjectures      : 13
% 0.72/0.92  # Proof object formula conjectures     : 3
% 0.72/0.92  # Proof object initial clauses used    : 16
% 0.72/0.92  # Proof object initial formulas used   : 11
% 0.72/0.92  # Proof object generating inferences   : 18
% 0.72/0.92  # Proof object simplifying inferences  : 11
% 0.72/0.92  # Training examples: 0 positive, 0 negative
% 0.72/0.92  # Parsed axioms                        : 11
% 0.72/0.92  # Removed by relevancy pruning/SinE    : 0
% 0.72/0.92  # Initial clauses                      : 27
% 0.72/0.92  # Removed in clause preprocessing      : 0
% 0.72/0.92  # Initial clauses in saturation        : 27
% 0.72/0.92  # Processed clauses                    : 2517
% 0.72/0.92  # ...of these trivial                  : 40
% 0.72/0.92  # ...subsumed                          : 1582
% 0.72/0.92  # ...remaining for further processing  : 895
% 0.72/0.92  # Other redundant clauses eliminated   : 4
% 0.72/0.92  # Clauses deleted for lack of memory   : 0
% 0.72/0.92  # Backward-subsumed                    : 115
% 0.72/0.92  # Backward-rewritten                   : 5
% 0.72/0.92  # Generated clauses                    : 30398
% 0.72/0.92  # ...of the previous two non-trivial   : 28893
% 0.72/0.92  # Contextual simplify-reflections      : 17
% 0.72/0.92  # Paramodulations                      : 30343
% 0.72/0.92  # Factorizations                       : 50
% 0.72/0.92  # Equation resolutions                 : 4
% 0.72/0.92  # Propositional unsat checks           : 0
% 0.72/0.92  #    Propositional check models        : 0
% 0.72/0.92  #    Propositional check unsatisfiable : 0
% 0.72/0.92  #    Propositional clauses             : 0
% 0.72/0.92  #    Propositional clauses after purity: 0
% 0.72/0.92  #    Propositional unsat core size     : 0
% 0.72/0.92  #    Propositional preprocessing time  : 0.000
% 0.72/0.92  #    Propositional encoding time       : 0.000
% 0.72/0.92  #    Propositional solver time         : 0.000
% 0.72/0.92  #    Success case prop preproc time    : 0.000
% 0.72/0.92  #    Success case prop encoding time   : 0.000
% 0.72/0.92  #    Success case prop solver time     : 0.000
% 0.72/0.92  # Current number of processed clauses  : 744
% 0.72/0.92  #    Positive orientable unit clauses  : 38
% 0.72/0.92  #    Positive unorientable unit clauses: 0
% 0.72/0.92  #    Negative unit clauses             : 5
% 0.72/0.92  #    Non-unit-clauses                  : 701
% 0.72/0.92  # Current number of unprocessed clauses: 26079
% 0.72/0.92  # ...number of literals in the above   : 123387
% 0.72/0.92  # Current number of archived formulas  : 0
% 0.72/0.92  # Current number of archived clauses   : 147
% 0.72/0.92  # Clause-clause subsumption calls (NU) : 87678
% 0.72/0.92  # Rec. Clause-clause subsumption calls : 38287
% 0.72/0.92  # Non-unit clause-clause subsumptions  : 1630
% 0.72/0.92  # Unit Clause-clause subsumption calls : 844
% 0.72/0.92  # Rewrite failures with RHS unbound    : 0
% 0.72/0.92  # BW rewrite match attempts            : 44
% 0.72/0.92  # BW rewrite match successes           : 15
% 0.72/0.92  # Condensation attempts                : 0
% 0.72/0.92  # Condensation successes               : 0
% 0.72/0.92  # Termbank termtop insertions          : 729263
% 0.72/0.92  
% 0.72/0.92  # -------------------------------------------------
% 0.72/0.92  # User time                : 0.555 s
% 0.72/0.92  # System time              : 0.018 s
% 0.72/0.92  # Total time               : 0.574 s
% 0.72/0.92  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
