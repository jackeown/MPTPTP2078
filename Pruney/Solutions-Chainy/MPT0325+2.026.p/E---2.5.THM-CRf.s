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
% DateTime   : Thu Dec  3 10:44:09 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 135 expanded)
%              Number of clauses        :   39 (  63 expanded)
%              Number of leaves         :    9 (  33 expanded)
%              Depth                    :   12
%              Number of atoms          :  164 ( 464 expanded)
%              Number of equality atoms :   50 ( 125 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t138_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
     => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
        | ( r1_tarski(X1,X3)
          & r1_tarski(X2,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t117_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))
          | r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) )
        & ~ r1_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t118_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => ( r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
        & r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(c_0_9,plain,(
    ! [X35,X36,X37,X38] : k2_zfmisc_1(k3_xboole_0(X35,X36),k3_xboole_0(X37,X38)) = k3_xboole_0(k2_zfmisc_1(X35,X37),k2_zfmisc_1(X36,X38)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

fof(c_0_10,plain,(
    ! [X24,X25] :
      ( ~ r1_tarski(X24,X25)
      | k3_xboole_0(X24,X25) = X24 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
       => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
          | ( r1_tarski(X1,X3)
            & r1_tarski(X2,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t138_zfmisc_1])).

cnf(c_0_12,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))
    & k2_zfmisc_1(esk3_0,esk4_0) != k1_xboole_0
    & ( ~ r1_tarski(esk3_0,esk5_0)
      | ~ r1_tarski(esk4_0,esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

cnf(c_0_15,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k2_zfmisc_1(X1,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_17,plain,(
    ! [X27,X28] :
      ( ( k2_zfmisc_1(X27,X28) != k1_xboole_0
        | X27 = k1_xboole_0
        | X28 = k1_xboole_0 )
      & ( X27 != k1_xboole_0
        | k2_zfmisc_1(X27,X28) = k1_xboole_0 )
      & ( X28 != k1_xboole_0
        | k2_zfmisc_1(X27,X28) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_18,plain,(
    ! [X29,X30,X31] :
      ( ( ~ r1_tarski(k2_zfmisc_1(X30,X29),k2_zfmisc_1(X31,X29))
        | X29 = k1_xboole_0
        | r1_tarski(X30,X31) )
      & ( ~ r1_tarski(k2_zfmisc_1(X29,X30),k2_zfmisc_1(X29,X31))
        | X29 = k1_xboole_0
        | r1_tarski(X30,X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).

cnf(c_0_19,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk3_0,esk5_0),k3_xboole_0(esk4_0,esk6_0)) = k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X20,X21] :
      ( ( r1_tarski(X20,X21)
        | X20 != X21 )
      & ( r1_tarski(X21,X20)
        | X20 != X21 )
      & ( ~ r1_tarski(X20,X21)
        | ~ r1_tarski(X21,X20)
        | X20 = X21 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_23,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | ~ r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X17)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_24,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(X2,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,k3_xboole_0(esk4_0,esk6_0)) = k2_zfmisc_1(esk3_0,esk4_0)
    | ~ r1_tarski(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_13])).

cnf(c_0_26,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_29,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(X1,k3_xboole_0(esk4_0,esk6_0))
    | ~ r1_tarski(k2_zfmisc_1(esk3_0,X1),k2_zfmisc_1(esk3_0,esk4_0))
    | ~ r1_tarski(esk3_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(esk4_0,k3_xboole_0(esk4_0,esk6_0))
    | ~ r1_tarski(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,plain,
    ( X2 = k1_xboole_0
    | r1_tarski(X1,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_39,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk6_0) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_19]),c_0_20])).

fof(c_0_40,plain,(
    ! [X32,X33,X34] :
      ( ( r1_tarski(k2_zfmisc_1(X32,X34),k2_zfmisc_1(X33,X34))
        | ~ r1_tarski(X32,X33) )
      & ( r1_tarski(k2_zfmisc_1(X34,X32),k2_zfmisc_1(X34,X33))
        | ~ r1_tarski(X32,X33) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,plain,
    ( r2_hidden(esk1_2(k3_xboole_0(X1,X2),X3),X1)
    | r1_tarski(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(X1,k3_xboole_0(esk4_0,esk6_0))
    | ~ r2_hidden(X1,esk4_0)
    | ~ r1_tarski(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(X1,k3_xboole_0(esk3_0,esk5_0))
    | ~ r1_tarski(k2_zfmisc_1(X1,k3_xboole_0(esk4_0,esk6_0)),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_19]),c_0_39])).

cnf(c_0_46,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ r1_tarski(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,plain,
    ( r2_hidden(esk1_2(k3_xboole_0(X1,X2),X3),X2)
    | r1_tarski(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_43,c_0_34])).

cnf(c_0_50,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk3_0,k3_xboole_0(esk3_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(X1,esk6_0)
    | ~ r2_hidden(esk1_2(X1,esk6_0),esk4_0)
    | ~ r1_tarski(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk5_0)
    | ~ r1_tarski(esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_54,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk5_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_47])])).

cnf(c_0_56,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_34]),c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:17:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.34  # Version: 2.5pre002
% 0.20/0.34  # No SInE strategy applied
% 0.20/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.51  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.20/0.51  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.51  #
% 0.20/0.51  # Preprocessing time       : 0.027 s
% 0.20/0.51  # Presaturation interreduction done
% 0.20/0.51  
% 0.20/0.51  # Proof found!
% 0.20/0.51  # SZS status Theorem
% 0.20/0.51  # SZS output start CNFRefutation
% 0.20/0.51  fof(t123_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 0.20/0.51  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.20/0.51  fof(t138_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 0.20/0.51  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.20/0.51  fof(t117_zfmisc_1, axiom, ![X1, X2, X3]:~(((X1!=k1_xboole_0&(r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))|r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))))&~(r1_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 0.20/0.51  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.51  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.20/0.51  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.51  fof(t118_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>(r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 0.20/0.51  fof(c_0_9, plain, ![X35, X36, X37, X38]:k2_zfmisc_1(k3_xboole_0(X35,X36),k3_xboole_0(X37,X38))=k3_xboole_0(k2_zfmisc_1(X35,X37),k2_zfmisc_1(X36,X38)), inference(variable_rename,[status(thm)],[t123_zfmisc_1])).
% 0.20/0.51  fof(c_0_10, plain, ![X24, X25]:(~r1_tarski(X24,X25)|k3_xboole_0(X24,X25)=X24), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.20/0.51  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4))))), inference(assume_negation,[status(cth)],[t138_zfmisc_1])).
% 0.20/0.51  cnf(c_0_12, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.51  cnf(c_0_13, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.51  fof(c_0_14, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))&(k2_zfmisc_1(esk3_0,esk4_0)!=k1_xboole_0&(~r1_tarski(esk3_0,esk5_0)|~r1_tarski(esk4_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.20/0.51  cnf(c_0_15, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k2_zfmisc_1(X1,X3)|~r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.20/0.51  cnf(c_0_16, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.51  fof(c_0_17, plain, ![X27, X28]:((k2_zfmisc_1(X27,X28)!=k1_xboole_0|(X27=k1_xboole_0|X28=k1_xboole_0))&((X27!=k1_xboole_0|k2_zfmisc_1(X27,X28)=k1_xboole_0)&(X28!=k1_xboole_0|k2_zfmisc_1(X27,X28)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.20/0.51  fof(c_0_18, plain, ![X29, X30, X31]:((~r1_tarski(k2_zfmisc_1(X30,X29),k2_zfmisc_1(X31,X29))|X29=k1_xboole_0|r1_tarski(X30,X31))&(~r1_tarski(k2_zfmisc_1(X29,X30),k2_zfmisc_1(X29,X31))|X29=k1_xboole_0|r1_tarski(X30,X31))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).
% 0.20/0.51  cnf(c_0_19, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk3_0,esk5_0),k3_xboole_0(esk4_0,esk6_0))=k2_zfmisc_1(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.20/0.51  cnf(c_0_20, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.51  cnf(c_0_21, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.51  fof(c_0_22, plain, ![X20, X21]:(((r1_tarski(X20,X21)|X20!=X21)&(r1_tarski(X21,X20)|X20!=X21))&(~r1_tarski(X20,X21)|~r1_tarski(X21,X20)|X20=X21)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.51  fof(c_0_23, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12))&(r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|~r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k3_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|~r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k3_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))&(r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.20/0.51  cnf(c_0_24, plain, (X1=k1_xboole_0|r1_tarski(X2,X3)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.51  cnf(c_0_25, negated_conjecture, (k2_zfmisc_1(esk3_0,k3_xboole_0(esk4_0,esk6_0))=k2_zfmisc_1(esk3_0,esk4_0)|~r1_tarski(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_19, c_0_13])).
% 0.20/0.51  cnf(c_0_26, negated_conjecture, (esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.51  cnf(c_0_27, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.51  cnf(c_0_28, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.51  fof(c_0_29, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.51  cnf(c_0_30, negated_conjecture, (r1_tarski(X1,k3_xboole_0(esk4_0,esk6_0))|~r1_tarski(k2_zfmisc_1(esk3_0,X1),k2_zfmisc_1(esk3_0,esk4_0))|~r1_tarski(esk3_0,esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])).
% 0.20/0.51  cnf(c_0_31, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_27])).
% 0.20/0.51  cnf(c_0_32, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.51  cnf(c_0_33, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_28])).
% 0.20/0.51  cnf(c_0_34, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.51  cnf(c_0_35, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.51  cnf(c_0_36, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.51  cnf(c_0_37, negated_conjecture, (r1_tarski(esk4_0,k3_xboole_0(esk4_0,esk6_0))|~r1_tarski(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.51  cnf(c_0_38, plain, (X2=k1_xboole_0|r1_tarski(X1,X3)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.51  cnf(c_0_39, negated_conjecture, (k3_xboole_0(esk4_0,esk6_0)!=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_19]), c_0_20])).
% 0.20/0.51  fof(c_0_40, plain, ![X32, X33, X34]:((r1_tarski(k2_zfmisc_1(X32,X34),k2_zfmisc_1(X33,X34))|~r1_tarski(X32,X33))&(r1_tarski(k2_zfmisc_1(X34,X32),k2_zfmisc_1(X34,X33))|~r1_tarski(X32,X33))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).
% 0.20/0.51  cnf(c_0_41, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.51  cnf(c_0_42, plain, (r2_hidden(esk1_2(k3_xboole_0(X1,X2),X3),X1)|r1_tarski(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.51  cnf(c_0_43, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_35])).
% 0.20/0.51  cnf(c_0_44, negated_conjecture, (r2_hidden(X1,k3_xboole_0(esk4_0,esk6_0))|~r2_hidden(X1,esk4_0)|~r1_tarski(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.51  cnf(c_0_45, negated_conjecture, (r1_tarski(X1,k3_xboole_0(esk3_0,esk5_0))|~r1_tarski(k2_zfmisc_1(X1,k3_xboole_0(esk4_0,esk6_0)),k2_zfmisc_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_19]), c_0_39])).
% 0.20/0.51  cnf(c_0_46, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.51  cnf(c_0_47, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.51  cnf(c_0_48, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk4_0)|~r1_tarski(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.51  cnf(c_0_49, plain, (r2_hidden(esk1_2(k3_xboole_0(X1,X2),X3),X2)|r1_tarski(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_43, c_0_34])).
% 0.20/0.51  cnf(c_0_50, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.51  cnf(c_0_51, negated_conjecture, (r1_tarski(esk3_0,k3_xboole_0(esk3_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])])).
% 0.20/0.51  cnf(c_0_52, negated_conjecture, (r1_tarski(X1,esk6_0)|~r2_hidden(esk1_2(X1,esk6_0),esk4_0)|~r1_tarski(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_41, c_0_48])).
% 0.20/0.51  cnf(c_0_53, negated_conjecture, (~r1_tarski(esk3_0,esk5_0)|~r1_tarski(esk4_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.51  cnf(c_0_54, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_41, c_0_49])).
% 0.20/0.51  cnf(c_0_55, negated_conjecture, (k3_xboole_0(esk3_0,esk5_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_47])])).
% 0.20/0.51  cnf(c_0_56, negated_conjecture, (~r1_tarski(esk3_0,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_34]), c_0_53])).
% 0.20/0.51  cnf(c_0_57, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), ['proof']).
% 0.20/0.51  # SZS output end CNFRefutation
% 0.20/0.51  # Proof object total steps             : 58
% 0.20/0.51  # Proof object clause steps            : 39
% 0.20/0.51  # Proof object formula steps           : 19
% 0.20/0.51  # Proof object conjectures             : 20
% 0.20/0.51  # Proof object clause conjectures      : 17
% 0.20/0.51  # Proof object formula conjectures     : 3
% 0.20/0.51  # Proof object initial clauses used    : 17
% 0.20/0.51  # Proof object initial formulas used   : 9
% 0.20/0.51  # Proof object generating inferences   : 21
% 0.20/0.51  # Proof object simplifying inferences  : 10
% 0.20/0.51  # Training examples: 0 positive, 0 negative
% 0.20/0.51  # Parsed axioms                        : 11
% 0.20/0.51  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.51  # Initial clauses                      : 27
% 0.20/0.51  # Removed in clause preprocessing      : 0
% 0.20/0.51  # Initial clauses in saturation        : 27
% 0.20/0.51  # Processed clauses                    : 1560
% 0.20/0.51  # ...of these trivial                  : 57
% 0.20/0.51  # ...subsumed                          : 1002
% 0.20/0.51  # ...remaining for further processing  : 501
% 0.20/0.51  # Other redundant clauses eliminated   : 60
% 0.20/0.51  # Clauses deleted for lack of memory   : 0
% 0.20/0.51  # Backward-subsumed                    : 76
% 0.20/0.51  # Backward-rewritten                   : 145
% 0.20/0.51  # Generated clauses                    : 11079
% 0.20/0.51  # ...of the previous two non-trivial   : 9556
% 0.20/0.51  # Contextual simplify-reflections      : 26
% 0.20/0.51  # Paramodulations                      : 10963
% 0.20/0.51  # Factorizations                       : 23
% 0.20/0.51  # Equation resolutions                 : 93
% 0.20/0.51  # Propositional unsat checks           : 0
% 0.20/0.51  #    Propositional check models        : 0
% 0.20/0.51  #    Propositional check unsatisfiable : 0
% 0.20/0.51  #    Propositional clauses             : 0
% 0.20/0.51  #    Propositional clauses after purity: 0
% 0.20/0.51  #    Propositional unsat core size     : 0
% 0.20/0.51  #    Propositional preprocessing time  : 0.000
% 0.20/0.51  #    Propositional encoding time       : 0.000
% 0.20/0.51  #    Propositional solver time         : 0.000
% 0.20/0.51  #    Success case prop preproc time    : 0.000
% 0.20/0.51  #    Success case prop encoding time   : 0.000
% 0.20/0.51  #    Success case prop solver time     : 0.000
% 0.20/0.51  # Current number of processed clauses  : 252
% 0.20/0.51  #    Positive orientable unit clauses  : 18
% 0.20/0.51  #    Positive unorientable unit clauses: 0
% 0.20/0.51  #    Negative unit clauses             : 13
% 0.20/0.51  #    Non-unit-clauses                  : 221
% 0.20/0.51  # Current number of unprocessed clauses: 7601
% 0.20/0.51  # ...number of literals in the above   : 26669
% 0.20/0.51  # Current number of archived formulas  : 0
% 0.20/0.51  # Current number of archived clauses   : 247
% 0.20/0.51  # Clause-clause subsumption calls (NU) : 12680
% 0.20/0.51  # Rec. Clause-clause subsumption calls : 11604
% 0.20/0.51  # Non-unit clause-clause subsumptions  : 488
% 0.20/0.51  # Unit Clause-clause subsumption calls : 565
% 0.20/0.51  # Rewrite failures with RHS unbound    : 0
% 0.20/0.51  # BW rewrite match attempts            : 95
% 0.20/0.51  # BW rewrite match successes           : 57
% 0.20/0.51  # Condensation attempts                : 0
% 0.20/0.51  # Condensation successes               : 0
% 0.20/0.51  # Termbank termtop insertions          : 129510
% 0.20/0.51  
% 0.20/0.51  # -------------------------------------------------
% 0.20/0.51  # User time                : 0.161 s
% 0.20/0.51  # System time              : 0.010 s
% 0.20/0.51  # Total time               : 0.172 s
% 0.20/0.51  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
