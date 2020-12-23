%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:26 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 114 expanded)
%              Number of clauses        :   26 (  47 expanded)
%              Number of leaves         :   14 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :  113 ( 195 expanded)
%              Number of equality atoms :   43 (  93 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l24_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_xboole_0(k1_tarski(X1),X2)
        & r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

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

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(d1_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
    <=> ! [X2] :
          ~ ( r2_hidden(X2,X1)
            & ! [X3,X4] : X2 != k4_tarski(X3,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(t172_relat_1,conjecture,(
    ! [X1] : k10_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

fof(c_0_14,plain,(
    ! [X37,X38] :
      ( ~ r1_xboole_0(k1_tarski(X37),X38)
      | ~ r2_hidden(X37,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).

fof(c_0_15,plain,(
    ! [X9] : k2_tarski(X9,X9) = k1_tarski(X9) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_16,plain,(
    ! [X10,X11] : k1_enumset1(X10,X10,X11) = k2_tarski(X10,X11) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_17,plain,(
    ! [X12,X13,X14] : k2_enumset1(X12,X12,X13,X14) = k1_enumset1(X12,X13,X14) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_18,plain,(
    ! [X15,X16,X17,X18] : k3_enumset1(X15,X15,X16,X17,X18) = k2_enumset1(X15,X16,X17,X18) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_19,plain,(
    ! [X19,X20,X21,X22,X23] : k4_enumset1(X19,X19,X20,X21,X22,X23) = k3_enumset1(X19,X20,X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_20,plain,(
    ! [X24,X25,X26,X27,X28,X29] : k5_enumset1(X24,X24,X25,X26,X27,X28,X29) = k4_enumset1(X24,X25,X26,X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_21,plain,(
    ! [X30,X31,X32,X33,X34,X35,X36] : k6_enumset1(X30,X30,X31,X32,X33,X34,X35,X36) = k5_enumset1(X30,X31,X32,X33,X34,X35,X36) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_22,plain,(
    ! [X47,X48,X49,X51,X52,X53,X54,X56] :
      ( ( ~ r2_hidden(X49,X48)
        | r2_hidden(k4_tarski(esk4_3(X47,X48,X49),X49),X47)
        | X48 != k2_relat_1(X47) )
      & ( ~ r2_hidden(k4_tarski(X52,X51),X47)
        | r2_hidden(X51,X48)
        | X48 != k2_relat_1(X47) )
      & ( ~ r2_hidden(esk5_2(X53,X54),X54)
        | ~ r2_hidden(k4_tarski(X56,esk5_2(X53,X54)),X53)
        | X54 = k2_relat_1(X53) )
      & ( r2_hidden(esk5_2(X53,X54),X54)
        | r2_hidden(k4_tarski(esk6_2(X53,X54),esk5_2(X53,X54)),X53)
        | X54 = k2_relat_1(X53) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_23,plain,
    ( ~ r1_xboole_0(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_31,plain,(
    ! [X39,X40,X43,X45,X46] :
      ( ( ~ v1_relat_1(X39)
        | ~ r2_hidden(X40,X39)
        | X40 = k4_tarski(esk1_2(X39,X40),esk2_2(X39,X40)) )
      & ( r2_hidden(esk3_1(X43),X43)
        | v1_relat_1(X43) )
      & ( esk3_1(X43) != k4_tarski(X45,X46)
        | v1_relat_1(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).

cnf(c_0_32,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_34,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_35,plain,(
    ! [X8] : r1_xboole_0(X8,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_37,plain,
    ( r2_hidden(esk5_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk6_2(X1,X2),esk5_2(X1,X2)),X1)
    | X2 = k2_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_38,plain,(
    ! [X58,X59,X60,X62] :
      ( ( r2_hidden(esk7_3(X58,X59,X60),k2_relat_1(X60))
        | ~ r2_hidden(X58,k10_relat_1(X60,X59))
        | ~ v1_relat_1(X60) )
      & ( r2_hidden(k4_tarski(X58,esk7_3(X58,X59,X60)),X60)
        | ~ r2_hidden(X58,k10_relat_1(X60,X59))
        | ~ v1_relat_1(X60) )
      & ( r2_hidden(esk7_3(X58,X59,X60),X59)
        | ~ r2_hidden(X58,k10_relat_1(X60,X59))
        | ~ v1_relat_1(X60) )
      & ( ~ r2_hidden(X62,k2_relat_1(X60))
        | ~ r2_hidden(k4_tarski(X58,X62),X60)
        | ~ r2_hidden(X62,X59)
        | r2_hidden(X58,k10_relat_1(X60,X59))
        | ~ v1_relat_1(X60) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

cnf(c_0_39,plain,
    ( v1_relat_1(X1)
    | ~ r1_xboole_0(k6_enumset1(esk3_1(X1),esk3_1(X1),esk3_1(X1),esk3_1(X1),esk3_1(X1),esk3_1(X1),esk3_1(X1),esk3_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,plain,
    ( X1 = k2_relat_1(X2)
    | r2_hidden(esk5_2(X2,X1),k2_relat_1(X2))
    | r2_hidden(esk5_2(X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_43,plain,
    ( r2_hidden(esk7_3(X1,X2,X3),k2_relat_1(X3))
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk5_2(k1_xboole_0,X1),k1_xboole_0)
    | r2_hidden(esk5_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_46,negated_conjecture,(
    ~ ! [X1] : k10_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t172_relat_1])).

cnf(c_0_47,plain,
    ( r2_hidden(esk7_3(X1,X2,k1_xboole_0),k1_xboole_0)
    | ~ r2_hidden(X1,k10_relat_1(k1_xboole_0,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_42])).

cnf(c_0_48,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk5_2(k1_xboole_0,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_45]),c_0_40])])).

fof(c_0_49,negated_conjecture,(
    k10_relat_1(k1_xboole_0,esk8_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_46])])])).

cnf(c_0_50,plain,
    ( k10_relat_1(k1_xboole_0,X1) = k1_xboole_0
    | r2_hidden(esk7_3(esk5_2(k1_xboole_0,k10_relat_1(k1_xboole_0,X1)),X1,k1_xboole_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( k10_relat_1(k1_xboole_0,esk8_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_52,plain,
    ( k10_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_50]),c_0_40])])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:42:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.20/0.38  # and selection function GSelectMinInfpos.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.029 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(l24_zfmisc_1, axiom, ![X1, X2]:~((r1_xboole_0(k1_tarski(X1),X2)&r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 0.20/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.38  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.38  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.20/0.38  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.20/0.38  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 0.20/0.38  fof(d1_relat_1, axiom, ![X1]:(v1_relat_1(X1)<=>![X2]:~((r2_hidden(X2,X1)&![X3, X4]:X2!=k4_tarski(X3,X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 0.20/0.38  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.20/0.38  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 0.20/0.38  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.20/0.38  fof(t172_relat_1, conjecture, ![X1]:k10_relat_1(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 0.20/0.38  fof(c_0_14, plain, ![X37, X38]:(~r1_xboole_0(k1_tarski(X37),X38)|~r2_hidden(X37,X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).
% 0.20/0.38  fof(c_0_15, plain, ![X9]:k2_tarski(X9,X9)=k1_tarski(X9), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.38  fof(c_0_16, plain, ![X10, X11]:k1_enumset1(X10,X10,X11)=k2_tarski(X10,X11), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.38  fof(c_0_17, plain, ![X12, X13, X14]:k2_enumset1(X12,X12,X13,X14)=k1_enumset1(X12,X13,X14), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.38  fof(c_0_18, plain, ![X15, X16, X17, X18]:k3_enumset1(X15,X15,X16,X17,X18)=k2_enumset1(X15,X16,X17,X18), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.38  fof(c_0_19, plain, ![X19, X20, X21, X22, X23]:k4_enumset1(X19,X19,X20,X21,X22,X23)=k3_enumset1(X19,X20,X21,X22,X23), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.38  fof(c_0_20, plain, ![X24, X25, X26, X27, X28, X29]:k5_enumset1(X24,X24,X25,X26,X27,X28,X29)=k4_enumset1(X24,X25,X26,X27,X28,X29), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.20/0.38  fof(c_0_21, plain, ![X30, X31, X32, X33, X34, X35, X36]:k6_enumset1(X30,X30,X31,X32,X33,X34,X35,X36)=k5_enumset1(X30,X31,X32,X33,X34,X35,X36), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.20/0.38  fof(c_0_22, plain, ![X47, X48, X49, X51, X52, X53, X54, X56]:(((~r2_hidden(X49,X48)|r2_hidden(k4_tarski(esk4_3(X47,X48,X49),X49),X47)|X48!=k2_relat_1(X47))&(~r2_hidden(k4_tarski(X52,X51),X47)|r2_hidden(X51,X48)|X48!=k2_relat_1(X47)))&((~r2_hidden(esk5_2(X53,X54),X54)|~r2_hidden(k4_tarski(X56,esk5_2(X53,X54)),X53)|X54=k2_relat_1(X53))&(r2_hidden(esk5_2(X53,X54),X54)|r2_hidden(k4_tarski(esk6_2(X53,X54),esk5_2(X53,X54)),X53)|X54=k2_relat_1(X53)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.20/0.38  cnf(c_0_23, plain, (~r1_xboole_0(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  cnf(c_0_24, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  cnf(c_0_25, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  cnf(c_0_26, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_27, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_28, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  cnf(c_0_29, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.38  cnf(c_0_30, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.38  fof(c_0_31, plain, ![X39, X40, X43, X45, X46]:((~v1_relat_1(X39)|(~r2_hidden(X40,X39)|X40=k4_tarski(esk1_2(X39,X40),esk2_2(X39,X40))))&((r2_hidden(esk3_1(X43),X43)|v1_relat_1(X43))&(esk3_1(X43)!=k4_tarski(X45,X46)|v1_relat_1(X43)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).
% 0.20/0.38  cnf(c_0_32, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.38  cnf(c_0_33, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30])).
% 0.20/0.38  cnf(c_0_34, plain, (r2_hidden(esk3_1(X1),X1)|v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.38  fof(c_0_35, plain, ![X8]:r1_xboole_0(X8,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.20/0.38  cnf(c_0_36, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)), inference(er,[status(thm)],[c_0_32])).
% 0.20/0.38  cnf(c_0_37, plain, (r2_hidden(esk5_2(X1,X2),X2)|r2_hidden(k4_tarski(esk6_2(X1,X2),esk5_2(X1,X2)),X1)|X2=k2_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.38  fof(c_0_38, plain, ![X58, X59, X60, X62]:((((r2_hidden(esk7_3(X58,X59,X60),k2_relat_1(X60))|~r2_hidden(X58,k10_relat_1(X60,X59))|~v1_relat_1(X60))&(r2_hidden(k4_tarski(X58,esk7_3(X58,X59,X60)),X60)|~r2_hidden(X58,k10_relat_1(X60,X59))|~v1_relat_1(X60)))&(r2_hidden(esk7_3(X58,X59,X60),X59)|~r2_hidden(X58,k10_relat_1(X60,X59))|~v1_relat_1(X60)))&(~r2_hidden(X62,k2_relat_1(X60))|~r2_hidden(k4_tarski(X58,X62),X60)|~r2_hidden(X62,X59)|r2_hidden(X58,k10_relat_1(X60,X59))|~v1_relat_1(X60))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.20/0.38  cnf(c_0_39, plain, (v1_relat_1(X1)|~r1_xboole_0(k6_enumset1(esk3_1(X1),esk3_1(X1),esk3_1(X1),esk3_1(X1),esk3_1(X1),esk3_1(X1),esk3_1(X1),esk3_1(X1)),X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.38  cnf(c_0_40, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.38  cnf(c_0_41, plain, (X1=k2_relat_1(X2)|r2_hidden(esk5_2(X2,X1),k2_relat_1(X2))|r2_hidden(esk5_2(X2,X1),X1)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.38  cnf(c_0_42, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.20/0.38  cnf(c_0_43, plain, (r2_hidden(esk7_3(X1,X2,X3),k2_relat_1(X3))|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.38  cnf(c_0_44, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.38  cnf(c_0_45, plain, (X1=k1_xboole_0|r2_hidden(esk5_2(k1_xboole_0,X1),k1_xboole_0)|r2_hidden(esk5_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.38  fof(c_0_46, negated_conjecture, ~(![X1]:k10_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(assume_negation,[status(cth)],[t172_relat_1])).
% 0.20/0.38  cnf(c_0_47, plain, (r2_hidden(esk7_3(X1,X2,k1_xboole_0),k1_xboole_0)|~r2_hidden(X1,k10_relat_1(k1_xboole_0,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_42])).
% 0.20/0.38  cnf(c_0_48, plain, (X1=k1_xboole_0|r2_hidden(esk5_2(k1_xboole_0,X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_45]), c_0_40])])).
% 0.20/0.38  fof(c_0_49, negated_conjecture, k10_relat_1(k1_xboole_0,esk8_0)!=k1_xboole_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_46])])])).
% 0.20/0.38  cnf(c_0_50, plain, (k10_relat_1(k1_xboole_0,X1)=k1_xboole_0|r2_hidden(esk7_3(esk5_2(k1_xboole_0,k10_relat_1(k1_xboole_0,X1)),X1,k1_xboole_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.38  cnf(c_0_51, negated_conjecture, (k10_relat_1(k1_xboole_0,esk8_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.38  cnf(c_0_52, plain, (k10_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_50]), c_0_40])])).
% 0.20/0.38  cnf(c_0_53, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_52])]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 54
% 0.20/0.38  # Proof object clause steps            : 26
% 0.20/0.38  # Proof object formula steps           : 28
% 0.20/0.38  # Proof object conjectures             : 5
% 0.20/0.38  # Proof object clause conjectures      : 2
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 15
% 0.20/0.38  # Proof object initial formulas used   : 14
% 0.20/0.38  # Proof object generating inferences   : 8
% 0.20/0.38  # Proof object simplifying inferences  : 15
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 14
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 23
% 0.20/0.38  # Removed in clause preprocessing      : 7
% 0.20/0.38  # Initial clauses in saturation        : 16
% 0.20/0.38  # Processed clauses                    : 85
% 0.20/0.38  # ...of these trivial                  : 1
% 0.20/0.38  # ...subsumed                          : 3
% 0.20/0.38  # ...remaining for further processing  : 81
% 0.20/0.38  # Other redundant clauses eliminated   : 2
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 3
% 0.20/0.38  # Backward-rewritten                   : 36
% 0.20/0.38  # Generated clauses                    : 244
% 0.20/0.38  # ...of the previous two non-trivial   : 246
% 0.20/0.38  # Contextual simplify-reflections      : 1
% 0.20/0.38  # Paramodulations                      : 238
% 0.20/0.38  # Factorizations                       : 4
% 0.20/0.38  # Equation resolutions                 : 2
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 24
% 0.20/0.38  #    Positive orientable unit clauses  : 5
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 0
% 0.20/0.38  #    Non-unit-clauses                  : 19
% 0.20/0.38  # Current number of unprocessed clauses: 161
% 0.20/0.38  # ...number of literals in the above   : 463
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 62
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 258
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 192
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 7
% 0.20/0.38  # Unit Clause-clause subsumption calls : 20
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 9
% 0.20/0.38  # BW rewrite match successes           : 9
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 9258
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.037 s
% 0.20/0.38  # System time              : 0.005 s
% 0.20/0.38  # Total time               : 0.042 s
% 0.20/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
