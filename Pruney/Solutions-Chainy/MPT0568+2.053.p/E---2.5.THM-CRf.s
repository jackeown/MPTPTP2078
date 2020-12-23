%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:24 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 231 expanded)
%              Number of clauses        :   33 ( 102 expanded)
%              Number of leaves         :   12 (  67 expanded)
%              Depth                    :   13
%              Number of atoms          :  121 ( 485 expanded)
%              Number of equality atoms :   54 ( 237 expanded)
%              Maximal formula depth    :   19 (   3 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

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

fof(t81_relat_1,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(t172_relat_1,conjecture,(
    ! [X1] : k10_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

fof(c_0_12,plain,(
    ! [X43] : v1_relat_1(k6_relat_1(X43)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_13,plain,(
    ! [X29,X30] :
      ( ( k4_xboole_0(X29,k1_tarski(X30)) != X29
        | ~ r2_hidden(X30,X29) )
      & ( r2_hidden(X30,X29)
        | k4_xboole_0(X29,k1_tarski(X30)) = X29 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

fof(c_0_14,plain,(
    ! [X8] : k2_tarski(X8,X8) = k1_tarski(X8) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_15,plain,(
    ! [X9,X10] : k1_enumset1(X9,X9,X10) = k2_tarski(X9,X10) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,plain,(
    ! [X11,X12,X13] : k2_enumset1(X11,X11,X12,X13) = k1_enumset1(X11,X12,X13) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_17,plain,(
    ! [X14,X15,X16,X17] : k3_enumset1(X14,X14,X15,X16,X17) = k2_enumset1(X14,X15,X16,X17) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_18,plain,(
    ! [X18,X19,X20,X21,X22] : k4_enumset1(X18,X18,X19,X20,X21,X22) = k3_enumset1(X18,X19,X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_19,plain,(
    ! [X23,X24,X25,X26,X27,X28] : k5_enumset1(X23,X23,X24,X25,X26,X27,X28) = k4_enumset1(X23,X24,X25,X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_20,plain,(
    ! [X31,X32,X33,X34,X36,X37,X38,X39,X41] :
      ( ( r2_hidden(k4_tarski(X34,esk1_4(X31,X32,X33,X34)),X31)
        | ~ r2_hidden(X34,X33)
        | X33 != k10_relat_1(X31,X32)
        | ~ v1_relat_1(X31) )
      & ( r2_hidden(esk1_4(X31,X32,X33,X34),X32)
        | ~ r2_hidden(X34,X33)
        | X33 != k10_relat_1(X31,X32)
        | ~ v1_relat_1(X31) )
      & ( ~ r2_hidden(k4_tarski(X36,X37),X31)
        | ~ r2_hidden(X37,X32)
        | r2_hidden(X36,X33)
        | X33 != k10_relat_1(X31,X32)
        | ~ v1_relat_1(X31) )
      & ( ~ r2_hidden(esk2_3(X31,X38,X39),X39)
        | ~ r2_hidden(k4_tarski(esk2_3(X31,X38,X39),X41),X31)
        | ~ r2_hidden(X41,X38)
        | X39 = k10_relat_1(X31,X38)
        | ~ v1_relat_1(X31) )
      & ( r2_hidden(k4_tarski(esk2_3(X31,X38,X39),esk3_3(X31,X38,X39)),X31)
        | r2_hidden(esk2_3(X31,X38,X39),X39)
        | X39 = k10_relat_1(X31,X38)
        | ~ v1_relat_1(X31) )
      & ( r2_hidden(esk3_3(X31,X38,X39),X38)
        | r2_hidden(esk2_3(X31,X38,X39),X39)
        | X39 = k10_relat_1(X31,X38)
        | ~ v1_relat_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

cnf(c_0_21,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t81_relat_1])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k1_tarski(X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_32,plain,
    ( r2_hidden(k4_tarski(X1,esk1_4(X2,X3,X4,X1)),X2)
    | ~ r2_hidden(X1,X4)
    | X4 != k10_relat_1(X2,X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_34,plain,
    ( X1 = k10_relat_1(k1_xboole_0,X2)
    | r2_hidden(esk3_3(k1_xboole_0,X2,X1),X2)
    | r2_hidden(esk2_3(k1_xboole_0,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_35,plain,(
    ! [X7] : k4_xboole_0(k1_xboole_0,X7) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_36,plain,
    ( r2_hidden(k4_tarski(X1,esk1_4(X2,X3,k10_relat_1(X2,X3),X1)),X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k10_relat_1(X2,X3)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_37,plain,
    ( X1 = k10_relat_1(k1_xboole_0,X2)
    | r2_hidden(esk3_3(k1_xboole_0,X2,X1),X2)
    | k4_xboole_0(X1,k5_enumset1(esk2_3(k1_xboole_0,X2,X1),esk2_3(k1_xboole_0,X2,X1),esk2_3(k1_xboole_0,X2,X1),esk2_3(k1_xboole_0,X2,X1),esk2_3(k1_xboole_0,X2,X1),esk2_3(k1_xboole_0,X2,X1),esk2_3(k1_xboole_0,X2,X1))) != X1 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_39,plain,
    ( r2_hidden(k4_tarski(X1,esk1_4(k1_xboole_0,X2,k10_relat_1(k1_xboole_0,X2),X1)),k1_xboole_0)
    | ~ r2_hidden(X1,k10_relat_1(k1_xboole_0,X2)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_31])).

cnf(c_0_40,plain,
    ( k10_relat_1(k1_xboole_0,X1) = k1_xboole_0
    | r2_hidden(esk3_3(k1_xboole_0,X1,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_41,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_42,plain,
    ( k10_relat_1(k1_xboole_0,k10_relat_1(k1_xboole_0,X1)) = k1_xboole_0
    | r2_hidden(k4_tarski(esk3_3(k1_xboole_0,k10_relat_1(k1_xboole_0,X1),k1_xboole_0),esk1_4(k1_xboole_0,X1,k10_relat_1(k1_xboole_0,X1),esk3_3(k1_xboole_0,k10_relat_1(k1_xboole_0,X1),k1_xboole_0))),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_43,plain,
    ( r2_hidden(esk1_4(X1,X2,k10_relat_1(X1,X2),X3),X2)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,k10_relat_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_44,plain,
    ( k10_relat_1(k1_xboole_0,k10_relat_1(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_42]),c_0_38])])).

cnf(c_0_45,plain,
    ( r2_hidden(k4_tarski(esk2_3(X1,X2,X3),esk3_3(X1,X2,X3)),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_46,plain,
    ( r2_hidden(esk1_4(k1_xboole_0,X1,k10_relat_1(k1_xboole_0,X1),X2),X1)
    | ~ r2_hidden(X2,k10_relat_1(k1_xboole_0,X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_31])).

cnf(c_0_47,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_44])).

cnf(c_0_48,plain,
    ( X1 = k10_relat_1(k1_xboole_0,X2)
    | r2_hidden(k4_tarski(esk2_3(k1_xboole_0,X2,X1),esk3_3(k1_xboole_0,X2,X1)),k1_xboole_0)
    | r2_hidden(esk2_3(k1_xboole_0,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_31])).

fof(c_0_49,negated_conjecture,(
    ~ ! [X1] : k10_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t172_relat_1])).

cnf(c_0_50,plain,
    ( r2_hidden(esk1_4(k1_xboole_0,k1_xboole_0,k1_xboole_0,X1),k1_xboole_0)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_51,plain,
    ( X1 = k10_relat_1(k1_xboole_0,X2)
    | r2_hidden(esk2_3(k1_xboole_0,X2,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_48]),c_0_38])])).

fof(c_0_52,negated_conjecture,(
    k10_relat_1(k1_xboole_0,esk4_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_49])])])).

cnf(c_0_53,plain,
    ( k10_relat_1(k1_xboole_0,X1) = k1_xboole_0
    | r2_hidden(esk1_4(k1_xboole_0,k1_xboole_0,k1_xboole_0,esk2_3(k1_xboole_0,X1,k1_xboole_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_54,negated_conjecture,
    ( k10_relat_1(k1_xboole_0,esk4_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_55,plain,
    ( k10_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_53]),c_0_38])])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:05:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.20/0.37  # and selection function GSelectMinInfpos.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.027 s
% 0.20/0.37  # Presaturation interreduction done
% 0.20/0.37  
% 0.20/0.37  # Proof found!
% 0.20/0.37  # SZS status Theorem
% 0.20/0.37  # SZS output start CNFRefutation
% 0.20/0.37  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.20/0.37  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.20/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.37  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.37  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.37  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.20/0.37  fof(d14_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X4,X5),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 0.20/0.37  fof(t81_relat_1, axiom, k6_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 0.20/0.37  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 0.20/0.37  fof(t172_relat_1, conjecture, ![X1]:k10_relat_1(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 0.20/0.37  fof(c_0_12, plain, ![X43]:v1_relat_1(k6_relat_1(X43)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.20/0.37  fof(c_0_13, plain, ![X29, X30]:((k4_xboole_0(X29,k1_tarski(X30))!=X29|~r2_hidden(X30,X29))&(r2_hidden(X30,X29)|k4_xboole_0(X29,k1_tarski(X30))=X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.20/0.37  fof(c_0_14, plain, ![X8]:k2_tarski(X8,X8)=k1_tarski(X8), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.37  fof(c_0_15, plain, ![X9, X10]:k1_enumset1(X9,X9,X10)=k2_tarski(X9,X10), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.37  fof(c_0_16, plain, ![X11, X12, X13]:k2_enumset1(X11,X11,X12,X13)=k1_enumset1(X11,X12,X13), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.37  fof(c_0_17, plain, ![X14, X15, X16, X17]:k3_enumset1(X14,X14,X15,X16,X17)=k2_enumset1(X14,X15,X16,X17), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.37  fof(c_0_18, plain, ![X18, X19, X20, X21, X22]:k4_enumset1(X18,X18,X19,X20,X21,X22)=k3_enumset1(X18,X19,X20,X21,X22), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.37  fof(c_0_19, plain, ![X23, X24, X25, X26, X27, X28]:k5_enumset1(X23,X23,X24,X25,X26,X27,X28)=k4_enumset1(X23,X24,X25,X26,X27,X28), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.20/0.37  fof(c_0_20, plain, ![X31, X32, X33, X34, X36, X37, X38, X39, X41]:((((r2_hidden(k4_tarski(X34,esk1_4(X31,X32,X33,X34)),X31)|~r2_hidden(X34,X33)|X33!=k10_relat_1(X31,X32)|~v1_relat_1(X31))&(r2_hidden(esk1_4(X31,X32,X33,X34),X32)|~r2_hidden(X34,X33)|X33!=k10_relat_1(X31,X32)|~v1_relat_1(X31)))&(~r2_hidden(k4_tarski(X36,X37),X31)|~r2_hidden(X37,X32)|r2_hidden(X36,X33)|X33!=k10_relat_1(X31,X32)|~v1_relat_1(X31)))&((~r2_hidden(esk2_3(X31,X38,X39),X39)|(~r2_hidden(k4_tarski(esk2_3(X31,X38,X39),X41),X31)|~r2_hidden(X41,X38))|X39=k10_relat_1(X31,X38)|~v1_relat_1(X31))&((r2_hidden(k4_tarski(esk2_3(X31,X38,X39),esk3_3(X31,X38,X39)),X31)|r2_hidden(esk2_3(X31,X38,X39),X39)|X39=k10_relat_1(X31,X38)|~v1_relat_1(X31))&(r2_hidden(esk3_3(X31,X38,X39),X38)|r2_hidden(esk2_3(X31,X38,X39),X39)|X39=k10_relat_1(X31,X38)|~v1_relat_1(X31))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).
% 0.20/0.37  cnf(c_0_21, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.37  cnf(c_0_22, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t81_relat_1])).
% 0.20/0.37  cnf(c_0_23, plain, (k4_xboole_0(X1,k1_tarski(X2))!=X1|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.37  cnf(c_0_24, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.37  cnf(c_0_25, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.37  cnf(c_0_26, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.37  cnf(c_0_27, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.37  cnf(c_0_28, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.37  cnf(c_0_29, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.37  cnf(c_0_30, plain, (r2_hidden(esk3_3(X1,X2,X3),X2)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k10_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.37  cnf(c_0_31, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.37  cnf(c_0_32, plain, (r2_hidden(k4_tarski(X1,esk1_4(X2,X3,X4,X1)),X2)|~r2_hidden(X1,X4)|X4!=k10_relat_1(X2,X3)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.37  cnf(c_0_33, plain, (k4_xboole_0(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2))!=X1|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29])).
% 0.20/0.37  cnf(c_0_34, plain, (X1=k10_relat_1(k1_xboole_0,X2)|r2_hidden(esk3_3(k1_xboole_0,X2,X1),X2)|r2_hidden(esk2_3(k1_xboole_0,X2,X1),X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.37  fof(c_0_35, plain, ![X7]:k4_xboole_0(k1_xboole_0,X7)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.20/0.37  cnf(c_0_36, plain, (r2_hidden(k4_tarski(X1,esk1_4(X2,X3,k10_relat_1(X2,X3),X1)),X2)|~v1_relat_1(X2)|~r2_hidden(X1,k10_relat_1(X2,X3))), inference(er,[status(thm)],[c_0_32])).
% 0.20/0.37  cnf(c_0_37, plain, (X1=k10_relat_1(k1_xboole_0,X2)|r2_hidden(esk3_3(k1_xboole_0,X2,X1),X2)|k4_xboole_0(X1,k5_enumset1(esk2_3(k1_xboole_0,X2,X1),esk2_3(k1_xboole_0,X2,X1),esk2_3(k1_xboole_0,X2,X1),esk2_3(k1_xboole_0,X2,X1),esk2_3(k1_xboole_0,X2,X1),esk2_3(k1_xboole_0,X2,X1),esk2_3(k1_xboole_0,X2,X1)))!=X1), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.37  cnf(c_0_38, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.37  cnf(c_0_39, plain, (r2_hidden(k4_tarski(X1,esk1_4(k1_xboole_0,X2,k10_relat_1(k1_xboole_0,X2),X1)),k1_xboole_0)|~r2_hidden(X1,k10_relat_1(k1_xboole_0,X2))), inference(spm,[status(thm)],[c_0_36, c_0_31])).
% 0.20/0.37  cnf(c_0_40, plain, (k10_relat_1(k1_xboole_0,X1)=k1_xboole_0|r2_hidden(esk3_3(k1_xboole_0,X1,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.37  cnf(c_0_41, plain, (r2_hidden(esk1_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k10_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.37  cnf(c_0_42, plain, (k10_relat_1(k1_xboole_0,k10_relat_1(k1_xboole_0,X1))=k1_xboole_0|r2_hidden(k4_tarski(esk3_3(k1_xboole_0,k10_relat_1(k1_xboole_0,X1),k1_xboole_0),esk1_4(k1_xboole_0,X1,k10_relat_1(k1_xboole_0,X1),esk3_3(k1_xboole_0,k10_relat_1(k1_xboole_0,X1),k1_xboole_0))),k1_xboole_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.37  cnf(c_0_43, plain, (r2_hidden(esk1_4(X1,X2,k10_relat_1(X1,X2),X3),X2)|~v1_relat_1(X1)|~r2_hidden(X3,k10_relat_1(X1,X2))), inference(er,[status(thm)],[c_0_41])).
% 0.20/0.37  cnf(c_0_44, plain, (k10_relat_1(k1_xboole_0,k10_relat_1(k1_xboole_0,X1))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_42]), c_0_38])])).
% 0.20/0.37  cnf(c_0_45, plain, (r2_hidden(k4_tarski(esk2_3(X1,X2,X3),esk3_3(X1,X2,X3)),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k10_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.37  cnf(c_0_46, plain, (r2_hidden(esk1_4(k1_xboole_0,X1,k10_relat_1(k1_xboole_0,X1),X2),X1)|~r2_hidden(X2,k10_relat_1(k1_xboole_0,X1))), inference(spm,[status(thm)],[c_0_43, c_0_31])).
% 0.20/0.37  cnf(c_0_47, plain, (k10_relat_1(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_44, c_0_44])).
% 0.20/0.37  cnf(c_0_48, plain, (X1=k10_relat_1(k1_xboole_0,X2)|r2_hidden(k4_tarski(esk2_3(k1_xboole_0,X2,X1),esk3_3(k1_xboole_0,X2,X1)),k1_xboole_0)|r2_hidden(esk2_3(k1_xboole_0,X2,X1),X1)), inference(spm,[status(thm)],[c_0_45, c_0_31])).
% 0.20/0.37  fof(c_0_49, negated_conjecture, ~(![X1]:k10_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(assume_negation,[status(cth)],[t172_relat_1])).
% 0.20/0.37  cnf(c_0_50, plain, (r2_hidden(esk1_4(k1_xboole_0,k1_xboole_0,k1_xboole_0,X1),k1_xboole_0)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.37  cnf(c_0_51, plain, (X1=k10_relat_1(k1_xboole_0,X2)|r2_hidden(esk2_3(k1_xboole_0,X2,X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_48]), c_0_38])])).
% 0.20/0.37  fof(c_0_52, negated_conjecture, k10_relat_1(k1_xboole_0,esk4_0)!=k1_xboole_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_49])])])).
% 0.20/0.37  cnf(c_0_53, plain, (k10_relat_1(k1_xboole_0,X1)=k1_xboole_0|r2_hidden(esk1_4(k1_xboole_0,k1_xboole_0,k1_xboole_0,esk2_3(k1_xboole_0,X1,k1_xboole_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.37  cnf(c_0_54, negated_conjecture, (k10_relat_1(k1_xboole_0,esk4_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.37  cnf(c_0_55, plain, (k10_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_53]), c_0_38])])).
% 0.20/0.37  cnf(c_0_56, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55])]), ['proof']).
% 0.20/0.37  # SZS output end CNFRefutation
% 0.20/0.37  # Proof object total steps             : 57
% 0.20/0.37  # Proof object clause steps            : 33
% 0.20/0.37  # Proof object formula steps           : 24
% 0.20/0.37  # Proof object conjectures             : 5
% 0.20/0.37  # Proof object clause conjectures      : 2
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 15
% 0.20/0.37  # Proof object initial formulas used   : 12
% 0.20/0.37  # Proof object generating inferences   : 14
% 0.20/0.37  # Proof object simplifying inferences  : 16
% 0.20/0.37  # Training examples: 0 positive, 0 negative
% 0.20/0.37  # Parsed axioms                        : 12
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 18
% 0.20/0.37  # Removed in clause preprocessing      : 6
% 0.20/0.37  # Initial clauses in saturation        : 12
% 0.20/0.37  # Processed clauses                    : 79
% 0.20/0.37  # ...of these trivial                  : 0
% 0.20/0.37  # ...subsumed                          : 8
% 0.20/0.37  # ...remaining for further processing  : 71
% 0.20/0.37  # Other redundant clauses eliminated   : 3
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 6
% 0.20/0.37  # Backward-rewritten                   : 27
% 0.20/0.37  # Generated clauses                    : 195
% 0.20/0.37  # ...of the previous two non-trivial   : 193
% 0.20/0.37  # Contextual simplify-reflections      : 0
% 0.20/0.37  # Paramodulations                      : 192
% 0.20/0.37  # Factorizations                       : 0
% 0.20/0.37  # Equation resolutions                 : 3
% 0.20/0.37  # Propositional unsat checks           : 0
% 0.20/0.37  #    Propositional check models        : 0
% 0.20/0.37  #    Propositional check unsatisfiable : 0
% 0.20/0.37  #    Propositional clauses             : 0
% 0.20/0.37  #    Propositional clauses after purity: 0
% 0.20/0.37  #    Propositional unsat core size     : 0
% 0.20/0.37  #    Propositional preprocessing time  : 0.000
% 0.20/0.37  #    Propositional encoding time       : 0.000
% 0.20/0.37  #    Propositional solver time         : 0.000
% 0.20/0.37  #    Success case prop preproc time    : 0.000
% 0.20/0.37  #    Success case prop encoding time   : 0.000
% 0.20/0.37  #    Success case prop solver time     : 0.000
% 0.20/0.37  # Current number of processed clauses  : 23
% 0.20/0.37  #    Positive orientable unit clauses  : 5
% 0.20/0.37  #    Positive unorientable unit clauses: 0
% 0.20/0.37  #    Negative unit clauses             : 0
% 0.20/0.37  #    Non-unit-clauses                  : 18
% 0.20/0.37  # Current number of unprocessed clauses: 125
% 0.20/0.37  # ...number of literals in the above   : 406
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 51
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 263
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 139
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 14
% 0.20/0.37  # Unit Clause-clause subsumption calls : 13
% 0.20/0.37  # Rewrite failures with RHS unbound    : 0
% 0.20/0.37  # BW rewrite match attempts            : 7
% 0.20/0.37  # BW rewrite match successes           : 7
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 6289
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.036 s
% 0.20/0.38  # System time              : 0.003 s
% 0.20/0.38  # Total time               : 0.038 s
% 0.20/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
