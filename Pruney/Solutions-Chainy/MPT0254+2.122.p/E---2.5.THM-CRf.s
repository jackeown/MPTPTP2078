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
% DateTime   : Thu Dec  3 10:41:14 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 159 expanded)
%              Number of clauses        :   30 (  63 expanded)
%              Number of leaves         :   15 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :   97 ( 196 expanded)
%              Number of equality atoms :   60 ( 159 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t49_zfmisc_1,conjecture,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t77_enumset1,axiom,(
    ! [X1,X2] : k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(t85_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k5_enumset1(X1,X1,X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_enumset1)).

fof(t125_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X3,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

fof(t32_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(k1_tarski(X1),k1_tarski(X2))) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).

fof(l68_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(fc5_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X1)
     => ~ v1_xboole_0(k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_xboole_0)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(l24_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_xboole_0(k1_tarski(X1),X2)
        & r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t49_zfmisc_1])).

fof(c_0_16,negated_conjecture,(
    k2_xboole_0(k1_tarski(esk2_0),esk3_0) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_17,plain,(
    ! [X41] : k2_tarski(X41,X41) = k1_tarski(X41) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_18,plain,(
    ! [X53,X54] : k3_tarski(k2_tarski(X53,X54)) = k2_xboole_0(X53,X54) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_19,plain,(
    ! [X45,X46] : k2_enumset1(X45,X45,X45,X46) = k2_tarski(X45,X46) ),
    inference(variable_rename,[status(thm)],[t77_enumset1])).

fof(c_0_20,plain,(
    ! [X47,X48,X49,X50] : k5_enumset1(X47,X47,X47,X47,X48,X49,X50) = k2_enumset1(X47,X48,X49,X50) ),
    inference(variable_rename,[status(thm)],[t85_enumset1])).

fof(c_0_21,plain,(
    ! [X37,X38,X39,X40] : k2_enumset1(X37,X38,X39,X40) = k2_enumset1(X40,X39,X38,X37) ),
    inference(variable_rename,[status(thm)],[t125_enumset1])).

fof(c_0_22,plain,(
    ! [X55,X56] : k3_tarski(k2_tarski(k1_tarski(X55),k1_tarski(X56))) = k2_tarski(X55,X56) ),
    inference(variable_rename,[status(thm)],[t32_zfmisc_1])).

fof(c_0_23,plain,(
    ! [X30,X31,X32,X33,X34,X35,X36] : k5_enumset1(X30,X31,X32,X33,X34,X35,X36) = k2_xboole_0(k2_enumset1(X30,X31,X32,X33),k1_enumset1(X34,X35,X36)) ),
    inference(variable_rename,[status(thm)],[l68_enumset1])).

fof(c_0_24,plain,(
    ! [X42,X43,X44] : k2_enumset1(X42,X42,X43,X44) = k1_enumset1(X42,X43,X44) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

cnf(c_0_25,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk2_0),esk3_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( k5_enumset1(X1,X1,X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k3_tarski(k2_tarski(k1_tarski(X1),k1_tarski(X2))) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_34,plain,(
    ! [X11,X12] :
      ( v1_xboole_0(X11)
      | ~ v1_xboole_0(k2_xboole_0(X12,X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_xboole_0])])])).

cnf(c_0_35,negated_conjecture,
    ( k3_tarski(k5_enumset1(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28]),c_0_28]),c_0_29]),c_0_29]),c_0_29]),c_0_29])).

cnf(c_0_36,plain,
    ( k5_enumset1(X1,X1,X1,X1,X2,X3,X4) = k5_enumset1(X4,X4,X4,X4,X3,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_29]),c_0_29])).

cnf(c_0_37,plain,
    ( k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X2))) = k5_enumset1(X1,X1,X1,X1,X1,X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_26]),c_0_26]),c_0_28]),c_0_28]),c_0_28]),c_0_28]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_29])).

cnf(c_0_38,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X6,X7))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_27]),c_0_28]),c_0_33]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_29])).

fof(c_0_39,plain,(
    ! [X21,X22,X23,X24,X25,X26,X27,X28] :
      ( ( ~ r2_hidden(X24,X23)
        | X24 = X21
        | X24 = X22
        | X23 != k2_tarski(X21,X22) )
      & ( X25 != X21
        | r2_hidden(X25,X23)
        | X23 != k2_tarski(X21,X22) )
      & ( X25 != X22
        | r2_hidden(X25,X23)
        | X23 != k2_tarski(X21,X22) )
      & ( esk1_3(X26,X27,X28) != X26
        | ~ r2_hidden(esk1_3(X26,X27,X28),X28)
        | X28 = k2_tarski(X26,X27) )
      & ( esk1_3(X26,X27,X28) != X27
        | ~ r2_hidden(esk1_3(X26,X27,X28),X28)
        | X28 = k2_tarski(X26,X27) )
      & ( r2_hidden(esk1_3(X26,X27,X28),X28)
        | esk1_3(X26,X27,X28) = X26
        | esk1_3(X26,X27,X28) = X27
        | X28 = k2_tarski(X26,X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_40,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(k2_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,plain,
    ( k5_enumset1(X1,X1,X1,X1,X2,X2,X2) = k5_enumset1(X1,X1,X1,X1,X1,X1,X2) ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_43,plain,(
    ! [X51,X52] :
      ( ~ r1_xboole_0(k1_tarski(X51),X52)
      | ~ r2_hidden(X51,X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_45,plain,(
    ! [X8] :
      ( ~ v1_xboole_0(X8)
      | X8 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_46,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_47,negated_conjecture,
    ( k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_49,plain,
    ( ~ r1_xboole_0(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_50,plain,(
    ! [X18] : r1_xboole_0(X18,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k5_enumset1(X2,X2,X2,X2,X2,X2,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_28]),c_0_29])).

cnf(c_0_52,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( v1_xboole_0(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])])).

cnf(c_0_54,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_26]),c_0_28]),c_0_29])).

cnf(c_0_55,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_51])])).

cnf(c_0_57,negated_conjecture,
    ( k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:47:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.33  # Version: 2.5pre002
% 0.19/0.34  # No SInE strategy applied
% 0.19/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S032I
% 0.19/0.37  # and selection function SelectUnlessUniqMax.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.028 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t49_zfmisc_1, conjecture, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.19/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.37  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.19/0.37  fof(t77_enumset1, axiom, ![X1, X2]:k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_enumset1)).
% 0.19/0.37  fof(t85_enumset1, axiom, ![X1, X2, X3, X4]:k5_enumset1(X1,X1,X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_enumset1)).
% 0.19/0.37  fof(t125_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X3,X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_enumset1)).
% 0.19/0.37  fof(t32_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(k1_tarski(X1),k1_tarski(X2)))=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 0.19/0.37  fof(l68_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l68_enumset1)).
% 0.19/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.37  fof(fc5_xboole_0, axiom, ![X1, X2]:(~(v1_xboole_0(X1))=>~(v1_xboole_0(k2_xboole_0(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_xboole_0)).
% 0.19/0.37  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.19/0.37  fof(l24_zfmisc_1, axiom, ![X1, X2]:~((r1_xboole_0(k1_tarski(X1),X2)&r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 0.19/0.37  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.19/0.37  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.37  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.19/0.37  fof(c_0_15, negated_conjecture, ~(![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(assume_negation,[status(cth)],[t49_zfmisc_1])).
% 0.19/0.37  fof(c_0_16, negated_conjecture, k2_xboole_0(k1_tarski(esk2_0),esk3_0)=k1_xboole_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.19/0.37  fof(c_0_17, plain, ![X41]:k2_tarski(X41,X41)=k1_tarski(X41), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.37  fof(c_0_18, plain, ![X53, X54]:k3_tarski(k2_tarski(X53,X54))=k2_xboole_0(X53,X54), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.19/0.37  fof(c_0_19, plain, ![X45, X46]:k2_enumset1(X45,X45,X45,X46)=k2_tarski(X45,X46), inference(variable_rename,[status(thm)],[t77_enumset1])).
% 0.19/0.37  fof(c_0_20, plain, ![X47, X48, X49, X50]:k5_enumset1(X47,X47,X47,X47,X48,X49,X50)=k2_enumset1(X47,X48,X49,X50), inference(variable_rename,[status(thm)],[t85_enumset1])).
% 0.19/0.37  fof(c_0_21, plain, ![X37, X38, X39, X40]:k2_enumset1(X37,X38,X39,X40)=k2_enumset1(X40,X39,X38,X37), inference(variable_rename,[status(thm)],[t125_enumset1])).
% 0.19/0.37  fof(c_0_22, plain, ![X55, X56]:k3_tarski(k2_tarski(k1_tarski(X55),k1_tarski(X56)))=k2_tarski(X55,X56), inference(variable_rename,[status(thm)],[t32_zfmisc_1])).
% 0.19/0.37  fof(c_0_23, plain, ![X30, X31, X32, X33, X34, X35, X36]:k5_enumset1(X30,X31,X32,X33,X34,X35,X36)=k2_xboole_0(k2_enumset1(X30,X31,X32,X33),k1_enumset1(X34,X35,X36)), inference(variable_rename,[status(thm)],[l68_enumset1])).
% 0.19/0.37  fof(c_0_24, plain, ![X42, X43, X44]:k2_enumset1(X42,X42,X43,X44)=k1_enumset1(X42,X43,X44), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.37  cnf(c_0_25, negated_conjecture, (k2_xboole_0(k1_tarski(esk2_0),esk3_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.37  cnf(c_0_26, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.37  cnf(c_0_27, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.37  cnf(c_0_28, plain, (k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.37  cnf(c_0_29, plain, (k5_enumset1(X1,X1,X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.37  cnf(c_0_30, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.37  cnf(c_0_31, plain, (k3_tarski(k2_tarski(k1_tarski(X1),k1_tarski(X2)))=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.37  cnf(c_0_32, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.37  cnf(c_0_33, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.37  fof(c_0_34, plain, ![X11, X12]:(v1_xboole_0(X11)|~v1_xboole_0(k2_xboole_0(X12,X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_xboole_0])])])).
% 0.19/0.37  cnf(c_0_35, negated_conjecture, (k3_tarski(k5_enumset1(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28]), c_0_28]), c_0_29]), c_0_29]), c_0_29]), c_0_29])).
% 0.19/0.37  cnf(c_0_36, plain, (k5_enumset1(X1,X1,X1,X1,X2,X3,X4)=k5_enumset1(X4,X4,X4,X4,X3,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_29]), c_0_29])).
% 0.19/0.37  cnf(c_0_37, plain, (k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X2)))=k5_enumset1(X1,X1,X1,X1,X1,X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_26]), c_0_26]), c_0_28]), c_0_28]), c_0_28]), c_0_28]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_29])).
% 0.19/0.37  cnf(c_0_38, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X6,X7)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_27]), c_0_28]), c_0_33]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_29])).
% 0.19/0.37  fof(c_0_39, plain, ![X21, X22, X23, X24, X25, X26, X27, X28]:(((~r2_hidden(X24,X23)|(X24=X21|X24=X22)|X23!=k2_tarski(X21,X22))&((X25!=X21|r2_hidden(X25,X23)|X23!=k2_tarski(X21,X22))&(X25!=X22|r2_hidden(X25,X23)|X23!=k2_tarski(X21,X22))))&(((esk1_3(X26,X27,X28)!=X26|~r2_hidden(esk1_3(X26,X27,X28),X28)|X28=k2_tarski(X26,X27))&(esk1_3(X26,X27,X28)!=X27|~r2_hidden(esk1_3(X26,X27,X28),X28)|X28=k2_tarski(X26,X27)))&(r2_hidden(esk1_3(X26,X27,X28),X28)|(esk1_3(X26,X27,X28)=X26|esk1_3(X26,X27,X28)=X27)|X28=k2_tarski(X26,X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.19/0.37  cnf(c_0_40, plain, (v1_xboole_0(X1)|~v1_xboole_0(k2_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.37  cnf(c_0_41, negated_conjecture, (k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)))=k1_xboole_0), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.37  cnf(c_0_42, plain, (k5_enumset1(X1,X1,X1,X1,X2,X2,X2)=k5_enumset1(X1,X1,X1,X1,X1,X1,X2)), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.37  fof(c_0_43, plain, ![X51, X52]:(~r1_xboole_0(k1_tarski(X51),X52)|~r2_hidden(X51,X52)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).
% 0.19/0.37  cnf(c_0_44, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.37  fof(c_0_45, plain, ![X8]:(~v1_xboole_0(X8)|X8=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.19/0.37  cnf(c_0_46, plain, (v1_xboole_0(X1)|~v1_xboole_0(k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_27]), c_0_28]), c_0_29])).
% 0.19/0.37  cnf(c_0_47, negated_conjecture, (k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)))=k1_xboole_0), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.37  cnf(c_0_48, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.37  cnf(c_0_49, plain, (~r1_xboole_0(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.37  fof(c_0_50, plain, ![X18]:r1_xboole_0(X18,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.19/0.37  cnf(c_0_51, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k5_enumset1(X2,X2,X2,X2,X2,X2,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_28]), c_0_29])).
% 0.19/0.37  cnf(c_0_52, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.37  cnf(c_0_53, negated_conjecture, (v1_xboole_0(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])])).
% 0.19/0.37  cnf(c_0_54, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_26]), c_0_28]), c_0_29])).
% 0.19/0.37  cnf(c_0_55, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.37  cnf(c_0_56, plain, (r2_hidden(X1,k5_enumset1(X1,X1,X1,X1,X1,X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_51])])).
% 0.19/0.37  cnf(c_0_57, negated_conjecture, (k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.19/0.37  cnf(c_0_58, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.19/0.37  cnf(c_0_59, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 60
% 0.19/0.37  # Proof object clause steps            : 30
% 0.19/0.37  # Proof object formula steps           : 30
% 0.19/0.37  # Proof object conjectures             : 10
% 0.19/0.37  # Proof object clause conjectures      : 7
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 15
% 0.19/0.37  # Proof object initial formulas used   : 15
% 0.19/0.37  # Proof object generating inferences   : 4
% 0.19/0.37  # Proof object simplifying inferences  : 46
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 20
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 28
% 0.19/0.37  # Removed in clause preprocessing      : 6
% 0.19/0.37  # Initial clauses in saturation        : 22
% 0.19/0.37  # Processed clauses                    : 47
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 0
% 0.19/0.37  # ...remaining for further processing  : 47
% 0.19/0.37  # Other redundant clauses eliminated   : 7
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 4
% 0.19/0.37  # Generated clauses                    : 17
% 0.19/0.37  # ...of the previous two non-trivial   : 13
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 12
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 7
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 17
% 0.19/0.37  #    Positive orientable unit clauses  : 8
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 1
% 0.19/0.37  #    Non-unit-clauses                  : 8
% 0.19/0.37  # Current number of unprocessed clauses: 8
% 0.19/0.37  # ...number of literals in the above   : 17
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 31
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 5
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 4
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.37  # Unit Clause-clause subsumption calls : 4
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 44
% 0.19/0.37  # BW rewrite match successes           : 25
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 1670
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.031 s
% 0.19/0.37  # System time              : 0.002 s
% 0.19/0.37  # Total time               : 0.033 s
% 0.19/0.37  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
