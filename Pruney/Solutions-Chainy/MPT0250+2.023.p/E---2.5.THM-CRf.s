%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:40:10 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 315 expanded)
%              Number of clauses        :   39 ( 132 expanded)
%              Number of leaves         :   12 (  90 expanded)
%              Depth                    :   14
%              Number of atoms          :  137 ( 518 expanded)
%              Number of equality atoms :   47 ( 310 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t45_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)
     => r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

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

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)
       => r2_hidden(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t45_zfmisc_1])).

fof(c_0_13,plain,(
    ! [X57,X58] : k3_tarski(k2_tarski(X57,X58)) = k2_xboole_0(X57,X58) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_14,plain,(
    ! [X48,X49] : k1_enumset1(X48,X48,X49) = k2_tarski(X48,X49) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_15,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k1_tarski(esk5_0),esk6_0),esk6_0)
    & ~ r2_hidden(esk5_0,esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_16,plain,(
    ! [X47] : k2_tarski(X47,X47) = k1_tarski(X47) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_17,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X50,X51,X52] : k2_enumset1(X50,X50,X51,X52) = k1_enumset1(X50,X51,X52) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_20,plain,(
    ! [X53,X54,X55,X56] : k3_enumset1(X53,X53,X54,X55,X56) = k2_enumset1(X53,X54,X55,X56) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_21,plain,(
    ! [X38,X39] : k2_tarski(X38,X39) = k2_tarski(X39,X38) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k1_tarski(esk5_0),esk6_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_28,plain,(
    ! [X27,X28] :
      ( ( r1_tarski(X27,X28)
        | X27 != X28 )
      & ( r1_tarski(X28,X27)
        | X27 != X28 )
      & ( ~ r1_tarski(X27,X28)
        | ~ r1_tarski(X28,X27)
        | X27 = X28 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(k3_tarski(k3_enumset1(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0)),esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_18]),c_0_24]),c_0_25]),c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_26]),c_0_26])).

cnf(c_0_30,plain,
    ( k3_enumset1(X1,X1,X1,X1,X2) = k3_enumset1(X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_18]),c_0_18]),c_0_25]),c_0_25]),c_0_26]),c_0_26])).

fof(c_0_31,plain,(
    ! [X36,X37] : r1_tarski(X36,k2_xboole_0(X36,X37)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_32,plain,(
    ! [X31,X32,X33] :
      ( ( r1_xboole_0(X31,k2_xboole_0(X32,X33))
        | ~ r1_xboole_0(X31,X32)
        | ~ r1_xboole_0(X31,X33) )
      & ( r1_xboole_0(X31,X32)
        | ~ r1_xboole_0(X31,k2_xboole_0(X32,X33)) )
      & ( r1_xboole_0(X31,X33)
        | ~ r1_xboole_0(X31,k2_xboole_0(X32,X33)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

cnf(c_0_33,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),esk6_0) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_36,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k2_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) = esk6_0
    | ~ r1_tarski(esk6_0,k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_39,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k3_tarski(k3_enumset1(X3,X3,X3,X3,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_40,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38])])).

fof(c_0_41,plain,(
    ! [X21,X22,X24,X25,X26] :
      ( ( r2_hidden(esk3_2(X21,X22),X21)
        | r1_xboole_0(X21,X22) )
      & ( r2_hidden(esk3_2(X21,X22),X22)
        | r1_xboole_0(X21,X22) )
      & ( ~ r2_hidden(X26,X24)
        | ~ r2_hidden(X26,X25)
        | ~ r1_xboole_0(X24,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_42,plain,(
    ! [X40,X41,X42,X43,X44,X45] :
      ( ( ~ r2_hidden(X42,X41)
        | X42 = X40
        | X41 != k1_tarski(X40) )
      & ( X43 != X40
        | r2_hidden(X43,X41)
        | X41 != k1_tarski(X40) )
      & ( ~ r2_hidden(esk4_2(X44,X45),X45)
        | esk4_2(X44,X45) != X44
        | X45 = k1_tarski(X44) )
      & ( r2_hidden(esk4_2(X44,X45),X45)
        | esk4_2(X44,X45) = X44
        | X45 = k1_tarski(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_43,negated_conjecture,
    ( r1_xboole_0(X1,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))
    | ~ r1_xboole_0(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_46,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( r1_xboole_0(X1,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))
    | r2_hidden(esk3_2(X1,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X2,X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_23]),c_0_18]),c_0_25]),c_0_26])).

cnf(c_0_50,negated_conjecture,
    ( r1_xboole_0(X1,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))
    | r2_hidden(esk3_2(X1,esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_46])).

cnf(c_0_51,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk3_2(X1,esk6_0),X1)
    | ~ r2_hidden(X2,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,k3_enumset1(X1,X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_49])])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk3_2(X1,esk6_0),esk6_0)
    | ~ r2_hidden(X2,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_50])).

cnf(c_0_55,plain,
    ( X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_23]),c_0_18]),c_0_25]),c_0_26])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk3_2(X1,esk6_0),X1)
    | ~ r2_hidden(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk3_2(X1,esk6_0),esk6_0)
    | ~ r2_hidden(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_53])).

cnf(c_0_58,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk3_2(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk3_2(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_53])).

cnf(c_0_61,negated_conjecture,
    ( esk3_2(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_62,negated_conjecture,
    ( ~ r2_hidden(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61]),c_0_62]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:40:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.43  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.19/0.43  # and selection function SelectNegativeLiterals.
% 0.19/0.43  #
% 0.19/0.43  # Preprocessing time       : 0.028 s
% 0.19/0.43  # Presaturation interreduction done
% 0.19/0.43  
% 0.19/0.43  # Proof found!
% 0.19/0.43  # SZS status Theorem
% 0.19/0.43  # SZS output start CNFRefutation
% 0.19/0.43  fof(t45_zfmisc_1, conjecture, ![X1, X2]:(r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 0.19/0.43  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.19/0.43  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.43  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.43  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.43  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.43  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.19/0.43  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.43  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.19/0.43  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 0.19/0.43  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.19/0.43  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.19/0.43  fof(c_0_12, negated_conjecture, ~(![X1, X2]:(r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)=>r2_hidden(X1,X2))), inference(assume_negation,[status(cth)],[t45_zfmisc_1])).
% 0.19/0.43  fof(c_0_13, plain, ![X57, X58]:k3_tarski(k2_tarski(X57,X58))=k2_xboole_0(X57,X58), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.19/0.43  fof(c_0_14, plain, ![X48, X49]:k1_enumset1(X48,X48,X49)=k2_tarski(X48,X49), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.43  fof(c_0_15, negated_conjecture, (r1_tarski(k2_xboole_0(k1_tarski(esk5_0),esk6_0),esk6_0)&~r2_hidden(esk5_0,esk6_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.19/0.43  fof(c_0_16, plain, ![X47]:k2_tarski(X47,X47)=k1_tarski(X47), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.43  cnf(c_0_17, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.43  cnf(c_0_18, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.43  fof(c_0_19, plain, ![X50, X51, X52]:k2_enumset1(X50,X50,X51,X52)=k1_enumset1(X50,X51,X52), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.43  fof(c_0_20, plain, ![X53, X54, X55, X56]:k3_enumset1(X53,X53,X54,X55,X56)=k2_enumset1(X53,X54,X55,X56), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.43  fof(c_0_21, plain, ![X38, X39]:k2_tarski(X38,X39)=k2_tarski(X39,X38), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.19/0.43  cnf(c_0_22, negated_conjecture, (r1_tarski(k2_xboole_0(k1_tarski(esk5_0),esk6_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.43  cnf(c_0_23, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.43  cnf(c_0_24, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.43  cnf(c_0_25, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.43  cnf(c_0_26, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.43  cnf(c_0_27, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.43  fof(c_0_28, plain, ![X27, X28]:(((r1_tarski(X27,X28)|X27!=X28)&(r1_tarski(X28,X27)|X27!=X28))&(~r1_tarski(X27,X28)|~r1_tarski(X28,X27)|X27=X28)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.43  cnf(c_0_29, negated_conjecture, (r1_tarski(k3_tarski(k3_enumset1(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0)),esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_18]), c_0_24]), c_0_25]), c_0_25]), c_0_25]), c_0_26]), c_0_26]), c_0_26]), c_0_26])).
% 0.19/0.43  cnf(c_0_30, plain, (k3_enumset1(X1,X1,X1,X1,X2)=k3_enumset1(X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_18]), c_0_18]), c_0_25]), c_0_25]), c_0_26]), c_0_26])).
% 0.19/0.43  fof(c_0_31, plain, ![X36, X37]:r1_tarski(X36,k2_xboole_0(X36,X37)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.19/0.43  fof(c_0_32, plain, ![X31, X32, X33]:((r1_xboole_0(X31,k2_xboole_0(X32,X33))|~r1_xboole_0(X31,X32)|~r1_xboole_0(X31,X33))&((r1_xboole_0(X31,X32)|~r1_xboole_0(X31,k2_xboole_0(X32,X33)))&(r1_xboole_0(X31,X33)|~r1_xboole_0(X31,k2_xboole_0(X32,X33))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 0.19/0.43  cnf(c_0_33, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.43  cnf(c_0_34, negated_conjecture, (r1_tarski(k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),esk6_0)), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.43  cnf(c_0_35, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.43  cnf(c_0_36, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k2_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.43  cnf(c_0_37, negated_conjecture, (k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))=esk6_0|~r1_tarski(esk6_0,k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.43  cnf(c_0_38, plain, (r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_24]), c_0_25]), c_0_26])).
% 0.19/0.43  cnf(c_0_39, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k3_tarski(k3_enumset1(X3,X3,X3,X3,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_24]), c_0_25]), c_0_26])).
% 0.19/0.43  cnf(c_0_40, negated_conjecture, (k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38])])).
% 0.19/0.43  fof(c_0_41, plain, ![X21, X22, X24, X25, X26]:(((r2_hidden(esk3_2(X21,X22),X21)|r1_xboole_0(X21,X22))&(r2_hidden(esk3_2(X21,X22),X22)|r1_xboole_0(X21,X22)))&(~r2_hidden(X26,X24)|~r2_hidden(X26,X25)|~r1_xboole_0(X24,X25))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.19/0.43  fof(c_0_42, plain, ![X40, X41, X42, X43, X44, X45]:(((~r2_hidden(X42,X41)|X42=X40|X41!=k1_tarski(X40))&(X43!=X40|r2_hidden(X43,X41)|X41!=k1_tarski(X40)))&((~r2_hidden(esk4_2(X44,X45),X45)|esk4_2(X44,X45)!=X44|X45=k1_tarski(X44))&(r2_hidden(esk4_2(X44,X45),X45)|esk4_2(X44,X45)=X44|X45=k1_tarski(X44)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.19/0.43  cnf(c_0_43, negated_conjecture, (r1_xboole_0(X1,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))|~r1_xboole_0(X1,esk6_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.43  cnf(c_0_44, plain, (r2_hidden(esk3_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.43  cnf(c_0_45, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.43  cnf(c_0_46, plain, (r2_hidden(esk3_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.43  cnf(c_0_47, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.43  cnf(c_0_48, negated_conjecture, (r1_xboole_0(X1,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))|r2_hidden(esk3_2(X1,esk6_0),X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.43  cnf(c_0_49, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X2,X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_23]), c_0_18]), c_0_25]), c_0_26])).
% 0.19/0.43  cnf(c_0_50, negated_conjecture, (r1_xboole_0(X1,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))|r2_hidden(esk3_2(X1,esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_43, c_0_46])).
% 0.19/0.43  cnf(c_0_51, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.43  cnf(c_0_52, negated_conjecture, (r2_hidden(esk3_2(X1,esk6_0),X1)|~r2_hidden(X2,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.43  cnf(c_0_53, plain, (r2_hidden(X1,k3_enumset1(X1,X1,X1,X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_49])])).
% 0.19/0.43  cnf(c_0_54, negated_conjecture, (r2_hidden(esk3_2(X1,esk6_0),esk6_0)|~r2_hidden(X2,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_47, c_0_50])).
% 0.19/0.43  cnf(c_0_55, plain, (X1=X3|X2!=k3_enumset1(X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_23]), c_0_18]), c_0_25]), c_0_26])).
% 0.19/0.43  cnf(c_0_56, negated_conjecture, (r2_hidden(esk3_2(X1,esk6_0),X1)|~r2_hidden(esk5_0,X1)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.19/0.43  cnf(c_0_57, negated_conjecture, (r2_hidden(esk3_2(X1,esk6_0),esk6_0)|~r2_hidden(esk5_0,X1)), inference(spm,[status(thm)],[c_0_54, c_0_53])).
% 0.19/0.43  cnf(c_0_58, plain, (X1=X2|~r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_55])).
% 0.19/0.43  cnf(c_0_59, negated_conjecture, (r2_hidden(esk3_2(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_56, c_0_53])).
% 0.19/0.43  cnf(c_0_60, negated_conjecture, (r2_hidden(esk3_2(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_57, c_0_53])).
% 0.19/0.43  cnf(c_0_61, negated_conjecture, (esk3_2(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0)=esk5_0), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.43  cnf(c_0_62, negated_conjecture, (~r2_hidden(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.43  cnf(c_0_63, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_61]), c_0_62]), ['proof']).
% 0.19/0.43  # SZS output end CNFRefutation
% 0.19/0.43  # Proof object total steps             : 64
% 0.19/0.43  # Proof object clause steps            : 39
% 0.19/0.43  # Proof object formula steps           : 25
% 0.19/0.43  # Proof object conjectures             : 20
% 0.19/0.43  # Proof object clause conjectures      : 17
% 0.19/0.43  # Proof object formula conjectures     : 3
% 0.19/0.43  # Proof object initial clauses used    : 16
% 0.19/0.43  # Proof object initial formulas used   : 12
% 0.19/0.43  # Proof object generating inferences   : 11
% 0.19/0.43  # Proof object simplifying inferences  : 39
% 0.19/0.43  # Training examples: 0 positive, 0 negative
% 0.19/0.43  # Parsed axioms                        : 17
% 0.19/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.43  # Initial clauses                      : 36
% 0.19/0.43  # Removed in clause preprocessing      : 6
% 0.19/0.43  # Initial clauses in saturation        : 30
% 0.19/0.43  # Processed clauses                    : 333
% 0.19/0.43  # ...of these trivial                  : 23
% 0.19/0.43  # ...subsumed                          : 54
% 0.19/0.43  # ...remaining for further processing  : 256
% 0.19/0.43  # Other redundant clauses eliminated   : 11
% 0.19/0.43  # Clauses deleted for lack of memory   : 0
% 0.19/0.43  # Backward-subsumed                    : 0
% 0.19/0.43  # Backward-rewritten                   : 15
% 0.19/0.43  # Generated clauses                    : 3537
% 0.19/0.43  # ...of the previous two non-trivial   : 3281
% 0.19/0.43  # Contextual simplify-reflections      : 0
% 0.19/0.43  # Paramodulations                      : 3527
% 0.19/0.43  # Factorizations                       : 0
% 0.19/0.43  # Equation resolutions                 : 11
% 0.19/0.43  # Propositional unsat checks           : 0
% 0.19/0.43  #    Propositional check models        : 0
% 0.19/0.43  #    Propositional check unsatisfiable : 0
% 0.19/0.43  #    Propositional clauses             : 0
% 0.19/0.43  #    Propositional clauses after purity: 0
% 0.19/0.43  #    Propositional unsat core size     : 0
% 0.19/0.43  #    Propositional preprocessing time  : 0.000
% 0.19/0.43  #    Propositional encoding time       : 0.000
% 0.19/0.43  #    Propositional solver time         : 0.000
% 0.19/0.43  #    Success case prop preproc time    : 0.000
% 0.19/0.43  #    Success case prop encoding time   : 0.000
% 0.19/0.43  #    Success case prop solver time     : 0.000
% 0.19/0.43  # Current number of processed clauses  : 205
% 0.19/0.43  #    Positive orientable unit clauses  : 56
% 0.19/0.43  #    Positive unorientable unit clauses: 1
% 0.19/0.43  #    Negative unit clauses             : 3
% 0.19/0.43  #    Non-unit-clauses                  : 145
% 0.19/0.43  # Current number of unprocessed clauses: 2996
% 0.19/0.43  # ...number of literals in the above   : 7667
% 0.19/0.43  # Current number of archived formulas  : 0
% 0.19/0.43  # Current number of archived clauses   : 50
% 0.19/0.43  # Clause-clause subsumption calls (NU) : 3073
% 0.19/0.43  # Rec. Clause-clause subsumption calls : 3032
% 0.19/0.43  # Non-unit clause-clause subsumptions  : 50
% 0.19/0.43  # Unit Clause-clause subsumption calls : 16
% 0.19/0.43  # Rewrite failures with RHS unbound    : 0
% 0.19/0.43  # BW rewrite match attempts            : 106
% 0.19/0.43  # BW rewrite match successes           : 32
% 0.19/0.43  # Condensation attempts                : 0
% 0.19/0.43  # Condensation successes               : 0
% 0.19/0.43  # Termbank termtop insertions          : 72051
% 0.19/0.43  
% 0.19/0.43  # -------------------------------------------------
% 0.19/0.43  # User time                : 0.083 s
% 0.19/0.43  # System time              : 0.005 s
% 0.19/0.43  # Total time               : 0.088 s
% 0.19/0.43  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
