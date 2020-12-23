%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:28 EST 2020

% Result     : Theorem 0.48s
% Output     : CNFRefutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 172 expanded)
%              Number of clauses        :   30 (  75 expanded)
%              Number of leaves         :    8 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :   90 ( 259 expanded)
%              Number of equality atoms :   17 ( 138 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t143_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
        & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
     => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t120_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(c_0_8,plain,(
    ! [X24,X25,X26] :
      ( ~ r1_tarski(X24,X25)
      | r1_tarski(X24,k2_xboole_0(X26,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

fof(c_0_9,plain,(
    ! [X35,X36] : k3_tarski(k2_tarski(X35,X36)) = k2_xboole_0(X35,X36) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_10,plain,(
    ! [X30,X31] : r1_tarski(X30,k2_xboole_0(X30,X31)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
          & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
       => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    inference(assume_negation,[status(cth)],[t143_zfmisc_1])).

fof(c_0_12,plain,(
    ! [X27,X28,X29] :
      ( ~ r1_tarski(X27,X28)
      | ~ r1_tarski(X28,X29)
      | r1_tarski(X27,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,negated_conjecture,
    ( r1_tarski(esk3_0,k2_zfmisc_1(esk5_0,esk6_0))
    & r1_tarski(esk4_0,k2_zfmisc_1(esk7_0,esk8_0))
    & ~ r1_tarski(k2_xboole_0(esk3_0,esk4_0),k2_zfmisc_1(k2_xboole_0(esk5_0,esk7_0),k2_xboole_0(esk6_0,esk8_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_17,plain,(
    ! [X37,X38,X39] :
      ( k2_zfmisc_1(k2_xboole_0(X37,X38),X39) = k2_xboole_0(k2_zfmisc_1(X37,X39),k2_zfmisc_1(X38,X39))
      & k2_zfmisc_1(X39,k2_xboole_0(X37,X38)) = k2_xboole_0(k2_zfmisc_1(X39,X37),k2_zfmisc_1(X39,X38)) ) ),
    inference(variable_rename,[status(thm)],[t120_zfmisc_1])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_15,c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(esk3_0,esk4_0),k2_zfmisc_1(k2_xboole_0(esk5_0,esk7_0),k2_xboole_0(esk6_0,esk8_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k2_zfmisc_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_tarski(X1,X4)
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(esk4_0,k2_zfmisc_1(esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_26,plain,(
    ! [X22,X23] :
      ( ( r1_tarski(X22,X23)
        | X22 != X23 )
      & ( r1_tarski(X23,X22)
        | X22 != X23 )
      & ( ~ r1_tarski(X22,X23)
        | ~ r1_tarski(X23,X22)
        | X22 = X23 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k2_tarski(esk3_0,esk4_0)),k2_zfmisc_1(k3_tarski(k2_tarski(esk5_0,esk7_0)),k3_tarski(k2_tarski(esk6_0,esk8_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_14]),c_0_14]),c_0_14])).

cnf(c_0_29,plain,
    ( k2_zfmisc_1(k3_tarski(k2_tarski(X1,X2)),X3) = k3_tarski(k2_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_14]),c_0_14])).

cnf(c_0_30,plain,
    ( k2_zfmisc_1(X1,k3_tarski(k2_tarski(X2,X3))) = k3_tarski(k2_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_14]),c_0_14])).

fof(c_0_31,plain,(
    ! [X32,X33,X34] :
      ( ~ r1_tarski(X32,X33)
      | ~ r1_tarski(X34,X33)
      | r1_tarski(k2_xboole_0(X32,X34),X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(esk4_0,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_tarski(k2_zfmisc_1(esk7_0,esk8_0),X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_tarski(X1,X4)
    | ~ r1_tarski(X4,X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(esk3_0,k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_36,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k2_tarski(esk3_0,esk4_0)),k3_tarski(k2_tarski(k3_tarski(k2_tarski(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(esk5_0,esk8_0))),k3_tarski(k2_tarski(k2_zfmisc_1(esk7_0,esk6_0),k2_zfmisc_1(esk7_0,esk8_0)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_30])).

cnf(c_0_37,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))),k3_tarski(k2_tarski(k2_zfmisc_1(X4,X2),k2_zfmisc_1(X4,X3))))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X4,X2))),k3_tarski(k2_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X4,X3))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_29]),c_0_30]),c_0_30]),c_0_29]),c_0_29])).

cnf(c_0_38,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(esk4_0,k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X2,X3)))))
    | ~ r1_tarski(k2_zfmisc_1(esk7_0,esk8_0),X3) ),
    inference(spm,[status(thm)],[c_0_32,c_0_19])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(esk3_0,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_tarski(k2_zfmisc_1(esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k2_tarski(esk3_0,esk4_0)),k3_tarski(k2_tarski(k3_tarski(k2_tarski(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(esk7_0,esk6_0))),k3_tarski(k2_tarski(k2_zfmisc_1(esk5_0,esk8_0),k2_zfmisc_1(esk7_0,esk8_0)))))) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,plain,
    ( r1_tarski(k3_tarski(k2_tarski(X1,X3)),X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_38,c_0_14])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(esk4_0,k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X2,k2_zfmisc_1(esk7_0,esk8_0)))))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(esk3_0,k3_tarski(k2_tarski(k3_tarski(k2_tarski(k2_zfmisc_1(esk5_0,esk6_0),X1)),X2))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_20])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_45])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:29:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.48/0.64  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0YI
% 0.48/0.64  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.48/0.64  #
% 0.48/0.64  # Preprocessing time       : 0.028 s
% 0.48/0.64  # Presaturation interreduction done
% 0.48/0.64  
% 0.48/0.64  # Proof found!
% 0.48/0.64  # SZS status Theorem
% 0.48/0.64  # SZS output start CNFRefutation
% 0.48/0.64  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 0.48/0.64  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.48/0.64  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.48/0.64  fof(t143_zfmisc_1, conjecture, ![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 0.48/0.64  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.48/0.64  fof(t120_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 0.48/0.64  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.48/0.64  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 0.48/0.64  fof(c_0_8, plain, ![X24, X25, X26]:(~r1_tarski(X24,X25)|r1_tarski(X24,k2_xboole_0(X26,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 0.48/0.64  fof(c_0_9, plain, ![X35, X36]:k3_tarski(k2_tarski(X35,X36))=k2_xboole_0(X35,X36), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.48/0.64  fof(c_0_10, plain, ![X30, X31]:r1_tarski(X30,k2_xboole_0(X30,X31)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.48/0.64  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))))), inference(assume_negation,[status(cth)],[t143_zfmisc_1])).
% 0.48/0.64  fof(c_0_12, plain, ![X27, X28, X29]:(~r1_tarski(X27,X28)|~r1_tarski(X28,X29)|r1_tarski(X27,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.48/0.64  cnf(c_0_13, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.48/0.64  cnf(c_0_14, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.48/0.64  cnf(c_0_15, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.48/0.64  fof(c_0_16, negated_conjecture, ((r1_tarski(esk3_0,k2_zfmisc_1(esk5_0,esk6_0))&r1_tarski(esk4_0,k2_zfmisc_1(esk7_0,esk8_0)))&~r1_tarski(k2_xboole_0(esk3_0,esk4_0),k2_zfmisc_1(k2_xboole_0(esk5_0,esk7_0),k2_xboole_0(esk6_0,esk8_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.48/0.64  fof(c_0_17, plain, ![X37, X38, X39]:(k2_zfmisc_1(k2_xboole_0(X37,X38),X39)=k2_xboole_0(k2_zfmisc_1(X37,X39),k2_zfmisc_1(X38,X39))&k2_zfmisc_1(X39,k2_xboole_0(X37,X38))=k2_xboole_0(k2_zfmisc_1(X39,X37),k2_zfmisc_1(X39,X38))), inference(variable_rename,[status(thm)],[t120_zfmisc_1])).
% 0.48/0.64  cnf(c_0_18, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.48/0.64  cnf(c_0_19, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.48/0.64  cnf(c_0_20, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_15, c_0_14])).
% 0.48/0.64  cnf(c_0_21, negated_conjecture, (~r1_tarski(k2_xboole_0(esk3_0,esk4_0),k2_zfmisc_1(k2_xboole_0(esk5_0,esk7_0),k2_xboole_0(esk6_0,esk8_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.48/0.64  cnf(c_0_22, plain, (k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.48/0.64  cnf(c_0_23, plain, (k2_zfmisc_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.48/0.64  cnf(c_0_24, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))|~r1_tarski(X1,X4)|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.48/0.64  cnf(c_0_25, negated_conjecture, (r1_tarski(esk4_0,k2_zfmisc_1(esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.48/0.64  fof(c_0_26, plain, ![X22, X23]:(((r1_tarski(X22,X23)|X22!=X23)&(r1_tarski(X23,X22)|X22!=X23))&(~r1_tarski(X22,X23)|~r1_tarski(X23,X22)|X22=X23)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.48/0.64  cnf(c_0_27, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_18, c_0_20])).
% 0.48/0.64  cnf(c_0_28, negated_conjecture, (~r1_tarski(k3_tarski(k2_tarski(esk3_0,esk4_0)),k2_zfmisc_1(k3_tarski(k2_tarski(esk5_0,esk7_0)),k3_tarski(k2_tarski(esk6_0,esk8_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_14]), c_0_14]), c_0_14])).
% 0.48/0.64  cnf(c_0_29, plain, (k2_zfmisc_1(k3_tarski(k2_tarski(X1,X2)),X3)=k3_tarski(k2_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_14]), c_0_14])).
% 0.48/0.64  cnf(c_0_30, plain, (k2_zfmisc_1(X1,k3_tarski(k2_tarski(X2,X3)))=k3_tarski(k2_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_14]), c_0_14])).
% 0.48/0.64  fof(c_0_31, plain, ![X32, X33, X34]:(~r1_tarski(X32,X33)|~r1_tarski(X34,X33)|r1_tarski(k2_xboole_0(X32,X34),X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 0.48/0.64  cnf(c_0_32, negated_conjecture, (r1_tarski(esk4_0,k3_tarski(k2_tarski(X1,X2)))|~r1_tarski(k2_zfmisc_1(esk7_0,esk8_0),X2)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.48/0.64  cnf(c_0_33, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.48/0.64  cnf(c_0_34, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))|~r1_tarski(X1,X4)|~r1_tarski(X4,X2)), inference(spm,[status(thm)],[c_0_18, c_0_27])).
% 0.48/0.64  cnf(c_0_35, negated_conjecture, (r1_tarski(esk3_0,k2_zfmisc_1(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.48/0.64  cnf(c_0_36, negated_conjecture, (~r1_tarski(k3_tarski(k2_tarski(esk3_0,esk4_0)),k3_tarski(k2_tarski(k3_tarski(k2_tarski(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(esk5_0,esk8_0))),k3_tarski(k2_tarski(k2_zfmisc_1(esk7_0,esk6_0),k2_zfmisc_1(esk7_0,esk8_0))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_30])).
% 0.48/0.64  cnf(c_0_37, plain, (k3_tarski(k2_tarski(k3_tarski(k2_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))),k3_tarski(k2_tarski(k2_zfmisc_1(X4,X2),k2_zfmisc_1(X4,X3)))))=k3_tarski(k2_tarski(k3_tarski(k2_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X4,X2))),k3_tarski(k2_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X4,X3)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_29]), c_0_30]), c_0_30]), c_0_29]), c_0_29])).
% 0.48/0.64  cnf(c_0_38, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.48/0.64  cnf(c_0_39, negated_conjecture, (r1_tarski(esk4_0,k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X2,X3)))))|~r1_tarski(k2_zfmisc_1(esk7_0,esk8_0),X3)), inference(spm,[status(thm)],[c_0_32, c_0_19])).
% 0.48/0.64  cnf(c_0_40, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_33])).
% 0.48/0.64  cnf(c_0_41, negated_conjecture, (r1_tarski(esk3_0,k3_tarski(k2_tarski(X1,X2)))|~r1_tarski(k2_zfmisc_1(esk5_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.48/0.64  cnf(c_0_42, negated_conjecture, (~r1_tarski(k3_tarski(k2_tarski(esk3_0,esk4_0)),k3_tarski(k2_tarski(k3_tarski(k2_tarski(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(esk7_0,esk6_0))),k3_tarski(k2_tarski(k2_zfmisc_1(esk5_0,esk8_0),k2_zfmisc_1(esk7_0,esk8_0))))))), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.48/0.64  cnf(c_0_43, plain, (r1_tarski(k3_tarski(k2_tarski(X1,X3)),X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_38, c_0_14])).
% 0.48/0.64  cnf(c_0_44, negated_conjecture, (r1_tarski(esk4_0,k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X2,k2_zfmisc_1(esk7_0,esk8_0))))))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.48/0.64  cnf(c_0_45, negated_conjecture, (r1_tarski(esk3_0,k3_tarski(k2_tarski(k3_tarski(k2_tarski(k2_zfmisc_1(esk5_0,esk6_0),X1)),X2)))), inference(spm,[status(thm)],[c_0_41, c_0_20])).
% 0.48/0.64  cnf(c_0_46, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_45])]), ['proof']).
% 0.48/0.64  # SZS output end CNFRefutation
% 0.48/0.64  # Proof object total steps             : 47
% 0.48/0.64  # Proof object clause steps            : 30
% 0.48/0.64  # Proof object formula steps           : 17
% 0.48/0.64  # Proof object conjectures             : 15
% 0.48/0.64  # Proof object clause conjectures      : 12
% 0.48/0.64  # Proof object formula conjectures     : 3
% 0.48/0.64  # Proof object initial clauses used    : 11
% 0.48/0.64  # Proof object initial formulas used   : 8
% 0.48/0.64  # Proof object generating inferences   : 10
% 0.48/0.64  # Proof object simplifying inferences  : 22
% 0.48/0.64  # Training examples: 0 positive, 0 negative
% 0.48/0.64  # Parsed axioms                        : 10
% 0.48/0.64  # Removed by relevancy pruning/SinE    : 0
% 0.48/0.64  # Initial clauses                      : 22
% 0.48/0.64  # Removed in clause preprocessing      : 1
% 0.48/0.64  # Initial clauses in saturation        : 21
% 0.48/0.64  # Processed clauses                    : 2475
% 0.48/0.64  # ...of these trivial                  : 53
% 0.48/0.64  # ...subsumed                          : 1515
% 0.48/0.64  # ...remaining for further processing  : 906
% 0.48/0.64  # Other redundant clauses eliminated   : 5
% 0.48/0.64  # Clauses deleted for lack of memory   : 0
% 0.48/0.64  # Backward-subsumed                    : 2
% 0.48/0.64  # Backward-rewritten                   : 54
% 0.48/0.64  # Generated clauses                    : 20232
% 0.48/0.64  # ...of the previous two non-trivial   : 17815
% 0.48/0.64  # Contextual simplify-reflections      : 0
% 0.48/0.64  # Paramodulations                      : 20120
% 0.48/0.64  # Factorizations                       : 68
% 0.48/0.64  # Equation resolutions                 : 5
% 0.48/0.64  # Propositional unsat checks           : 0
% 0.48/0.64  #    Propositional check models        : 0
% 0.48/0.64  #    Propositional check unsatisfiable : 0
% 0.48/0.64  #    Propositional clauses             : 0
% 0.48/0.64  #    Propositional clauses after purity: 0
% 0.48/0.64  #    Propositional unsat core size     : 0
% 0.48/0.64  #    Propositional preprocessing time  : 0.000
% 0.48/0.64  #    Propositional encoding time       : 0.000
% 0.48/0.64  #    Propositional solver time         : 0.000
% 0.48/0.64  #    Success case prop preproc time    : 0.000
% 0.48/0.64  #    Success case prop encoding time   : 0.000
% 0.48/0.64  #    Success case prop solver time     : 0.000
% 0.48/0.64  # Current number of processed clauses  : 812
% 0.48/0.64  #    Positive orientable unit clauses  : 126
% 0.48/0.64  #    Positive unorientable unit clauses: 7
% 0.48/0.64  #    Negative unit clauses             : 202
% 0.48/0.64  #    Non-unit-clauses                  : 477
% 0.48/0.64  # Current number of unprocessed clauses: 15219
% 0.48/0.64  # ...number of literals in the above   : 40974
% 0.48/0.64  # Current number of archived formulas  : 0
% 0.48/0.64  # Current number of archived clauses   : 77
% 0.48/0.64  # Clause-clause subsumption calls (NU) : 24024
% 0.48/0.64  # Rec. Clause-clause subsumption calls : 20323
% 0.48/0.64  # Non-unit clause-clause subsumptions  : 696
% 0.48/0.64  # Unit Clause-clause subsumption calls : 14986
% 0.48/0.64  # Rewrite failures with RHS unbound    : 0
% 0.48/0.64  # BW rewrite match attempts            : 953
% 0.48/0.64  # BW rewrite match successes           : 36
% 0.48/0.64  # Condensation attempts                : 0
% 0.48/0.64  # Condensation successes               : 0
% 0.48/0.64  # Termbank termtop insertions          : 406822
% 0.48/0.64  
% 0.48/0.64  # -------------------------------------------------
% 0.48/0.64  # User time                : 0.286 s
% 0.48/0.64  # System time              : 0.014 s
% 0.48/0.64  # Total time               : 0.300 s
% 0.48/0.64  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
