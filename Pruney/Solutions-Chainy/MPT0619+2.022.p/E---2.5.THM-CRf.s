%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:53 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 210 expanded)
%              Number of clauses        :   38 (  89 expanded)
%              Number of leaves         :    9 (  53 expanded)
%              Depth                    :   11
%              Number of atoms          :  188 ( 577 expanded)
%              Number of equality atoms :   99 ( 335 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t14_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( k1_relat_1(X2) = k1_tarski(X1)
       => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(d16_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(d5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( X2 = k2_relat_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                  & X3 = k1_funct_1(X1,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(t41_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_tarski(X2)
        & X1 != k1_xboole_0
        & ! [X3] :
            ~ ( r2_hidden(X3,X1)
              & X3 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(t205_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k1_relat_1(X2))
      <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( k1_relat_1(X2) = k1_tarski(X1)
         => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t14_funct_1])).

fof(c_0_10,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X20)
      | k11_relat_1(X20,X21) = k9_relat_1(X20,k1_tarski(X21)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).

fof(c_0_11,plain,(
    ! [X14] : k2_tarski(X14,X14) = k1_tarski(X14) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_12,plain,(
    ! [X15,X16] : k1_enumset1(X15,X15,X16) = k2_tarski(X15,X16) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & v1_funct_1(esk7_0)
    & k1_relat_1(esk7_0) = k1_tarski(esk6_0)
    & k2_relat_1(esk7_0) != k1_tarski(k1_funct_1(esk7_0,esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_14,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X8,X7)
        | X8 = X5
        | X8 = X6
        | X7 != k2_tarski(X5,X6) )
      & ( X9 != X5
        | r2_hidden(X9,X7)
        | X7 != k2_tarski(X5,X6) )
      & ( X9 != X6
        | r2_hidden(X9,X7)
        | X7 != k2_tarski(X5,X6) )
      & ( esk1_3(X10,X11,X12) != X10
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_tarski(X10,X11) )
      & ( esk1_3(X10,X11,X12) != X11
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_tarski(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X12)
        | esk1_3(X10,X11,X12) = X10
        | esk1_3(X10,X11,X12) = X11
        | X12 = k2_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_15,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( k1_relat_1(esk7_0) = k1_tarski(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_20,plain,(
    ! [X22] :
      ( ~ v1_relat_1(X22)
      | k9_relat_1(X22,k1_relat_1(X22)) = k2_relat_1(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

cnf(c_0_21,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_enumset1(X2,X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( k1_relat_1(esk7_0) = k1_enumset1(esk6_0,esk6_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_16]),c_0_17])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k1_enumset1(X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_17])).

fof(c_0_25,plain,(
    ! [X25,X26,X27,X29,X30,X31,X33] :
      ( ( r2_hidden(esk3_3(X25,X26,X27),k1_relat_1(X25))
        | ~ r2_hidden(X27,X26)
        | X26 != k2_relat_1(X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( X27 = k1_funct_1(X25,esk3_3(X25,X26,X27))
        | ~ r2_hidden(X27,X26)
        | X26 != k2_relat_1(X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( ~ r2_hidden(X30,k1_relat_1(X25))
        | X29 != k1_funct_1(X25,X30)
        | r2_hidden(X29,X26)
        | X26 != k2_relat_1(X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( ~ r2_hidden(esk4_2(X25,X31),X31)
        | ~ r2_hidden(X33,k1_relat_1(X25))
        | esk4_2(X25,X31) != k1_funct_1(X25,X33)
        | X31 = k2_relat_1(X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( r2_hidden(esk5_2(X25,X31),k1_relat_1(X25))
        | r2_hidden(esk4_2(X25,X31),X31)
        | X31 = k2_relat_1(X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( esk4_2(X25,X31) = k1_funct_1(X25,esk5_2(X25,X31))
        | r2_hidden(esk4_2(X25,X31),X31)
        | X31 = k2_relat_1(X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_26,plain,(
    ! [X17,X18] :
      ( ( r2_hidden(esk2_2(X17,X18),X17)
        | X17 = k1_tarski(X18)
        | X17 = k1_xboole_0 )
      & ( esk2_2(X17,X18) != X18
        | X17 = k1_tarski(X18)
        | X17 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_zfmisc_1])])])])).

fof(c_0_27,plain,(
    ! [X23,X24] :
      ( ( ~ r2_hidden(X23,k1_relat_1(X24))
        | k11_relat_1(X24,X23) != k1_xboole_0
        | ~ v1_relat_1(X24) )
      & ( k11_relat_1(X24,X23) = k1_xboole_0
        | r2_hidden(X23,k1_relat_1(X24))
        | ~ v1_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t205_relat_1])])])).

cnf(c_0_28,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( k9_relat_1(X1,k1_relat_1(esk7_0)) = k11_relat_1(X1,esk6_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X4,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_17])).

cnf(c_0_32,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k1_enumset1(X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( k2_relat_1(esk7_0) != k1_tarski(k1_funct_1(esk7_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_35,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | X1 = k1_tarski(X2)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,k1_relat_1(X2))
    | k11_relat_1(X2,X1) != k1_xboole_0
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( k11_relat_1(esk7_0,esk6_0) = k2_relat_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_31])])).

cnf(c_0_39,plain,
    ( X1 = k1_funct_1(X2,esk3_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_40,negated_conjecture,
    ( X1 = esk6_0
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_22])).

cnf(c_0_41,plain,
    ( r2_hidden(esk3_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_43,negated_conjecture,
    ( k2_relat_1(esk7_0) != k1_enumset1(k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_16]),c_0_17])).

cnf(c_0_44,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_enumset1(X2,X2,X2)
    | r2_hidden(esk2_2(X1,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_16]),c_0_17])).

cnf(c_0_45,negated_conjecture,
    ( k2_relat_1(esk7_0) != k1_xboole_0
    | ~ r2_hidden(esk6_0,k1_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_30])])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk6_0,k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_22])).

cnf(c_0_47,plain,
    ( k1_funct_1(X1,esk3_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( esk3_3(esk7_0,k2_relat_1(esk7_0),X1) = esk6_0
    | ~ r2_hidden(X1,k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_30])])).

cnf(c_0_49,negated_conjecture,
    ( k2_relat_1(esk7_0) = k1_xboole_0
    | r2_hidden(esk2_2(k2_relat_1(esk7_0),k1_funct_1(esk7_0,esk6_0)),k2_relat_1(esk7_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44])])).

cnf(c_0_50,negated_conjecture,
    ( k2_relat_1(esk7_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46])])).

cnf(c_0_51,plain,
    ( X1 = k1_tarski(X2)
    | X1 = k1_xboole_0
    | esk2_2(X1,X2) != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_52,negated_conjecture,
    ( k1_funct_1(esk7_0,esk6_0) = X1
    | ~ r2_hidden(X1,k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_42]),c_0_30])])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk2_2(k2_relat_1(esk7_0),k1_funct_1(esk7_0,esk6_0)),k2_relat_1(esk7_0)) ),
    inference(sr,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_54,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_enumset1(X2,X2,X2)
    | esk2_2(X1,X2) != X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_16]),c_0_17])).

cnf(c_0_55,negated_conjecture,
    ( esk2_2(k2_relat_1(esk7_0),k1_funct_1(esk7_0,esk6_0)) = k1_funct_1(esk7_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_43]),c_0_50]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:53:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.20/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.028 s
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t14_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 0.20/0.38  fof(d16_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 0.20/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.38  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.20/0.38  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 0.20/0.38  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 0.20/0.38  fof(t41_zfmisc_1, axiom, ![X1, X2]:~(((X1!=k1_tarski(X2)&X1!=k1_xboole_0)&![X3]:~((r2_hidden(X3,X1)&X3!=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 0.20/0.38  fof(t205_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 0.20/0.38  fof(c_0_9, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1))))), inference(assume_negation,[status(cth)],[t14_funct_1])).
% 0.20/0.38  fof(c_0_10, plain, ![X20, X21]:(~v1_relat_1(X20)|k11_relat_1(X20,X21)=k9_relat_1(X20,k1_tarski(X21))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).
% 0.20/0.38  fof(c_0_11, plain, ![X14]:k2_tarski(X14,X14)=k1_tarski(X14), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.38  fof(c_0_12, plain, ![X15, X16]:k1_enumset1(X15,X15,X16)=k2_tarski(X15,X16), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.38  fof(c_0_13, negated_conjecture, ((v1_relat_1(esk7_0)&v1_funct_1(esk7_0))&(k1_relat_1(esk7_0)=k1_tarski(esk6_0)&k2_relat_1(esk7_0)!=k1_tarski(k1_funct_1(esk7_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.20/0.38  fof(c_0_14, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:(((~r2_hidden(X8,X7)|(X8=X5|X8=X6)|X7!=k2_tarski(X5,X6))&((X9!=X5|r2_hidden(X9,X7)|X7!=k2_tarski(X5,X6))&(X9!=X6|r2_hidden(X9,X7)|X7!=k2_tarski(X5,X6))))&(((esk1_3(X10,X11,X12)!=X10|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_tarski(X10,X11))&(esk1_3(X10,X11,X12)!=X11|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_tarski(X10,X11)))&(r2_hidden(esk1_3(X10,X11,X12),X12)|(esk1_3(X10,X11,X12)=X10|esk1_3(X10,X11,X12)=X11)|X12=k2_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.20/0.38  cnf(c_0_15, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_16, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  cnf(c_0_17, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_18, negated_conjecture, (k1_relat_1(esk7_0)=k1_tarski(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_19, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  fof(c_0_20, plain, ![X22]:(~v1_relat_1(X22)|k9_relat_1(X22,k1_relat_1(X22))=k2_relat_1(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.20/0.38  cnf(c_0_21, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k1_enumset1(X2,X2,X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_17])).
% 0.20/0.38  cnf(c_0_22, negated_conjecture, (k1_relat_1(esk7_0)=k1_enumset1(esk6_0,esk6_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_16]), c_0_17])).
% 0.20/0.38  cnf(c_0_23, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  cnf(c_0_24, plain, (X1=X4|X1=X3|X2!=k1_enumset1(X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_19, c_0_17])).
% 0.20/0.38  fof(c_0_25, plain, ![X25, X26, X27, X29, X30, X31, X33]:((((r2_hidden(esk3_3(X25,X26,X27),k1_relat_1(X25))|~r2_hidden(X27,X26)|X26!=k2_relat_1(X25)|(~v1_relat_1(X25)|~v1_funct_1(X25)))&(X27=k1_funct_1(X25,esk3_3(X25,X26,X27))|~r2_hidden(X27,X26)|X26!=k2_relat_1(X25)|(~v1_relat_1(X25)|~v1_funct_1(X25))))&(~r2_hidden(X30,k1_relat_1(X25))|X29!=k1_funct_1(X25,X30)|r2_hidden(X29,X26)|X26!=k2_relat_1(X25)|(~v1_relat_1(X25)|~v1_funct_1(X25))))&((~r2_hidden(esk4_2(X25,X31),X31)|(~r2_hidden(X33,k1_relat_1(X25))|esk4_2(X25,X31)!=k1_funct_1(X25,X33))|X31=k2_relat_1(X25)|(~v1_relat_1(X25)|~v1_funct_1(X25)))&((r2_hidden(esk5_2(X25,X31),k1_relat_1(X25))|r2_hidden(esk4_2(X25,X31),X31)|X31=k2_relat_1(X25)|(~v1_relat_1(X25)|~v1_funct_1(X25)))&(esk4_2(X25,X31)=k1_funct_1(X25,esk5_2(X25,X31))|r2_hidden(esk4_2(X25,X31),X31)|X31=k2_relat_1(X25)|(~v1_relat_1(X25)|~v1_funct_1(X25)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.20/0.38  fof(c_0_26, plain, ![X17, X18]:((r2_hidden(esk2_2(X17,X18),X17)|(X17=k1_tarski(X18)|X17=k1_xboole_0))&(esk2_2(X17,X18)!=X18|(X17=k1_tarski(X18)|X17=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_zfmisc_1])])])])).
% 0.20/0.38  fof(c_0_27, plain, ![X23, X24]:((~r2_hidden(X23,k1_relat_1(X24))|k11_relat_1(X24,X23)!=k1_xboole_0|~v1_relat_1(X24))&(k11_relat_1(X24,X23)=k1_xboole_0|r2_hidden(X23,k1_relat_1(X24))|~v1_relat_1(X24))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t205_relat_1])])])).
% 0.20/0.38  cnf(c_0_28, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.38  cnf(c_0_29, negated_conjecture, (k9_relat_1(X1,k1_relat_1(esk7_0))=k11_relat_1(X1,esk6_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.38  cnf(c_0_30, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_31, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X4,X2)), inference(rw,[status(thm)],[c_0_23, c_0_17])).
% 0.20/0.38  cnf(c_0_32, plain, (X1=X2|X1=X3|~r2_hidden(X1,k1_enumset1(X3,X3,X2))), inference(er,[status(thm)],[c_0_24])).
% 0.20/0.38  cnf(c_0_33, plain, (r2_hidden(esk3_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.38  cnf(c_0_34, negated_conjecture, (k2_relat_1(esk7_0)!=k1_tarski(k1_funct_1(esk7_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_35, plain, (r2_hidden(esk2_2(X1,X2),X1)|X1=k1_tarski(X2)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.38  cnf(c_0_36, plain, (~r2_hidden(X1,k1_relat_1(X2))|k11_relat_1(X2,X1)!=k1_xboole_0|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.38  cnf(c_0_37, negated_conjecture, (k11_relat_1(esk7_0,esk6_0)=k2_relat_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])])).
% 0.20/0.38  cnf(c_0_38, plain, (r2_hidden(X1,k1_enumset1(X2,X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_31])])).
% 0.20/0.38  cnf(c_0_39, plain, (X1=k1_funct_1(X2,esk3_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.38  cnf(c_0_40, negated_conjecture, (X1=esk6_0|~r2_hidden(X1,k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_32, c_0_22])).
% 0.20/0.38  cnf(c_0_41, plain, (r2_hidden(esk3_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_33])).
% 0.20/0.38  cnf(c_0_42, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_43, negated_conjecture, (k2_relat_1(esk7_0)!=k1_enumset1(k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_16]), c_0_17])).
% 0.20/0.38  cnf(c_0_44, plain, (X1=k1_xboole_0|X1=k1_enumset1(X2,X2,X2)|r2_hidden(esk2_2(X1,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_16]), c_0_17])).
% 0.20/0.38  cnf(c_0_45, negated_conjecture, (k2_relat_1(esk7_0)!=k1_xboole_0|~r2_hidden(esk6_0,k1_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_30])])).
% 0.20/0.38  cnf(c_0_46, negated_conjecture, (r2_hidden(esk6_0,k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_38, c_0_22])).
% 0.20/0.38  cnf(c_0_47, plain, (k1_funct_1(X1,esk3_3(X1,k2_relat_1(X1),X2))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_39])).
% 0.20/0.38  cnf(c_0_48, negated_conjecture, (esk3_3(esk7_0,k2_relat_1(esk7_0),X1)=esk6_0|~r2_hidden(X1,k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42]), c_0_30])])).
% 0.20/0.38  cnf(c_0_49, negated_conjecture, (k2_relat_1(esk7_0)=k1_xboole_0|r2_hidden(esk2_2(k2_relat_1(esk7_0),k1_funct_1(esk7_0,esk6_0)),k2_relat_1(esk7_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44])])).
% 0.20/0.38  cnf(c_0_50, negated_conjecture, (k2_relat_1(esk7_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46])])).
% 0.20/0.38  cnf(c_0_51, plain, (X1=k1_tarski(X2)|X1=k1_xboole_0|esk2_2(X1,X2)!=X2), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.38  cnf(c_0_52, negated_conjecture, (k1_funct_1(esk7_0,esk6_0)=X1|~r2_hidden(X1,k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_42]), c_0_30])])).
% 0.20/0.38  cnf(c_0_53, negated_conjecture, (r2_hidden(esk2_2(k2_relat_1(esk7_0),k1_funct_1(esk7_0,esk6_0)),k2_relat_1(esk7_0))), inference(sr,[status(thm)],[c_0_49, c_0_50])).
% 0.20/0.38  cnf(c_0_54, plain, (X1=k1_xboole_0|X1=k1_enumset1(X2,X2,X2)|esk2_2(X1,X2)!=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_16]), c_0_17])).
% 0.20/0.38  cnf(c_0_55, negated_conjecture, (esk2_2(k2_relat_1(esk7_0),k1_funct_1(esk7_0,esk6_0))=k1_funct_1(esk7_0,esk6_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.38  cnf(c_0_56, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_43]), c_0_50]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 57
% 0.20/0.38  # Proof object clause steps            : 38
% 0.20/0.38  # Proof object formula steps           : 19
% 0.20/0.38  # Proof object conjectures             : 21
% 0.20/0.38  # Proof object clause conjectures      : 18
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 15
% 0.20/0.38  # Proof object initial formulas used   : 9
% 0.20/0.38  # Proof object generating inferences   : 10
% 0.20/0.38  # Proof object simplifying inferences  : 33
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 9
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 24
% 0.20/0.38  # Removed in clause preprocessing      : 2
% 0.20/0.38  # Initial clauses in saturation        : 22
% 0.20/0.38  # Processed clauses                    : 69
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 10
% 0.20/0.38  # ...remaining for further processing  : 59
% 0.20/0.38  # Other redundant clauses eliminated   : 21
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 1
% 0.20/0.38  # Backward-rewritten                   : 2
% 0.20/0.38  # Generated clauses                    : 312
% 0.20/0.38  # ...of the previous two non-trivial   : 245
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 282
% 0.20/0.38  # Factorizations                       : 11
% 0.20/0.38  # Equation resolutions                 : 21
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
% 0.20/0.38  # Current number of processed clauses  : 49
% 0.20/0.38  #    Positive orientable unit clauses  : 8
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 2
% 0.20/0.38  #    Non-unit-clauses                  : 39
% 0.20/0.38  # Current number of unprocessed clauses: 197
% 0.20/0.38  # ...number of literals in the above   : 1126
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 6
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 320
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 131
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 10
% 0.20/0.38  # Unit Clause-clause subsumption calls : 16
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 4
% 0.20/0.38  # BW rewrite match successes           : 2
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 6100
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.037 s
% 0.20/0.38  # System time              : 0.004 s
% 0.20/0.38  # Total time               : 0.042 s
% 0.20/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
