%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:33 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 161 expanded)
%              Number of clauses        :   34 (  79 expanded)
%              Number of leaves         :    6 (  38 expanded)
%              Depth                    :   13
%              Number of atoms          :  147 ( 582 expanded)
%              Number of equality atoms :   32 ( 166 expanded)
%              Maximal formula depth    :   15 (   4 average)
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

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

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

fof(t173_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k10_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(c_0_6,plain,(
    ! [X16,X17] :
      ( ( k2_zfmisc_1(X16,X17) != k1_xboole_0
        | X16 = k1_xboole_0
        | X17 = k1_xboole_0 )
      & ( X16 != k1_xboole_0
        | k2_zfmisc_1(X16,X17) = k1_xboole_0 )
      & ( X17 != k1_xboole_0
        | k2_zfmisc_1(X16,X17) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_7,plain,(
    ! [X18,X19] : ~ r2_hidden(X18,k2_zfmisc_1(X18,X19)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_8,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_8])).

fof(c_0_11,plain,(
    ! [X20,X21,X22,X24,X25,X26,X27,X29] :
      ( ( ~ r2_hidden(X22,X21)
        | r2_hidden(k4_tarski(esk2_3(X20,X21,X22),X22),X20)
        | X21 != k2_relat_1(X20) )
      & ( ~ r2_hidden(k4_tarski(X25,X24),X20)
        | r2_hidden(X24,X21)
        | X21 != k2_relat_1(X20) )
      & ( ~ r2_hidden(esk3_2(X26,X27),X27)
        | ~ r2_hidden(k4_tarski(X29,esk3_2(X26,X27)),X26)
        | X27 = k2_relat_1(X26) )
      & ( r2_hidden(esk3_2(X26,X27),X27)
        | r2_hidden(k4_tarski(esk4_2(X26,X27),esk3_2(X26,X27)),X26)
        | X27 = k2_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

fof(c_0_12,plain,(
    ! [X5,X6,X8,X9,X10] :
      ( ( r2_hidden(esk1_2(X5,X6),X5)
        | r1_xboole_0(X5,X6) )
      & ( r2_hidden(esk1_2(X5,X6),X6)
        | r1_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | ~ r1_xboole_0(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_13,plain,(
    ! [X31,X32,X33,X35] :
      ( ( r2_hidden(esk5_3(X31,X32,X33),k2_relat_1(X33))
        | ~ r2_hidden(X31,k10_relat_1(X33,X32))
        | ~ v1_relat_1(X33) )
      & ( r2_hidden(k4_tarski(X31,esk5_3(X31,X32,X33)),X33)
        | ~ r2_hidden(X31,k10_relat_1(X33,X32))
        | ~ v1_relat_1(X33) )
      & ( r2_hidden(esk5_3(X31,X32,X33),X32)
        | ~ r2_hidden(X31,k10_relat_1(X33,X32))
        | ~ v1_relat_1(X33) )
      & ( ~ r2_hidden(X35,k2_relat_1(X33))
        | ~ r2_hidden(k4_tarski(X31,X35),X33)
        | ~ r2_hidden(X35,X32)
        | r2_hidden(X31,k10_relat_1(X33,X32))
        | ~ v1_relat_1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

cnf(c_0_14,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk4_2(X1,X2),esk3_2(X1,X2)),X1)
    | X2 = k2_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( X1 = k2_relat_1(k1_xboole_0)
    | r2_hidden(esk3_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(esk5_3(X2,X3,X1),X4)
    | ~ r2_hidden(X2,k10_relat_1(X1,X3))
    | ~ r1_xboole_0(X4,X3) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),k2_relat_1(X3))
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_14,c_0_18])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( k10_relat_1(X2,X1) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t173_relat_1])).

cnf(c_0_24,plain,
    ( r2_hidden(X3,k10_relat_1(X2,X4))
    | ~ r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( r2_hidden(k4_tarski(esk2_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_27,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k10_relat_1(X1,X3))
    | ~ r1_xboole_0(k2_relat_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[c_0_18,c_0_22])).

fof(c_0_29,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & ( k10_relat_1(esk7_0,esk6_0) != k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(esk7_0),esk6_0) )
    & ( k10_relat_1(esk7_0,esk6_0) = k1_xboole_0
      | r1_xboole_0(k2_relat_1(esk7_0),esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(csr,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( r2_hidden(k4_tarski(esk2_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( k10_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( k10_relat_1(esk7_0,esk6_0) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(esk7_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( k10_relat_1(esk7_0,esk6_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

cnf(c_0_37,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_38,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(esk7_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_34])]),c_0_14])).

cnf(c_0_39,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_40,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( r1_xboole_0(X1,k2_relat_1(esk7_0))
    | ~ r2_hidden(esk1_2(X1,k2_relat_1(esk7_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( k10_relat_1(esk7_0,esk6_0) != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(esk7_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( r1_xboole_0(esk6_0,k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(esk7_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_36])])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:07:47 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.45  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.18/0.45  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.18/0.45  #
% 0.18/0.45  # Preprocessing time       : 0.028 s
% 0.18/0.45  # Presaturation interreduction done
% 0.18/0.45  
% 0.18/0.45  # Proof found!
% 0.18/0.45  # SZS status Theorem
% 0.18/0.45  # SZS output start CNFRefutation
% 0.18/0.45  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.18/0.45  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.18/0.45  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 0.18/0.45  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.18/0.45  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 0.18/0.45  fof(t173_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 0.18/0.45  fof(c_0_6, plain, ![X16, X17]:((k2_zfmisc_1(X16,X17)!=k1_xboole_0|(X16=k1_xboole_0|X17=k1_xboole_0))&((X16!=k1_xboole_0|k2_zfmisc_1(X16,X17)=k1_xboole_0)&(X17!=k1_xboole_0|k2_zfmisc_1(X16,X17)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.18/0.45  fof(c_0_7, plain, ![X18, X19]:~r2_hidden(X18,k2_zfmisc_1(X18,X19)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.18/0.45  cnf(c_0_8, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.18/0.45  cnf(c_0_9, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.45  cnf(c_0_10, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_8])).
% 0.18/0.45  fof(c_0_11, plain, ![X20, X21, X22, X24, X25, X26, X27, X29]:(((~r2_hidden(X22,X21)|r2_hidden(k4_tarski(esk2_3(X20,X21,X22),X22),X20)|X21!=k2_relat_1(X20))&(~r2_hidden(k4_tarski(X25,X24),X20)|r2_hidden(X24,X21)|X21!=k2_relat_1(X20)))&((~r2_hidden(esk3_2(X26,X27),X27)|~r2_hidden(k4_tarski(X29,esk3_2(X26,X27)),X26)|X27=k2_relat_1(X26))&(r2_hidden(esk3_2(X26,X27),X27)|r2_hidden(k4_tarski(esk4_2(X26,X27),esk3_2(X26,X27)),X26)|X27=k2_relat_1(X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.18/0.45  fof(c_0_12, plain, ![X5, X6, X8, X9, X10]:(((r2_hidden(esk1_2(X5,X6),X5)|r1_xboole_0(X5,X6))&(r2_hidden(esk1_2(X5,X6),X6)|r1_xboole_0(X5,X6)))&(~r2_hidden(X10,X8)|~r2_hidden(X10,X9)|~r1_xboole_0(X8,X9))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.18/0.45  fof(c_0_13, plain, ![X31, X32, X33, X35]:((((r2_hidden(esk5_3(X31,X32,X33),k2_relat_1(X33))|~r2_hidden(X31,k10_relat_1(X33,X32))|~v1_relat_1(X33))&(r2_hidden(k4_tarski(X31,esk5_3(X31,X32,X33)),X33)|~r2_hidden(X31,k10_relat_1(X33,X32))|~v1_relat_1(X33)))&(r2_hidden(esk5_3(X31,X32,X33),X32)|~r2_hidden(X31,k10_relat_1(X33,X32))|~v1_relat_1(X33)))&(~r2_hidden(X35,k2_relat_1(X33))|~r2_hidden(k4_tarski(X31,X35),X33)|~r2_hidden(X35,X32)|r2_hidden(X31,k10_relat_1(X33,X32))|~v1_relat_1(X33))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.18/0.45  cnf(c_0_14, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.18/0.45  cnf(c_0_15, plain, (r2_hidden(esk3_2(X1,X2),X2)|r2_hidden(k4_tarski(esk4_2(X1,X2),esk3_2(X1,X2)),X1)|X2=k2_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.45  cnf(c_0_16, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.45  cnf(c_0_17, plain, (r2_hidden(esk5_3(X1,X2,X3),X2)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.45  cnf(c_0_18, plain, (X1=k2_relat_1(k1_xboole_0)|r2_hidden(esk3_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.18/0.45  cnf(c_0_19, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.45  cnf(c_0_20, plain, (~v1_relat_1(X1)|~r2_hidden(esk5_3(X2,X3,X1),X4)|~r2_hidden(X2,k10_relat_1(X1,X3))|~r1_xboole_0(X4,X3)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.18/0.45  cnf(c_0_21, plain, (r2_hidden(esk5_3(X1,X2,X3),k2_relat_1(X3))|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.45  cnf(c_0_22, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_14, c_0_18])).
% 0.18/0.45  fof(c_0_23, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1)))), inference(assume_negation,[status(cth)],[t173_relat_1])).
% 0.18/0.45  cnf(c_0_24, plain, (r2_hidden(X3,k10_relat_1(X2,X4))|~r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,X4)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.45  cnf(c_0_25, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)), inference(er,[status(thm)],[c_0_19])).
% 0.18/0.45  cnf(c_0_26, plain, (r2_hidden(k4_tarski(esk2_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.45  cnf(c_0_27, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k10_relat_1(X1,X3))|~r1_xboole_0(k2_relat_1(X1),X3)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.18/0.45  cnf(c_0_28, plain, (X1=k1_xboole_0|r2_hidden(esk3_2(k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[c_0_18, c_0_22])).
% 0.18/0.45  fof(c_0_29, negated_conjecture, (v1_relat_1(esk7_0)&((k10_relat_1(esk7_0,esk6_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk7_0),esk6_0))&(k10_relat_1(esk7_0,esk6_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk7_0),esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 0.18/0.45  cnf(c_0_30, plain, (r2_hidden(X1,k10_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X4),X2)|~r2_hidden(X4,X3)), inference(csr,[status(thm)],[c_0_24, c_0_25])).
% 0.18/0.45  cnf(c_0_31, plain, (r2_hidden(k4_tarski(esk2_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_26])).
% 0.18/0.45  cnf(c_0_32, plain, (k10_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.18/0.45  cnf(c_0_33, negated_conjecture, (k10_relat_1(esk7_0,esk6_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk7_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.45  cnf(c_0_34, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.45  cnf(c_0_35, plain, (r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.18/0.45  cnf(c_0_36, negated_conjecture, (k10_relat_1(esk7_0,esk6_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])])).
% 0.18/0.45  cnf(c_0_37, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.45  cnf(c_0_38, negated_conjecture, (~r2_hidden(X1,k2_relat_1(esk7_0))|~r2_hidden(X1,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_34])]), c_0_14])).
% 0.18/0.45  cnf(c_0_39, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.45  cnf(c_0_40, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_16, c_0_37])).
% 0.18/0.45  cnf(c_0_41, negated_conjecture, (r1_xboole_0(X1,k2_relat_1(esk7_0))|~r2_hidden(esk1_2(X1,k2_relat_1(esk7_0)),esk6_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.18/0.45  cnf(c_0_42, negated_conjecture, (k10_relat_1(esk7_0,esk6_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk7_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.45  cnf(c_0_43, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_40, c_0_39])).
% 0.18/0.45  cnf(c_0_44, negated_conjecture, (r1_xboole_0(esk6_0,k2_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_41, c_0_37])).
% 0.18/0.45  cnf(c_0_45, negated_conjecture, (~r1_xboole_0(k2_relat_1(esk7_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_36])])).
% 0.18/0.45  cnf(c_0_46, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), ['proof']).
% 0.18/0.45  # SZS output end CNFRefutation
% 0.18/0.45  # Proof object total steps             : 47
% 0.18/0.45  # Proof object clause steps            : 34
% 0.18/0.45  # Proof object formula steps           : 13
% 0.18/0.45  # Proof object conjectures             : 12
% 0.18/0.45  # Proof object clause conjectures      : 9
% 0.18/0.45  # Proof object formula conjectures     : 3
% 0.18/0.45  # Proof object initial clauses used    : 14
% 0.18/0.45  # Proof object initial formulas used   : 6
% 0.18/0.45  # Proof object generating inferences   : 14
% 0.18/0.45  # Proof object simplifying inferences  : 13
% 0.18/0.45  # Training examples: 0 positive, 0 negative
% 0.18/0.45  # Parsed axioms                        : 8
% 0.18/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.45  # Initial clauses                      : 22
% 0.18/0.45  # Removed in clause preprocessing      : 0
% 0.18/0.45  # Initial clauses in saturation        : 22
% 0.18/0.45  # Processed clauses                    : 1454
% 0.18/0.45  # ...of these trivial                  : 0
% 0.18/0.45  # ...subsumed                          : 1164
% 0.18/0.45  # ...remaining for further processing  : 290
% 0.18/0.45  # Other redundant clauses eliminated   : 6
% 0.18/0.45  # Clauses deleted for lack of memory   : 0
% 0.18/0.45  # Backward-subsumed                    : 0
% 0.18/0.45  # Backward-rewritten                   : 11
% 0.18/0.45  # Generated clauses                    : 4224
% 0.18/0.45  # ...of the previous two non-trivial   : 3826
% 0.18/0.45  # Contextual simplify-reflections      : 1
% 0.18/0.45  # Paramodulations                      : 4216
% 0.18/0.45  # Factorizations                       : 2
% 0.18/0.45  # Equation resolutions                 : 6
% 0.18/0.45  # Propositional unsat checks           : 0
% 0.18/0.45  #    Propositional check models        : 0
% 0.18/0.45  #    Propositional check unsatisfiable : 0
% 0.18/0.45  #    Propositional clauses             : 0
% 0.18/0.45  #    Propositional clauses after purity: 0
% 0.18/0.45  #    Propositional unsat core size     : 0
% 0.18/0.45  #    Propositional preprocessing time  : 0.000
% 0.18/0.45  #    Propositional encoding time       : 0.000
% 0.18/0.45  #    Propositional solver time         : 0.000
% 0.18/0.45  #    Success case prop preproc time    : 0.000
% 0.18/0.45  #    Success case prop encoding time   : 0.000
% 0.18/0.45  #    Success case prop solver time     : 0.000
% 0.18/0.45  # Current number of processed clauses  : 252
% 0.18/0.45  #    Positive orientable unit clauses  : 10
% 0.18/0.45  #    Positive unorientable unit clauses: 0
% 0.18/0.45  #    Negative unit clauses             : 4
% 0.18/0.45  #    Non-unit-clauses                  : 238
% 0.18/0.45  # Current number of unprocessed clauses: 2396
% 0.18/0.45  # ...number of literals in the above   : 8342
% 0.18/0.45  # Current number of archived formulas  : 0
% 0.18/0.45  # Current number of archived clauses   : 32
% 0.18/0.45  # Clause-clause subsumption calls (NU) : 15288
% 0.18/0.45  # Rec. Clause-clause subsumption calls : 11378
% 0.18/0.45  # Non-unit clause-clause subsumptions  : 624
% 0.18/0.45  # Unit Clause-clause subsumption calls : 8
% 0.18/0.45  # Rewrite failures with RHS unbound    : 0
% 0.18/0.45  # BW rewrite match attempts            : 2
% 0.18/0.45  # BW rewrite match successes           : 2
% 0.18/0.45  # Condensation attempts                : 0
% 0.18/0.45  # Condensation successes               : 0
% 0.18/0.45  # Termbank termtop insertions          : 67585
% 0.18/0.45  
% 0.18/0.45  # -------------------------------------------------
% 0.18/0.45  # User time                : 0.112 s
% 0.18/0.45  # System time              : 0.007 s
% 0.18/0.45  # Total time               : 0.119 s
% 0.18/0.45  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
