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
% DateTime   : Thu Dec  3 10:49:11 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   28 ( 105 expanded)
%              Number of clauses        :   17 (  52 expanded)
%              Number of leaves         :    5 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :  115 ( 337 expanded)
%              Number of equality atoms :   39 ( 158 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   38 (   2 average)
%              Maximal term depth       :    3 (   1 average)

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

fof(d1_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
    <=> ! [X2] :
          ~ ( r2_hidden(X2,X1)
            & ! [X3,X4] : X2 != k4_tarski(X3,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(d8_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( X3 = k5_relat_1(X1,X2)
              <=> ! [X4,X5] :
                    ( r2_hidden(k4_tarski(X4,X5),X3)
                  <=> ? [X6] :
                        ( r2_hidden(k4_tarski(X4,X6),X1)
                        & r2_hidden(k4_tarski(X6,X5),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

fof(t62_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
        & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(c_0_5,plain,(
    ! [X7,X8] :
      ( ( k2_zfmisc_1(X7,X8) != k1_xboole_0
        | X7 = k1_xboole_0
        | X8 = k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k2_zfmisc_1(X7,X8) = k1_xboole_0 )
      & ( X8 != k1_xboole_0
        | k2_zfmisc_1(X7,X8) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_6,plain,(
    ! [X9,X10] : ~ r2_hidden(X9,k2_zfmisc_1(X9,X10)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_7,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_7])).

fof(c_0_10,plain,(
    ! [X11,X12,X15,X17,X18] :
      ( ( ~ v1_relat_1(X11)
        | ~ r2_hidden(X12,X11)
        | X12 = k4_tarski(esk1_2(X11,X12),esk2_2(X11,X12)) )
      & ( r2_hidden(esk3_1(X15),X15)
        | v1_relat_1(X15) )
      & ( esk3_1(X15) != k4_tarski(X17,X18)
        | v1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).

fof(c_0_11,plain,(
    ! [X19,X20,X21,X22,X23,X25,X26,X27,X30] :
      ( ( r2_hidden(k4_tarski(X22,esk4_5(X19,X20,X21,X22,X23)),X19)
        | ~ r2_hidden(k4_tarski(X22,X23),X21)
        | X21 != k5_relat_1(X19,X20)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(k4_tarski(esk4_5(X19,X20,X21,X22,X23),X23),X20)
        | ~ r2_hidden(k4_tarski(X22,X23),X21)
        | X21 != k5_relat_1(X19,X20)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19) )
      & ( ~ r2_hidden(k4_tarski(X25,X27),X19)
        | ~ r2_hidden(k4_tarski(X27,X26),X20)
        | r2_hidden(k4_tarski(X25,X26),X21)
        | X21 != k5_relat_1(X19,X20)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19) )
      & ( ~ r2_hidden(k4_tarski(esk5_3(X19,X20,X21),esk6_3(X19,X20,X21)),X21)
        | ~ r2_hidden(k4_tarski(esk5_3(X19,X20,X21),X30),X19)
        | ~ r2_hidden(k4_tarski(X30,esk6_3(X19,X20,X21)),X20)
        | X21 = k5_relat_1(X19,X20)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(k4_tarski(esk5_3(X19,X20,X21),esk7_3(X19,X20,X21)),X19)
        | r2_hidden(k4_tarski(esk5_3(X19,X20,X21),esk6_3(X19,X20,X21)),X21)
        | X21 = k5_relat_1(X19,X20)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(k4_tarski(esk7_3(X19,X20,X21),esk6_3(X19,X20,X21)),X20)
        | r2_hidden(k4_tarski(esk5_3(X19,X20,X21),esk6_3(X19,X20,X21)),X21)
        | X21 = k5_relat_1(X19,X20)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

cnf(c_0_12,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
          & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t62_relat_1])).

cnf(c_0_15,plain,
    ( r2_hidden(k4_tarski(esk5_3(X1,X2,X3),esk7_3(X1,X2,X3)),X1)
    | r2_hidden(k4_tarski(esk5_3(X1,X2,X3),esk6_3(X1,X2,X3)),X3)
    | X3 = k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_17,negated_conjecture,
    ( v1_relat_1(esk8_0)
    & ( k5_relat_1(k1_xboole_0,esk8_0) != k1_xboole_0
      | k5_relat_1(esk8_0,k1_xboole_0) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

cnf(c_0_18,plain,
    ( k5_relat_1(X1,X2) = k1_xboole_0
    | r2_hidden(k4_tarski(esk5_3(X1,X2,k1_xboole_0),esk7_3(X1,X2,k1_xboole_0)),X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( k5_relat_1(X1,esk8_0) = k1_xboole_0
    | r2_hidden(k4_tarski(esk5_3(X1,esk8_0,k1_xboole_0),esk7_3(X1,esk8_0,k1_xboole_0)),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(esk7_3(X1,X2,X3),esk6_3(X1,X2,X3)),X2)
    | r2_hidden(k4_tarski(esk5_3(X1,X2,X3),esk6_3(X1,X2,X3)),X3)
    | X3 = k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk8_0) != k1_xboole_0
    | k5_relat_1(esk8_0,k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk8_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_16]),c_0_12])).

cnf(c_0_24,plain,
    ( k5_relat_1(X1,X2) = k1_xboole_0
    | r2_hidden(k4_tarski(esk7_3(X1,X2,k1_xboole_0),esk6_3(X1,X2,k1_xboole_0)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_16]),c_0_12])).

cnf(c_0_25,negated_conjecture,
    ( k5_relat_1(esk8_0,k1_xboole_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23])])).

cnf(c_0_26,plain,
    ( k5_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_16]),c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_19])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:52:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.027 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.12/0.37  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.12/0.37  fof(d1_relat_1, axiom, ![X1]:(v1_relat_1(X1)<=>![X2]:~((r2_hidden(X2,X1)&![X3, X4]:X2!=k4_tarski(X3,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 0.12/0.37  fof(d8_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(X3=k5_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>?[X6]:(r2_hidden(k4_tarski(X4,X6),X1)&r2_hidden(k4_tarski(X6,X5),X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_relat_1)).
% 0.12/0.37  fof(t62_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>(k5_relat_1(k1_xboole_0,X1)=k1_xboole_0&k5_relat_1(X1,k1_xboole_0)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 0.12/0.37  fof(c_0_5, plain, ![X7, X8]:((k2_zfmisc_1(X7,X8)!=k1_xboole_0|(X7=k1_xboole_0|X8=k1_xboole_0))&((X7!=k1_xboole_0|k2_zfmisc_1(X7,X8)=k1_xboole_0)&(X8!=k1_xboole_0|k2_zfmisc_1(X7,X8)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.12/0.37  fof(c_0_6, plain, ![X9, X10]:~r2_hidden(X9,k2_zfmisc_1(X9,X10)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.12/0.37  cnf(c_0_7, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.37  cnf(c_0_8, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_9, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_7])).
% 0.12/0.37  fof(c_0_10, plain, ![X11, X12, X15, X17, X18]:((~v1_relat_1(X11)|(~r2_hidden(X12,X11)|X12=k4_tarski(esk1_2(X11,X12),esk2_2(X11,X12))))&((r2_hidden(esk3_1(X15),X15)|v1_relat_1(X15))&(esk3_1(X15)!=k4_tarski(X17,X18)|v1_relat_1(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).
% 0.12/0.37  fof(c_0_11, plain, ![X19, X20, X21, X22, X23, X25, X26, X27, X30]:((((r2_hidden(k4_tarski(X22,esk4_5(X19,X20,X21,X22,X23)),X19)|~r2_hidden(k4_tarski(X22,X23),X21)|X21!=k5_relat_1(X19,X20)|~v1_relat_1(X21)|~v1_relat_1(X20)|~v1_relat_1(X19))&(r2_hidden(k4_tarski(esk4_5(X19,X20,X21,X22,X23),X23),X20)|~r2_hidden(k4_tarski(X22,X23),X21)|X21!=k5_relat_1(X19,X20)|~v1_relat_1(X21)|~v1_relat_1(X20)|~v1_relat_1(X19)))&(~r2_hidden(k4_tarski(X25,X27),X19)|~r2_hidden(k4_tarski(X27,X26),X20)|r2_hidden(k4_tarski(X25,X26),X21)|X21!=k5_relat_1(X19,X20)|~v1_relat_1(X21)|~v1_relat_1(X20)|~v1_relat_1(X19)))&((~r2_hidden(k4_tarski(esk5_3(X19,X20,X21),esk6_3(X19,X20,X21)),X21)|(~r2_hidden(k4_tarski(esk5_3(X19,X20,X21),X30),X19)|~r2_hidden(k4_tarski(X30,esk6_3(X19,X20,X21)),X20))|X21=k5_relat_1(X19,X20)|~v1_relat_1(X21)|~v1_relat_1(X20)|~v1_relat_1(X19))&((r2_hidden(k4_tarski(esk5_3(X19,X20,X21),esk7_3(X19,X20,X21)),X19)|r2_hidden(k4_tarski(esk5_3(X19,X20,X21),esk6_3(X19,X20,X21)),X21)|X21=k5_relat_1(X19,X20)|~v1_relat_1(X21)|~v1_relat_1(X20)|~v1_relat_1(X19))&(r2_hidden(k4_tarski(esk7_3(X19,X20,X21),esk6_3(X19,X20,X21)),X20)|r2_hidden(k4_tarski(esk5_3(X19,X20,X21),esk6_3(X19,X20,X21)),X21)|X21=k5_relat_1(X19,X20)|~v1_relat_1(X21)|~v1_relat_1(X20)|~v1_relat_1(X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).
% 0.12/0.37  cnf(c_0_12, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.12/0.37  cnf(c_0_13, plain, (r2_hidden(esk3_1(X1),X1)|v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  fof(c_0_14, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>(k5_relat_1(k1_xboole_0,X1)=k1_xboole_0&k5_relat_1(X1,k1_xboole_0)=k1_xboole_0))), inference(assume_negation,[status(cth)],[t62_relat_1])).
% 0.12/0.37  cnf(c_0_15, plain, (r2_hidden(k4_tarski(esk5_3(X1,X2,X3),esk7_3(X1,X2,X3)),X1)|r2_hidden(k4_tarski(esk5_3(X1,X2,X3),esk6_3(X1,X2,X3)),X3)|X3=k5_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_16, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.12/0.37  fof(c_0_17, negated_conjecture, (v1_relat_1(esk8_0)&(k5_relat_1(k1_xboole_0,esk8_0)!=k1_xboole_0|k5_relat_1(esk8_0,k1_xboole_0)!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.12/0.37  cnf(c_0_18, plain, (k5_relat_1(X1,X2)=k1_xboole_0|r2_hidden(k4_tarski(esk5_3(X1,X2,k1_xboole_0),esk7_3(X1,X2,k1_xboole_0)),X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_12])).
% 0.12/0.37  cnf(c_0_19, negated_conjecture, (v1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  cnf(c_0_20, negated_conjecture, (k5_relat_1(X1,esk8_0)=k1_xboole_0|r2_hidden(k4_tarski(esk5_3(X1,esk8_0,k1_xboole_0),esk7_3(X1,esk8_0,k1_xboole_0)),X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.12/0.37  cnf(c_0_21, plain, (r2_hidden(k4_tarski(esk7_3(X1,X2,X3),esk6_3(X1,X2,X3)),X2)|r2_hidden(k4_tarski(esk5_3(X1,X2,X3),esk6_3(X1,X2,X3)),X3)|X3=k5_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_22, negated_conjecture, (k5_relat_1(k1_xboole_0,esk8_0)!=k1_xboole_0|k5_relat_1(esk8_0,k1_xboole_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  cnf(c_0_23, negated_conjecture, (k5_relat_1(k1_xboole_0,esk8_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_16]), c_0_12])).
% 0.12/0.37  cnf(c_0_24, plain, (k5_relat_1(X1,X2)=k1_xboole_0|r2_hidden(k4_tarski(esk7_3(X1,X2,k1_xboole_0),esk6_3(X1,X2,k1_xboole_0)),X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_16]), c_0_12])).
% 0.12/0.37  cnf(c_0_25, negated_conjecture, (k5_relat_1(esk8_0,k1_xboole_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23])])).
% 0.12/0.37  cnf(c_0_26, plain, (k5_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_16]), c_0_12])).
% 0.12/0.37  cnf(c_0_27, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_19])]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 28
% 0.12/0.37  # Proof object clause steps            : 17
% 0.12/0.37  # Proof object formula steps           : 11
% 0.12/0.37  # Proof object conjectures             : 9
% 0.12/0.37  # Proof object clause conjectures      : 6
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 7
% 0.12/0.37  # Proof object initial formulas used   : 5
% 0.12/0.37  # Proof object generating inferences   : 8
% 0.12/0.37  # Proof object simplifying inferences  : 9
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 5
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 15
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 15
% 0.12/0.37  # Processed clauses                    : 74
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 18
% 0.12/0.37  # ...remaining for further processing  : 56
% 0.12/0.37  # Other redundant clauses eliminated   : 6
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 1
% 0.12/0.37  # Backward-rewritten                   : 1
% 0.12/0.37  # Generated clauses                    : 93
% 0.12/0.37  # ...of the previous two non-trivial   : 77
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 87
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 6
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 34
% 0.12/0.37  #    Positive orientable unit clauses  : 7
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 3
% 0.12/0.37  #    Non-unit-clauses                  : 24
% 0.12/0.37  # Current number of unprocessed clauses: 33
% 0.12/0.37  # ...number of literals in the above   : 218
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 17
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 443
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 37
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 2
% 0.12/0.37  # Unit Clause-clause subsumption calls : 12
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 2
% 0.12/0.37  # BW rewrite match successes           : 1
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 3705
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.032 s
% 0.12/0.37  # System time              : 0.004 s
% 0.12/0.37  # Total time               : 0.036 s
% 0.12/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
