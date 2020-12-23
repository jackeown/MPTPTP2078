%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:02 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   36 (  53 expanded)
%              Number of clauses        :   23 (  25 expanded)
%              Number of leaves         :    7 (  14 expanded)
%              Depth                    :   10
%              Number of atoms          :  114 ( 188 expanded)
%              Number of equality atoms :   50 (  74 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_setfam_1,conjecture,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(k1_setfam_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

fof(d1_setfam_1,axiom,(
    ! [X1,X2] :
      ( ( X1 != k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ! [X4] :
                  ( r2_hidden(X4,X1)
                 => r2_hidden(X3,X4) ) ) ) )
      & ( X1 = k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> X2 = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r2_hidden(X1,X2)
       => r1_tarski(k1_setfam_1(X2),X1) ) ),
    inference(assume_negation,[status(cth)],[t4_setfam_1])).

fof(c_0_6,plain,(
    ! [X15,X16,X17,X18,X19,X21,X24,X25,X26,X27] :
      ( ( ~ r2_hidden(X17,X16)
        | ~ r2_hidden(X18,X15)
        | r2_hidden(X17,X18)
        | X16 != k1_setfam_1(X15)
        | X15 = k1_xboole_0 )
      & ( r2_hidden(esk2_3(X15,X16,X19),X15)
        | r2_hidden(X19,X16)
        | X16 != k1_setfam_1(X15)
        | X15 = k1_xboole_0 )
      & ( ~ r2_hidden(X19,esk2_3(X15,X16,X19))
        | r2_hidden(X19,X16)
        | X16 != k1_setfam_1(X15)
        | X15 = k1_xboole_0 )
      & ( r2_hidden(esk4_2(X15,X21),X15)
        | ~ r2_hidden(esk3_2(X15,X21),X21)
        | X21 = k1_setfam_1(X15)
        | X15 = k1_xboole_0 )
      & ( ~ r2_hidden(esk3_2(X15,X21),esk4_2(X15,X21))
        | ~ r2_hidden(esk3_2(X15,X21),X21)
        | X21 = k1_setfam_1(X15)
        | X15 = k1_xboole_0 )
      & ( r2_hidden(esk3_2(X15,X21),X21)
        | ~ r2_hidden(X24,X15)
        | r2_hidden(esk3_2(X15,X21),X24)
        | X21 = k1_setfam_1(X15)
        | X15 = k1_xboole_0 )
      & ( X26 != k1_setfam_1(X25)
        | X26 = k1_xboole_0
        | X25 != k1_xboole_0 )
      & ( X27 != k1_xboole_0
        | X27 = k1_setfam_1(X25)
        | X25 != k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).

fof(c_0_7,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0)
    & ~ r1_tarski(k1_setfam_1(esk6_0),esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_8,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,X3)
    | X4 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X2 != k1_setfam_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( ~ r1_tarski(k1_setfam_1(esk6_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,X3)
    | ~ r2_hidden(X2,k1_setfam_1(X1))
    | ~ r2_hidden(X3,X1) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk1_2(k1_setfam_1(esk6_0),esk5_0),k1_setfam_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_15,plain,(
    ! [X13,X14] : ~ r2_hidden(X13,k2_zfmisc_1(X13,X14)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

fof(c_0_16,plain,(
    ! [X11,X12] :
      ( ( k2_zfmisc_1(X11,X12) != k1_xboole_0
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0 )
      & ( X11 != k1_xboole_0
        | k2_zfmisc_1(X11,X12) = k1_xboole_0 )
      & ( X12 != k1_xboole_0
        | k2_zfmisc_1(X11,X12) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_17,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk1_2(k1_setfam_1(esk6_0),esk5_0),X1)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,negated_conjecture,
    ( ~ r2_hidden(esk1_2(k1_setfam_1(esk6_0),esk5_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_14])).

fof(c_0_20,plain,
    ( ~ epred1_0
  <=> ! [X2] : X2 != k1_xboole_0 ),
    introduced(definition)).

fof(c_0_21,plain,
    ( ~ epred2_0
  <=> ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    introduced(definition)).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_25,plain,
    ( X1 = k1_setfam_1(X2)
    | X1 != k1_xboole_0
    | X2 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_26,plain,
    ( ~ epred2_0
    | ~ epred1_0 ),
    inference(apply_def,[status(thm)],[inference(apply_def,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_20]),c_0_21])).

cnf(c_0_27,plain,
    ( epred1_0
    | X1 != k1_xboole_0 ),
    inference(split_equiv,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( epred2_0
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(split_equiv,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk5_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_18,c_0_24])).

cnf(c_0_30,plain,
    ( X1 = k1_setfam_1(k1_xboole_0)
    | X1 != k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( X1 != k1_xboole_0
    | ~ epred2_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( epred2_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,plain,
    ( k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_34,plain,
    ( X1 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32])])).

cnf(c_0_35,plain,
    ( $false ),
    inference(sr,[status(thm)],[c_0_33,c_0_34]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:24:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S070I
% 0.14/0.38  # and selection function SelectVGNonCR.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.027 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t4_setfam_1, conjecture, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(k1_setfam_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 0.14/0.38  fof(d1_setfam_1, axiom, ![X1, X2]:((X1!=k1_xboole_0=>(X2=k1_setfam_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>![X4]:(r2_hidden(X4,X1)=>r2_hidden(X3,X4)))))&(X1=k1_xboole_0=>(X2=k1_setfam_1(X1)<=>X2=k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_setfam_1)).
% 0.14/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.14/0.38  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.14/0.38  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.14/0.38  fof(c_0_5, negated_conjecture, ~(![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(k1_setfam_1(X2),X1))), inference(assume_negation,[status(cth)],[t4_setfam_1])).
% 0.14/0.38  fof(c_0_6, plain, ![X15, X16, X17, X18, X19, X21, X24, X25, X26, X27]:((((~r2_hidden(X17,X16)|(~r2_hidden(X18,X15)|r2_hidden(X17,X18))|X16!=k1_setfam_1(X15)|X15=k1_xboole_0)&((r2_hidden(esk2_3(X15,X16,X19),X15)|r2_hidden(X19,X16)|X16!=k1_setfam_1(X15)|X15=k1_xboole_0)&(~r2_hidden(X19,esk2_3(X15,X16,X19))|r2_hidden(X19,X16)|X16!=k1_setfam_1(X15)|X15=k1_xboole_0)))&(((r2_hidden(esk4_2(X15,X21),X15)|~r2_hidden(esk3_2(X15,X21),X21)|X21=k1_setfam_1(X15)|X15=k1_xboole_0)&(~r2_hidden(esk3_2(X15,X21),esk4_2(X15,X21))|~r2_hidden(esk3_2(X15,X21),X21)|X21=k1_setfam_1(X15)|X15=k1_xboole_0))&(r2_hidden(esk3_2(X15,X21),X21)|(~r2_hidden(X24,X15)|r2_hidden(esk3_2(X15,X21),X24))|X21=k1_setfam_1(X15)|X15=k1_xboole_0)))&((X26!=k1_setfam_1(X25)|X26=k1_xboole_0|X25!=k1_xboole_0)&(X27!=k1_xboole_0|X27=k1_setfam_1(X25)|X25!=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).
% 0.14/0.38  fof(c_0_7, negated_conjecture, (r2_hidden(esk5_0,esk6_0)&~r1_tarski(k1_setfam_1(esk6_0),esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.14/0.38  fof(c_0_8, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.14/0.38  cnf(c_0_9, plain, (r2_hidden(X1,X3)|X4=k1_xboole_0|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X2!=k1_setfam_1(X4)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.38  cnf(c_0_10, negated_conjecture, (~r1_tarski(k1_setfam_1(esk6_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  cnf(c_0_11, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_12, plain, (X1=k1_xboole_0|r2_hidden(X2,X3)|~r2_hidden(X2,k1_setfam_1(X1))|~r2_hidden(X3,X1)), inference(er,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_13, negated_conjecture, (r2_hidden(esk1_2(k1_setfam_1(esk6_0),esk5_0),k1_setfam_1(esk6_0))), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.14/0.38  cnf(c_0_14, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  fof(c_0_15, plain, ![X13, X14]:~r2_hidden(X13,k2_zfmisc_1(X13,X14)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.14/0.38  fof(c_0_16, plain, ![X11, X12]:((k2_zfmisc_1(X11,X12)!=k1_xboole_0|(X11=k1_xboole_0|X12=k1_xboole_0))&((X11!=k1_xboole_0|k2_zfmisc_1(X11,X12)=k1_xboole_0)&(X12!=k1_xboole_0|k2_zfmisc_1(X11,X12)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.14/0.38  cnf(c_0_17, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk1_2(k1_setfam_1(esk6_0),esk5_0),X1)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.14/0.38  cnf(c_0_18, negated_conjecture, (r2_hidden(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  cnf(c_0_19, negated_conjecture, (~r2_hidden(esk1_2(k1_setfam_1(esk6_0),esk5_0),esk5_0)), inference(spm,[status(thm)],[c_0_10, c_0_14])).
% 0.14/0.38  fof(c_0_20, plain, (~epred1_0<=>![X2]:X2!=k1_xboole_0), introduced(definition)).
% 0.14/0.38  fof(c_0_21, plain, (~epred2_0<=>![X1]:~r2_hidden(X1,k1_xboole_0)), introduced(definition)).
% 0.14/0.38  cnf(c_0_22, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  cnf(c_0_23, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.38  cnf(c_0_24, negated_conjecture, (esk6_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])).
% 0.14/0.38  cnf(c_0_25, plain, (X1=k1_setfam_1(X2)|X1!=k1_xboole_0|X2!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.38  cnf(c_0_26, plain, (~epred2_0|~epred1_0), inference(apply_def,[status(thm)],[inference(apply_def,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_20]), c_0_21])).
% 0.14/0.38  cnf(c_0_27, plain, (epred1_0|X1!=k1_xboole_0), inference(split_equiv,[status(thm)],[c_0_20])).
% 0.14/0.38  cnf(c_0_28, plain, (epred2_0|~r2_hidden(X1,k1_xboole_0)), inference(split_equiv,[status(thm)],[c_0_21])).
% 0.14/0.38  cnf(c_0_29, negated_conjecture, (r2_hidden(esk5_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_18, c_0_24])).
% 0.14/0.38  cnf(c_0_30, plain, (X1=k1_setfam_1(k1_xboole_0)|X1!=k1_xboole_0), inference(er,[status(thm)],[c_0_25])).
% 0.14/0.38  cnf(c_0_31, plain, (X1!=k1_xboole_0|~epred2_0), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.14/0.38  cnf(c_0_32, negated_conjecture, (epred2_0), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.14/0.38  cnf(c_0_33, plain, (k1_setfam_1(k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_30])).
% 0.14/0.38  cnf(c_0_34, plain, (X1!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32])])).
% 0.14/0.38  cnf(c_0_35, plain, ($false), inference(sr,[status(thm)],[c_0_33, c_0_34]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 36
% 0.14/0.38  # Proof object clause steps            : 23
% 0.14/0.38  # Proof object formula steps           : 13
% 0.14/0.38  # Proof object conjectures             : 11
% 0.14/0.38  # Proof object clause conjectures      : 8
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 10
% 0.14/0.38  # Proof object initial formulas used   : 5
% 0.14/0.38  # Proof object generating inferences   : 10
% 0.14/0.38  # Proof object simplifying inferences  : 7
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 5
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 17
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 17
% 0.14/0.38  # Processed clauses                    : 58
% 0.14/0.38  # ...of these trivial                  : 1
% 0.14/0.38  # ...subsumed                          : 0
% 0.14/0.38  # ...remaining for further processing  : 57
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 12
% 0.14/0.38  # Generated clauses                    : 44
% 0.14/0.38  # ...of the previous two non-trivial   : 45
% 0.14/0.38  # Contextual simplify-reflections      : 0
% 0.14/0.38  # Paramodulations                      : 30
% 0.14/0.38  # Factorizations                       : 2
% 0.14/0.38  # Equation resolutions                 : 7
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 25
% 0.14/0.38  #    Positive orientable unit clauses  : 2
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 6
% 0.14/0.38  #    Non-unit-clauses                  : 17
% 0.14/0.38  # Current number of unprocessed clauses: 21
% 0.14/0.38  # ...number of literals in the above   : 84
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 31
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 48
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 26
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.38  # Unit Clause-clause subsumption calls : 56
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 3
% 0.14/0.38  # BW rewrite match successes           : 3
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 1870
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.029 s
% 0.14/0.38  # System time              : 0.004 s
% 0.14/0.38  # Total time               : 0.033 s
% 0.14/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
