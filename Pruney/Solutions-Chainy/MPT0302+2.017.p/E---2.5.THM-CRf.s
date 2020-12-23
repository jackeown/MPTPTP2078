%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:33 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 317 expanded)
%              Number of clauses        :   38 ( 160 expanded)
%              Number of leaves         :    8 (  82 expanded)
%              Depth                    :   16
%              Number of atoms          :  160 (1196 expanded)
%              Number of equality atoms :   40 ( 337 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t6_xboole_0,axiom,(
    ! [X1,X2] :
      ~ ( r2_xboole_0(X1,X2)
        & ! [X3] :
            ~ ( r2_hidden(X3,X2)
              & ~ r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t114_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X2,X1)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | X1 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(c_0_8,plain,(
    ! [X22,X23,X24,X25,X28,X29,X30,X31,X32,X33,X35,X36] :
      ( ( r2_hidden(esk4_4(X22,X23,X24,X25),X22)
        | ~ r2_hidden(X25,X24)
        | X24 != k2_zfmisc_1(X22,X23) )
      & ( r2_hidden(esk5_4(X22,X23,X24,X25),X23)
        | ~ r2_hidden(X25,X24)
        | X24 != k2_zfmisc_1(X22,X23) )
      & ( X25 = k4_tarski(esk4_4(X22,X23,X24,X25),esk5_4(X22,X23,X24,X25))
        | ~ r2_hidden(X25,X24)
        | X24 != k2_zfmisc_1(X22,X23) )
      & ( ~ r2_hidden(X29,X22)
        | ~ r2_hidden(X30,X23)
        | X28 != k4_tarski(X29,X30)
        | r2_hidden(X28,X24)
        | X24 != k2_zfmisc_1(X22,X23) )
      & ( ~ r2_hidden(esk6_3(X31,X32,X33),X33)
        | ~ r2_hidden(X35,X31)
        | ~ r2_hidden(X36,X32)
        | esk6_3(X31,X32,X33) != k4_tarski(X35,X36)
        | X33 = k2_zfmisc_1(X31,X32) )
      & ( r2_hidden(esk7_3(X31,X32,X33),X31)
        | r2_hidden(esk6_3(X31,X32,X33),X33)
        | X33 = k2_zfmisc_1(X31,X32) )
      & ( r2_hidden(esk8_3(X31,X32,X33),X32)
        | r2_hidden(esk6_3(X31,X32,X33),X33)
        | X33 = k2_zfmisc_1(X31,X32) )
      & ( esk6_3(X31,X32,X33) = k4_tarski(esk7_3(X31,X32,X33),esk8_3(X31,X32,X33))
        | r2_hidden(esk6_3(X31,X32,X33),X33)
        | X33 = k2_zfmisc_1(X31,X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

fof(c_0_9,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_10,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( ~ r1_tarski(X11,X12)
        | ~ r2_hidden(X13,X11)
        | r2_hidden(X13,X12) )
      & ( r2_hidden(esk2_2(X14,X15),X14)
        | r1_tarski(X14,X15) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | r1_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_11,plain,
    ( r2_hidden(esk4_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X19,X20] :
      ( ( r2_hidden(esk3_2(X19,X20),X20)
        | ~ r2_xboole_0(X19,X20) )
      & ( ~ r2_hidden(esk3_2(X19,X20),X19)
        | ~ r2_xboole_0(X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_xboole_0])])])])])).

fof(c_0_16,plain,(
    ! [X17,X18] :
      ( ( r1_tarski(X17,X18)
        | ~ r2_xboole_0(X17,X18) )
      & ( X17 != X18
        | ~ r2_xboole_0(X17,X18) )
      & ( ~ r1_tarski(X17,X18)
        | X17 = X18
        | r2_xboole_0(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_19,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X2,X3))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_14])).

cnf(c_0_20,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X2,X1)
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X1 = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t114_zfmisc_1])).

cnf(c_0_24,plain,
    ( ~ r2_xboole_0(X1,k2_zfmisc_1(X2,X3))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,plain,
    ( k1_xboole_0 = X1
    | r2_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_26,plain,(
    ! [X39,X40,X41,X42] :
      ( ( r2_hidden(X39,X41)
        | ~ r2_hidden(k4_tarski(X39,X40),k2_zfmisc_1(X41,X42)) )
      & ( r2_hidden(X40,X42)
        | ~ r2_hidden(k4_tarski(X39,X40),k2_zfmisc_1(X41,X42)) )
      & ( ~ r2_hidden(X39,X41)
        | ~ r2_hidden(X40,X42)
        | r2_hidden(k4_tarski(X39,X40),k2_zfmisc_1(X41,X42)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

fof(c_0_27,negated_conjecture,
    ( k2_zfmisc_1(esk9_0,esk10_0) = k2_zfmisc_1(esk10_0,esk9_0)
    & esk9_0 != k1_xboole_0
    & esk10_0 != k1_xboole_0
    & esk9_0 != esk10_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

cnf(c_0_28,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( k2_zfmisc_1(esk9_0,esk10_0) = k2_zfmisc_1(esk10_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_31,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_18])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(X1,esk9_0)
    | ~ r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk10_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_33,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_31]),c_0_18])])).

cnf(c_0_35,plain,
    ( r2_hidden(esk7_3(X1,X2,X3),X1)
    | r2_hidden(esk6_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(X1,esk9_0)
    | ~ r2_hidden(X2,esk9_0)
    | ~ r2_hidden(X1,esk10_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk6_3(k1_xboole_0,X2,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( esk9_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(X1,esk9_0)
    | ~ r2_hidden(X1,esk10_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(X1,esk10_0)
    | ~ r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(esk10_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_30])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(X1,esk9_0)
    | ~ r2_hidden(esk2_2(X1,esk9_0),esk10_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(X1,esk10_0)
    | ~ r2_hidden(X1,esk9_0)
    | ~ r2_hidden(X2,esk10_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_33])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(esk10_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_13])).

cnf(c_0_46,negated_conjecture,
    ( esk9_0 != esk10_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk3_2(X1,esk9_0),esk10_0)
    | ~ r2_xboole_0(X1,esk9_0)
    | ~ r2_hidden(X2,esk10_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_20])).

cnf(c_0_48,negated_conjecture,
    ( r2_xboole_0(esk10_0,esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_45]),c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk3_2(esk10_0,esk9_0),esk10_0)
    | ~ r2_hidden(X1,esk10_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_50,negated_conjecture,
    ( esk10_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_51,plain,
    ( ~ r2_hidden(esk3_2(X1,X2),X1)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk3_2(esk10_0,esk9_0),esk10_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_37]),c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_48])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:41:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.028 s
% 0.13/0.40  # Presaturation interreduction done
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.13/0.40  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.13/0.40  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.40  fof(t6_xboole_0, axiom, ![X1, X2]:~((r2_xboole_0(X1,X2)&![X3]:~((r2_hidden(X3,X2)&~(r2_hidden(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 0.13/0.40  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.13/0.40  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.13/0.40  fof(t114_zfmisc_1, conjecture, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X2,X1)=>(X1=k1_xboole_0|X2=k1_xboole_0|X1=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t114_zfmisc_1)).
% 0.13/0.40  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.13/0.40  fof(c_0_8, plain, ![X22, X23, X24, X25, X28, X29, X30, X31, X32, X33, X35, X36]:(((((r2_hidden(esk4_4(X22,X23,X24,X25),X22)|~r2_hidden(X25,X24)|X24!=k2_zfmisc_1(X22,X23))&(r2_hidden(esk5_4(X22,X23,X24,X25),X23)|~r2_hidden(X25,X24)|X24!=k2_zfmisc_1(X22,X23)))&(X25=k4_tarski(esk4_4(X22,X23,X24,X25),esk5_4(X22,X23,X24,X25))|~r2_hidden(X25,X24)|X24!=k2_zfmisc_1(X22,X23)))&(~r2_hidden(X29,X22)|~r2_hidden(X30,X23)|X28!=k4_tarski(X29,X30)|r2_hidden(X28,X24)|X24!=k2_zfmisc_1(X22,X23)))&((~r2_hidden(esk6_3(X31,X32,X33),X33)|(~r2_hidden(X35,X31)|~r2_hidden(X36,X32)|esk6_3(X31,X32,X33)!=k4_tarski(X35,X36))|X33=k2_zfmisc_1(X31,X32))&(((r2_hidden(esk7_3(X31,X32,X33),X31)|r2_hidden(esk6_3(X31,X32,X33),X33)|X33=k2_zfmisc_1(X31,X32))&(r2_hidden(esk8_3(X31,X32,X33),X32)|r2_hidden(esk6_3(X31,X32,X33),X33)|X33=k2_zfmisc_1(X31,X32)))&(esk6_3(X31,X32,X33)=k4_tarski(esk7_3(X31,X32,X33),esk8_3(X31,X32,X33))|r2_hidden(esk6_3(X31,X32,X33),X33)|X33=k2_zfmisc_1(X31,X32))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.13/0.40  fof(c_0_9, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.13/0.40  fof(c_0_10, plain, ![X11, X12, X13, X14, X15]:((~r1_tarski(X11,X12)|(~r2_hidden(X13,X11)|r2_hidden(X13,X12)))&((r2_hidden(esk2_2(X14,X15),X14)|r1_tarski(X14,X15))&(~r2_hidden(esk2_2(X14,X15),X15)|r1_tarski(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.40  cnf(c_0_11, plain, (r2_hidden(esk4_4(X1,X2,X3,X4),X1)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.40  cnf(c_0_12, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.40  cnf(c_0_13, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.40  cnf(c_0_14, plain, (r2_hidden(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_11])).
% 0.13/0.40  fof(c_0_15, plain, ![X19, X20]:((r2_hidden(esk3_2(X19,X20),X20)|~r2_xboole_0(X19,X20))&(~r2_hidden(esk3_2(X19,X20),X19)|~r2_xboole_0(X19,X20))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_xboole_0])])])])])).
% 0.13/0.40  fof(c_0_16, plain, ![X17, X18]:(((r1_tarski(X17,X18)|~r2_xboole_0(X17,X18))&(X17!=X18|~r2_xboole_0(X17,X18)))&(~r1_tarski(X17,X18)|X17=X18|r2_xboole_0(X17,X18))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.13/0.40  cnf(c_0_17, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.13/0.40  cnf(c_0_18, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.13/0.40  cnf(c_0_19, plain, (~r2_hidden(X1,k2_zfmisc_1(X2,X3))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_12, c_0_14])).
% 0.13/0.40  cnf(c_0_20, plain, (r2_hidden(esk3_2(X1,X2),X2)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.40  cnf(c_0_21, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  cnf(c_0_22, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.40  fof(c_0_23, negated_conjecture, ~(![X1, X2]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X2,X1)=>(X1=k1_xboole_0|X2=k1_xboole_0|X1=X2))), inference(assume_negation,[status(cth)],[t114_zfmisc_1])).
% 0.13/0.40  cnf(c_0_24, plain, (~r2_xboole_0(X1,k2_zfmisc_1(X2,X3))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.13/0.40  cnf(c_0_25, plain, (k1_xboole_0=X1|r2_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.13/0.40  fof(c_0_26, plain, ![X39, X40, X41, X42]:(((r2_hidden(X39,X41)|~r2_hidden(k4_tarski(X39,X40),k2_zfmisc_1(X41,X42)))&(r2_hidden(X40,X42)|~r2_hidden(k4_tarski(X39,X40),k2_zfmisc_1(X41,X42))))&(~r2_hidden(X39,X41)|~r2_hidden(X40,X42)|r2_hidden(k4_tarski(X39,X40),k2_zfmisc_1(X41,X42)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.13/0.40  fof(c_0_27, negated_conjecture, (k2_zfmisc_1(esk9_0,esk10_0)=k2_zfmisc_1(esk10_0,esk9_0)&((esk9_0!=k1_xboole_0&esk10_0!=k1_xboole_0)&esk9_0!=esk10_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 0.13/0.40  cnf(c_0_28, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.13/0.40  cnf(c_0_29, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.40  cnf(c_0_30, negated_conjecture, (k2_zfmisc_1(esk9_0,esk10_0)=k2_zfmisc_1(esk10_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.40  cnf(c_0_31, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_28, c_0_18])).
% 0.13/0.40  cnf(c_0_32, negated_conjecture, (r2_hidden(X1,esk9_0)|~r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk10_0,esk9_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.13/0.40  cnf(c_0_33, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.40  cnf(c_0_34, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_31]), c_0_18])])).
% 0.13/0.40  cnf(c_0_35, plain, (r2_hidden(esk7_3(X1,X2,X3),X1)|r2_hidden(esk6_3(X1,X2,X3),X3)|X3=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.40  cnf(c_0_36, negated_conjecture, (r2_hidden(X1,esk9_0)|~r2_hidden(X2,esk9_0)|~r2_hidden(X1,esk10_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.13/0.40  cnf(c_0_37, plain, (X1=k1_xboole_0|r2_hidden(esk6_3(k1_xboole_0,X2,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_31])).
% 0.13/0.40  cnf(c_0_38, negated_conjecture, (esk9_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.40  cnf(c_0_39, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.40  cnf(c_0_40, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.40  cnf(c_0_41, negated_conjecture, (r2_hidden(X1,esk9_0)|~r2_hidden(X1,esk10_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])).
% 0.13/0.40  cnf(c_0_42, negated_conjecture, (r2_hidden(X1,esk10_0)|~r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(esk10_0,esk9_0))), inference(spm,[status(thm)],[c_0_39, c_0_30])).
% 0.13/0.40  cnf(c_0_43, negated_conjecture, (r1_tarski(X1,esk9_0)|~r2_hidden(esk2_2(X1,esk9_0),esk10_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.13/0.40  cnf(c_0_44, negated_conjecture, (r2_hidden(X1,esk10_0)|~r2_hidden(X1,esk9_0)|~r2_hidden(X2,esk10_0)), inference(spm,[status(thm)],[c_0_42, c_0_33])).
% 0.13/0.40  cnf(c_0_45, negated_conjecture, (r1_tarski(esk10_0,esk9_0)), inference(spm,[status(thm)],[c_0_43, c_0_13])).
% 0.13/0.40  cnf(c_0_46, negated_conjecture, (esk9_0!=esk10_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.40  cnf(c_0_47, negated_conjecture, (r2_hidden(esk3_2(X1,esk9_0),esk10_0)|~r2_xboole_0(X1,esk9_0)|~r2_hidden(X2,esk10_0)), inference(spm,[status(thm)],[c_0_44, c_0_20])).
% 0.13/0.40  cnf(c_0_48, negated_conjecture, (r2_xboole_0(esk10_0,esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_45]), c_0_46])).
% 0.13/0.40  cnf(c_0_49, negated_conjecture, (r2_hidden(esk3_2(esk10_0,esk9_0),esk10_0)|~r2_hidden(X1,esk10_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.13/0.40  cnf(c_0_50, negated_conjecture, (esk10_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.40  cnf(c_0_51, plain, (~r2_hidden(esk3_2(X1,X2),X1)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.40  cnf(c_0_52, negated_conjecture, (r2_hidden(esk3_2(esk10_0,esk9_0),esk10_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_37]), c_0_50])).
% 0.13/0.40  cnf(c_0_53, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_48])]), ['proof']).
% 0.13/0.40  # SZS output end CNFRefutation
% 0.13/0.40  # Proof object total steps             : 54
% 0.13/0.40  # Proof object clause steps            : 38
% 0.13/0.40  # Proof object formula steps           : 16
% 0.13/0.40  # Proof object conjectures             : 19
% 0.13/0.40  # Proof object clause conjectures      : 16
% 0.13/0.40  # Proof object formula conjectures     : 3
% 0.13/0.40  # Proof object initial clauses used    : 16
% 0.13/0.40  # Proof object initial formulas used   : 8
% 0.13/0.40  # Proof object generating inferences   : 21
% 0.13/0.40  # Proof object simplifying inferences  : 9
% 0.13/0.40  # Training examples: 0 positive, 0 negative
% 0.13/0.40  # Parsed axioms                        : 8
% 0.13/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.40  # Initial clauses                      : 26
% 0.13/0.40  # Removed in clause preprocessing      : 0
% 0.13/0.40  # Initial clauses in saturation        : 26
% 0.13/0.40  # Processed clauses                    : 606
% 0.13/0.40  # ...of these trivial                  : 0
% 0.13/0.40  # ...subsumed                          : 420
% 0.13/0.40  # ...remaining for further processing  : 186
% 0.13/0.40  # Other redundant clauses eliminated   : 6
% 0.13/0.40  # Clauses deleted for lack of memory   : 0
% 0.13/0.40  # Backward-subsumed                    : 23
% 0.13/0.40  # Backward-rewritten                   : 3
% 0.13/0.40  # Generated clauses                    : 1823
% 0.13/0.40  # ...of the previous two non-trivial   : 1358
% 0.13/0.40  # Contextual simplify-reflections      : 0
% 0.13/0.40  # Paramodulations                      : 1817
% 0.13/0.40  # Factorizations                       : 0
% 0.13/0.40  # Equation resolutions                 : 6
% 0.13/0.40  # Propositional unsat checks           : 0
% 0.13/0.40  #    Propositional check models        : 0
% 0.13/0.40  #    Propositional check unsatisfiable : 0
% 0.13/0.40  #    Propositional clauses             : 0
% 0.13/0.40  #    Propositional clauses after purity: 0
% 0.13/0.40  #    Propositional unsat core size     : 0
% 0.13/0.40  #    Propositional preprocessing time  : 0.000
% 0.13/0.40  #    Propositional encoding time       : 0.000
% 0.13/0.40  #    Propositional solver time         : 0.000
% 0.13/0.40  #    Success case prop preproc time    : 0.000
% 0.13/0.40  #    Success case prop encoding time   : 0.000
% 0.13/0.40  #    Success case prop solver time     : 0.000
% 0.13/0.40  # Current number of processed clauses  : 129
% 0.13/0.40  #    Positive orientable unit clauses  : 12
% 0.13/0.40  #    Positive unorientable unit clauses: 0
% 0.13/0.40  #    Negative unit clauses             : 9
% 0.13/0.40  #    Non-unit-clauses                  : 108
% 0.13/0.40  # Current number of unprocessed clauses: 769
% 0.13/0.40  # ...number of literals in the above   : 2582
% 0.13/0.40  # Current number of archived formulas  : 0
% 0.13/0.40  # Current number of archived clauses   : 52
% 0.13/0.40  # Clause-clause subsumption calls (NU) : 2826
% 0.13/0.40  # Rec. Clause-clause subsumption calls : 2237
% 0.13/0.40  # Non-unit clause-clause subsumptions  : 114
% 0.13/0.40  # Unit Clause-clause subsumption calls : 236
% 0.13/0.40  # Rewrite failures with RHS unbound    : 0
% 0.13/0.40  # BW rewrite match attempts            : 4
% 0.13/0.40  # BW rewrite match successes           : 3
% 0.13/0.40  # Condensation attempts                : 0
% 0.13/0.40  # Condensation successes               : 0
% 0.13/0.40  # Termbank termtop insertions          : 20524
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.055 s
% 0.13/0.40  # System time              : 0.006 s
% 0.13/0.40  # Total time               : 0.061 s
% 0.13/0.40  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
