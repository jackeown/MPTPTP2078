%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:36 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 297 expanded)
%              Number of clauses        :   39 ( 134 expanded)
%              Number of leaves         :    9 (  70 expanded)
%              Depth                    :   13
%              Number of atoms          :  159 (1134 expanded)
%              Number of equality atoms :   26 ( 163 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t44_setfam_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
         => ( ! [X4] :
                ( m1_subset_1(X4,k1_zfmisc_1(X1))
               => ( r2_hidden(X4,X2)
                <=> r2_hidden(X4,X3) ) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_setfam_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t49_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( ! [X3] :
            ( m1_subset_1(X3,X1)
           => r2_hidden(X3,X2) )
       => X1 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
           => ( ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(X1))
                 => ( r2_hidden(X4,X2)
                  <=> r2_hidden(X4,X3) ) )
             => X2 = X3 ) ) ) ),
    inference(assume_negation,[status(cth)],[t44_setfam_1])).

fof(c_0_10,plain,(
    ! [X31,X32,X33] :
      ( ~ r2_hidden(X31,X32)
      | ~ m1_subset_1(X32,k1_zfmisc_1(X33))
      | m1_subset_1(X31,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_11,negated_conjecture,(
    ! [X37] :
      ( m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(esk6_0)))
      & m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(esk6_0)))
      & ( ~ r2_hidden(X37,esk7_0)
        | r2_hidden(X37,esk8_0)
        | ~ m1_subset_1(X37,k1_zfmisc_1(esk6_0)) )
      & ( ~ r2_hidden(X37,esk8_0)
        | r2_hidden(X37,esk7_0)
        | ~ m1_subset_1(X37,k1_zfmisc_1(esk6_0)) )
      & esk7_0 != esk8_0 ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])])).

cnf(c_0_12,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X24,X25] :
      ( ( m1_subset_1(esk5_2(X24,X25),X24)
        | X24 = X25
        | ~ m1_subset_1(X25,k1_zfmisc_1(X24)) )
      & ( ~ r2_hidden(esk5_2(X24,X25),X25)
        | X24 = X25
        | ~ m1_subset_1(X25,k1_zfmisc_1(X24)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_subset_1])])])])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,esk8_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(esk6_0))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_18,plain,(
    ! [X29,X30] :
      ( ~ m1_subset_1(X29,X30)
      | v1_xboole_0(X30)
      | r2_hidden(X29,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | ~ r2_hidden(X1,esk7_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(esk6_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_14])).

fof(c_0_21,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_22,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_23,plain,(
    ! [X15] :
      ( X15 = k1_xboole_0
      | r2_hidden(esk3_1(X15),X15) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_24,plain,
    ( X1 = X2
    | ~ r2_hidden(esk5_2(X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_26,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( m1_subset_1(esk5_2(X1,X2),X1)
    | X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_28,plain,(
    ! [X17,X18,X19,X20,X21,X22] :
      ( ( ~ r2_hidden(X19,X18)
        | r1_tarski(X19,X17)
        | X18 != k1_zfmisc_1(X17) )
      & ( ~ r1_tarski(X20,X17)
        | r2_hidden(X20,X18)
        | X18 != k1_zfmisc_1(X17) )
      & ( ~ r2_hidden(esk4_2(X21,X22),X22)
        | ~ r1_tarski(esk4_2(X21,X22),X21)
        | X22 = k1_zfmisc_1(X21) )
      & ( r2_hidden(esk4_2(X21,X22),X22)
        | r1_tarski(esk4_2(X21,X22),X21)
        | X22 = k1_zfmisc_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_30,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( X1 = esk7_0
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(X1))
    | ~ r2_hidden(esk5_2(X1,esk7_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_35,plain,
    ( X1 = X2
    | r2_hidden(esk5_2(X1,X2),X1)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( esk7_0 != esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(esk7_0,X1)
    | r2_hidden(esk2_2(esk7_0,X1),esk8_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk1_1(esk7_0),esk8_0)
    | v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_31])).

cnf(c_0_41,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( v1_xboole_0(esk8_0)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(esk8_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

fof(c_0_43,plain,(
    ! [X27,X28] :
      ( ~ r2_hidden(X27,X28)
      | m1_subset_1(X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(esk7_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( v1_xboole_0(esk7_0)
    | ~ v1_xboole_0(esk8_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk7_0,k1_zfmisc_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | ~ v1_xboole_0(esk8_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( esk8_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])])).

cnf(c_0_52,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_42])).

cnf(c_0_53,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_36,c_0_51])).

cnf(c_0_54,negated_conjecture,
    ( ~ m1_subset_1(esk7_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_51]),c_0_53])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(esk7_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_45,c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( ~ r2_hidden(esk7_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_48])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_55]),c_0_56]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:00:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.39  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.14/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.39  #
% 0.14/0.39  # Preprocessing time       : 0.028 s
% 0.14/0.39  
% 0.14/0.39  # Proof found!
% 0.14/0.39  # SZS status Theorem
% 0.14/0.39  # SZS output start CNFRefutation
% 0.14/0.39  fof(t44_setfam_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>(r2_hidden(X4,X2)<=>r2_hidden(X4,X3)))=>X2=X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_setfam_1)).
% 0.14/0.39  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.14/0.39  fof(t49_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(![X3]:(m1_subset_1(X3,X1)=>r2_hidden(X3,X2))=>X1=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_subset_1)).
% 0.14/0.39  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.14/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.14/0.39  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.14/0.39  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.14/0.39  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.14/0.39  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.14/0.39  fof(c_0_9, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>(r2_hidden(X4,X2)<=>r2_hidden(X4,X3)))=>X2=X3)))), inference(assume_negation,[status(cth)],[t44_setfam_1])).
% 0.14/0.39  fof(c_0_10, plain, ![X31, X32, X33]:(~r2_hidden(X31,X32)|~m1_subset_1(X32,k1_zfmisc_1(X33))|m1_subset_1(X31,X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.14/0.39  fof(c_0_11, negated_conjecture, ![X37]:(m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(esk6_0)))&(m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(esk6_0)))&(((~r2_hidden(X37,esk7_0)|r2_hidden(X37,esk8_0)|~m1_subset_1(X37,k1_zfmisc_1(esk6_0)))&(~r2_hidden(X37,esk8_0)|r2_hidden(X37,esk7_0)|~m1_subset_1(X37,k1_zfmisc_1(esk6_0))))&esk7_0!=esk8_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])])).
% 0.14/0.39  cnf(c_0_12, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.39  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.39  fof(c_0_15, plain, ![X24, X25]:((m1_subset_1(esk5_2(X24,X25),X24)|X24=X25|~m1_subset_1(X25,k1_zfmisc_1(X24)))&(~r2_hidden(esk5_2(X24,X25),X25)|X24=X25|~m1_subset_1(X25,k1_zfmisc_1(X24)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_subset_1])])])])).
% 0.14/0.39  cnf(c_0_16, negated_conjecture, (r2_hidden(X1,esk7_0)|~r2_hidden(X1,esk8_0)|~m1_subset_1(X1,k1_zfmisc_1(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.39  cnf(c_0_17, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(esk6_0))|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.14/0.39  fof(c_0_18, plain, ![X29, X30]:(~m1_subset_1(X29,X30)|(v1_xboole_0(X30)|r2_hidden(X29,X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.14/0.39  cnf(c_0_19, negated_conjecture, (r2_hidden(X1,esk8_0)|~r2_hidden(X1,esk7_0)|~m1_subset_1(X1,k1_zfmisc_1(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.39  cnf(c_0_20, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(esk6_0))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_12, c_0_14])).
% 0.14/0.39  fof(c_0_21, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.14/0.39  fof(c_0_22, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.14/0.39  fof(c_0_23, plain, ![X15]:(X15=k1_xboole_0|r2_hidden(esk3_1(X15),X15)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.14/0.39  cnf(c_0_24, plain, (X1=X2|~r2_hidden(esk5_2(X1,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.39  cnf(c_0_25, negated_conjecture, (r2_hidden(X1,esk7_0)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.14/0.39  cnf(c_0_26, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.39  cnf(c_0_27, plain, (m1_subset_1(esk5_2(X1,X2),X1)|X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.39  fof(c_0_28, plain, ![X17, X18, X19, X20, X21, X22]:(((~r2_hidden(X19,X18)|r1_tarski(X19,X17)|X18!=k1_zfmisc_1(X17))&(~r1_tarski(X20,X17)|r2_hidden(X20,X18)|X18!=k1_zfmisc_1(X17)))&((~r2_hidden(esk4_2(X21,X22),X22)|~r1_tarski(esk4_2(X21,X22),X21)|X22=k1_zfmisc_1(X21))&(r2_hidden(esk4_2(X21,X22),X22)|r1_tarski(esk4_2(X21,X22),X21)|X22=k1_zfmisc_1(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.14/0.39  cnf(c_0_29, negated_conjecture, (r2_hidden(X1,esk8_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.14/0.39  cnf(c_0_30, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.39  cnf(c_0_31, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.39  cnf(c_0_32, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.39  cnf(c_0_33, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.39  cnf(c_0_34, negated_conjecture, (X1=esk7_0|~m1_subset_1(esk7_0,k1_zfmisc_1(X1))|~r2_hidden(esk5_2(X1,esk7_0),esk8_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.14/0.39  cnf(c_0_35, plain, (X1=X2|r2_hidden(esk5_2(X1,X2),X1)|v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.14/0.39  cnf(c_0_36, negated_conjecture, (esk7_0!=esk8_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.39  cnf(c_0_37, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.14/0.39  cnf(c_0_38, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.39  cnf(c_0_39, negated_conjecture, (r1_tarski(esk7_0,X1)|r2_hidden(esk2_2(esk7_0,X1),esk8_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.14/0.39  cnf(c_0_40, negated_conjecture, (r2_hidden(esk1_1(esk7_0),esk8_0)|v1_xboole_0(esk7_0)), inference(spm,[status(thm)],[c_0_29, c_0_31])).
% 0.14/0.39  cnf(c_0_41, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.14/0.39  cnf(c_0_42, negated_conjecture, (v1_xboole_0(esk8_0)|~m1_subset_1(esk7_0,k1_zfmisc_1(esk8_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 0.14/0.39  fof(c_0_43, plain, ![X27, X28]:(~r2_hidden(X27,X28)|m1_subset_1(X27,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.14/0.39  cnf(c_0_44, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_37])).
% 0.14/0.39  cnf(c_0_45, negated_conjecture, (r1_tarski(esk7_0,esk8_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.14/0.39  cnf(c_0_46, negated_conjecture, (v1_xboole_0(esk7_0)|~v1_xboole_0(esk8_0)), inference(spm,[status(thm)],[c_0_32, c_0_40])).
% 0.14/0.39  cnf(c_0_47, negated_conjecture, (esk8_0=k1_xboole_0|~m1_subset_1(esk7_0,k1_zfmisc_1(esk8_0))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.14/0.39  cnf(c_0_48, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.14/0.39  cnf(c_0_49, negated_conjecture, (r2_hidden(esk7_0,k1_zfmisc_1(esk8_0))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.14/0.39  cnf(c_0_50, negated_conjecture, (esk7_0=k1_xboole_0|~v1_xboole_0(esk8_0)), inference(spm,[status(thm)],[c_0_41, c_0_46])).
% 0.14/0.39  cnf(c_0_51, negated_conjecture, (esk8_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])])).
% 0.14/0.39  cnf(c_0_52, negated_conjecture, (esk7_0=k1_xboole_0|~m1_subset_1(esk7_0,k1_zfmisc_1(esk8_0))), inference(spm,[status(thm)],[c_0_50, c_0_42])).
% 0.14/0.39  cnf(c_0_53, negated_conjecture, (esk7_0!=k1_xboole_0), inference(rw,[status(thm)],[c_0_36, c_0_51])).
% 0.14/0.39  cnf(c_0_54, negated_conjecture, (~m1_subset_1(esk7_0,k1_zfmisc_1(k1_xboole_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_51]), c_0_53])).
% 0.14/0.39  cnf(c_0_55, negated_conjecture, (r1_tarski(esk7_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_45, c_0_51])).
% 0.14/0.39  cnf(c_0_56, negated_conjecture, (~r2_hidden(esk7_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_54, c_0_48])).
% 0.14/0.39  cnf(c_0_57, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_55]), c_0_56]), ['proof']).
% 0.14/0.39  # SZS output end CNFRefutation
% 0.14/0.39  # Proof object total steps             : 58
% 0.14/0.39  # Proof object clause steps            : 39
% 0.14/0.39  # Proof object formula steps           : 19
% 0.14/0.39  # Proof object conjectures             : 28
% 0.14/0.39  # Proof object clause conjectures      : 25
% 0.14/0.39  # Proof object formula conjectures     : 3
% 0.14/0.39  # Proof object initial clauses used    : 16
% 0.14/0.39  # Proof object initial formulas used   : 9
% 0.14/0.39  # Proof object generating inferences   : 19
% 0.14/0.39  # Proof object simplifying inferences  : 9
% 0.14/0.39  # Training examples: 0 positive, 0 negative
% 0.14/0.39  # Parsed axioms                        : 9
% 0.14/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.39  # Initial clauses                      : 20
% 0.14/0.39  # Removed in clause preprocessing      : 0
% 0.14/0.39  # Initial clauses in saturation        : 20
% 0.14/0.39  # Processed clauses                    : 291
% 0.14/0.39  # ...of these trivial                  : 0
% 0.14/0.39  # ...subsumed                          : 109
% 0.14/0.39  # ...remaining for further processing  : 182
% 0.14/0.39  # Other redundant clauses eliminated   : 2
% 0.14/0.39  # Clauses deleted for lack of memory   : 0
% 0.14/0.39  # Backward-subsumed                    : 21
% 0.14/0.39  # Backward-rewritten                   : 77
% 0.14/0.39  # Generated clauses                    : 518
% 0.14/0.39  # ...of the previous two non-trivial   : 554
% 0.14/0.39  # Contextual simplify-reflections      : 2
% 0.14/0.39  # Paramodulations                      : 510
% 0.14/0.39  # Factorizations                       : 0
% 0.14/0.39  # Equation resolutions                 : 2
% 0.14/0.39  # Propositional unsat checks           : 0
% 0.14/0.39  #    Propositional check models        : 0
% 0.14/0.39  #    Propositional check unsatisfiable : 0
% 0.14/0.39  #    Propositional clauses             : 0
% 0.14/0.39  #    Propositional clauses after purity: 0
% 0.14/0.39  #    Propositional unsat core size     : 0
% 0.14/0.39  #    Propositional preprocessing time  : 0.000
% 0.14/0.39  #    Propositional encoding time       : 0.000
% 0.14/0.39  #    Propositional solver time         : 0.000
% 0.14/0.39  #    Success case prop preproc time    : 0.000
% 0.14/0.39  #    Success case prop encoding time   : 0.000
% 0.14/0.39  #    Success case prop solver time     : 0.000
% 0.14/0.39  # Current number of processed clauses  : 76
% 0.14/0.39  #    Positive orientable unit clauses  : 9
% 0.14/0.39  #    Positive unorientable unit clauses: 0
% 0.14/0.39  #    Negative unit clauses             : 4
% 0.14/0.39  #    Non-unit-clauses                  : 63
% 0.14/0.39  # Current number of unprocessed clauses: 270
% 0.14/0.39  # ...number of literals in the above   : 877
% 0.14/0.39  # Current number of archived formulas  : 0
% 0.14/0.39  # Current number of archived clauses   : 104
% 0.14/0.39  # Clause-clause subsumption calls (NU) : 2155
% 0.14/0.39  # Rec. Clause-clause subsumption calls : 1840
% 0.14/0.39  # Non-unit clause-clause subsumptions  : 118
% 0.14/0.39  # Unit Clause-clause subsumption calls : 97
% 0.14/0.39  # Rewrite failures with RHS unbound    : 0
% 0.14/0.39  # BW rewrite match attempts            : 8
% 0.14/0.39  # BW rewrite match successes           : 3
% 0.14/0.39  # Condensation attempts                : 0
% 0.14/0.39  # Condensation successes               : 0
% 0.14/0.39  # Termbank termtop insertions          : 7651
% 0.14/0.39  
% 0.14/0.39  # -------------------------------------------------
% 0.14/0.39  # User time                : 0.046 s
% 0.14/0.39  # System time              : 0.003 s
% 0.14/0.39  # Total time               : 0.049 s
% 0.14/0.39  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
