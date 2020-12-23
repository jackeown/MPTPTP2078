%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:04 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   39 (  95 expanded)
%              Number of clauses        :   24 (  44 expanded)
%              Number of leaves         :    7 (  22 expanded)
%              Depth                    :    9
%              Number of atoms          :  139 ( 440 expanded)
%              Number of equality atoms :   20 (  56 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => ( r2_hidden(X4,X2)
                 => r2_hidden(X4,X3) ) )
           => r1_tarski(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( ! [X4] :
                  ( m1_subset_1(X4,X1)
                 => ( r2_hidden(X4,X2)
                   => r2_hidden(X4,X3) ) )
             => r1_tarski(X2,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t7_subset_1])).

fof(c_0_8,plain,(
    ! [X23,X24] :
      ( ( ~ m1_subset_1(X24,X23)
        | r2_hidden(X24,X23)
        | v1_xboole_0(X23) )
      & ( ~ r2_hidden(X24,X23)
        | m1_subset_1(X24,X23)
        | v1_xboole_0(X23) )
      & ( ~ m1_subset_1(X24,X23)
        | v1_xboole_0(X24)
        | ~ v1_xboole_0(X23) )
      & ( ~ v1_xboole_0(X24)
        | m1_subset_1(X24,X23)
        | ~ v1_xboole_0(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_9,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_10,plain,(
    ! [X25,X26,X27] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(X25))
      | ~ r2_hidden(X27,X26)
      | r2_hidden(X27,X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_11,negated_conjecture,(
    ! [X31] :
      ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))
      & m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))
      & ( ~ m1_subset_1(X31,esk3_0)
        | ~ r2_hidden(X31,esk4_0)
        | r2_hidden(X31,esk5_0) )
      & ~ r1_tarski(esk4_0,esk5_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).

fof(c_0_12,plain,(
    ! [X9,X10,X11,X12,X13,X14,X15,X16] :
      ( ( ~ r2_hidden(X12,X11)
        | r2_hidden(X12,X9)
        | r2_hidden(X12,X10)
        | X11 != k2_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X13,X9)
        | r2_hidden(X13,X11)
        | X11 != k2_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X13,X10)
        | r2_hidden(X13,X11)
        | X11 != k2_xboole_0(X9,X10) )
      & ( ~ r2_hidden(esk2_3(X14,X15,X16),X14)
        | ~ r2_hidden(esk2_3(X14,X15,X16),X16)
        | X16 = k2_xboole_0(X14,X15) )
      & ( ~ r2_hidden(esk2_3(X14,X15,X16),X15)
        | ~ r2_hidden(esk2_3(X14,X15,X16),X16)
        | X16 = k2_xboole_0(X14,X15) )
      & ( r2_hidden(esk2_3(X14,X15,X16),X16)
        | r2_hidden(esk2_3(X14,X15,X16),X14)
        | r2_hidden(esk2_3(X14,X15,X16),X15)
        | X16 = k2_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_13,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X2)
    | X3 = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ m1_subset_1(X1,esk3_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,X2) = X2
    | r2_hidden(esk2_3(X1,X2,X2),X2)
    | r2_hidden(esk2_3(X1,X2,X2),X1) ),
    inference(ef,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X18,X19] :
      ( ( r1_tarski(X18,X19)
        | X18 != X19 )
      & ( r1_tarski(X19,X18)
        | X18 != X19 )
      & ( ~ r1_tarski(X18,X19)
        | ~ r1_tarski(X19,X18)
        | X18 = X19 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( k2_xboole_0(esk4_0,X1) = X1
    | r2_hidden(esk2_3(esk4_0,X1,X1),esk3_0)
    | r2_hidden(esk2_3(esk4_0,X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_27,plain,(
    ! [X20,X21,X22] :
      ( ~ r1_tarski(k2_xboole_0(X20,X21),X22)
      | r1_tarski(X20,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( X1 = k2_xboole_0(esk4_0,X2)
    | r2_hidden(esk2_3(esk4_0,X2,X1),esk5_0)
    | r2_hidden(esk2_3(esk4_0,X2,X1),X1)
    | r2_hidden(esk2_3(esk4_0,X2,X1),X2)
    | ~ r2_hidden(esk2_3(esk4_0,X2,X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_17])).

cnf(c_0_30,negated_conjecture,
    ( k2_xboole_0(esk4_0,esk5_0) = esk5_0
    | r2_hidden(esk2_3(esk4_0,esk5_0,esk5_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_34,negated_conjecture,
    ( k2_xboole_0(esk4_0,esk5_0) = esk5_0
    | r2_hidden(esk2_3(esk4_0,esk5_0,esk5_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( k2_xboole_0(esk4_0,esk5_0) = esk5_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( ~ r1_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:23:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.50  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.20/0.50  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.50  #
% 0.20/0.50  # Preprocessing time       : 0.028 s
% 0.20/0.50  
% 0.20/0.50  # Proof found!
% 0.20/0.50  # SZS status Theorem
% 0.20/0.50  # SZS output start CNFRefutation
% 0.20/0.50  fof(t7_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,X2)=>r2_hidden(X4,X3)))=>r1_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_subset_1)).
% 0.20/0.50  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.20/0.50  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.50  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.20/0.50  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.20/0.50  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.50  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.20/0.50  fof(c_0_7, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,X2)=>r2_hidden(X4,X3)))=>r1_tarski(X2,X3))))), inference(assume_negation,[status(cth)],[t7_subset_1])).
% 0.20/0.50  fof(c_0_8, plain, ![X23, X24]:(((~m1_subset_1(X24,X23)|r2_hidden(X24,X23)|v1_xboole_0(X23))&(~r2_hidden(X24,X23)|m1_subset_1(X24,X23)|v1_xboole_0(X23)))&((~m1_subset_1(X24,X23)|v1_xboole_0(X24)|~v1_xboole_0(X23))&(~v1_xboole_0(X24)|m1_subset_1(X24,X23)|~v1_xboole_0(X23)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.20/0.50  fof(c_0_9, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.50  fof(c_0_10, plain, ![X25, X26, X27]:(~m1_subset_1(X26,k1_zfmisc_1(X25))|(~r2_hidden(X27,X26)|r2_hidden(X27,X25))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.20/0.50  fof(c_0_11, negated_conjecture, ![X31]:(m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))&((~m1_subset_1(X31,esk3_0)|(~r2_hidden(X31,esk4_0)|r2_hidden(X31,esk5_0)))&~r1_tarski(esk4_0,esk5_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).
% 0.20/0.50  fof(c_0_12, plain, ![X9, X10, X11, X12, X13, X14, X15, X16]:(((~r2_hidden(X12,X11)|(r2_hidden(X12,X9)|r2_hidden(X12,X10))|X11!=k2_xboole_0(X9,X10))&((~r2_hidden(X13,X9)|r2_hidden(X13,X11)|X11!=k2_xboole_0(X9,X10))&(~r2_hidden(X13,X10)|r2_hidden(X13,X11)|X11!=k2_xboole_0(X9,X10))))&(((~r2_hidden(esk2_3(X14,X15,X16),X14)|~r2_hidden(esk2_3(X14,X15,X16),X16)|X16=k2_xboole_0(X14,X15))&(~r2_hidden(esk2_3(X14,X15,X16),X15)|~r2_hidden(esk2_3(X14,X15,X16),X16)|X16=k2_xboole_0(X14,X15)))&(r2_hidden(esk2_3(X14,X15,X16),X16)|(r2_hidden(esk2_3(X14,X15,X16),X14)|r2_hidden(esk2_3(X14,X15,X16),X15))|X16=k2_xboole_0(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.20/0.50  cnf(c_0_13, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.50  cnf(c_0_14, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.50  cnf(c_0_15, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.50  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.50  cnf(c_0_17, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X2)|X3=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.50  cnf(c_0_18, negated_conjecture, (r2_hidden(X1,esk5_0)|~m1_subset_1(X1,esk3_0)|~r2_hidden(X1,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.50  cnf(c_0_19, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_13, c_0_14])).
% 0.20/0.50  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.50  cnf(c_0_21, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.20/0.50  cnf(c_0_22, plain, (k2_xboole_0(X1,X2)=X2|r2_hidden(esk2_3(X1,X2,X2),X2)|r2_hidden(esk2_3(X1,X2,X2),X1)), inference(ef,[status(thm)],[c_0_17])).
% 0.20/0.50  fof(c_0_23, plain, ![X18, X19]:(((r1_tarski(X18,X19)|X18!=X19)&(r1_tarski(X19,X18)|X18!=X19))&(~r1_tarski(X18,X19)|~r1_tarski(X19,X18)|X18=X19)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.50  cnf(c_0_24, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.50  cnf(c_0_25, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_15, c_0_20])).
% 0.20/0.50  cnf(c_0_26, negated_conjecture, (k2_xboole_0(esk4_0,X1)=X1|r2_hidden(esk2_3(esk4_0,X1,X1),esk3_0)|r2_hidden(esk2_3(esk4_0,X1,X1),X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.50  fof(c_0_27, plain, ![X20, X21, X22]:(~r1_tarski(k2_xboole_0(X20,X21),X22)|r1_tarski(X20,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.20/0.50  cnf(c_0_28, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.50  cnf(c_0_29, negated_conjecture, (X1=k2_xboole_0(esk4_0,X2)|r2_hidden(esk2_3(esk4_0,X2,X1),esk5_0)|r2_hidden(esk2_3(esk4_0,X2,X1),X1)|r2_hidden(esk2_3(esk4_0,X2,X1),X2)|~r2_hidden(esk2_3(esk4_0,X2,X1),esk3_0)), inference(spm,[status(thm)],[c_0_24, c_0_17])).
% 0.20/0.50  cnf(c_0_30, negated_conjecture, (k2_xboole_0(esk4_0,esk5_0)=esk5_0|r2_hidden(esk2_3(esk4_0,esk5_0,esk5_0),esk3_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.50  cnf(c_0_31, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.50  cnf(c_0_32, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_28])).
% 0.20/0.50  cnf(c_0_33, plain, (X3=k2_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.50  cnf(c_0_34, negated_conjecture, (k2_xboole_0(esk4_0,esk5_0)=esk5_0|r2_hidden(esk2_3(esk4_0,esk5_0,esk5_0),esk5_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.50  cnf(c_0_35, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.50  cnf(c_0_36, negated_conjecture, (k2_xboole_0(esk4_0,esk5_0)=esk5_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_34])).
% 0.20/0.50  cnf(c_0_37, negated_conjecture, (~r1_tarski(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.50  cnf(c_0_38, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), ['proof']).
% 0.20/0.50  # SZS output end CNFRefutation
% 0.20/0.50  # Proof object total steps             : 39
% 0.20/0.50  # Proof object clause steps            : 24
% 0.20/0.50  # Proof object formula steps           : 15
% 0.20/0.50  # Proof object conjectures             : 16
% 0.20/0.50  # Proof object clause conjectures      : 13
% 0.20/0.50  # Proof object formula conjectures     : 3
% 0.20/0.50  # Proof object initial clauses used    : 11
% 0.20/0.50  # Proof object initial formulas used   : 7
% 0.20/0.50  # Proof object generating inferences   : 11
% 0.20/0.50  # Proof object simplifying inferences  : 4
% 0.20/0.50  # Training examples: 0 positive, 0 negative
% 0.20/0.50  # Parsed axioms                        : 7
% 0.20/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.50  # Initial clauses                      : 21
% 0.20/0.50  # Removed in clause preprocessing      : 0
% 0.20/0.50  # Initial clauses in saturation        : 21
% 0.20/0.50  # Processed clauses                    : 1424
% 0.20/0.50  # ...of these trivial                  : 8
% 0.20/0.50  # ...subsumed                          : 1014
% 0.20/0.50  # ...remaining for further processing  : 402
% 0.20/0.50  # Other redundant clauses eliminated   : 5
% 0.20/0.50  # Clauses deleted for lack of memory   : 0
% 0.20/0.50  # Backward-subsumed                    : 20
% 0.20/0.50  # Backward-rewritten                   : 65
% 0.20/0.50  # Generated clauses                    : 6905
% 0.20/0.50  # ...of the previous two non-trivial   : 6131
% 0.20/0.50  # Contextual simplify-reflections      : 20
% 0.20/0.50  # Paramodulations                      : 6728
% 0.20/0.50  # Factorizations                       : 168
% 0.20/0.50  # Equation resolutions                 : 5
% 0.20/0.50  # Propositional unsat checks           : 0
% 0.20/0.50  #    Propositional check models        : 0
% 0.20/0.50  #    Propositional check unsatisfiable : 0
% 0.20/0.50  #    Propositional clauses             : 0
% 0.20/0.50  #    Propositional clauses after purity: 0
% 0.20/0.50  #    Propositional unsat core size     : 0
% 0.20/0.50  #    Propositional preprocessing time  : 0.000
% 0.20/0.50  #    Propositional encoding time       : 0.000
% 0.20/0.50  #    Propositional solver time         : 0.000
% 0.20/0.50  #    Success case prop preproc time    : 0.000
% 0.20/0.50  #    Success case prop encoding time   : 0.000
% 0.20/0.50  #    Success case prop solver time     : 0.000
% 0.20/0.50  # Current number of processed clauses  : 308
% 0.20/0.50  #    Positive orientable unit clauses  : 35
% 0.20/0.50  #    Positive unorientable unit clauses: 0
% 0.20/0.50  #    Negative unit clauses             : 5
% 0.20/0.50  #    Non-unit-clauses                  : 268
% 0.20/0.50  # Current number of unprocessed clauses: 4666
% 0.20/0.50  # ...number of literals in the above   : 24154
% 0.20/0.50  # Current number of archived formulas  : 0
% 0.20/0.50  # Current number of archived clauses   : 89
% 0.20/0.50  # Clause-clause subsumption calls (NU) : 14243
% 0.20/0.50  # Rec. Clause-clause subsumption calls : 6699
% 0.20/0.50  # Non-unit clause-clause subsumptions  : 528
% 0.20/0.50  # Unit Clause-clause subsumption calls : 572
% 0.20/0.50  # Rewrite failures with RHS unbound    : 0
% 0.20/0.50  # BW rewrite match attempts            : 88
% 0.20/0.50  # BW rewrite match successes           : 13
% 0.20/0.50  # Condensation attempts                : 0
% 0.20/0.50  # Condensation successes               : 0
% 0.20/0.50  # Termbank termtop insertions          : 156026
% 0.20/0.50  
% 0.20/0.50  # -------------------------------------------------
% 0.20/0.50  # User time                : 0.160 s
% 0.20/0.50  # System time              : 0.009 s
% 0.20/0.50  # Total time               : 0.169 s
% 0.20/0.50  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
