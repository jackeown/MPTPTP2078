%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:35 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 137 expanded)
%              Number of clauses        :   38 (  61 expanded)
%              Number of leaves         :    6 (  33 expanded)
%              Depth                    :   15
%              Number of atoms          :  151 ( 578 expanded)
%              Number of equality atoms :   10 (  41 expanded)
%              Maximal formula depth    :   11 (   4 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_setfam_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_6,negated_conjecture,(
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

fof(c_0_7,plain,(
    ! [X15,X16] :
      ( ( ~ m1_subset_1(X15,k1_zfmisc_1(X16))
        | r1_tarski(X15,X16) )
      & ( ~ r1_tarski(X15,X16)
        | m1_subset_1(X15,k1_zfmisc_1(X16)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_8,negated_conjecture,(
    ! [X23] :
      ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
      & m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
      & ( ~ r2_hidden(X23,esk3_0)
        | r2_hidden(X23,esk4_0)
        | ~ m1_subset_1(X23,k1_zfmisc_1(esk2_0)) )
      & ( ~ r2_hidden(X23,esk4_0)
        | r2_hidden(X23,esk3_0)
        | ~ m1_subset_1(X23,k1_zfmisc_1(esk2_0)) )
      & esk3_0 != esk4_0 ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])])).

fof(c_0_9,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_10,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X17,X18,X19] :
      ( ~ r2_hidden(X17,X18)
      | ~ m1_subset_1(X18,k1_zfmisc_1(X19))
      | ~ v1_xboole_0(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_13,plain,(
    ! [X13,X14] :
      ( ( ~ m1_subset_1(X14,X13)
        | r2_hidden(X14,X13)
        | v1_xboole_0(X13) )
      & ( ~ r2_hidden(X14,X13)
        | m1_subset_1(X14,X13)
        | v1_xboole_0(X13) )
      & ( ~ m1_subset_1(X14,X13)
        | v1_xboole_0(X14)
        | ~ v1_xboole_0(X13) )
      & ( ~ v1_xboole_0(X14)
        | m1_subset_1(X14,X13)
        | ~ v1_xboole_0(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_14,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(X1,k1_zfmisc_1(esk2_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( ~ v1_xboole_0(k1_zfmisc_1(esk2_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(esk2_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_23,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(X1,esk3_0)
    | v1_xboole_0(esk3_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_22])).

cnf(c_0_25,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_27,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X3)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_23])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk1_2(esk4_0,X1),esk3_0)
    | v1_xboole_0(esk3_0)
    | r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_30,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,esk4_0)
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_22])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_34,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | r2_hidden(esk1_2(esk4_0,X1),esk3_0)
    | r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(X1,k1_zfmisc_1(esk2_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( ~ v1_xboole_0(k1_zfmisc_1(esk2_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | ~ v1_xboole_0(X2)
    | ~ r1_tarski(esk3_0,X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_25])).

cnf(c_0_39,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | r1_tarski(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(esk2_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_36]),c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0)
    | r1_tarski(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_45,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0) ),
    inference(ef,[status(thm)],[c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( esk3_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,X1),esk4_0)
    | r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_25])).

cnf(c_0_49,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_48]),c_0_49]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:50:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.19/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.027 s
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t44_setfam_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>(r2_hidden(X4,X2)<=>r2_hidden(X4,X3)))=>X2=X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_setfam_1)).
% 0.19/0.40  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.40  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.40  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.19/0.40  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.19/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.40  fof(c_0_6, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>(r2_hidden(X4,X2)<=>r2_hidden(X4,X3)))=>X2=X3)))), inference(assume_negation,[status(cth)],[t44_setfam_1])).
% 0.19/0.40  fof(c_0_7, plain, ![X15, X16]:((~m1_subset_1(X15,k1_zfmisc_1(X16))|r1_tarski(X15,X16))&(~r1_tarski(X15,X16)|m1_subset_1(X15,k1_zfmisc_1(X16)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.40  fof(c_0_8, negated_conjecture, ![X23]:(m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))&(m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))&(((~r2_hidden(X23,esk3_0)|r2_hidden(X23,esk4_0)|~m1_subset_1(X23,k1_zfmisc_1(esk2_0)))&(~r2_hidden(X23,esk4_0)|r2_hidden(X23,esk3_0)|~m1_subset_1(X23,k1_zfmisc_1(esk2_0))))&esk3_0!=esk4_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])])).
% 0.19/0.40  fof(c_0_9, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.40  cnf(c_0_10, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.40  cnf(c_0_11, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.40  fof(c_0_12, plain, ![X17, X18, X19]:(~r2_hidden(X17,X18)|~m1_subset_1(X18,k1_zfmisc_1(X19))|~v1_xboole_0(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.19/0.40  fof(c_0_13, plain, ![X13, X14]:(((~m1_subset_1(X14,X13)|r2_hidden(X14,X13)|v1_xboole_0(X13))&(~r2_hidden(X14,X13)|m1_subset_1(X14,X13)|v1_xboole_0(X13)))&((~m1_subset_1(X14,X13)|v1_xboole_0(X14)|~v1_xboole_0(X13))&(~v1_xboole_0(X14)|m1_subset_1(X14,X13)|~v1_xboole_0(X13)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.19/0.40  cnf(c_0_14, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.40  cnf(c_0_15, negated_conjecture, (r1_tarski(esk4_0,k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.19/0.40  cnf(c_0_16, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.40  cnf(c_0_17, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.40  cnf(c_0_18, negated_conjecture, (r2_hidden(X1,k1_zfmisc_1(esk2_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.40  cnf(c_0_19, negated_conjecture, (~v1_xboole_0(k1_zfmisc_1(esk2_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_16, c_0_11])).
% 0.19/0.40  cnf(c_0_20, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.40  cnf(c_0_21, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(esk2_0))|~r2_hidden(X1,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])).
% 0.19/0.40  cnf(c_0_22, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.40  cnf(c_0_23, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.40  cnf(c_0_24, negated_conjecture, (m1_subset_1(X1,esk3_0)|v1_xboole_0(esk3_0)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_17, c_0_22])).
% 0.19/0.40  cnf(c_0_25, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.40  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.40  cnf(c_0_27, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X3)|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_16, c_0_23])).
% 0.19/0.40  cnf(c_0_28, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.40  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk1_2(esk4_0,X1),esk3_0)|v1_xboole_0(esk3_0)|r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.40  fof(c_0_30, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.40  cnf(c_0_31, negated_conjecture, (r1_tarski(esk3_0,k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_10, c_0_26])).
% 0.19/0.40  cnf(c_0_32, negated_conjecture, (~v1_xboole_0(X1)|~r2_hidden(X2,esk4_0)|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_27, c_0_22])).
% 0.19/0.40  cnf(c_0_33, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.40  cnf(c_0_34, negated_conjecture, (v1_xboole_0(esk3_0)|r2_hidden(esk1_2(esk4_0,X1),esk3_0)|r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.40  cnf(c_0_35, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.40  cnf(c_0_36, negated_conjecture, (r2_hidden(X1,k1_zfmisc_1(esk2_0))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_14, c_0_31])).
% 0.19/0.40  cnf(c_0_37, negated_conjecture, (~v1_xboole_0(k1_zfmisc_1(esk2_0))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_16, c_0_26])).
% 0.19/0.40  cnf(c_0_38, negated_conjecture, (r1_tarski(esk4_0,X1)|~v1_xboole_0(X2)|~r1_tarski(esk3_0,X2)), inference(spm,[status(thm)],[c_0_32, c_0_25])).
% 0.19/0.40  cnf(c_0_39, negated_conjecture, (v1_xboole_0(esk3_0)|r1_tarski(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.40  cnf(c_0_40, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_35])).
% 0.19/0.40  cnf(c_0_41, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.40  cnf(c_0_42, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(esk2_0))|~r2_hidden(X1,esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_36]), c_0_37])).
% 0.19/0.40  cnf(c_0_43, negated_conjecture, (r1_tarski(esk4_0,esk3_0)|r1_tarski(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])])).
% 0.19/0.40  cnf(c_0_44, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.40  cnf(c_0_45, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.40  cnf(c_0_46, negated_conjecture, (r1_tarski(esk4_0,esk3_0)), inference(ef,[status(thm)],[c_0_43])).
% 0.19/0.40  cnf(c_0_47, negated_conjecture, (esk3_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.40  cnf(c_0_48, negated_conjecture, (r2_hidden(esk1_2(esk3_0,X1),esk4_0)|r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_44, c_0_25])).
% 0.19/0.40  cnf(c_0_49, negated_conjecture, (~r1_tarski(esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])).
% 0.19/0.40  cnf(c_0_50, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_48]), c_0_49]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 51
% 0.19/0.40  # Proof object clause steps            : 38
% 0.19/0.40  # Proof object formula steps           : 13
% 0.19/0.40  # Proof object conjectures             : 29
% 0.19/0.40  # Proof object clause conjectures      : 26
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 15
% 0.19/0.40  # Proof object initial formulas used   : 6
% 0.19/0.40  # Proof object generating inferences   : 22
% 0.19/0.40  # Proof object simplifying inferences  : 7
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 6
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 18
% 0.19/0.40  # Removed in clause preprocessing      : 0
% 0.19/0.40  # Initial clauses in saturation        : 18
% 0.19/0.40  # Processed clauses                    : 473
% 0.19/0.40  # ...of these trivial                  : 1
% 0.19/0.40  # ...subsumed                          : 236
% 0.19/0.40  # ...remaining for further processing  : 236
% 0.19/0.40  # Other redundant clauses eliminated   : 2
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 79
% 0.19/0.40  # Backward-rewritten                   : 45
% 0.19/0.40  # Generated clauses                    : 1124
% 0.19/0.40  # ...of the previous two non-trivial   : 1054
% 0.19/0.40  # Contextual simplify-reflections      : 11
% 0.19/0.40  # Paramodulations                      : 1112
% 0.19/0.40  # Factorizations                       : 8
% 0.19/0.40  # Equation resolutions                 : 2
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 108
% 0.19/0.40  #    Positive orientable unit clauses  : 10
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 3
% 0.19/0.40  #    Non-unit-clauses                  : 95
% 0.19/0.40  # Current number of unprocessed clauses: 542
% 0.19/0.40  # ...number of literals in the above   : 1925
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 126
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 1894
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 1328
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 308
% 0.19/0.40  # Unit Clause-clause subsumption calls : 94
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 5
% 0.19/0.40  # BW rewrite match successes           : 5
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 13580
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.056 s
% 0.19/0.40  # System time              : 0.010 s
% 0.19/0.40  # Total time               : 0.067 s
% 0.19/0.40  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
