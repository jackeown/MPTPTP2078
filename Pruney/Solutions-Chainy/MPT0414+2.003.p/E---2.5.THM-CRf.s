%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:35 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 214 expanded)
%              Number of clauses        :   31 (  95 expanded)
%              Number of leaves         :    6 (  54 expanded)
%              Depth                    :   15
%              Number of atoms          :  123 ( 782 expanded)
%              Number of equality atoms :   10 (  53 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

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

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_6,plain,(
    ! [X16,X17] :
      ( ( ~ m1_subset_1(X16,k1_zfmisc_1(X17))
        | r1_tarski(X16,X17) )
      & ( ~ r1_tarski(X16,X17)
        | m1_subset_1(X16,k1_zfmisc_1(X17)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_7,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_8,negated_conjecture,(
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

cnf(c_0_9,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,negated_conjecture,(
    ! [X21] :
      ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
      & m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
      & ( ~ r2_hidden(X21,esk3_0)
        | r2_hidden(X21,esk4_0)
        | ~ m1_subset_1(X21,k1_zfmisc_1(esk2_0)) )
      & ( ~ r2_hidden(X21,esk4_0)
        | r2_hidden(X21,esk3_0)
        | ~ m1_subset_1(X21,k1_zfmisc_1(esk2_0)) )
      & esk3_0 != esk4_0 ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])])).

cnf(c_0_12,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | r2_hidden(esk1_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
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

cnf(c_0_17,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_19,plain,(
    ! [X15] : ~ v1_xboole_0(k1_zfmisc_1(X15)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(X1))
    | r2_hidden(esk1_2(esk4_0,X1),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(X1))
    | r2_hidden(esk1_2(esk4_0,X1),esk3_0)
    | ~ m1_subset_1(esk1_2(esk4_0,X1),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk1_2(esk4_0,X1),k1_zfmisc_1(esk2_0))
    | m1_subset_1(esk4_0,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

fof(c_0_26,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(X1))
    | r2_hidden(esk1_2(esk4_0,X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_9])).

cnf(c_0_31,plain,
    ( X1 = X2
    | r2_hidden(esk1_2(X2,X1),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_10])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( esk3_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,esk4_0),X1)
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,esk4_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk1_2(esk3_0,esk4_0),k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_38]),c_0_23])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_34]),c_0_40])])).

cnf(c_0_42,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_32]),c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_41]),c_0_42]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:35:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.42  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00DA
% 0.20/0.42  # and selection function SelectSmallestOrientable.
% 0.20/0.42  #
% 0.20/0.42  # Preprocessing time       : 0.027 s
% 0.20/0.42  # Presaturation interreduction done
% 0.20/0.42  
% 0.20/0.42  # Proof found!
% 0.20/0.42  # SZS status Theorem
% 0.20/0.42  # SZS output start CNFRefutation
% 0.20/0.42  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.42  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.42  fof(t44_setfam_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>(r2_hidden(X4,X2)<=>r2_hidden(X4,X3)))=>X2=X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_setfam_1)).
% 0.20/0.42  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.20/0.42  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.20/0.42  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.42  fof(c_0_6, plain, ![X16, X17]:((~m1_subset_1(X16,k1_zfmisc_1(X17))|r1_tarski(X16,X17))&(~r1_tarski(X16,X17)|m1_subset_1(X16,k1_zfmisc_1(X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.42  fof(c_0_7, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.42  fof(c_0_8, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>(r2_hidden(X4,X2)<=>r2_hidden(X4,X3)))=>X2=X3)))), inference(assume_negation,[status(cth)],[t44_setfam_1])).
% 0.20/0.42  cnf(c_0_9, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.42  cnf(c_0_10, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.42  fof(c_0_11, negated_conjecture, ![X21]:(m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))&(m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))&(((~r2_hidden(X21,esk3_0)|r2_hidden(X21,esk4_0)|~m1_subset_1(X21,k1_zfmisc_1(esk2_0)))&(~r2_hidden(X21,esk4_0)|r2_hidden(X21,esk3_0)|~m1_subset_1(X21,k1_zfmisc_1(esk2_0))))&esk3_0!=esk4_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])])).
% 0.20/0.42  cnf(c_0_12, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.42  cnf(c_0_13, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|r2_hidden(esk1_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.20/0.42  cnf(c_0_14, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.42  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.42  fof(c_0_16, plain, ![X13, X14]:(((~m1_subset_1(X14,X13)|r2_hidden(X14,X13)|v1_xboole_0(X13))&(~r2_hidden(X14,X13)|m1_subset_1(X14,X13)|v1_xboole_0(X13)))&((~m1_subset_1(X14,X13)|v1_xboole_0(X14)|~v1_xboole_0(X13))&(~v1_xboole_0(X14)|m1_subset_1(X14,X13)|~v1_xboole_0(X13)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.20/0.42  cnf(c_0_17, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|r2_hidden(esk1_2(X1,X2),X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.20/0.42  cnf(c_0_18, negated_conjecture, (r1_tarski(esk4_0,k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.42  fof(c_0_19, plain, ![X15]:~v1_xboole_0(k1_zfmisc_1(X15)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.20/0.42  cnf(c_0_20, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.42  cnf(c_0_21, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.42  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(X1))|r2_hidden(esk1_2(esk4_0,X1),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.42  cnf(c_0_23, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.42  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(X1))|r2_hidden(esk1_2(esk4_0,X1),esk3_0)|~m1_subset_1(esk1_2(esk4_0,X1),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_20, c_0_13])).
% 0.20/0.42  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk1_2(esk4_0,X1),k1_zfmisc_1(esk2_0))|m1_subset_1(esk4_0,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])).
% 0.20/0.42  fof(c_0_26, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.42  cnf(c_0_27, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.42  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(X1))|r2_hidden(esk1_2(esk4_0,X1),esk3_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.42  cnf(c_0_29, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.42  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_9])).
% 0.20/0.42  cnf(c_0_31, plain, (X1=X2|r2_hidden(esk1_2(X2,X1),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_29, c_0_10])).
% 0.20/0.42  cnf(c_0_32, negated_conjecture, (r1_tarski(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_14, c_0_30])).
% 0.20/0.42  cnf(c_0_33, negated_conjecture, (esk3_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.42  cnf(c_0_34, negated_conjecture, (r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])).
% 0.20/0.42  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.42  cnf(c_0_36, negated_conjecture, (r2_hidden(esk1_2(esk3_0,esk4_0),X1)|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_12, c_0_34])).
% 0.20/0.42  cnf(c_0_37, negated_conjecture, (r1_tarski(esk3_0,k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_14, c_0_35])).
% 0.20/0.42  cnf(c_0_38, negated_conjecture, (r2_hidden(esk1_2(esk3_0,esk4_0),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.42  cnf(c_0_39, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.42  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk1_2(esk3_0,esk4_0),k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_38]), c_0_23])).
% 0.20/0.42  cnf(c_0_41, negated_conjecture, (r2_hidden(esk1_2(esk3_0,esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_34]), c_0_40])])).
% 0.20/0.42  cnf(c_0_42, negated_conjecture, (~r1_tarski(esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_32]), c_0_33])).
% 0.20/0.42  cnf(c_0_43, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_41]), c_0_42]), ['proof']).
% 0.20/0.42  # SZS output end CNFRefutation
% 0.20/0.42  # Proof object total steps             : 44
% 0.20/0.42  # Proof object clause steps            : 31
% 0.20/0.42  # Proof object formula steps           : 13
% 0.20/0.42  # Proof object conjectures             : 23
% 0.20/0.42  # Proof object clause conjectures      : 20
% 0.20/0.42  # Proof object formula conjectures     : 3
% 0.20/0.42  # Proof object initial clauses used    : 13
% 0.20/0.42  # Proof object initial formulas used   : 6
% 0.20/0.42  # Proof object generating inferences   : 18
% 0.20/0.42  # Proof object simplifying inferences  : 8
% 0.20/0.42  # Training examples: 0 positive, 0 negative
% 0.20/0.42  # Parsed axioms                        : 6
% 0.20/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.42  # Initial clauses                      : 18
% 0.20/0.42  # Removed in clause preprocessing      : 0
% 0.20/0.42  # Initial clauses in saturation        : 18
% 0.20/0.42  # Processed clauses                    : 484
% 0.20/0.42  # ...of these trivial                  : 1
% 0.20/0.42  # ...subsumed                          : 157
% 0.20/0.42  # ...remaining for further processing  : 326
% 0.20/0.42  # Other redundant clauses eliminated   : 2
% 0.20/0.42  # Clauses deleted for lack of memory   : 0
% 0.20/0.42  # Backward-subsumed                    : 36
% 0.20/0.42  # Backward-rewritten                   : 33
% 0.20/0.42  # Generated clauses                    : 2282
% 0.20/0.42  # ...of the previous two non-trivial   : 2085
% 0.20/0.42  # Contextual simplify-reflections      : 1
% 0.20/0.42  # Paramodulations                      : 2274
% 0.20/0.42  # Factorizations                       : 4
% 0.20/0.42  # Equation resolutions                 : 2
% 0.20/0.42  # Propositional unsat checks           : 0
% 0.20/0.42  #    Propositional check models        : 0
% 0.20/0.42  #    Propositional check unsatisfiable : 0
% 0.20/0.42  #    Propositional clauses             : 0
% 0.20/0.42  #    Propositional clauses after purity: 0
% 0.20/0.42  #    Propositional unsat core size     : 0
% 0.20/0.42  #    Propositional preprocessing time  : 0.000
% 0.20/0.42  #    Propositional encoding time       : 0.000
% 0.20/0.42  #    Propositional solver time         : 0.000
% 0.20/0.42  #    Success case prop preproc time    : 0.000
% 0.20/0.42  #    Success case prop encoding time   : 0.000
% 0.20/0.42  #    Success case prop solver time     : 0.000
% 0.20/0.42  # Current number of processed clauses  : 236
% 0.20/0.42  #    Positive orientable unit clauses  : 19
% 0.20/0.42  #    Positive unorientable unit clauses: 0
% 0.20/0.42  #    Negative unit clauses             : 3
% 0.20/0.42  #    Non-unit-clauses                  : 214
% 0.20/0.42  # Current number of unprocessed clauses: 1632
% 0.20/0.42  # ...number of literals in the above   : 5862
% 0.20/0.42  # Current number of archived formulas  : 0
% 0.20/0.42  # Current number of archived clauses   : 88
% 0.20/0.42  # Clause-clause subsumption calls (NU) : 6331
% 0.20/0.42  # Rec. Clause-clause subsumption calls : 3151
% 0.20/0.42  # Non-unit clause-clause subsumptions  : 178
% 0.20/0.42  # Unit Clause-clause subsumption calls : 634
% 0.20/0.42  # Rewrite failures with RHS unbound    : 0
% 0.20/0.42  # BW rewrite match attempts            : 14
% 0.20/0.42  # BW rewrite match successes           : 8
% 0.20/0.42  # Condensation attempts                : 0
% 0.20/0.42  # Condensation successes               : 0
% 0.20/0.42  # Termbank termtop insertions          : 36075
% 0.20/0.42  
% 0.20/0.42  # -------------------------------------------------
% 0.20/0.42  # User time                : 0.076 s
% 0.20/0.42  # System time              : 0.007 s
% 0.20/0.42  # Total time               : 0.083 s
% 0.20/0.42  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
