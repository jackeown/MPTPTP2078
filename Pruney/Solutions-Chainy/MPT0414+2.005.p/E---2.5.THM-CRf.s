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
% DateTime   : Thu Dec  3 10:47:36 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   36 (  74 expanded)
%              Number of clauses        :   25 (  33 expanded)
%              Number of leaves         :    5 (  18 expanded)
%              Depth                    :   10
%              Number of atoms          :  100 ( 282 expanded)
%              Number of equality atoms :    9 (  21 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    9 (   2 average)
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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_5,negated_conjecture,(
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

fof(c_0_6,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_7,plain,(
    ! [X15,X16] :
      ( ( ~ m1_subset_1(X15,k1_zfmisc_1(X16))
        | r1_tarski(X15,X16) )
      & ( ~ r1_tarski(X15,X16)
        | m1_subset_1(X15,k1_zfmisc_1(X16)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_8,negated_conjecture,(
    ! [X20] :
      ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
      & m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
      & ( ~ r2_hidden(X20,esk3_0)
        | r2_hidden(X20,esk4_0)
        | ~ m1_subset_1(X20,k1_zfmisc_1(esk2_0)) )
      & ( ~ r2_hidden(X20,esk4_0)
        | r2_hidden(X20,esk3_0)
        | ~ m1_subset_1(X20,k1_zfmisc_1(esk2_0)) )
      & esk3_0 != esk4_0 ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])])).

cnf(c_0_9,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,plain,(
    ! [X13,X14] :
      ( ~ r2_hidden(X13,X14)
      | m1_subset_1(X13,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_14,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,X1),k1_zfmisc_1(esk2_0))
    | r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,X1),esk3_0)
    | r1_tarski(esk4_0,X1)
    | ~ m1_subset_1(esk1_2(esk4_0,X1),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk1_2(esk4_0,X1),k1_zfmisc_1(esk2_0))
    | r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,X1),k1_zfmisc_1(esk2_0))
    | r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_20])).

fof(c_0_25,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,X1),esk3_0)
    | r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,X1),esk4_0)
    | r1_tarski(esk3_0,X1)
    | ~ m1_subset_1(esk1_2(esk3_0,X1),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_10])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk1_2(esk3_0,X1),k1_zfmisc_1(esk2_0))
    | r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_24])).

cnf(c_0_30,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( esk3_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,X1),esk4_0)
    | r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_33]),c_0_34]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:13:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00DA
% 0.13/0.37  # and selection function SelectSmallestOrientable.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.026 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t44_setfam_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>(r2_hidden(X4,X2)<=>r2_hidden(X4,X3)))=>X2=X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_setfam_1)).
% 0.13/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.37  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.37  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.13/0.37  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.37  fof(c_0_5, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>(r2_hidden(X4,X2)<=>r2_hidden(X4,X3)))=>X2=X3)))), inference(assume_negation,[status(cth)],[t44_setfam_1])).
% 0.13/0.37  fof(c_0_6, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.37  fof(c_0_7, plain, ![X15, X16]:((~m1_subset_1(X15,k1_zfmisc_1(X16))|r1_tarski(X15,X16))&(~r1_tarski(X15,X16)|m1_subset_1(X15,k1_zfmisc_1(X16)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.37  fof(c_0_8, negated_conjecture, ![X20]:(m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))&(m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))&(((~r2_hidden(X20,esk3_0)|r2_hidden(X20,esk4_0)|~m1_subset_1(X20,k1_zfmisc_1(esk2_0)))&(~r2_hidden(X20,esk4_0)|r2_hidden(X20,esk3_0)|~m1_subset_1(X20,k1_zfmisc_1(esk2_0))))&esk3_0!=esk4_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])])).
% 0.13/0.37  cnf(c_0_9, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_10, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_11, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  fof(c_0_13, plain, ![X13, X14]:(~r2_hidden(X13,X14)|m1_subset_1(X13,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.13/0.37  cnf(c_0_14, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.13/0.37  cnf(c_0_15, negated_conjecture, (r1_tarski(esk4_0,k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.13/0.37  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_17, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_18, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_19, negated_conjecture, (r2_hidden(esk1_2(esk4_0,X1),k1_zfmisc_1(esk2_0))|r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.13/0.37  cnf(c_0_20, negated_conjecture, (r1_tarski(esk3_0,k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_11, c_0_16])).
% 0.13/0.37  cnf(c_0_21, negated_conjecture, (r2_hidden(esk1_2(esk4_0,X1),esk3_0)|r1_tarski(esk4_0,X1)|~m1_subset_1(esk1_2(esk4_0,X1),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_17, c_0_10])).
% 0.13/0.37  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk1_2(esk4_0,X1),k1_zfmisc_1(esk2_0))|r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.13/0.37  cnf(c_0_23, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_24, negated_conjecture, (r2_hidden(esk1_2(esk3_0,X1),k1_zfmisc_1(esk2_0))|r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_14, c_0_20])).
% 0.13/0.37  fof(c_0_25, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.37  cnf(c_0_26, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_27, negated_conjecture, (r2_hidden(esk1_2(esk4_0,X1),esk3_0)|r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.13/0.37  cnf(c_0_28, negated_conjecture, (r2_hidden(esk1_2(esk3_0,X1),esk4_0)|r1_tarski(esk3_0,X1)|~m1_subset_1(esk1_2(esk3_0,X1),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_23, c_0_10])).
% 0.13/0.37  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk1_2(esk3_0,X1),k1_zfmisc_1(esk2_0))|r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_18, c_0_24])).
% 0.13/0.37  cnf(c_0_30, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.37  cnf(c_0_31, negated_conjecture, (r1_tarski(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.13/0.37  cnf(c_0_32, negated_conjecture, (esk3_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_33, negated_conjecture, (r2_hidden(esk1_2(esk3_0,X1),esk4_0)|r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.37  cnf(c_0_34, negated_conjecture, (~r1_tarski(esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 0.13/0.37  cnf(c_0_35, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_33]), c_0_34]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 36
% 0.13/0.37  # Proof object clause steps            : 25
% 0.13/0.37  # Proof object formula steps           : 11
% 0.13/0.37  # Proof object conjectures             : 21
% 0.13/0.37  # Proof object clause conjectures      : 18
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 11
% 0.13/0.37  # Proof object initial formulas used   : 5
% 0.13/0.37  # Proof object generating inferences   : 14
% 0.13/0.37  # Proof object simplifying inferences  : 2
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 5
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 14
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 14
% 0.13/0.37  # Processed clauses                    : 57
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 4
% 0.13/0.37  # ...remaining for further processing  : 53
% 0.13/0.37  # Other redundant clauses eliminated   : 2
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 2
% 0.13/0.37  # Backward-rewritten                   : 0
% 0.13/0.37  # Generated clauses                    : 51
% 0.13/0.37  # ...of the previous two non-trivial   : 42
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 49
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 2
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 36
% 0.13/0.37  #    Positive orientable unit clauses  : 8
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 2
% 0.13/0.37  #    Non-unit-clauses                  : 26
% 0.13/0.37  # Current number of unprocessed clauses: 9
% 0.13/0.37  # ...number of literals in the above   : 22
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 15
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 65
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 53
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 6
% 0.13/0.37  # Unit Clause-clause subsumption calls : 3
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 4
% 0.13/0.37  # BW rewrite match successes           : 0
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 1609
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.029 s
% 0.13/0.37  # System time              : 0.003 s
% 0.13/0.37  # Total time               : 0.032 s
% 0.13/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
