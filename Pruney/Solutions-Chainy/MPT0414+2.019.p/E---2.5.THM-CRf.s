%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:37 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   26 ( 180 expanded)
%              Number of clauses        :   21 (  69 expanded)
%              Number of leaves         :    2 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :  118 (1132 expanded)
%              Number of equality atoms :   21 ( 175 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    3 (   2 average)

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

fof(t15_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ! [X4] :
              ( m1_subset_1(X4,k1_zfmisc_1(X1))
             => ( ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r2_hidden(X5,X2)
                    <=> ( r2_hidden(X5,X3)
                        | r2_hidden(X5,X4) ) ) )
               => X2 = k4_subset_1(X1,X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_subset_1)).

fof(c_0_2,negated_conjecture,(
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

fof(c_0_3,plain,(
    ! [X6,X7,X8,X9] :
      ( ( m1_subset_1(esk1_4(X6,X7,X8,X9),X6)
        | X7 = k4_subset_1(X6,X8,X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(X6))
        | ~ m1_subset_1(X8,k1_zfmisc_1(X6))
        | ~ m1_subset_1(X7,k1_zfmisc_1(X6)) )
      & ( ~ r2_hidden(esk1_4(X6,X7,X8,X9),X8)
        | ~ r2_hidden(esk1_4(X6,X7,X8,X9),X7)
        | X7 = k4_subset_1(X6,X8,X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(X6))
        | ~ m1_subset_1(X8,k1_zfmisc_1(X6))
        | ~ m1_subset_1(X7,k1_zfmisc_1(X6)) )
      & ( ~ r2_hidden(esk1_4(X6,X7,X8,X9),X9)
        | ~ r2_hidden(esk1_4(X6,X7,X8,X9),X7)
        | X7 = k4_subset_1(X6,X8,X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(X6))
        | ~ m1_subset_1(X8,k1_zfmisc_1(X6))
        | ~ m1_subset_1(X7,k1_zfmisc_1(X6)) )
      & ( r2_hidden(esk1_4(X6,X7,X8,X9),X7)
        | r2_hidden(esk1_4(X6,X7,X8,X9),X8)
        | r2_hidden(esk1_4(X6,X7,X8,X9),X9)
        | X7 = k4_subset_1(X6,X8,X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(X6))
        | ~ m1_subset_1(X8,k1_zfmisc_1(X6))
        | ~ m1_subset_1(X7,k1_zfmisc_1(X6)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_subset_1])])])])])).

fof(c_0_4,negated_conjecture,(
    ! [X14] :
      ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
      & m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
      & ( ~ r2_hidden(X14,esk3_0)
        | r2_hidden(X14,esk4_0)
        | ~ m1_subset_1(X14,k1_zfmisc_1(esk2_0)) )
      & ( ~ r2_hidden(X14,esk4_0)
        | r2_hidden(X14,esk3_0)
        | ~ m1_subset_1(X14,k1_zfmisc_1(esk2_0)) )
      & esk3_0 != esk4_0 ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])])])).

cnf(c_0_5,plain,
    ( X2 = k4_subset_1(X1,X3,X4)
    | ~ r2_hidden(esk1_4(X1,X2,X3,X4),X4)
    | ~ r2_hidden(esk1_4(X1,X2,X3,X4),X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X2)
    | r2_hidden(esk1_4(X1,X2,X3,X4),X3)
    | r2_hidden(esk1_4(X1,X2,X3,X4),X4)
    | X2 = k4_subset_1(X1,X3,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_8,negated_conjecture,
    ( X1 = k4_subset_1(k1_zfmisc_1(esk2_0),X2,esk4_0)
    | ~ r2_hidden(esk1_4(k1_zfmisc_1(esk2_0),X1,X2,esk4_0),esk4_0)
    | ~ r2_hidden(esk1_4(k1_zfmisc_1(esk2_0),X1,X2,esk4_0),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_5,c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( X1 = k4_subset_1(k1_zfmisc_1(esk2_0),X2,esk4_0)
    | r2_hidden(esk1_4(k1_zfmisc_1(esk2_0),X1,X2,esk4_0),esk4_0)
    | r2_hidden(esk1_4(k1_zfmisc_1(esk2_0),X1,X2,esk4_0),X1)
    | r2_hidden(esk1_4(k1_zfmisc_1(esk2_0),X1,X2,esk4_0),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_7,c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( X1 = k4_subset_1(k1_zfmisc_1(esk2_0),esk4_0,esk4_0)
    | ~ r2_hidden(esk1_4(k1_zfmisc_1(esk2_0),X1,esk4_0,esk4_0),esk4_0)
    | ~ r2_hidden(esk1_4(k1_zfmisc_1(esk2_0),X1,esk4_0,esk4_0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_8,c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( X1 = k4_subset_1(k1_zfmisc_1(esk2_0),esk4_0,esk4_0)
    | r2_hidden(esk1_4(k1_zfmisc_1(esk2_0),X1,esk4_0,esk4_0),esk4_0)
    | r2_hidden(esk1_4(k1_zfmisc_1(esk2_0),X1,esk4_0,esk4_0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_9,c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( k4_subset_1(k1_zfmisc_1(esk2_0),esk4_0,esk4_0) = esk4_0
    | ~ r2_hidden(esk1_4(k1_zfmisc_1(esk2_0),esk4_0,esk4_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_14,negated_conjecture,
    ( k4_subset_1(k1_zfmisc_1(esk2_0),esk4_0,esk4_0) = esk4_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_6]),c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( esk3_0 = k4_subset_1(k1_zfmisc_1(esk2_0),esk4_0,esk4_0)
    | ~ r2_hidden(esk1_4(k1_zfmisc_1(esk2_0),esk3_0,esk4_0,esk4_0),esk4_0)
    | ~ r2_hidden(esk1_4(k1_zfmisc_1(esk2_0),esk3_0,esk4_0,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_17,negated_conjecture,
    ( X1 = esk4_0
    | r2_hidden(esk1_4(k1_zfmisc_1(esk2_0),X1,esk4_0,esk4_0),esk4_0)
    | r2_hidden(esk1_4(k1_zfmisc_1(esk2_0),X1,esk4_0,esk4_0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(rw,[status(thm)],[c_0_11,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( esk3_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_19,negated_conjecture,
    ( esk3_0 = k4_subset_1(k1_zfmisc_1(esk2_0),esk4_0,esk4_0)
    | ~ r2_hidden(esk1_4(k1_zfmisc_1(esk2_0),esk3_0,esk4_0,esk4_0),esk4_0)
    | ~ m1_subset_1(esk1_4(k1_zfmisc_1(esk2_0),esk3_0,esk4_0,esk4_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk1_4(k1_zfmisc_1(esk2_0),esk3_0,esk4_0,esk4_0),esk3_0)
    | r2_hidden(esk1_4(k1_zfmisc_1(esk2_0),esk3_0,esk4_0,esk4_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_13]),c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( ~ r2_hidden(esk1_4(k1_zfmisc_1(esk2_0),esk3_0,esk4_0,esk4_0),esk4_0)
    | ~ m1_subset_1(esk1_4(k1_zfmisc_1(esk2_0),esk3_0,esk4_0,esk4_0),k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_14]),c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( ~ m1_subset_1(esk1_4(k1_zfmisc_1(esk2_0),esk3_0,esk4_0,esk4_0),k1_zfmisc_1(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_24,plain,
    ( m1_subset_1(esk1_4(X1,X2,X3,X4),X1)
    | X2 = k4_subset_1(X1,X3,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_25,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_14]),c_0_6]),c_0_13])]),c_0_18]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:27:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S070I
% 0.13/0.38  # and selection function SelectVGNonCR.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.026 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t44_setfam_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>(r2_hidden(X4,X2)<=>r2_hidden(X4,X3)))=>X2=X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_setfam_1)).
% 0.13/0.38  fof(t15_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>(![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,X2)<=>(r2_hidden(X5,X3)|r2_hidden(X5,X4))))=>X2=k4_subset_1(X1,X3,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_subset_1)).
% 0.13/0.38  fof(c_0_2, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>(r2_hidden(X4,X2)<=>r2_hidden(X4,X3)))=>X2=X3)))), inference(assume_negation,[status(cth)],[t44_setfam_1])).
% 0.13/0.38  fof(c_0_3, plain, ![X6, X7, X8, X9]:((m1_subset_1(esk1_4(X6,X7,X8,X9),X6)|X7=k4_subset_1(X6,X8,X9)|~m1_subset_1(X9,k1_zfmisc_1(X6))|~m1_subset_1(X8,k1_zfmisc_1(X6))|~m1_subset_1(X7,k1_zfmisc_1(X6)))&(((~r2_hidden(esk1_4(X6,X7,X8,X9),X8)|~r2_hidden(esk1_4(X6,X7,X8,X9),X7)|X7=k4_subset_1(X6,X8,X9)|~m1_subset_1(X9,k1_zfmisc_1(X6))|~m1_subset_1(X8,k1_zfmisc_1(X6))|~m1_subset_1(X7,k1_zfmisc_1(X6)))&(~r2_hidden(esk1_4(X6,X7,X8,X9),X9)|~r2_hidden(esk1_4(X6,X7,X8,X9),X7)|X7=k4_subset_1(X6,X8,X9)|~m1_subset_1(X9,k1_zfmisc_1(X6))|~m1_subset_1(X8,k1_zfmisc_1(X6))|~m1_subset_1(X7,k1_zfmisc_1(X6))))&(r2_hidden(esk1_4(X6,X7,X8,X9),X7)|(r2_hidden(esk1_4(X6,X7,X8,X9),X8)|r2_hidden(esk1_4(X6,X7,X8,X9),X9))|X7=k4_subset_1(X6,X8,X9)|~m1_subset_1(X9,k1_zfmisc_1(X6))|~m1_subset_1(X8,k1_zfmisc_1(X6))|~m1_subset_1(X7,k1_zfmisc_1(X6))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_subset_1])])])])])).
% 0.13/0.38  fof(c_0_4, negated_conjecture, ![X14]:(m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))&(m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))&(((~r2_hidden(X14,esk3_0)|r2_hidden(X14,esk4_0)|~m1_subset_1(X14,k1_zfmisc_1(esk2_0)))&(~r2_hidden(X14,esk4_0)|r2_hidden(X14,esk3_0)|~m1_subset_1(X14,k1_zfmisc_1(esk2_0))))&esk3_0!=esk4_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])])])).
% 0.13/0.38  cnf(c_0_5, plain, (X2=k4_subset_1(X1,X3,X4)|~r2_hidden(esk1_4(X1,X2,X3,X4),X4)|~r2_hidden(esk1_4(X1,X2,X3,X4),X2)|~m1_subset_1(X4,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.13/0.38  cnf(c_0_6, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.38  cnf(c_0_7, plain, (r2_hidden(esk1_4(X1,X2,X3,X4),X2)|r2_hidden(esk1_4(X1,X2,X3,X4),X3)|r2_hidden(esk1_4(X1,X2,X3,X4),X4)|X2=k4_subset_1(X1,X3,X4)|~m1_subset_1(X4,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.13/0.38  cnf(c_0_8, negated_conjecture, (X1=k4_subset_1(k1_zfmisc_1(esk2_0),X2,esk4_0)|~r2_hidden(esk1_4(k1_zfmisc_1(esk2_0),X1,X2,esk4_0),esk4_0)|~r2_hidden(esk1_4(k1_zfmisc_1(esk2_0),X1,X2,esk4_0),X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(spm,[status(thm)],[c_0_5, c_0_6])).
% 0.13/0.38  cnf(c_0_9, negated_conjecture, (X1=k4_subset_1(k1_zfmisc_1(esk2_0),X2,esk4_0)|r2_hidden(esk1_4(k1_zfmisc_1(esk2_0),X1,X2,esk4_0),esk4_0)|r2_hidden(esk1_4(k1_zfmisc_1(esk2_0),X1,X2,esk4_0),X1)|r2_hidden(esk1_4(k1_zfmisc_1(esk2_0),X1,X2,esk4_0),X2)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(spm,[status(thm)],[c_0_7, c_0_6])).
% 0.13/0.38  cnf(c_0_10, negated_conjecture, (X1=k4_subset_1(k1_zfmisc_1(esk2_0),esk4_0,esk4_0)|~r2_hidden(esk1_4(k1_zfmisc_1(esk2_0),X1,esk4_0,esk4_0),esk4_0)|~r2_hidden(esk1_4(k1_zfmisc_1(esk2_0),X1,esk4_0,esk4_0),X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(spm,[status(thm)],[c_0_8, c_0_6])).
% 0.13/0.38  cnf(c_0_11, negated_conjecture, (X1=k4_subset_1(k1_zfmisc_1(esk2_0),esk4_0,esk4_0)|r2_hidden(esk1_4(k1_zfmisc_1(esk2_0),X1,esk4_0,esk4_0),esk4_0)|r2_hidden(esk1_4(k1_zfmisc_1(esk2_0),X1,esk4_0,esk4_0),X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(spm,[status(thm)],[c_0_9, c_0_6])).
% 0.13/0.38  cnf(c_0_12, negated_conjecture, (k4_subset_1(k1_zfmisc_1(esk2_0),esk4_0,esk4_0)=esk4_0|~r2_hidden(esk1_4(k1_zfmisc_1(esk2_0),esk4_0,esk4_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_10, c_0_6])).
% 0.13/0.38  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.38  cnf(c_0_14, negated_conjecture, (k4_subset_1(k1_zfmisc_1(esk2_0),esk4_0,esk4_0)=esk4_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_6]), c_0_12])).
% 0.13/0.38  cnf(c_0_15, negated_conjecture, (esk3_0=k4_subset_1(k1_zfmisc_1(esk2_0),esk4_0,esk4_0)|~r2_hidden(esk1_4(k1_zfmisc_1(esk2_0),esk3_0,esk4_0,esk4_0),esk4_0)|~r2_hidden(esk1_4(k1_zfmisc_1(esk2_0),esk3_0,esk4_0,esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_10, c_0_13])).
% 0.13/0.38  cnf(c_0_16, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.38  cnf(c_0_17, negated_conjecture, (X1=esk4_0|r2_hidden(esk1_4(k1_zfmisc_1(esk2_0),X1,esk4_0,esk4_0),esk4_0)|r2_hidden(esk1_4(k1_zfmisc_1(esk2_0),X1,esk4_0,esk4_0),X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(rw,[status(thm)],[c_0_11, c_0_14])).
% 0.13/0.38  cnf(c_0_18, negated_conjecture, (esk3_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.38  cnf(c_0_19, negated_conjecture, (esk3_0=k4_subset_1(k1_zfmisc_1(esk2_0),esk4_0,esk4_0)|~r2_hidden(esk1_4(k1_zfmisc_1(esk2_0),esk3_0,esk4_0,esk4_0),esk4_0)|~m1_subset_1(esk1_4(k1_zfmisc_1(esk2_0),esk3_0,esk4_0,esk4_0),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.13/0.38  cnf(c_0_20, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.38  cnf(c_0_21, negated_conjecture, (r2_hidden(esk1_4(k1_zfmisc_1(esk2_0),esk3_0,esk4_0,esk4_0),esk3_0)|r2_hidden(esk1_4(k1_zfmisc_1(esk2_0),esk3_0,esk4_0,esk4_0),esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_13]), c_0_18])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (~r2_hidden(esk1_4(k1_zfmisc_1(esk2_0),esk3_0,esk4_0,esk4_0),esk4_0)|~m1_subset_1(esk1_4(k1_zfmisc_1(esk2_0),esk3_0,esk4_0,esk4_0),k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_14]), c_0_18])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (~m1_subset_1(esk1_4(k1_zfmisc_1(esk2_0),esk3_0,esk4_0,esk4_0),k1_zfmisc_1(esk2_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 0.13/0.38  cnf(c_0_24, plain, (m1_subset_1(esk1_4(X1,X2,X3,X4),X1)|X2=k4_subset_1(X1,X3,X4)|~m1_subset_1(X4,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_14]), c_0_6]), c_0_13])]), c_0_18]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 26
% 0.13/0.38  # Proof object clause steps            : 21
% 0.13/0.38  # Proof object formula steps           : 5
% 0.13/0.38  # Proof object conjectures             : 21
% 0.13/0.38  # Proof object clause conjectures      : 18
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 8
% 0.13/0.38  # Proof object initial formulas used   : 2
% 0.13/0.38  # Proof object generating inferences   : 11
% 0.13/0.38  # Proof object simplifying inferences  : 11
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 2
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 9
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 9
% 0.13/0.38  # Processed clauses                    : 59
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 6
% 0.13/0.38  # ...remaining for further processing  : 53
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 3
% 0.13/0.38  # Backward-rewritten                   : 5
% 0.13/0.38  # Generated clauses                    : 62
% 0.13/0.38  # ...of the previous two non-trivial   : 63
% 0.13/0.38  # Contextual simplify-reflections      : 2
% 0.13/0.38  # Paramodulations                      : 62
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 0
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 36
% 0.13/0.38  #    Positive orientable unit clauses  : 3
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 2
% 0.13/0.38  #    Non-unit-clauses                  : 31
% 0.13/0.38  # Current number of unprocessed clauses: 22
% 0.13/0.38  # ...number of literals in the above   : 162
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 17
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 106
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 75
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 11
% 0.13/0.38  # Unit Clause-clause subsumption calls : 11
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 2
% 0.13/0.38  # BW rewrite match successes           : 1
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 3451
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.027 s
% 0.13/0.38  # System time              : 0.006 s
% 0.13/0.38  # Total time               : 0.033 s
% 0.13/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
