%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:46:38 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 116 expanded)
%              Number of clauses        :   31 (  47 expanded)
%              Number of leaves         :    7 (  27 expanded)
%              Depth                    :   13
%              Number of atoms          :  131 ( 456 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t47_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ! [X4] :
              ( m1_subset_1(X4,k1_zfmisc_1(X1))
             => ( ( r1_tarski(X2,X3)
                  & r1_xboole_0(X4,X3) )
               => r1_tarski(X2,k3_subset_1(X1,X4)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_subset_1)).

fof(t43_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_xboole_0(X2,X3)
          <=> r1_tarski(X2,k3_subset_1(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(t31_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(X2,X3)
          <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(t44_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_xboole_0(X2,k3_subset_1(X1,X3))
          <=> r1_tarski(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_subset_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ! [X4] :
                ( m1_subset_1(X4,k1_zfmisc_1(X1))
               => ( ( r1_tarski(X2,X3)
                    & r1_xboole_0(X4,X3) )
                 => r1_tarski(X2,k3_subset_1(X1,X4)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t47_subset_1])).

fof(c_0_8,plain,(
    ! [X15,X16,X17] :
      ( ( ~ r1_xboole_0(X16,X17)
        | r1_tarski(X16,k3_subset_1(X15,X17))
        | ~ m1_subset_1(X17,k1_zfmisc_1(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(X15)) )
      & ( ~ r1_tarski(X16,k3_subset_1(X15,X17))
        | r1_xboole_0(X16,X17)
        | ~ m1_subset_1(X17,k1_zfmisc_1(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(X15)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_subset_1])])])])).

fof(c_0_9,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0))
    & r1_tarski(esk2_0,esk3_0)
    & r1_xboole_0(esk4_0,esk3_0)
    & ~ r1_tarski(esk2_0,k3_subset_1(esk1_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | m1_subset_1(k3_subset_1(X10,X11),k1_zfmisc_1(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_11,plain,
    ( r1_tarski(X1,k3_subset_1(X3,X2))
    | ~ r1_xboole_0(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_15,plain,(
    ! [X12,X13,X14] :
      ( ( ~ r1_tarski(X13,X14)
        | r1_tarski(k3_subset_1(X12,X14),k3_subset_1(X12,X13))
        | ~ m1_subset_1(X14,k1_zfmisc_1(X12))
        | ~ m1_subset_1(X13,k1_zfmisc_1(X12)) )
      & ( ~ r1_tarski(k3_subset_1(X12,X14),k3_subset_1(X12,X13))
        | r1_tarski(X13,X14)
        | ~ m1_subset_1(X14,k1_zfmisc_1(X12))
        | ~ m1_subset_1(X13,k1_zfmisc_1(X12)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_subset_1])])])])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(esk4_0,k3_subset_1(X1,esk3_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk1_0,esk3_0),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,plain,
    ( r1_tarski(k3_subset_1(X3,X2),k3_subset_1(X3,X1))
    | ~ r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(esk4_0,k3_subset_1(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_14]),c_0_17])])).

fof(c_0_22,plain,(
    ! [X18,X19,X20] :
      ( ( ~ r1_xboole_0(X19,k3_subset_1(X18,X20))
        | r1_tarski(X19,X20)
        | ~ m1_subset_1(X20,k1_zfmisc_1(X18))
        | ~ m1_subset_1(X19,k1_zfmisc_1(X18)) )
      & ( ~ r1_tarski(X19,X20)
        | r1_xboole_0(X19,k3_subset_1(X18,X20))
        | ~ m1_subset_1(X20,k1_zfmisc_1(X18))
        | ~ m1_subset_1(X19,k1_zfmisc_1(X18)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_subset_1])])])])).

cnf(c_0_23,negated_conjecture,
    ( r1_xboole_0(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0))
    | ~ r1_tarski(X1,k3_subset_1(esk1_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk1_0,k3_subset_1(esk1_0,esk3_0)),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(k3_subset_1(X1,k3_subset_1(esk1_0,esk3_0)),k3_subset_1(X1,esk4_0))
    | ~ m1_subset_1(k3_subset_1(esk1_0,esk3_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( r1_xboole_0(X1,k3_subset_1(X3,X2))
    | ~ r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_28,plain,(
    ! [X8,X9] :
      ( ( ~ r1_xboole_0(X8,X9)
        | k4_xboole_0(X8,X9) = X8 )
      & ( k4_xboole_0(X8,X9) != X8
        | r1_xboole_0(X8,X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_29,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(esk1_0,k3_subset_1(esk1_0,esk3_0)),esk4_0)
    | ~ r1_tarski(k3_subset_1(esk1_0,k3_subset_1(esk1_0,esk3_0)),k3_subset_1(esk1_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk1_0,k3_subset_1(esk1_0,esk3_0)),k3_subset_1(esk1_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_17]),c_0_19])])).

cnf(c_0_31,negated_conjecture,
    ( r1_xboole_0(esk2_0,k3_subset_1(X1,esk3_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_33,plain,(
    ! [X5,X6,X7] :
      ( ( r1_tarski(X5,X6)
        | ~ r1_tarski(X5,k4_xboole_0(X6,X7)) )
      & ( r1_xboole_0(X5,X7)
        | ~ r1_tarski(X5,k4_xboole_0(X6,X7)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(esk1_0,k3_subset_1(esk1_0,esk3_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30])])).

cnf(c_0_36,negated_conjecture,
    ( r1_xboole_0(esk2_0,k3_subset_1(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_14]),c_0_32])])).

cnf(c_0_37,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( k4_xboole_0(k3_subset_1(esk1_0,k3_subset_1(esk1_0,esk3_0)),esk4_0) = k3_subset_1(esk1_0,k3_subset_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(esk2_0,k3_subset_1(X1,k3_subset_1(esk1_0,esk3_0)))
    | ~ m1_subset_1(k3_subset_1(esk1_0,esk3_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( r1_xboole_0(X1,esk4_0)
    | ~ r1_tarski(X1,k3_subset_1(esk1_0,k3_subset_1(esk1_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(esk2_0,k3_subset_1(esk1_0,k3_subset_1(esk1_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_32]),c_0_19])])).

cnf(c_0_42,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(esk2_0,k3_subset_1(X1,esk4_0))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_42])).

cnf(c_0_44,negated_conjecture,
    ( ~ r1_tarski(esk2_0,k3_subset_1(esk1_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_17]),c_0_32])]),c_0_44]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:01:09 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___107_C00_02_nc_F1_PI_AE_Q4_CS_SP_PS_S00EN
% 0.13/0.39  # and selection function PSelectSmallestOrientable.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.028 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t47_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>((r1_tarski(X2,X3)&r1_xboole_0(X4,X3))=>r1_tarski(X2,k3_subset_1(X1,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_subset_1)).
% 0.13/0.39  fof(t43_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_xboole_0(X2,X3)<=>r1_tarski(X2,k3_subset_1(X1,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_subset_1)).
% 0.13/0.39  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.13/0.39  fof(t31_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 0.13/0.39  fof(t44_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_xboole_0(X2,k3_subset_1(X1,X3))<=>r1_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_subset_1)).
% 0.13/0.39  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.13/0.39  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.13/0.39  fof(c_0_7, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>((r1_tarski(X2,X3)&r1_xboole_0(X4,X3))=>r1_tarski(X2,k3_subset_1(X1,X4))))))), inference(assume_negation,[status(cth)],[t47_subset_1])).
% 0.13/0.39  fof(c_0_8, plain, ![X15, X16, X17]:((~r1_xboole_0(X16,X17)|r1_tarski(X16,k3_subset_1(X15,X17))|~m1_subset_1(X17,k1_zfmisc_1(X15))|~m1_subset_1(X16,k1_zfmisc_1(X15)))&(~r1_tarski(X16,k3_subset_1(X15,X17))|r1_xboole_0(X16,X17)|~m1_subset_1(X17,k1_zfmisc_1(X15))|~m1_subset_1(X16,k1_zfmisc_1(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_subset_1])])])])).
% 0.13/0.39  fof(c_0_9, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0))&((r1_tarski(esk2_0,esk3_0)&r1_xboole_0(esk4_0,esk3_0))&~r1_tarski(esk2_0,k3_subset_1(esk1_0,esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.13/0.39  fof(c_0_10, plain, ![X10, X11]:(~m1_subset_1(X11,k1_zfmisc_1(X10))|m1_subset_1(k3_subset_1(X10,X11),k1_zfmisc_1(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.13/0.39  cnf(c_0_11, plain, (r1_tarski(X1,k3_subset_1(X3,X2))|~r1_xboole_0(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.39  cnf(c_0_12, negated_conjecture, (r1_xboole_0(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.39  cnf(c_0_13, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.39  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.39  fof(c_0_15, plain, ![X12, X13, X14]:((~r1_tarski(X13,X14)|r1_tarski(k3_subset_1(X12,X14),k3_subset_1(X12,X13))|~m1_subset_1(X14,k1_zfmisc_1(X12))|~m1_subset_1(X13,k1_zfmisc_1(X12)))&(~r1_tarski(k3_subset_1(X12,X14),k3_subset_1(X12,X13))|r1_tarski(X13,X14)|~m1_subset_1(X14,k1_zfmisc_1(X12))|~m1_subset_1(X13,k1_zfmisc_1(X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_subset_1])])])])).
% 0.13/0.39  cnf(c_0_16, negated_conjecture, (r1_tarski(esk4_0,k3_subset_1(X1,esk3_0))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~m1_subset_1(esk4_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.13/0.39  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.39  cnf(c_0_18, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,k3_subset_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.39  cnf(c_0_19, negated_conjecture, (m1_subset_1(k3_subset_1(esk1_0,esk3_0),k1_zfmisc_1(esk1_0))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.13/0.39  cnf(c_0_20, plain, (r1_tarski(k3_subset_1(X3,X2),k3_subset_1(X3,X1))|~r1_tarski(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_21, negated_conjecture, (r1_tarski(esk4_0,k3_subset_1(esk1_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_14]), c_0_17])])).
% 0.13/0.39  fof(c_0_22, plain, ![X18, X19, X20]:((~r1_xboole_0(X19,k3_subset_1(X18,X20))|r1_tarski(X19,X20)|~m1_subset_1(X20,k1_zfmisc_1(X18))|~m1_subset_1(X19,k1_zfmisc_1(X18)))&(~r1_tarski(X19,X20)|r1_xboole_0(X19,k3_subset_1(X18,X20))|~m1_subset_1(X20,k1_zfmisc_1(X18))|~m1_subset_1(X19,k1_zfmisc_1(X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_subset_1])])])])).
% 0.13/0.39  cnf(c_0_23, negated_conjecture, (r1_xboole_0(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(esk1_0))|~r1_tarski(X1,k3_subset_1(esk1_0,esk4_0))), inference(spm,[status(thm)],[c_0_18, c_0_17])).
% 0.13/0.39  cnf(c_0_24, negated_conjecture, (m1_subset_1(k3_subset_1(esk1_0,k3_subset_1(esk1_0,esk3_0)),k1_zfmisc_1(esk1_0))), inference(spm,[status(thm)],[c_0_13, c_0_19])).
% 0.13/0.39  cnf(c_0_25, negated_conjecture, (r1_tarski(k3_subset_1(X1,k3_subset_1(esk1_0,esk3_0)),k3_subset_1(X1,esk4_0))|~m1_subset_1(k3_subset_1(esk1_0,esk3_0),k1_zfmisc_1(X1))|~m1_subset_1(esk4_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.39  cnf(c_0_26, plain, (r1_xboole_0(X1,k3_subset_1(X3,X2))|~r1_tarski(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  cnf(c_0_27, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.39  fof(c_0_28, plain, ![X8, X9]:((~r1_xboole_0(X8,X9)|k4_xboole_0(X8,X9)=X8)&(k4_xboole_0(X8,X9)!=X8|r1_xboole_0(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.13/0.39  cnf(c_0_29, negated_conjecture, (r1_xboole_0(k3_subset_1(esk1_0,k3_subset_1(esk1_0,esk3_0)),esk4_0)|~r1_tarski(k3_subset_1(esk1_0,k3_subset_1(esk1_0,esk3_0)),k3_subset_1(esk1_0,esk4_0))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.39  cnf(c_0_30, negated_conjecture, (r1_tarski(k3_subset_1(esk1_0,k3_subset_1(esk1_0,esk3_0)),k3_subset_1(esk1_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_17]), c_0_19])])).
% 0.13/0.39  cnf(c_0_31, negated_conjecture, (r1_xboole_0(esk2_0,k3_subset_1(X1,esk3_0))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.13/0.39  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.39  fof(c_0_33, plain, ![X5, X6, X7]:((r1_tarski(X5,X6)|~r1_tarski(X5,k4_xboole_0(X6,X7)))&(r1_xboole_0(X5,X7)|~r1_tarski(X5,k4_xboole_0(X6,X7)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 0.13/0.39  cnf(c_0_34, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.39  cnf(c_0_35, negated_conjecture, (r1_xboole_0(k3_subset_1(esk1_0,k3_subset_1(esk1_0,esk3_0)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30])])).
% 0.13/0.39  cnf(c_0_36, negated_conjecture, (r1_xboole_0(esk2_0,k3_subset_1(esk1_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_14]), c_0_32])])).
% 0.13/0.39  cnf(c_0_37, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.39  cnf(c_0_38, negated_conjecture, (k4_xboole_0(k3_subset_1(esk1_0,k3_subset_1(esk1_0,esk3_0)),esk4_0)=k3_subset_1(esk1_0,k3_subset_1(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.13/0.39  cnf(c_0_39, negated_conjecture, (r1_tarski(esk2_0,k3_subset_1(X1,k3_subset_1(esk1_0,esk3_0)))|~m1_subset_1(k3_subset_1(esk1_0,esk3_0),k1_zfmisc_1(X1))|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_11, c_0_36])).
% 0.13/0.39  cnf(c_0_40, negated_conjecture, (r1_xboole_0(X1,esk4_0)|~r1_tarski(X1,k3_subset_1(esk1_0,k3_subset_1(esk1_0,esk3_0)))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.13/0.39  cnf(c_0_41, negated_conjecture, (r1_tarski(esk2_0,k3_subset_1(esk1_0,k3_subset_1(esk1_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_32]), c_0_19])])).
% 0.13/0.39  cnf(c_0_42, negated_conjecture, (r1_xboole_0(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.13/0.39  cnf(c_0_43, negated_conjecture, (r1_tarski(esk2_0,k3_subset_1(X1,esk4_0))|~m1_subset_1(esk4_0,k1_zfmisc_1(X1))|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_11, c_0_42])).
% 0.13/0.39  cnf(c_0_44, negated_conjecture, (~r1_tarski(esk2_0,k3_subset_1(esk1_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.39  cnf(c_0_45, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_17]), c_0_32])]), c_0_44]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 46
% 0.13/0.39  # Proof object clause steps            : 31
% 0.13/0.39  # Proof object formula steps           : 15
% 0.13/0.39  # Proof object conjectures             : 27
% 0.13/0.39  # Proof object clause conjectures      : 24
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 13
% 0.13/0.39  # Proof object initial formulas used   : 7
% 0.13/0.39  # Proof object generating inferences   : 17
% 0.13/0.39  # Proof object simplifying inferences  : 13
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 7
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 17
% 0.13/0.39  # Removed in clause preprocessing      : 0
% 0.13/0.39  # Initial clauses in saturation        : 17
% 0.13/0.39  # Processed clauses                    : 283
% 0.13/0.39  # ...of these trivial                  : 2
% 0.13/0.39  # ...subsumed                          : 2
% 0.13/0.39  # ...remaining for further processing  : 279
% 0.13/0.39  # Other redundant clauses eliminated   : 0
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 4
% 0.13/0.39  # Backward-rewritten                   : 1
% 0.13/0.39  # Generated clauses                    : 928
% 0.13/0.39  # ...of the previous two non-trivial   : 902
% 0.13/0.39  # Contextual simplify-reflections      : 0
% 0.13/0.39  # Paramodulations                      : 928
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 0
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 257
% 0.13/0.39  #    Positive orientable unit clauses  : 46
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 10
% 0.13/0.39  #    Non-unit-clauses                  : 201
% 0.13/0.39  # Current number of unprocessed clauses: 653
% 0.13/0.39  # ...number of literals in the above   : 1353
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 22
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 1115
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 1111
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.39  # Unit Clause-clause subsumption calls : 67
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 180
% 0.13/0.39  # BW rewrite match successes           : 5
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 30204
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.050 s
% 0.13/0.39  # System time              : 0.005 s
% 0.13/0.39  # Total time               : 0.056 s
% 0.13/0.39  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
