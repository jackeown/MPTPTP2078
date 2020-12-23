%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:01 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   41 (  86 expanded)
%              Number of clauses        :   26 (  36 expanded)
%              Number of leaves         :    7 (  20 expanded)
%              Depth                    :   10
%              Number of atoms          :   97 ( 240 expanded)
%              Number of equality atoms :    5 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t157_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( r1_tarski(X2,X3)
           => r1_tarski(k9_relat_1(X2,X1),k9_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_relat_1)).

fof(t88_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k7_relat_1(X2,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(t105_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( r1_tarski(X2,X3)
           => r1_tarski(k7_relat_1(X2,X1),k7_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( r1_tarski(X2,X3)
             => r1_tarski(k9_relat_1(X2,X1),k9_relat_1(X3,X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t157_relat_1])).

fof(c_0_8,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X16)
      | r1_tarski(k7_relat_1(X16,X15),X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & r1_tarski(esk2_0,esk3_0)
    & ~ r1_tarski(k9_relat_1(esk2_0,esk1_0),k9_relat_1(esk3_0,esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X6,X7] :
      ( ~ v1_relat_1(X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | v1_relat_1(X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_11,plain,(
    ! [X4,X5] :
      ( ( ~ m1_subset_1(X4,k1_zfmisc_1(X5))
        | r1_tarski(X4,X5) )
      & ( ~ r1_tarski(X4,X5)
        | m1_subset_1(X4,k1_zfmisc_1(X5)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_12,plain,
    ( r1_tarski(k7_relat_1(X1,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(k7_relat_1(esk3_0,X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_17,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X12)
      | k2_relat_1(k7_relat_1(X12,X11)) = k9_relat_1(X12,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_18,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_19,plain,(
    ! [X13,X14] :
      ( ( r1_tarski(k1_relat_1(X13),k1_relat_1(X14))
        | ~ r1_tarski(X13,X14)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13) )
      & ( r1_tarski(k2_relat_1(X13),k2_relat_1(X14))
        | ~ r1_tarski(X13,X14)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk3_0,X1),k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(k7_relat_1(esk2_0,X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_18])).

fof(c_0_24,plain,(
    ! [X8,X9,X10] :
      ( ~ v1_relat_1(X9)
      | ~ v1_relat_1(X10)
      | ~ r1_tarski(X9,X10)
      | r1_tarski(k7_relat_1(X9,X8),k7_relat_1(X10,X8)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t105_relat_1])])])).

cnf(c_0_25,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk3_0,X1)) = k9_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_13])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk2_0,X1),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_23])).

cnf(c_0_30,plain,
    ( r1_tarski(k7_relat_1(X1,X3),k7_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(k2_relat_1(X1),k9_relat_1(esk3_0,X2))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,k7_relat_1(esk3_0,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk2_0,X1)) = k9_relat_1(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_18])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(k7_relat_1(X1,X2),k7_relat_1(esk3_0,X2))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_13])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk2_0,X1),k9_relat_1(esk3_0,X2))
    | ~ r1_tarski(k7_relat_1(esk2_0,X1),k7_relat_1(esk3_0,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k7_relat_1(esk2_0,X1),k7_relat_1(esk3_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_18]),c_0_35])])).

cnf(c_0_38,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk2_0,esk1_0),k9_relat_1(esk3_0,esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk2_0,X1),k9_relat_1(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:34:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___107_C00_02_nc_F1_PI_AE_Q4_CS_SP_PS_S00EN
% 0.13/0.39  # and selection function PSelectSmallestOrientable.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.037 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t157_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X2,X3)=>r1_tarski(k9_relat_1(X2,X1),k9_relat_1(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_relat_1)).
% 0.13/0.39  fof(t88_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k7_relat_1(X2,X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 0.13/0.39  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.13/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.39  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.13/0.39  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 0.13/0.39  fof(t105_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X2,X3)=>r1_tarski(k7_relat_1(X2,X1),k7_relat_1(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_relat_1)).
% 0.13/0.39  fof(c_0_7, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X2,X3)=>r1_tarski(k9_relat_1(X2,X1),k9_relat_1(X3,X1)))))), inference(assume_negation,[status(cth)],[t157_relat_1])).
% 0.13/0.39  fof(c_0_8, plain, ![X15, X16]:(~v1_relat_1(X16)|r1_tarski(k7_relat_1(X16,X15),X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).
% 0.13/0.39  fof(c_0_9, negated_conjecture, (v1_relat_1(esk2_0)&(v1_relat_1(esk3_0)&(r1_tarski(esk2_0,esk3_0)&~r1_tarski(k9_relat_1(esk2_0,esk1_0),k9_relat_1(esk3_0,esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.13/0.39  fof(c_0_10, plain, ![X6, X7]:(~v1_relat_1(X6)|(~m1_subset_1(X7,k1_zfmisc_1(X6))|v1_relat_1(X7))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.13/0.39  fof(c_0_11, plain, ![X4, X5]:((~m1_subset_1(X4,k1_zfmisc_1(X5))|r1_tarski(X4,X5))&(~r1_tarski(X4,X5)|m1_subset_1(X4,k1_zfmisc_1(X5)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.39  cnf(c_0_12, plain, (r1_tarski(k7_relat_1(X1,X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.39  cnf(c_0_13, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.39  cnf(c_0_14, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.39  cnf(c_0_15, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.39  cnf(c_0_16, negated_conjecture, (r1_tarski(k7_relat_1(esk3_0,X1),esk3_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.13/0.39  fof(c_0_17, plain, ![X11, X12]:(~v1_relat_1(X12)|k2_relat_1(k7_relat_1(X12,X11))=k9_relat_1(X12,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.13/0.39  cnf(c_0_18, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.39  fof(c_0_19, plain, ![X13, X14]:((r1_tarski(k1_relat_1(X13),k1_relat_1(X14))|~r1_tarski(X13,X14)|~v1_relat_1(X14)|~v1_relat_1(X13))&(r1_tarski(k2_relat_1(X13),k2_relat_1(X14))|~r1_tarski(X13,X14)|~v1_relat_1(X14)|~v1_relat_1(X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.13/0.39  cnf(c_0_20, negated_conjecture, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_14, c_0_13])).
% 0.13/0.39  cnf(c_0_21, negated_conjecture, (m1_subset_1(k7_relat_1(esk3_0,X1),k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.13/0.39  cnf(c_0_22, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_23, negated_conjecture, (r1_tarski(k7_relat_1(esk2_0,X1),esk2_0)), inference(spm,[status(thm)],[c_0_12, c_0_18])).
% 0.13/0.39  fof(c_0_24, plain, ![X8, X9, X10]:(~v1_relat_1(X9)|(~v1_relat_1(X10)|(~r1_tarski(X9,X10)|r1_tarski(k7_relat_1(X9,X8),k7_relat_1(X10,X8))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t105_relat_1])])])).
% 0.13/0.39  cnf(c_0_25, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.39  cnf(c_0_26, negated_conjecture, (v1_relat_1(k7_relat_1(esk3_0,X1))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.39  cnf(c_0_27, negated_conjecture, (k2_relat_1(k7_relat_1(esk3_0,X1))=k9_relat_1(esk3_0,X1)), inference(spm,[status(thm)],[c_0_22, c_0_13])).
% 0.13/0.39  cnf(c_0_28, negated_conjecture, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_14, c_0_18])).
% 0.13/0.39  cnf(c_0_29, negated_conjecture, (m1_subset_1(k7_relat_1(esk2_0,X1),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_15, c_0_23])).
% 0.13/0.39  cnf(c_0_30, plain, (r1_tarski(k7_relat_1(X1,X3),k7_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.39  cnf(c_0_31, negated_conjecture, (r1_tarski(k2_relat_1(X1),k9_relat_1(esk3_0,X2))|~v1_relat_1(X1)|~r1_tarski(X1,k7_relat_1(esk3_0,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])).
% 0.13/0.39  cnf(c_0_32, negated_conjecture, (v1_relat_1(k7_relat_1(esk2_0,X1))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.39  cnf(c_0_33, negated_conjecture, (k2_relat_1(k7_relat_1(esk2_0,X1))=k9_relat_1(esk2_0,X1)), inference(spm,[status(thm)],[c_0_22, c_0_18])).
% 0.13/0.39  cnf(c_0_34, negated_conjecture, (r1_tarski(k7_relat_1(X1,X2),k7_relat_1(esk3_0,X2))|~v1_relat_1(X1)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_30, c_0_13])).
% 0.13/0.39  cnf(c_0_35, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.39  cnf(c_0_36, negated_conjecture, (r1_tarski(k9_relat_1(esk2_0,X1),k9_relat_1(esk3_0,X2))|~r1_tarski(k7_relat_1(esk2_0,X1),k7_relat_1(esk3_0,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])).
% 0.13/0.39  cnf(c_0_37, negated_conjecture, (r1_tarski(k7_relat_1(esk2_0,X1),k7_relat_1(esk3_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_18]), c_0_35])])).
% 0.13/0.39  cnf(c_0_38, negated_conjecture, (~r1_tarski(k9_relat_1(esk2_0,esk1_0),k9_relat_1(esk3_0,esk1_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.39  cnf(c_0_39, negated_conjecture, (r1_tarski(k9_relat_1(esk2_0,X1),k9_relat_1(esk3_0,X1))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.13/0.39  cnf(c_0_40, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39])]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 41
% 0.13/0.39  # Proof object clause steps            : 26
% 0.13/0.39  # Proof object formula steps           : 15
% 0.13/0.39  # Proof object conjectures             : 23
% 0.13/0.39  # Proof object clause conjectures      : 20
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 10
% 0.13/0.39  # Proof object initial formulas used   : 7
% 0.13/0.39  # Proof object generating inferences   : 15
% 0.13/0.39  # Proof object simplifying inferences  : 6
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 7
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 12
% 0.13/0.39  # Removed in clause preprocessing      : 0
% 0.13/0.39  # Initial clauses in saturation        : 12
% 0.13/0.39  # Processed clauses                    : 95
% 0.13/0.39  # ...of these trivial                  : 2
% 0.13/0.39  # ...subsumed                          : 5
% 0.13/0.39  # ...remaining for further processing  : 88
% 0.13/0.39  # Other redundant clauses eliminated   : 0
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 0
% 0.13/0.39  # Backward-rewritten                   : 1
% 0.13/0.39  # Generated clauses                    : 144
% 0.13/0.39  # ...of the previous two non-trivial   : 128
% 0.13/0.39  # Contextual simplify-reflections      : 0
% 0.13/0.39  # Paramodulations                      : 144
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
% 0.13/0.39  # Current number of processed clauses  : 75
% 0.13/0.39  #    Positive orientable unit clauses  : 35
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 0
% 0.13/0.39  #    Non-unit-clauses                  : 40
% 0.13/0.39  # Current number of unprocessed clauses: 57
% 0.13/0.39  # ...number of literals in the above   : 138
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 13
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 97
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 65
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 5
% 0.13/0.39  # Unit Clause-clause subsumption calls : 9
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 6
% 0.13/0.39  # BW rewrite match successes           : 1
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 3475
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.049 s
% 0.13/0.39  # System time              : 0.001 s
% 0.13/0.39  # Total time               : 0.050 s
% 0.13/0.39  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
