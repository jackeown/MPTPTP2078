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
% DateTime   : Thu Dec  3 10:50:12 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   36 (  64 expanded)
%              Number of clauses        :   21 (  26 expanded)
%              Number of leaves         :    7 (  15 expanded)
%              Depth                    :    7
%              Number of atoms          :   88 ( 203 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t133_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ! [X4] :
          ( v1_relat_1(X4)
         => ( ( r1_tarski(X3,X4)
              & r1_tarski(X1,X2) )
           => r1_tarski(k8_relat_1(X1,X3),k8_relat_1(X2,X4)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_relat_1)).

fof(t117_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k8_relat_1(X1,X2),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

fof(t129_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => k8_relat_1(X2,k8_relat_1(X1,X3)) = k8_relat_1(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).

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

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t132_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( r1_tarski(X2,X3)
           => r1_tarski(k8_relat_1(X1,X2),k8_relat_1(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_relat_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ! [X4] :
            ( v1_relat_1(X4)
           => ( ( r1_tarski(X3,X4)
                & r1_tarski(X1,X2) )
             => r1_tarski(k8_relat_1(X1,X3),k8_relat_1(X2,X4)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t133_relat_1])).

fof(c_0_8,plain,(
    ! [X12,X13] :
      ( ~ v1_relat_1(X13)
      | r1_tarski(k8_relat_1(X12,X13),X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t117_relat_1])])).

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_relat_1(esk4_0)
    & r1_tarski(esk3_0,esk4_0)
    & r1_tarski(esk1_0,esk2_0)
    & ~ r1_tarski(k8_relat_1(esk1_0,esk3_0),k8_relat_1(esk2_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X14,X15,X16] :
      ( ~ v1_relat_1(X16)
      | ~ r1_tarski(X14,X15)
      | k8_relat_1(X15,k8_relat_1(X14,X16)) = k8_relat_1(X14,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t129_relat_1])])).

fof(c_0_11,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | v1_relat_1(X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_12,plain,(
    ! [X8,X9] :
      ( ( ~ m1_subset_1(X8,k1_zfmisc_1(X9))
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | m1_subset_1(X8,k1_zfmisc_1(X9)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_13,plain,
    ( r1_tarski(k8_relat_1(X2,X1),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_15,plain,(
    ! [X5,X6,X7] :
      ( ~ r1_tarski(X5,X6)
      | ~ r1_tarski(X6,X7)
      | r1_tarski(X5,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_16,plain,(
    ! [X17,X18,X19] :
      ( ~ v1_relat_1(X18)
      | ~ v1_relat_1(X19)
      | ~ r1_tarski(X18,X19)
      | r1_tarski(k8_relat_1(X17,X18),k8_relat_1(X17,X19)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_relat_1])])])).

cnf(c_0_17,plain,
    ( k8_relat_1(X3,k8_relat_1(X2,X1)) = k8_relat_1(X2,X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(k8_relat_1(X1,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,plain,
    ( r1_tarski(k8_relat_1(X3,X1),k8_relat_1(X3,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,negated_conjecture,
    ( k8_relat_1(X1,k8_relat_1(X2,esk3_0)) = k8_relat_1(X2,esk3_0)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_14])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_27,negated_conjecture,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_14])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(k8_relat_1(X1,esk3_0),k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(k8_relat_1(X1,X2),k8_relat_1(X1,esk4_0))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X2,esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( k8_relat_1(esk2_0,k8_relat_1(esk1_0,esk3_0)) = k8_relat_1(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( v1_relat_1(k8_relat_1(X1,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k8_relat_1(X1,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_20])).

cnf(c_0_34,negated_conjecture,
    ( ~ r1_tarski(k8_relat_1(esk1_0,esk3_0),k8_relat_1(esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_35,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33])]),c_0_34]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:52:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_E___107_C00_02_nc_F1_PI_AE_Q4_CS_SP_PS_S00EN
% 0.20/0.37  # and selection function PSelectSmallestOrientable.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.029 s
% 0.20/0.37  # Presaturation interreduction done
% 0.20/0.37  
% 0.20/0.37  # Proof found!
% 0.20/0.37  # SZS status Theorem
% 0.20/0.37  # SZS output start CNFRefutation
% 0.20/0.37  fof(t133_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>![X4]:(v1_relat_1(X4)=>((r1_tarski(X3,X4)&r1_tarski(X1,X2))=>r1_tarski(k8_relat_1(X1,X3),k8_relat_1(X2,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t133_relat_1)).
% 0.20/0.37  fof(t117_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k8_relat_1(X1,X2),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_relat_1)).
% 0.20/0.37  fof(t129_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k8_relat_1(X2,k8_relat_1(X1,X3))=k8_relat_1(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_relat_1)).
% 0.20/0.37  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.20/0.37  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.37  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.20/0.37  fof(t132_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X2,X3)=>r1_tarski(k8_relat_1(X1,X2),k8_relat_1(X1,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_relat_1)).
% 0.20/0.37  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>![X4]:(v1_relat_1(X4)=>((r1_tarski(X3,X4)&r1_tarski(X1,X2))=>r1_tarski(k8_relat_1(X1,X3),k8_relat_1(X2,X4)))))), inference(assume_negation,[status(cth)],[t133_relat_1])).
% 0.20/0.37  fof(c_0_8, plain, ![X12, X13]:(~v1_relat_1(X13)|r1_tarski(k8_relat_1(X12,X13),X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t117_relat_1])])).
% 0.20/0.37  fof(c_0_9, negated_conjecture, (v1_relat_1(esk3_0)&(v1_relat_1(esk4_0)&((r1_tarski(esk3_0,esk4_0)&r1_tarski(esk1_0,esk2_0))&~r1_tarski(k8_relat_1(esk1_0,esk3_0),k8_relat_1(esk2_0,esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.20/0.37  fof(c_0_10, plain, ![X14, X15, X16]:(~v1_relat_1(X16)|(~r1_tarski(X14,X15)|k8_relat_1(X15,k8_relat_1(X14,X16))=k8_relat_1(X14,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t129_relat_1])])).
% 0.20/0.37  fof(c_0_11, plain, ![X10, X11]:(~v1_relat_1(X10)|(~m1_subset_1(X11,k1_zfmisc_1(X10))|v1_relat_1(X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.20/0.37  fof(c_0_12, plain, ![X8, X9]:((~m1_subset_1(X8,k1_zfmisc_1(X9))|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|m1_subset_1(X8,k1_zfmisc_1(X9)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.37  cnf(c_0_13, plain, (r1_tarski(k8_relat_1(X2,X1),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.37  cnf(c_0_14, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.37  fof(c_0_15, plain, ![X5, X6, X7]:(~r1_tarski(X5,X6)|~r1_tarski(X6,X7)|r1_tarski(X5,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.20/0.37  fof(c_0_16, plain, ![X17, X18, X19]:(~v1_relat_1(X18)|(~v1_relat_1(X19)|(~r1_tarski(X18,X19)|r1_tarski(k8_relat_1(X17,X18),k8_relat_1(X17,X19))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_relat_1])])])).
% 0.20/0.37  cnf(c_0_17, plain, (k8_relat_1(X3,k8_relat_1(X2,X1))=k8_relat_1(X2,X1)|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.37  cnf(c_0_18, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.37  cnf(c_0_19, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.37  cnf(c_0_20, negated_conjecture, (r1_tarski(k8_relat_1(X1,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.20/0.37  cnf(c_0_21, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.37  cnf(c_0_22, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.37  cnf(c_0_23, plain, (r1_tarski(k8_relat_1(X3,X1),k8_relat_1(X3,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.37  cnf(c_0_24, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.37  cnf(c_0_25, negated_conjecture, (k8_relat_1(X1,k8_relat_1(X2,esk3_0))=k8_relat_1(X2,esk3_0)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_17, c_0_14])).
% 0.20/0.37  cnf(c_0_26, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.37  cnf(c_0_27, negated_conjecture, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_18, c_0_14])).
% 0.20/0.37  cnf(c_0_28, negated_conjecture, (m1_subset_1(k8_relat_1(X1,esk3_0),k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.37  cnf(c_0_29, negated_conjecture, (r1_tarski(X1,esk4_0)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.37  cnf(c_0_30, negated_conjecture, (r1_tarski(k8_relat_1(X1,X2),k8_relat_1(X1,esk4_0))|~v1_relat_1(X2)|~r1_tarski(X2,esk4_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.37  cnf(c_0_31, negated_conjecture, (k8_relat_1(esk2_0,k8_relat_1(esk1_0,esk3_0))=k8_relat_1(esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.37  cnf(c_0_32, negated_conjecture, (v1_relat_1(k8_relat_1(X1,esk3_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.37  cnf(c_0_33, negated_conjecture, (r1_tarski(k8_relat_1(X1,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_29, c_0_20])).
% 0.20/0.37  cnf(c_0_34, negated_conjecture, (~r1_tarski(k8_relat_1(esk1_0,esk3_0),k8_relat_1(esk2_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.37  cnf(c_0_35, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33])]), c_0_34]), ['proof']).
% 0.20/0.37  # SZS output end CNFRefutation
% 0.20/0.37  # Proof object total steps             : 36
% 0.20/0.37  # Proof object clause steps            : 21
% 0.20/0.37  # Proof object formula steps           : 15
% 0.20/0.37  # Proof object conjectures             : 18
% 0.20/0.37  # Proof object clause conjectures      : 15
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 11
% 0.20/0.37  # Proof object initial formulas used   : 7
% 0.20/0.37  # Proof object generating inferences   : 10
% 0.20/0.37  # Proof object simplifying inferences  : 4
% 0.20/0.37  # Training examples: 0 positive, 0 negative
% 0.20/0.37  # Parsed axioms                        : 7
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 12
% 0.20/0.37  # Removed in clause preprocessing      : 0
% 0.20/0.37  # Initial clauses in saturation        : 12
% 0.20/0.37  # Processed clauses                    : 63
% 0.20/0.37  # ...of these trivial                  : 5
% 0.20/0.37  # ...subsumed                          : 0
% 0.20/0.37  # ...remaining for further processing  : 58
% 0.20/0.37  # Other redundant clauses eliminated   : 0
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 0
% 0.20/0.37  # Backward-rewritten                   : 0
% 0.20/0.37  # Generated clauses                    : 126
% 0.20/0.37  # ...of the previous two non-trivial   : 102
% 0.20/0.37  # Contextual simplify-reflections      : 0
% 0.20/0.37  # Paramodulations                      : 126
% 0.20/0.37  # Factorizations                       : 0
% 0.20/0.37  # Equation resolutions                 : 0
% 0.20/0.37  # Propositional unsat checks           : 0
% 0.20/0.37  #    Propositional check models        : 0
% 0.20/0.37  #    Propositional check unsatisfiable : 0
% 0.20/0.37  #    Propositional clauses             : 0
% 0.20/0.37  #    Propositional clauses after purity: 0
% 0.20/0.37  #    Propositional unsat core size     : 0
% 0.20/0.37  #    Propositional preprocessing time  : 0.000
% 0.20/0.37  #    Propositional encoding time       : 0.000
% 0.20/0.37  #    Propositional solver time         : 0.000
% 0.20/0.37  #    Success case prop preproc time    : 0.000
% 0.20/0.37  #    Success case prop encoding time   : 0.000
% 0.20/0.37  #    Success case prop solver time     : 0.000
% 0.20/0.37  # Current number of processed clauses  : 46
% 0.20/0.37  #    Positive orientable unit clauses  : 27
% 0.20/0.37  #    Positive unorientable unit clauses: 0
% 0.20/0.37  #    Negative unit clauses             : 1
% 0.20/0.37  #    Non-unit-clauses                  : 18
% 0.20/0.37  # Current number of unprocessed clauses: 56
% 0.20/0.37  # ...number of literals in the above   : 90
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 12
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 24
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 22
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.37  # Unit Clause-clause subsumption calls : 0
% 0.20/0.37  # Rewrite failures with RHS unbound    : 0
% 0.20/0.37  # BW rewrite match attempts            : 1
% 0.20/0.37  # BW rewrite match successes           : 0
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 2617
% 0.20/0.37  
% 0.20/0.37  # -------------------------------------------------
% 0.20/0.37  # User time                : 0.031 s
% 0.20/0.37  # System time              : 0.004 s
% 0.20/0.37  # Total time               : 0.035 s
% 0.20/0.37  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
