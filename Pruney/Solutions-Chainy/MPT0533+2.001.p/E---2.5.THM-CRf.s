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
% DateTime   : Thu Dec  3 10:50:12 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 112 expanded)
%              Number of clauses        :   25 (  48 expanded)
%              Number of leaves         :    8 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :   98 ( 338 expanded)
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

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t117_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k8_relat_1(X1,X2),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

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

fof(t116_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k2_relat_1(k8_relat_1(X1,X2)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

fof(t125_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k8_relat_1(X1,X2) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(t132_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( r1_tarski(X2,X3)
           => r1_tarski(k8_relat_1(X1,X2),k8_relat_1(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_relat_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ! [X4] :
            ( v1_relat_1(X4)
           => ( ( r1_tarski(X3,X4)
                & r1_tarski(X1,X2) )
             => r1_tarski(k8_relat_1(X1,X3),k8_relat_1(X2,X4)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t133_relat_1])).

fof(c_0_9,plain,(
    ! [X5,X6,X7] :
      ( ~ r1_tarski(X5,X6)
      | ~ r1_tarski(X6,X7)
      | r1_tarski(X5,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_10,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_relat_1(esk4_0)
    & r1_tarski(esk3_0,esk4_0)
    & r1_tarski(esk1_0,esk2_0)
    & ~ r1_tarski(k8_relat_1(esk1_0,esk3_0),k8_relat_1(esk2_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_11,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X15)
      | r1_tarski(k8_relat_1(X14,X15),X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t117_relat_1])])).

cnf(c_0_12,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( r1_tarski(k8_relat_1(X2,X1),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | v1_relat_1(X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_17,plain,(
    ! [X8,X9] :
      ( ( ~ m1_subset_1(X8,k1_zfmisc_1(X9))
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | m1_subset_1(X8,k1_zfmisc_1(X9)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(k8_relat_1(X1,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(k8_relat_1(X1,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_24,plain,(
    ! [X12,X13] :
      ( ~ v1_relat_1(X13)
      | r1_tarski(k2_relat_1(k8_relat_1(X12,X13)),X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t116_relat_1])])).

fof(c_0_25,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X17)
      | ~ r1_tarski(k2_relat_1(X17),X16)
      | k8_relat_1(X16,X17) = X17 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(k8_relat_1(X1,esk3_0),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_29,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X2,X1)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_30,plain,(
    ! [X18,X19,X20] :
      ( ~ v1_relat_1(X19)
      | ~ v1_relat_1(X20)
      | ~ r1_tarski(X19,X20)
      | r1_tarski(k8_relat_1(X18,X19),k8_relat_1(X18,X20)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_relat_1])])])).

cnf(c_0_31,plain,
    ( k8_relat_1(X2,X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( v1_relat_1(k8_relat_1(X1,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(k2_relat_1(k8_relat_1(X1,esk3_0)),X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_15])).

cnf(c_0_35,plain,
    ( r1_tarski(k8_relat_1(X3,X1),k8_relat_1(X3,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( k8_relat_1(X1,k8_relat_1(X2,esk3_0)) = k8_relat_1(X2,esk3_0)
    | ~ r1_tarski(k2_relat_1(k8_relat_1(X2,esk3_0)),X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k2_relat_1(k8_relat_1(esk1_0,esk3_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(k8_relat_1(X1,X2),k8_relat_1(X1,esk4_0))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X2,esk4_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_21])).

cnf(c_0_39,negated_conjecture,
    ( k8_relat_1(esk2_0,k8_relat_1(esk1_0,esk3_0)) = k8_relat_1(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( ~ r1_tarski(k8_relat_1(esk1_0,esk3_0),k8_relat_1(esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_32]),c_0_23])]),c_0_40]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:59:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___107_C00_02_nc_F1_PI_AE_Q4_CS_SP_PS_S00EN
% 0.12/0.38  # and selection function PSelectSmallestOrientable.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.036 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(t133_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>![X4]:(v1_relat_1(X4)=>((r1_tarski(X3,X4)&r1_tarski(X1,X2))=>r1_tarski(k8_relat_1(X1,X3),k8_relat_1(X2,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t133_relat_1)).
% 0.12/0.38  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.12/0.38  fof(t117_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k8_relat_1(X1,X2),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_relat_1)).
% 0.12/0.38  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.12/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.12/0.38  fof(t116_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k8_relat_1(X1,X2)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_relat_1)).
% 0.12/0.38  fof(t125_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X2),X1)=>k8_relat_1(X1,X2)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 0.12/0.38  fof(t132_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X2,X3)=>r1_tarski(k8_relat_1(X1,X2),k8_relat_1(X1,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_relat_1)).
% 0.12/0.38  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>![X4]:(v1_relat_1(X4)=>((r1_tarski(X3,X4)&r1_tarski(X1,X2))=>r1_tarski(k8_relat_1(X1,X3),k8_relat_1(X2,X4)))))), inference(assume_negation,[status(cth)],[t133_relat_1])).
% 0.12/0.38  fof(c_0_9, plain, ![X5, X6, X7]:(~r1_tarski(X5,X6)|~r1_tarski(X6,X7)|r1_tarski(X5,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.12/0.38  fof(c_0_10, negated_conjecture, (v1_relat_1(esk3_0)&(v1_relat_1(esk4_0)&((r1_tarski(esk3_0,esk4_0)&r1_tarski(esk1_0,esk2_0))&~r1_tarski(k8_relat_1(esk1_0,esk3_0),k8_relat_1(esk2_0,esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.12/0.38  fof(c_0_11, plain, ![X14, X15]:(~v1_relat_1(X15)|r1_tarski(k8_relat_1(X14,X15),X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t117_relat_1])])).
% 0.12/0.38  cnf(c_0_12, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.38  cnf(c_0_13, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.38  cnf(c_0_14, plain, (r1_tarski(k8_relat_1(X2,X1),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  cnf(c_0_15, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.38  fof(c_0_16, plain, ![X10, X11]:(~v1_relat_1(X10)|(~m1_subset_1(X11,k1_zfmisc_1(X10))|v1_relat_1(X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.12/0.38  fof(c_0_17, plain, ![X8, X9]:((~m1_subset_1(X8,k1_zfmisc_1(X9))|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|m1_subset_1(X8,k1_zfmisc_1(X9)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.12/0.38  cnf(c_0_18, negated_conjecture, (r1_tarski(X1,esk4_0)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.12/0.38  cnf(c_0_19, negated_conjecture, (r1_tarski(k8_relat_1(X1,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.12/0.38  cnf(c_0_20, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.38  cnf(c_0_21, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.38  cnf(c_0_22, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.38  cnf(c_0_23, negated_conjecture, (r1_tarski(k8_relat_1(X1,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.12/0.38  fof(c_0_24, plain, ![X12, X13]:(~v1_relat_1(X13)|r1_tarski(k2_relat_1(k8_relat_1(X12,X13)),X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t116_relat_1])])).
% 0.12/0.38  fof(c_0_25, plain, ![X16, X17]:(~v1_relat_1(X17)|(~r1_tarski(k2_relat_1(X17),X16)|k8_relat_1(X16,X17)=X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).
% 0.12/0.38  cnf(c_0_26, negated_conjecture, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.12/0.38  cnf(c_0_27, negated_conjecture, (m1_subset_1(k8_relat_1(X1,esk3_0),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.12/0.38  cnf(c_0_28, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.38  cnf(c_0_29, plain, (r1_tarski(k2_relat_1(k8_relat_1(X2,X1)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.38  fof(c_0_30, plain, ![X18, X19, X20]:(~v1_relat_1(X19)|(~v1_relat_1(X20)|(~r1_tarski(X19,X20)|r1_tarski(k8_relat_1(X18,X19),k8_relat_1(X18,X20))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_relat_1])])])).
% 0.12/0.38  cnf(c_0_31, plain, (k8_relat_1(X2,X1)=X1|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.38  cnf(c_0_32, negated_conjecture, (v1_relat_1(k8_relat_1(X1,esk3_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.12/0.38  cnf(c_0_33, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,esk1_0)), inference(spm,[status(thm)],[c_0_12, c_0_28])).
% 0.12/0.38  cnf(c_0_34, negated_conjecture, (r1_tarski(k2_relat_1(k8_relat_1(X1,esk3_0)),X1)), inference(spm,[status(thm)],[c_0_29, c_0_15])).
% 0.12/0.38  cnf(c_0_35, plain, (r1_tarski(k8_relat_1(X3,X1),k8_relat_1(X3,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.38  cnf(c_0_36, negated_conjecture, (k8_relat_1(X1,k8_relat_1(X2,esk3_0))=k8_relat_1(X2,esk3_0)|~r1_tarski(k2_relat_1(k8_relat_1(X2,esk3_0)),X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.12/0.38  cnf(c_0_37, negated_conjecture, (r1_tarski(k2_relat_1(k8_relat_1(esk1_0,esk3_0)),esk2_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.12/0.38  cnf(c_0_38, negated_conjecture, (r1_tarski(k8_relat_1(X1,X2),k8_relat_1(X1,esk4_0))|~v1_relat_1(X2)|~r1_tarski(X2,esk4_0)), inference(spm,[status(thm)],[c_0_35, c_0_21])).
% 0.12/0.38  cnf(c_0_39, negated_conjecture, (k8_relat_1(esk2_0,k8_relat_1(esk1_0,esk3_0))=k8_relat_1(esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.12/0.38  cnf(c_0_40, negated_conjecture, (~r1_tarski(k8_relat_1(esk1_0,esk3_0),k8_relat_1(esk2_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.38  cnf(c_0_41, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_32]), c_0_23])]), c_0_40]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 42
% 0.12/0.38  # Proof object clause steps            : 25
% 0.12/0.38  # Proof object formula steps           : 17
% 0.12/0.38  # Proof object conjectures             : 21
% 0.12/0.38  # Proof object clause conjectures      : 18
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 12
% 0.12/0.38  # Proof object initial formulas used   : 8
% 0.12/0.38  # Proof object generating inferences   : 13
% 0.12/0.38  # Proof object simplifying inferences  : 4
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 8
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 13
% 0.12/0.38  # Removed in clause preprocessing      : 0
% 0.12/0.38  # Initial clauses in saturation        : 13
% 0.12/0.38  # Processed clauses                    : 137
% 0.12/0.38  # ...of these trivial                  : 9
% 0.12/0.38  # ...subsumed                          : 0
% 0.12/0.38  # ...remaining for further processing  : 128
% 0.12/0.38  # Other redundant clauses eliminated   : 0
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 1
% 0.12/0.38  # Backward-rewritten                   : 2
% 0.12/0.38  # Generated clauses                    : 412
% 0.12/0.38  # ...of the previous two non-trivial   : 332
% 0.12/0.38  # Contextual simplify-reflections      : 0
% 0.12/0.38  # Paramodulations                      : 412
% 0.12/0.38  # Factorizations                       : 0
% 0.12/0.38  # Equation resolutions                 : 0
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 112
% 0.12/0.38  #    Positive orientable unit clauses  : 74
% 0.12/0.38  #    Positive unorientable unit clauses: 0
% 0.12/0.38  #    Negative unit clauses             : 1
% 0.12/0.38  #    Non-unit-clauses                  : 37
% 0.12/0.38  # Current number of unprocessed clauses: 219
% 0.12/0.38  # ...number of literals in the above   : 337
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 16
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 137
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 121
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.38  # Unit Clause-clause subsumption calls : 2
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 124
% 0.12/0.38  # BW rewrite match successes           : 3
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 6716
% 0.12/0.39  
% 0.12/0.39  # -------------------------------------------------
% 0.12/0.39  # User time                : 0.047 s
% 0.12/0.39  # System time              : 0.006 s
% 0.12/0.39  # Total time               : 0.053 s
% 0.12/0.39  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
