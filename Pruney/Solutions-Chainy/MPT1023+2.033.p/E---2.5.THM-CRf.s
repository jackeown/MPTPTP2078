%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:26 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   32 (  83 expanded)
%              Number of clauses        :   21 (  28 expanded)
%              Number of leaves         :    5 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :  117 ( 527 expanded)
%              Number of equality atoms :   11 (  55 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t113_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( ! [X5] :
                ( m1_subset_1(X5,X1)
               => k1_funct_1(X3,X5) = k1_funct_1(X4,X5) )
           => r2_relset_1(X1,X2,X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_funct_2)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(t18_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( ! [X5] :
                ( r2_hidden(X5,X1)
               => k1_funct_1(X3,X5) = k1_funct_1(X4,X5) )
           => r2_relset_1(X1,X2,X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,X2)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
           => ( ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => k1_funct_1(X3,X5) = k1_funct_1(X4,X5) )
             => r2_relset_1(X1,X2,X3,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t113_funct_2])).

fof(c_0_6,plain,(
    ! [X7] : m1_subset_1(k2_subset_1(X7),k1_zfmisc_1(X7)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_7,plain,(
    ! [X6] : k2_subset_1(X6) = X6 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_8,plain,(
    ! [X11,X12,X13,X14] :
      ( ( r2_hidden(esk1_4(X11,X12,X13,X14),X11)
        | r2_relset_1(X11,X12,X13,X14)
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,X11,X12)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,X11,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) )
      & ( k1_funct_1(X13,esk1_4(X11,X12,X13,X14)) != k1_funct_1(X14,esk1_4(X11,X12,X13,X14))
        | r2_relset_1(X11,X12,X13,X14)
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,X11,X12)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,X11,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_funct_2])])])])])).

fof(c_0_9,negated_conjecture,(
    ! [X20] :
      ( v1_funct_1(esk4_0)
      & v1_funct_2(esk4_0,esk2_0,esk3_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
      & v1_funct_1(esk5_0)
      & v1_funct_2(esk5_0,esk2_0,esk3_0)
      & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
      & ( ~ m1_subset_1(X20,esk2_0)
        | k1_funct_1(esk4_0,X20) = k1_funct_1(esk5_0,X20) )
      & ~ r2_relset_1(esk2_0,esk3_0,esk4_0,esk5_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).

fof(c_0_10,plain,(
    ! [X8,X9,X10] :
      ( ~ r2_hidden(X8,X9)
      | ~ m1_subset_1(X9,k1_zfmisc_1(X10))
      | m1_subset_1(X8,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_11,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X1)
    | r2_relset_1(X1,X2,X3,X4)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( v1_funct_2(esk5_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( r2_relset_1(X2,X3,X1,X4)
    | k1_funct_1(X1,esk1_4(X2,X3,X1,X4)) != k1_funct_1(X4,esk1_4(X2,X3,X1,X4))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,negated_conjecture,
    ( k1_funct_1(esk4_0,X1) = k1_funct_1(esk5_0,X1)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( r2_relset_1(esk2_0,esk3_0,X1,esk5_0)
    | r2_hidden(esk1_4(esk2_0,esk3_0,X1,esk5_0),esk2_0)
    | ~ v1_funct_2(X1,esk2_0,esk3_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,negated_conjecture,
    ( ~ r2_relset_1(esk2_0,esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,negated_conjecture,
    ( r2_relset_1(X1,X2,X3,esk5_0)
    | k1_funct_1(X3,esk1_4(X1,X2,X3,esk5_0)) != k1_funct_1(esk4_0,esk1_4(X1,X2,X3,esk5_0))
    | ~ v1_funct_2(esk5_0,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(esk1_4(X1,X2,X3,esk5_0),esk2_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_16])])).

cnf(c_0_27,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk1_4(esk2_0,esk3_0,esk4_0,esk5_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( r2_relset_1(X1,X2,esk4_0,esk5_0)
    | ~ v1_funct_2(esk5_0,X1,X2)
    | ~ v1_funct_2(esk4_0,X1,X2)
    | ~ m1_subset_1(esk1_4(X1,X2,esk4_0,esk5_0),esk2_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_26]),c_0_24])])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk1_4(esk2_0,esk3_0,esk4_0,esk5_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_15]),c_0_23]),c_0_14]),c_0_22])]),c_0_25]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:18:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.027 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t113_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X5]:(m1_subset_1(X5,X1)=>k1_funct_1(X3,X5)=k1_funct_1(X4,X5))=>r2_relset_1(X1,X2,X3,X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_funct_2)).
% 0.13/0.37  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.13/0.37  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.13/0.37  fof(t18_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X5]:(r2_hidden(X5,X1)=>k1_funct_1(X3,X5)=k1_funct_1(X4,X5))=>r2_relset_1(X1,X2,X3,X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_2)).
% 0.13/0.37  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.13/0.37  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X5]:(m1_subset_1(X5,X1)=>k1_funct_1(X3,X5)=k1_funct_1(X4,X5))=>r2_relset_1(X1,X2,X3,X4))))), inference(assume_negation,[status(cth)],[t113_funct_2])).
% 0.13/0.37  fof(c_0_6, plain, ![X7]:m1_subset_1(k2_subset_1(X7),k1_zfmisc_1(X7)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.13/0.37  fof(c_0_7, plain, ![X6]:k2_subset_1(X6)=X6, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.13/0.37  fof(c_0_8, plain, ![X11, X12, X13, X14]:((r2_hidden(esk1_4(X11,X12,X13,X14),X11)|r2_relset_1(X11,X12,X13,X14)|(~v1_funct_1(X14)|~v1_funct_2(X14,X11,X12)|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12))))|(~v1_funct_1(X13)|~v1_funct_2(X13,X11,X12)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))))&(k1_funct_1(X13,esk1_4(X11,X12,X13,X14))!=k1_funct_1(X14,esk1_4(X11,X12,X13,X14))|r2_relset_1(X11,X12,X13,X14)|(~v1_funct_1(X14)|~v1_funct_2(X14,X11,X12)|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12))))|(~v1_funct_1(X13)|~v1_funct_2(X13,X11,X12)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_funct_2])])])])])).
% 0.13/0.37  fof(c_0_9, negated_conjecture, ![X20]:(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk2_0,esk3_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk2_0,esk3_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))&((~m1_subset_1(X20,esk2_0)|k1_funct_1(esk4_0,X20)=k1_funct_1(esk5_0,X20))&~r2_relset_1(esk2_0,esk3_0,esk4_0,esk5_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).
% 0.13/0.37  fof(c_0_10, plain, ![X8, X9, X10]:(~r2_hidden(X8,X9)|~m1_subset_1(X9,k1_zfmisc_1(X10))|m1_subset_1(X8,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.13/0.37  cnf(c_0_11, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_12, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_13, plain, (r2_hidden(esk1_4(X1,X2,X3,X4),X1)|r2_relset_1(X1,X2,X3,X4)|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_15, negated_conjecture, (v1_funct_2(esk5_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_16, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_17, plain, (r2_relset_1(X2,X3,X1,X4)|k1_funct_1(X1,esk1_4(X2,X3,X1,X4))!=k1_funct_1(X4,esk1_4(X2,X3,X1,X4))|~v1_funct_1(X4)|~v1_funct_2(X4,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_18, negated_conjecture, (k1_funct_1(esk4_0,X1)=k1_funct_1(esk5_0,X1)|~m1_subset_1(X1,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_19, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  cnf(c_0_20, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 0.13/0.37  cnf(c_0_21, negated_conjecture, (r2_relset_1(esk2_0,esk3_0,X1,esk5_0)|r2_hidden(esk1_4(esk2_0,esk3_0,X1,esk5_0),esk2_0)|~v1_funct_2(X1,esk2_0,esk3_0)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15]), c_0_16])])).
% 0.13/0.37  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_23, negated_conjecture, (v1_funct_2(esk4_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_24, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_25, negated_conjecture, (~r2_relset_1(esk2_0,esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_26, negated_conjecture, (r2_relset_1(X1,X2,X3,esk5_0)|k1_funct_1(X3,esk1_4(X1,X2,X3,esk5_0))!=k1_funct_1(esk4_0,esk1_4(X1,X2,X3,esk5_0))|~v1_funct_2(esk5_0,X1,X2)|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X3)|~m1_subset_1(esk1_4(X1,X2,X3,esk5_0),esk2_0)|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_16])])).
% 0.13/0.37  cnf(c_0_27, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.13/0.37  cnf(c_0_28, negated_conjecture, (r2_hidden(esk1_4(esk2_0,esk3_0,esk4_0,esk5_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24])]), c_0_25])).
% 0.13/0.37  cnf(c_0_29, negated_conjecture, (r2_relset_1(X1,X2,esk4_0,esk5_0)|~v1_funct_2(esk5_0,X1,X2)|~v1_funct_2(esk4_0,X1,X2)|~m1_subset_1(esk1_4(X1,X2,esk4_0,esk5_0),esk2_0)|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_26]), c_0_24])])).
% 0.13/0.37  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk1_4(esk2_0,esk3_0,esk4_0,esk5_0),esk2_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.37  cnf(c_0_31, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_15]), c_0_23]), c_0_14]), c_0_22])]), c_0_25]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 32
% 0.13/0.37  # Proof object clause steps            : 21
% 0.13/0.37  # Proof object formula steps           : 11
% 0.13/0.37  # Proof object conjectures             : 17
% 0.13/0.37  # Proof object clause conjectures      : 14
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 13
% 0.13/0.37  # Proof object initial formulas used   : 5
% 0.13/0.37  # Proof object generating inferences   : 7
% 0.13/0.37  # Proof object simplifying inferences  : 18
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 5
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 13
% 0.13/0.37  # Removed in clause preprocessing      : 1
% 0.13/0.37  # Initial clauses in saturation        : 12
% 0.13/0.37  # Processed clauses                    : 48
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 0
% 0.13/0.37  # ...remaining for further processing  : 48
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 2
% 0.13/0.37  # Generated clauses                    : 26
% 0.13/0.37  # ...of the previous two non-trivial   : 25
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 24
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
% 0.13/0.37  # Current number of processed clauses  : 34
% 0.13/0.37  #    Positive orientable unit clauses  : 10
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 1
% 0.13/0.37  #    Non-unit-clauses                  : 23
% 0.13/0.37  # Current number of unprocessed clauses: 1
% 0.13/0.37  # ...number of literals in the above   : 8
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 15
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 86
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 29
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.37  # Unit Clause-clause subsumption calls : 5
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 11
% 0.13/0.37  # BW rewrite match successes           : 1
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 1943
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.029 s
% 0.13/0.37  # System time              : 0.004 s
% 0.13/0.37  # Total time               : 0.033 s
% 0.13/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
