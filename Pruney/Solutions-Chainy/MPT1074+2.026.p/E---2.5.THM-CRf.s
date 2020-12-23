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
% DateTime   : Thu Dec  3 11:08:13 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 116 expanded)
%              Number of clauses        :   26 (  45 expanded)
%              Number of leaves         :    5 (  27 expanded)
%              Depth                    :   12
%              Number of atoms          :  146 ( 643 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t191_funct_2,conjecture,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ~ v1_xboole_0(X3)
         => ! [X4] :
              ( ( v1_funct_1(X4)
                & v1_funct_2(X4,X2,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
             => ( ! [X5] :
                    ( m1_subset_1(X5,X2)
                   => r2_hidden(k3_funct_2(X2,X3,X4,X5),X1) )
               => r1_tarski(k2_relset_1(X2,X3,X4),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_funct_2)).

fof(t17_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ~ ( r2_hidden(X3,k2_relset_1(X1,X2,X4))
          & ! [X5] :
              ~ ( r2_hidden(X5,X1)
                & k1_funct_1(X4,X5) = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_2)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(redefinition_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => k3_funct_2(X1,X2,X3,X4) = k1_funct_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ! [X3] :
            ( ~ v1_xboole_0(X3)
           => ! [X4] :
                ( ( v1_funct_1(X4)
                  & v1_funct_2(X4,X2,X3)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
               => ( ! [X5] :
                      ( m1_subset_1(X5,X2)
                     => r2_hidden(k3_funct_2(X2,X3,X4,X5),X1) )
                 => r1_tarski(k2_relset_1(X2,X3,X4),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t191_funct_2])).

fof(c_0_6,plain,(
    ! [X18,X19,X20,X21] :
      ( ( r2_hidden(esk2_4(X18,X19,X20,X21),X18)
        | ~ r2_hidden(X20,k2_relset_1(X18,X19,X21))
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,X18,X19)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) )
      & ( k1_funct_1(X21,esk2_4(X18,X19,X20,X21)) = X20
        | ~ r2_hidden(X20,k2_relset_1(X18,X19,X21))
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,X18,X19)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_funct_2])])])])).

fof(c_0_7,negated_conjecture,(
    ! [X27] :
      ( ~ v1_xboole_0(esk4_0)
      & ~ v1_xboole_0(esk5_0)
      & v1_funct_1(esk6_0)
      & v1_funct_2(esk6_0,esk4_0,esk5_0)
      & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
      & ( ~ m1_subset_1(X27,esk4_0)
        | r2_hidden(k3_funct_2(esk4_0,esk5_0,esk6_0,X27),esk3_0) )
      & ~ r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),esk3_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])])).

cnf(c_0_8,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X3,k2_relset_1(X1,X2,X4))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( r2_hidden(esk2_4(X1,X2,X3,esk6_0),X1)
    | ~ v1_funct_2(esk6_0,X1,X2)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k2_relset_1(X1,X2,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_13,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_14,plain,(
    ! [X14,X15,X16,X17] :
      ( v1_xboole_0(X14)
      | ~ v1_funct_1(X16)
      | ~ v1_funct_2(X16,X14,X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
      | ~ m1_subset_1(X17,X14)
      | k3_funct_2(X14,X15,X16,X17) = k1_funct_1(X16,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).

fof(c_0_15,plain,(
    ! [X12,X13] :
      ( ( ~ m1_subset_1(X13,X12)
        | r2_hidden(X13,X12)
        | v1_xboole_0(X12) )
      & ( ~ r2_hidden(X13,X12)
        | m1_subset_1(X13,X12)
        | v1_xboole_0(X12) )
      & ( ~ m1_subset_1(X13,X12)
        | v1_xboole_0(X13)
        | ~ v1_xboole_0(X12) )
      & ( ~ v1_xboole_0(X13)
        | m1_subset_1(X13,X12)
        | ~ v1_xboole_0(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk2_4(esk4_0,esk5_0,X1,esk6_0),esk4_0)
    | ~ r2_hidden(X1,k2_relset_1(esk4_0,esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])])).

cnf(c_0_17,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X4) = k1_funct_1(X2,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk2_4(esk4_0,esk5_0,esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X1),esk6_0),esk4_0)
    | r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_22,negated_conjecture,
    ( k3_funct_2(X1,X2,esk6_0,X3) = k1_funct_1(esk6_0,X3)
    | v1_xboole_0(X1)
    | ~ v1_funct_2(esk6_0,X1,X2)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_9])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk2_4(esk4_0,esk5_0,esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X1),esk6_0),esk4_0)
    | r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

cnf(c_0_24,plain,
    ( k1_funct_1(X1,esk2_4(X2,X3,X4,X1)) = X4
    | ~ r2_hidden(X4,k2_relset_1(X2,X3,X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(k3_funct_2(esk4_0,esk5_0,esk6_0,X1),esk3_0)
    | ~ m1_subset_1(X1,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_26,negated_conjecture,
    ( k3_funct_2(esk4_0,X1,esk6_0,esk2_4(esk4_0,esk5_0,esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X2),esk6_0)) = k1_funct_1(esk6_0,esk2_4(esk4_0,esk5_0,esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X2),esk6_0))
    | r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),X2)
    | ~ v1_funct_2(esk6_0,esk4_0,X1)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( k1_funct_1(esk6_0,esk2_4(X1,X2,X3,esk6_0)) = X3
    | ~ v1_funct_2(esk6_0,X1,X2)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k2_relset_1(X1,X2,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_9])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(k3_funct_2(esk4_0,esk5_0,esk6_0,esk2_4(esk4_0,esk5_0,esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X1),esk6_0)),esk3_0)
    | r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( k3_funct_2(esk4_0,esk5_0,esk6_0,esk2_4(esk4_0,esk5_0,esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X1),esk6_0)) = k1_funct_1(esk6_0,esk2_4(esk4_0,esk5_0,esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X1),esk6_0))
    | r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_11]),c_0_12])])).

cnf(c_0_30,negated_conjecture,
    ( k1_funct_1(esk6_0,esk2_4(esk4_0,esk5_0,X1,esk6_0)) = X1
    | ~ r2_hidden(X1,k2_relset_1(esk4_0,esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_11]),c_0_12])])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk6_0,esk2_4(esk4_0,esk5_0,esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X1),esk6_0)),esk3_0)
    | r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( k1_funct_1(esk6_0,esk2_4(esk4_0,esk5_0,esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X1),esk6_0)) = esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X1)
    | r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_17])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X1),esk3_0)
    | r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( ~ r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:05:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S076N
% 0.19/0.40  # and selection function SelectCQIAr.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.050 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t191_funct_2, conjecture, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>(![X5]:(m1_subset_1(X5,X2)=>r2_hidden(k3_funct_2(X2,X3,X4,X5),X1))=>r1_tarski(k2_relset_1(X2,X3,X4),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t191_funct_2)).
% 0.19/0.40  fof(t17_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>~((r2_hidden(X3,k2_relset_1(X1,X2,X4))&![X5]:~((r2_hidden(X5,X1)&k1_funct_1(X4,X5)=X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_funct_2)).
% 0.19/0.40  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.40  fof(redefinition_k3_funct_2, axiom, ![X1, X2, X3, X4]:(((((~(v1_xboole_0(X1))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,X1))=>k3_funct_2(X1,X2,X3,X4)=k1_funct_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 0.19/0.40  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.19/0.40  fof(c_0_5, negated_conjecture, ~(![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>(![X5]:(m1_subset_1(X5,X2)=>r2_hidden(k3_funct_2(X2,X3,X4,X5),X1))=>r1_tarski(k2_relset_1(X2,X3,X4),X1)))))), inference(assume_negation,[status(cth)],[t191_funct_2])).
% 0.19/0.40  fof(c_0_6, plain, ![X18, X19, X20, X21]:((r2_hidden(esk2_4(X18,X19,X20,X21),X18)|~r2_hidden(X20,k2_relset_1(X18,X19,X21))|(~v1_funct_1(X21)|~v1_funct_2(X21,X18,X19)|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))))&(k1_funct_1(X21,esk2_4(X18,X19,X20,X21))=X20|~r2_hidden(X20,k2_relset_1(X18,X19,X21))|(~v1_funct_1(X21)|~v1_funct_2(X21,X18,X19)|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_funct_2])])])])).
% 0.19/0.40  fof(c_0_7, negated_conjecture, ![X27]:(~v1_xboole_0(esk4_0)&(~v1_xboole_0(esk5_0)&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk4_0,esk5_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))))&((~m1_subset_1(X27,esk4_0)|r2_hidden(k3_funct_2(esk4_0,esk5_0,esk6_0,X27),esk3_0))&~r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),esk3_0))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])])).
% 0.19/0.40  cnf(c_0_8, plain, (r2_hidden(esk2_4(X1,X2,X3,X4),X1)|~r2_hidden(X3,k2_relset_1(X1,X2,X4))|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.40  cnf(c_0_9, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.40  cnf(c_0_10, negated_conjecture, (r2_hidden(esk2_4(X1,X2,X3,esk6_0),X1)|~v1_funct_2(esk6_0,X1,X2)|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r2_hidden(X3,k2_relset_1(X1,X2,esk6_0))), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.19/0.40  cnf(c_0_11, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.40  cnf(c_0_12, negated_conjecture, (v1_funct_2(esk6_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.40  fof(c_0_13, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.40  fof(c_0_14, plain, ![X14, X15, X16, X17]:(v1_xboole_0(X14)|~v1_funct_1(X16)|~v1_funct_2(X16,X14,X15)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))|~m1_subset_1(X17,X14)|k3_funct_2(X14,X15,X16,X17)=k1_funct_1(X16,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).
% 0.19/0.40  fof(c_0_15, plain, ![X12, X13]:(((~m1_subset_1(X13,X12)|r2_hidden(X13,X12)|v1_xboole_0(X12))&(~r2_hidden(X13,X12)|m1_subset_1(X13,X12)|v1_xboole_0(X12)))&((~m1_subset_1(X13,X12)|v1_xboole_0(X13)|~v1_xboole_0(X12))&(~v1_xboole_0(X13)|m1_subset_1(X13,X12)|~v1_xboole_0(X12)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.19/0.40  cnf(c_0_16, negated_conjecture, (r2_hidden(esk2_4(esk4_0,esk5_0,X1,esk6_0),esk4_0)|~r2_hidden(X1,k2_relset_1(esk4_0,esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12])])).
% 0.19/0.40  cnf(c_0_17, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.40  cnf(c_0_18, plain, (v1_xboole_0(X1)|k3_funct_2(X1,X3,X2,X4)=k1_funct_1(X2,X4)|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~m1_subset_1(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.40  cnf(c_0_19, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.40  cnf(c_0_20, negated_conjecture, (r2_hidden(esk2_4(esk4_0,esk5_0,esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X1),esk6_0),esk4_0)|r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.40  cnf(c_0_21, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.40  cnf(c_0_22, negated_conjecture, (k3_funct_2(X1,X2,esk6_0,X3)=k1_funct_1(esk6_0,X3)|v1_xboole_0(X1)|~v1_funct_2(esk6_0,X1,X2)|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,X1)), inference(spm,[status(thm)],[c_0_18, c_0_9])).
% 0.19/0.40  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk2_4(esk4_0,esk5_0,esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X1),esk6_0),esk4_0)|r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])).
% 0.19/0.40  cnf(c_0_24, plain, (k1_funct_1(X1,esk2_4(X2,X3,X4,X1))=X4|~r2_hidden(X4,k2_relset_1(X2,X3,X1))|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.40  cnf(c_0_25, negated_conjecture, (r2_hidden(k3_funct_2(esk4_0,esk5_0,esk6_0,X1),esk3_0)|~m1_subset_1(X1,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.40  cnf(c_0_26, negated_conjecture, (k3_funct_2(esk4_0,X1,esk6_0,esk2_4(esk4_0,esk5_0,esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X2),esk6_0))=k1_funct_1(esk6_0,esk2_4(esk4_0,esk5_0,esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X2),esk6_0))|r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),X2)|~v1_funct_2(esk6_0,esk4_0,X1)|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_21])).
% 0.19/0.40  cnf(c_0_27, negated_conjecture, (k1_funct_1(esk6_0,esk2_4(X1,X2,X3,esk6_0))=X3|~v1_funct_2(esk6_0,X1,X2)|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r2_hidden(X3,k2_relset_1(X1,X2,esk6_0))), inference(spm,[status(thm)],[c_0_24, c_0_9])).
% 0.19/0.40  cnf(c_0_28, negated_conjecture, (r2_hidden(k3_funct_2(esk4_0,esk5_0,esk6_0,esk2_4(esk4_0,esk5_0,esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X1),esk6_0)),esk3_0)|r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_25, c_0_23])).
% 0.19/0.40  cnf(c_0_29, negated_conjecture, (k3_funct_2(esk4_0,esk5_0,esk6_0,esk2_4(esk4_0,esk5_0,esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X1),esk6_0))=k1_funct_1(esk6_0,esk2_4(esk4_0,esk5_0,esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X1),esk6_0))|r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_11]), c_0_12])])).
% 0.19/0.40  cnf(c_0_30, negated_conjecture, (k1_funct_1(esk6_0,esk2_4(esk4_0,esk5_0,X1,esk6_0))=X1|~r2_hidden(X1,k2_relset_1(esk4_0,esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_11]), c_0_12])])).
% 0.19/0.40  cnf(c_0_31, negated_conjecture, (r2_hidden(k1_funct_1(esk6_0,esk2_4(esk4_0,esk5_0,esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X1),esk6_0)),esk3_0)|r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.40  cnf(c_0_32, negated_conjecture, (k1_funct_1(esk6_0,esk2_4(esk4_0,esk5_0,esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X1),esk6_0))=esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X1)|r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_30, c_0_17])).
% 0.19/0.40  cnf(c_0_33, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.40  cnf(c_0_34, negated_conjecture, (r2_hidden(esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X1),esk3_0)|r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.40  cnf(c_0_35, negated_conjecture, (~r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.40  cnf(c_0_36, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 37
% 0.19/0.40  # Proof object clause steps            : 26
% 0.19/0.40  # Proof object formula steps           : 11
% 0.19/0.40  # Proof object conjectures             : 23
% 0.19/0.40  # Proof object clause conjectures      : 20
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 12
% 0.19/0.40  # Proof object initial formulas used   : 5
% 0.19/0.40  # Proof object generating inferences   : 14
% 0.19/0.40  # Proof object simplifying inferences  : 9
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 5
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 17
% 0.19/0.40  # Removed in clause preprocessing      : 0
% 0.19/0.40  # Initial clauses in saturation        : 17
% 0.19/0.40  # Processed clauses                    : 75
% 0.19/0.40  # ...of these trivial                  : 0
% 0.19/0.40  # ...subsumed                          : 10
% 0.19/0.40  # ...remaining for further processing  : 65
% 0.19/0.40  # Other redundant clauses eliminated   : 0
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 0
% 0.19/0.40  # Backward-rewritten                   : 0
% 0.19/0.40  # Generated clauses                    : 47
% 0.19/0.40  # ...of the previous two non-trivial   : 44
% 0.19/0.40  # Contextual simplify-reflections      : 0
% 0.19/0.40  # Paramodulations                      : 47
% 0.19/0.40  # Factorizations                       : 0
% 0.19/0.40  # Equation resolutions                 : 0
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
% 0.19/0.40  # Current number of processed clauses  : 48
% 0.19/0.40  #    Positive orientable unit clauses  : 4
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 3
% 0.19/0.40  #    Non-unit-clauses                  : 41
% 0.19/0.40  # Current number of unprocessed clauses: 2
% 0.19/0.40  # ...number of literals in the above   : 6
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 17
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 324
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 111
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 10
% 0.19/0.40  # Unit Clause-clause subsumption calls : 13
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 3
% 0.19/0.40  # BW rewrite match successes           : 0
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 3119
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.055 s
% 0.19/0.40  # System time              : 0.006 s
% 0.19/0.40  # Total time               : 0.061 s
% 0.19/0.40  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
