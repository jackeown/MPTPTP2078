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
% DateTime   : Thu Dec  3 11:08:14 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   33 ( 100 expanded)
%              Number of clauses        :   24 (  39 expanded)
%              Number of leaves         :    4 (  23 expanded)
%              Depth                    :   11
%              Number of atoms          :  123 ( 547 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   10 (   3 average)
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

fof(t190_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X2,X3)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
     => ~ ( r2_hidden(X1,k2_relset_1(X2,X3,X4))
          & ! [X5] :
              ( m1_subset_1(X5,X2)
             => X1 != k1_funct_1(X4,X5) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).

fof(redefinition_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => k3_funct_2(X1,X2,X3,X4) = k1_funct_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_4,negated_conjecture,(
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

fof(c_0_5,plain,(
    ! [X16,X17,X18,X19] :
      ( ( m1_subset_1(esk2_4(X16,X17,X18,X19),X17)
        | ~ r2_hidden(X16,k2_relset_1(X17,X18,X19))
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,X17,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( X16 = k1_funct_1(X19,esk2_4(X16,X17,X18,X19))
        | ~ r2_hidden(X16,k2_relset_1(X17,X18,X19))
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,X17,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t190_funct_2])])])])).

fof(c_0_6,negated_conjecture,(
    ! [X25] :
      ( ~ v1_xboole_0(esk4_0)
      & ~ v1_xboole_0(esk5_0)
      & v1_funct_1(esk6_0)
      & v1_funct_2(esk6_0,esk4_0,esk5_0)
      & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
      & ( ~ m1_subset_1(X25,esk4_0)
        | r2_hidden(k3_funct_2(esk4_0,esk5_0,esk6_0,X25),esk3_0) )
      & ~ r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),esk3_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])])).

cnf(c_0_7,plain,
    ( m1_subset_1(esk2_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X1,k2_relset_1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,plain,(
    ! [X12,X13,X14,X15] :
      ( v1_xboole_0(X12)
      | ~ v1_funct_1(X14)
      | ~ v1_funct_2(X14,X12,X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
      | ~ m1_subset_1(X15,X12)
      | k3_funct_2(X12,X13,X14,X15) = k1_funct_1(X14,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk2_4(X1,X2,X3,esk6_0),X2)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_2(esk6_0,X2,X3)
    | ~ r2_hidden(X1,k2_relset_1(X2,X3,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

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

cnf(c_0_14,plain,
    ( v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X4) = k1_funct_1(X2,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk2_4(X1,esk4_0,esk5_0,esk6_0),esk4_0)
    | ~ r2_hidden(X1,k2_relset_1(esk4_0,esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])])).

cnf(c_0_16,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( k3_funct_2(X1,X2,esk6_0,X3) = k1_funct_1(esk6_0,X3)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,X1)
    | ~ v1_funct_2(esk6_0,X1,X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_8])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk2_4(esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X1),esk4_0,esk5_0,esk6_0),esk4_0)
    | r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,plain,
    ( X1 = k1_funct_1(X2,esk2_4(X1,X3,X4,X2))
    | ~ r2_hidden(X1,k2_relset_1(X3,X4,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(k3_funct_2(esk4_0,esk5_0,esk6_0,X1),esk3_0)
    | ~ m1_subset_1(X1,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,negated_conjecture,
    ( k3_funct_2(esk4_0,X1,esk6_0,esk2_4(esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X2),esk4_0,esk5_0,esk6_0)) = k1_funct_1(esk6_0,esk2_4(esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X2),esk4_0,esk5_0,esk6_0))
    | r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),X2)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))
    | ~ v1_funct_2(esk6_0,esk4_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( k1_funct_1(esk6_0,esk2_4(X1,X2,X3,esk6_0)) = X1
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_2(esk6_0,X2,X3)
    | ~ r2_hidden(X1,k2_relset_1(X2,X3,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_8])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(k3_funct_2(esk4_0,esk5_0,esk6_0,esk2_4(esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X1),esk4_0,esk5_0,esk6_0)),esk3_0)
    | r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( k3_funct_2(esk4_0,esk5_0,esk6_0,esk2_4(esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X1),esk4_0,esk5_0,esk6_0)) = k1_funct_1(esk6_0,esk2_4(esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X1),esk4_0,esk5_0,esk6_0))
    | r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_11]),c_0_12])])).

cnf(c_0_26,negated_conjecture,
    ( k1_funct_1(esk6_0,esk2_4(X1,esk4_0,esk5_0,esk6_0)) = X1
    | ~ r2_hidden(X1,k2_relset_1(esk4_0,esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_11]),c_0_12])])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk6_0,esk2_4(esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X1),esk4_0,esk5_0,esk6_0)),esk3_0)
    | r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( k1_funct_1(esk6_0,esk2_4(esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X1),esk4_0,esk5_0,esk6_0)) = esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X1)
    | r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_16])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X1),esk3_0)
    | r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( ~ r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:44:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S076N
% 0.13/0.38  # and selection function SelectCQIAr.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t191_funct_2, conjecture, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>(![X5]:(m1_subset_1(X5,X2)=>r2_hidden(k3_funct_2(X2,X3,X4,X5),X1))=>r1_tarski(k2_relset_1(X2,X3,X4),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t191_funct_2)).
% 0.13/0.38  fof(t190_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>~((r2_hidden(X1,k2_relset_1(X2,X3,X4))&![X5]:(m1_subset_1(X5,X2)=>X1!=k1_funct_1(X4,X5))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t190_funct_2)).
% 0.13/0.38  fof(redefinition_k3_funct_2, axiom, ![X1, X2, X3, X4]:(((((~(v1_xboole_0(X1))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,X1))=>k3_funct_2(X1,X2,X3,X4)=k1_funct_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 0.13/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.38  fof(c_0_4, negated_conjecture, ~(![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>(![X5]:(m1_subset_1(X5,X2)=>r2_hidden(k3_funct_2(X2,X3,X4,X5),X1))=>r1_tarski(k2_relset_1(X2,X3,X4),X1)))))), inference(assume_negation,[status(cth)],[t191_funct_2])).
% 0.13/0.38  fof(c_0_5, plain, ![X16, X17, X18, X19]:((m1_subset_1(esk2_4(X16,X17,X18,X19),X17)|~r2_hidden(X16,k2_relset_1(X17,X18,X19))|(~v1_funct_1(X19)|~v1_funct_2(X19,X17,X18)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))))&(X16=k1_funct_1(X19,esk2_4(X16,X17,X18,X19))|~r2_hidden(X16,k2_relset_1(X17,X18,X19))|(~v1_funct_1(X19)|~v1_funct_2(X19,X17,X18)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t190_funct_2])])])])).
% 0.13/0.38  fof(c_0_6, negated_conjecture, ![X25]:(~v1_xboole_0(esk4_0)&(~v1_xboole_0(esk5_0)&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk4_0,esk5_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))))&((~m1_subset_1(X25,esk4_0)|r2_hidden(k3_funct_2(esk4_0,esk5_0,esk6_0,X25),esk3_0))&~r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),esk3_0))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])])).
% 0.13/0.38  cnf(c_0_7, plain, (m1_subset_1(esk2_4(X1,X2,X3,X4),X2)|~r2_hidden(X1,k2_relset_1(X2,X3,X4))|~v1_funct_1(X4)|~v1_funct_2(X4,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.38  cnf(c_0_8, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  fof(c_0_9, plain, ![X12, X13, X14, X15]:(v1_xboole_0(X12)|~v1_funct_1(X14)|~v1_funct_2(X14,X12,X13)|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))|~m1_subset_1(X15,X12)|k3_funct_2(X12,X13,X14,X15)=k1_funct_1(X14,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).
% 0.13/0.38  cnf(c_0_10, negated_conjecture, (m1_subset_1(esk2_4(X1,X2,X3,esk6_0),X2)|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_2(esk6_0,X2,X3)|~r2_hidden(X1,k2_relset_1(X2,X3,esk6_0))), inference(spm,[status(thm)],[c_0_7, c_0_8])).
% 0.13/0.38  cnf(c_0_11, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_12, negated_conjecture, (v1_funct_2(esk6_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  fof(c_0_13, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.38  cnf(c_0_14, plain, (v1_xboole_0(X1)|k3_funct_2(X1,X3,X2,X4)=k1_funct_1(X2,X4)|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~m1_subset_1(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk2_4(X1,esk4_0,esk5_0,esk6_0),esk4_0)|~r2_hidden(X1,k2_relset_1(esk4_0,esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12])])).
% 0.13/0.38  cnf(c_0_16, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_17, negated_conjecture, (k3_funct_2(X1,X2,esk6_0,X3)=k1_funct_1(esk6_0,X3)|v1_xboole_0(X1)|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,X1)|~v1_funct_2(esk6_0,X1,X2)), inference(spm,[status(thm)],[c_0_14, c_0_8])).
% 0.13/0.38  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk2_4(esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X1),esk4_0,esk5_0,esk6_0),esk4_0)|r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.13/0.38  cnf(c_0_19, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_20, plain, (X1=k1_funct_1(X2,esk2_4(X1,X3,X4,X2))|~r2_hidden(X1,k2_relset_1(X3,X4,X2))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.38  cnf(c_0_21, negated_conjecture, (r2_hidden(k3_funct_2(esk4_0,esk5_0,esk6_0,X1),esk3_0)|~m1_subset_1(X1,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (k3_funct_2(esk4_0,X1,esk6_0,esk2_4(esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X2),esk4_0,esk5_0,esk6_0))=k1_funct_1(esk6_0,esk2_4(esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X2),esk4_0,esk5_0,esk6_0))|r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),X2)|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))|~v1_funct_2(esk6_0,esk4_0,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (k1_funct_1(esk6_0,esk2_4(X1,X2,X3,esk6_0))=X1|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_2(esk6_0,X2,X3)|~r2_hidden(X1,k2_relset_1(X2,X3,esk6_0))), inference(spm,[status(thm)],[c_0_20, c_0_8])).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (r2_hidden(k3_funct_2(esk4_0,esk5_0,esk6_0,esk2_4(esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X1),esk4_0,esk5_0,esk6_0)),esk3_0)|r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_21, c_0_18])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (k3_funct_2(esk4_0,esk5_0,esk6_0,esk2_4(esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X1),esk4_0,esk5_0,esk6_0))=k1_funct_1(esk6_0,esk2_4(esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X1),esk4_0,esk5_0,esk6_0))|r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_11]), c_0_12])])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (k1_funct_1(esk6_0,esk2_4(X1,esk4_0,esk5_0,esk6_0))=X1|~r2_hidden(X1,k2_relset_1(esk4_0,esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_11]), c_0_12])])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (r2_hidden(k1_funct_1(esk6_0,esk2_4(esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X1),esk4_0,esk5_0,esk6_0)),esk3_0)|r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (k1_funct_1(esk6_0,esk2_4(esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X1),esk4_0,esk5_0,esk6_0))=esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X1)|r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_26, c_0_16])).
% 0.13/0.38  cnf(c_0_29, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (r2_hidden(esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X1),esk3_0)|r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (~r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 33
% 0.13/0.38  # Proof object clause steps            : 24
% 0.13/0.38  # Proof object formula steps           : 9
% 0.13/0.38  # Proof object conjectures             : 22
% 0.13/0.38  # Proof object clause conjectures      : 19
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 11
% 0.13/0.38  # Proof object initial formulas used   : 4
% 0.13/0.38  # Proof object generating inferences   : 13
% 0.13/0.38  # Proof object simplifying inferences  : 8
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 4
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 13
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 13
% 0.13/0.38  # Processed clauses                    : 40
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 0
% 0.13/0.38  # ...remaining for further processing  : 40
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 0
% 0.13/0.38  # Generated clauses                    : 16
% 0.13/0.38  # ...of the previous two non-trivial   : 14
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 16
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
% 0.13/0.38  # Current number of processed clauses  : 27
% 0.13/0.38  #    Positive orientable unit clauses  : 4
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 3
% 0.13/0.38  #    Non-unit-clauses                  : 20
% 0.13/0.38  # Current number of unprocessed clauses: 0
% 0.13/0.38  # ...number of literals in the above   : 0
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 13
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 43
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 19
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.38  # Unit Clause-clause subsumption calls : 4
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 3
% 0.13/0.38  # BW rewrite match successes           : 0
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 1889
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.029 s
% 0.13/0.38  # System time              : 0.004 s
% 0.13/0.38  # Total time               : 0.033 s
% 0.13/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
