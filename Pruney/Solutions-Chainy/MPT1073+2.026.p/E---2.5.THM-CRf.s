%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:08:05 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   35 (  62 expanded)
%              Number of clauses        :   20 (  25 expanded)
%              Number of leaves         :    7 (  15 expanded)
%              Depth                    :    9
%              Number of atoms          :  154 ( 323 expanded)
%              Number of equality atoms :   37 (  69 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t190_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X2,X3)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
     => ~ ( r2_hidden(X1,k2_relset_1(X2,X3,X4))
          & ! [X5] :
              ( m1_subset_1(X5,X2)
             => X1 != k1_funct_1(X4,X5) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d12_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( X3 = k9_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(X5,k1_relat_1(X1))
                  & r2_hidden(X5,X2)
                  & X4 = k1_funct_1(X1,X5) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(t38_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( k7_relset_1(X1,X2,X3,X1) = k2_relset_1(X1,X2,X3)
        & k8_relset_1(X1,X2,X3,X2) = k1_relset_1(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X2,X3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
       => ~ ( r2_hidden(X1,k2_relset_1(X2,X3,X4))
            & ! [X5] :
                ( m1_subset_1(X5,X2)
               => X1 != k1_funct_1(X4,X5) ) ) ) ),
    inference(assume_negation,[status(cth)],[t190_funct_2])).

fof(c_0_8,plain,(
    ! [X24,X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
      | v1_relat_1(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_9,negated_conjecture,(
    ! [X38] :
      ( v1_funct_1(esk8_0)
      & v1_funct_2(esk8_0,esk6_0,esk7_0)
      & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))
      & r2_hidden(esk5_0,k2_relset_1(esk6_0,esk7_0,esk8_0))
      & ( ~ m1_subset_1(X38,esk6_0)
        | esk5_0 != k1_funct_1(esk8_0,X38) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).

fof(c_0_10,plain,(
    ! [X12,X13,X14,X15,X17,X18,X19,X20,X22] :
      ( ( r2_hidden(esk2_4(X12,X13,X14,X15),k1_relat_1(X12))
        | ~ r2_hidden(X15,X14)
        | X14 != k9_relat_1(X12,X13)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( r2_hidden(esk2_4(X12,X13,X14,X15),X13)
        | ~ r2_hidden(X15,X14)
        | X14 != k9_relat_1(X12,X13)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( X15 = k1_funct_1(X12,esk2_4(X12,X13,X14,X15))
        | ~ r2_hidden(X15,X14)
        | X14 != k9_relat_1(X12,X13)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( ~ r2_hidden(X18,k1_relat_1(X12))
        | ~ r2_hidden(X18,X13)
        | X17 != k1_funct_1(X12,X18)
        | r2_hidden(X17,X14)
        | X14 != k9_relat_1(X12,X13)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( ~ r2_hidden(esk3_3(X12,X19,X20),X20)
        | ~ r2_hidden(X22,k1_relat_1(X12))
        | ~ r2_hidden(X22,X19)
        | esk3_3(X12,X19,X20) != k1_funct_1(X12,X22)
        | X20 = k9_relat_1(X12,X19)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( r2_hidden(esk4_3(X12,X19,X20),k1_relat_1(X12))
        | r2_hidden(esk3_3(X12,X19,X20),X20)
        | X20 = k9_relat_1(X12,X19)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( r2_hidden(esk4_3(X12,X19,X20),X19)
        | r2_hidden(esk3_3(X12,X19,X20),X20)
        | X20 = k9_relat_1(X12,X19)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( esk3_3(X12,X19,X20) = k1_funct_1(X12,esk4_3(X12,X19,X20))
        | r2_hidden(esk3_3(X12,X19,X20),X20)
        | X20 = k9_relat_1(X12,X19)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).

cnf(c_0_11,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X10,X11] :
      ( ( ~ m1_subset_1(X11,X10)
        | r2_hidden(X11,X10)
        | v1_xboole_0(X10) )
      & ( ~ r2_hidden(X11,X10)
        | m1_subset_1(X11,X10)
        | v1_xboole_0(X10) )
      & ( ~ m1_subset_1(X11,X10)
        | v1_xboole_0(X11)
        | ~ v1_xboole_0(X10) )
      & ( ~ v1_xboole_0(X11)
        | m1_subset_1(X11,X10)
        | ~ v1_xboole_0(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_14,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_15,negated_conjecture,
    ( ~ m1_subset_1(X1,esk6_0)
    | esk5_0 != k1_funct_1(esk8_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( X1 = k1_funct_1(X2,esk2_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k9_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_19,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( X1 != k9_relat_1(esk8_0,X2)
    | esk5_0 != X3
    | ~ m1_subset_1(esk2_4(esk8_0,X2,X1,X3),esk6_0)
    | ~ r2_hidden(X3,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])]),c_0_18])])).

cnf(c_0_22,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_23,plain,(
    ! [X27,X28,X29,X30] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | k7_relset_1(X27,X28,X29,X30) = k9_relat_1(X29,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_24,plain,(
    ! [X31,X32,X33] :
      ( ( k7_relset_1(X31,X32,X33,X31) = k2_relset_1(X31,X32,X33)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( k8_relset_1(X31,X32,X33,X32) = k1_relset_1(X31,X32,X33)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).

cnf(c_0_25,negated_conjecture,
    ( X1 != k9_relat_1(esk8_0,X2)
    | esk5_0 != X3
    | ~ r2_hidden(esk2_4(esk8_0,X2,X1,X3),esk6_0)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_27,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( k7_relset_1(X1,X2,X3,X1) = k2_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( X1 != k9_relat_1(esk8_0,esk6_0)
    | esk5_0 != X2
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_17]),c_0_18])])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk5_0,k2_relset_1(esk6_0,esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_31,plain,
    ( k2_relset_1(X1,X2,X3) = k9_relat_1(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( esk5_0 != X1
    | ~ r2_hidden(X1,k9_relat_1(esk8_0,esk6_0)) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk5_0,k9_relat_1(esk8_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_12])])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_32,c_0_33]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:39:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.13/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.042 s
% 0.13/0.40  # Presaturation interreduction done
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(t190_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>~((r2_hidden(X1,k2_relset_1(X2,X3,X4))&![X5]:(m1_subset_1(X5,X2)=>X1!=k1_funct_1(X4,X5))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t190_funct_2)).
% 0.13/0.40  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.13/0.40  fof(d12_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(X3=k9_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((r2_hidden(X5,k1_relat_1(X1))&r2_hidden(X5,X2))&X4=k1_funct_1(X1,X5))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_1)).
% 0.13/0.40  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.13/0.40  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.13/0.40  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.13/0.40  fof(t38_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(k7_relset_1(X1,X2,X3,X1)=k2_relset_1(X1,X2,X3)&k8_relset_1(X1,X2,X3,X2)=k1_relset_1(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 0.13/0.40  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>~((r2_hidden(X1,k2_relset_1(X2,X3,X4))&![X5]:(m1_subset_1(X5,X2)=>X1!=k1_funct_1(X4,X5)))))), inference(assume_negation,[status(cth)],[t190_funct_2])).
% 0.13/0.40  fof(c_0_8, plain, ![X24, X25, X26]:(~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))|v1_relat_1(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.13/0.40  fof(c_0_9, negated_conjecture, ![X38]:(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,esk6_0,esk7_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))))&(r2_hidden(esk5_0,k2_relset_1(esk6_0,esk7_0,esk8_0))&(~m1_subset_1(X38,esk6_0)|esk5_0!=k1_funct_1(esk8_0,X38)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).
% 0.13/0.40  fof(c_0_10, plain, ![X12, X13, X14, X15, X17, X18, X19, X20, X22]:(((((r2_hidden(esk2_4(X12,X13,X14,X15),k1_relat_1(X12))|~r2_hidden(X15,X14)|X14!=k9_relat_1(X12,X13)|(~v1_relat_1(X12)|~v1_funct_1(X12)))&(r2_hidden(esk2_4(X12,X13,X14,X15),X13)|~r2_hidden(X15,X14)|X14!=k9_relat_1(X12,X13)|(~v1_relat_1(X12)|~v1_funct_1(X12))))&(X15=k1_funct_1(X12,esk2_4(X12,X13,X14,X15))|~r2_hidden(X15,X14)|X14!=k9_relat_1(X12,X13)|(~v1_relat_1(X12)|~v1_funct_1(X12))))&(~r2_hidden(X18,k1_relat_1(X12))|~r2_hidden(X18,X13)|X17!=k1_funct_1(X12,X18)|r2_hidden(X17,X14)|X14!=k9_relat_1(X12,X13)|(~v1_relat_1(X12)|~v1_funct_1(X12))))&((~r2_hidden(esk3_3(X12,X19,X20),X20)|(~r2_hidden(X22,k1_relat_1(X12))|~r2_hidden(X22,X19)|esk3_3(X12,X19,X20)!=k1_funct_1(X12,X22))|X20=k9_relat_1(X12,X19)|(~v1_relat_1(X12)|~v1_funct_1(X12)))&(((r2_hidden(esk4_3(X12,X19,X20),k1_relat_1(X12))|r2_hidden(esk3_3(X12,X19,X20),X20)|X20=k9_relat_1(X12,X19)|(~v1_relat_1(X12)|~v1_funct_1(X12)))&(r2_hidden(esk4_3(X12,X19,X20),X19)|r2_hidden(esk3_3(X12,X19,X20),X20)|X20=k9_relat_1(X12,X19)|(~v1_relat_1(X12)|~v1_funct_1(X12))))&(esk3_3(X12,X19,X20)=k1_funct_1(X12,esk4_3(X12,X19,X20))|r2_hidden(esk3_3(X12,X19,X20),X20)|X20=k9_relat_1(X12,X19)|(~v1_relat_1(X12)|~v1_funct_1(X12)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).
% 0.13/0.40  cnf(c_0_11, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.40  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.40  fof(c_0_13, plain, ![X10, X11]:(((~m1_subset_1(X11,X10)|r2_hidden(X11,X10)|v1_xboole_0(X10))&(~r2_hidden(X11,X10)|m1_subset_1(X11,X10)|v1_xboole_0(X10)))&((~m1_subset_1(X11,X10)|v1_xboole_0(X11)|~v1_xboole_0(X10))&(~v1_xboole_0(X11)|m1_subset_1(X11,X10)|~v1_xboole_0(X10)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.13/0.40  fof(c_0_14, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.13/0.40  cnf(c_0_15, negated_conjecture, (~m1_subset_1(X1,esk6_0)|esk5_0!=k1_funct_1(esk8_0,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.40  cnf(c_0_16, plain, (X1=k1_funct_1(X2,esk2_4(X2,X3,X4,X1))|~r2_hidden(X1,X4)|X4!=k9_relat_1(X2,X3)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.40  cnf(c_0_17, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.40  cnf(c_0_18, negated_conjecture, (v1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.13/0.40  cnf(c_0_19, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.40  cnf(c_0_20, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.40  cnf(c_0_21, negated_conjecture, (X1!=k9_relat_1(esk8_0,X2)|esk5_0!=X3|~m1_subset_1(esk2_4(esk8_0,X2,X1,X3),esk6_0)|~r2_hidden(X3,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])]), c_0_18])])).
% 0.13/0.40  cnf(c_0_22, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_19, c_0_20])).
% 0.13/0.40  fof(c_0_23, plain, ![X27, X28, X29, X30]:(~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|k7_relset_1(X27,X28,X29,X30)=k9_relat_1(X29,X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.13/0.40  fof(c_0_24, plain, ![X31, X32, X33]:((k7_relset_1(X31,X32,X33,X31)=k2_relset_1(X31,X32,X33)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))&(k8_relset_1(X31,X32,X33,X32)=k1_relset_1(X31,X32,X33)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).
% 0.13/0.40  cnf(c_0_25, negated_conjecture, (X1!=k9_relat_1(esk8_0,X2)|esk5_0!=X3|~r2_hidden(esk2_4(esk8_0,X2,X1,X3),esk6_0)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.13/0.40  cnf(c_0_26, plain, (r2_hidden(esk2_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.40  cnf(c_0_27, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.40  cnf(c_0_28, plain, (k7_relset_1(X1,X2,X3,X1)=k2_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.40  cnf(c_0_29, negated_conjecture, (X1!=k9_relat_1(esk8_0,esk6_0)|esk5_0!=X2|~r2_hidden(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_17]), c_0_18])])).
% 0.13/0.40  cnf(c_0_30, negated_conjecture, (r2_hidden(esk5_0,k2_relset_1(esk6_0,esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.40  cnf(c_0_31, plain, (k2_relset_1(X1,X2,X3)=k9_relat_1(X3,X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.40  cnf(c_0_32, negated_conjecture, (esk5_0!=X1|~r2_hidden(X1,k9_relat_1(esk8_0,esk6_0))), inference(er,[status(thm)],[c_0_29])).
% 0.13/0.40  cnf(c_0_33, negated_conjecture, (r2_hidden(esk5_0,k9_relat_1(esk8_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_12])])).
% 0.13/0.40  cnf(c_0_34, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_32, c_0_33]), ['proof']).
% 0.13/0.40  # SZS output end CNFRefutation
% 0.13/0.40  # Proof object total steps             : 35
% 0.13/0.40  # Proof object clause steps            : 20
% 0.13/0.40  # Proof object formula steps           : 15
% 0.13/0.40  # Proof object conjectures             : 14
% 0.13/0.40  # Proof object clause conjectures      : 11
% 0.13/0.40  # Proof object formula conjectures     : 3
% 0.13/0.40  # Proof object initial clauses used    : 11
% 0.13/0.40  # Proof object initial formulas used   : 7
% 0.13/0.40  # Proof object generating inferences   : 8
% 0.13/0.40  # Proof object simplifying inferences  : 10
% 0.13/0.40  # Training examples: 0 positive, 0 negative
% 0.13/0.40  # Parsed axioms                        : 7
% 0.13/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.40  # Initial clauses                      : 23
% 0.13/0.40  # Removed in clause preprocessing      : 0
% 0.13/0.40  # Initial clauses in saturation        : 23
% 0.13/0.40  # Processed clauses                    : 76
% 0.13/0.40  # ...of these trivial                  : 0
% 0.13/0.40  # ...subsumed                          : 5
% 0.13/0.40  # ...remaining for further processing  : 71
% 0.13/0.40  # Other redundant clauses eliminated   : 0
% 0.13/0.40  # Clauses deleted for lack of memory   : 0
% 0.13/0.40  # Backward-subsumed                    : 0
% 0.13/0.40  # Backward-rewritten                   : 0
% 0.13/0.40  # Generated clauses                    : 56
% 0.13/0.40  # ...of the previous two non-trivial   : 48
% 0.13/0.40  # Contextual simplify-reflections      : 1
% 0.13/0.40  # Paramodulations                      : 54
% 0.13/0.40  # Factorizations                       : 0
% 0.13/0.40  # Equation resolutions                 : 2
% 0.13/0.40  # Propositional unsat checks           : 0
% 0.13/0.40  #    Propositional check models        : 0
% 0.13/0.40  #    Propositional check unsatisfiable : 0
% 0.13/0.40  #    Propositional clauses             : 0
% 0.13/0.40  #    Propositional clauses after purity: 0
% 0.13/0.40  #    Propositional unsat core size     : 0
% 0.13/0.40  #    Propositional preprocessing time  : 0.000
% 0.13/0.40  #    Propositional encoding time       : 0.000
% 0.13/0.40  #    Propositional solver time         : 0.000
% 0.13/0.40  #    Success case prop preproc time    : 0.000
% 0.13/0.40  #    Success case prop encoding time   : 0.000
% 0.13/0.40  #    Success case prop solver time     : 0.000
% 0.13/0.40  # Current number of processed clauses  : 48
% 0.13/0.40  #    Positive orientable unit clauses  : 6
% 0.13/0.40  #    Positive unorientable unit clauses: 0
% 0.13/0.40  #    Negative unit clauses             : 3
% 0.13/0.40  #    Non-unit-clauses                  : 39
% 0.13/0.40  # Current number of unprocessed clauses: 18
% 0.13/0.40  # ...number of literals in the above   : 115
% 0.13/0.40  # Current number of archived formulas  : 0
% 0.13/0.40  # Current number of archived clauses   : 23
% 0.13/0.40  # Clause-clause subsumption calls (NU) : 204
% 0.13/0.40  # Rec. Clause-clause subsumption calls : 58
% 0.13/0.40  # Non-unit clause-clause subsumptions  : 4
% 0.13/0.40  # Unit Clause-clause subsumption calls : 6
% 0.13/0.40  # Rewrite failures with RHS unbound    : 0
% 0.13/0.40  # BW rewrite match attempts            : 0
% 0.13/0.40  # BW rewrite match successes           : 0
% 0.13/0.40  # Condensation attempts                : 0
% 0.13/0.40  # Condensation successes               : 0
% 0.13/0.40  # Termbank termtop insertions          : 2947
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.047 s
% 0.13/0.40  # System time              : 0.006 s
% 0.13/0.40  # Total time               : 0.054 s
% 0.13/0.40  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
