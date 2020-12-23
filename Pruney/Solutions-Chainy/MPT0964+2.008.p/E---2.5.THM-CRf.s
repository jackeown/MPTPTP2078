%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:01:09 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 131 expanded)
%              Number of clauses        :   25 (  49 expanded)
%              Number of leaves         :    8 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :  151 ( 577 expanded)
%              Number of equality atoms :   42 ( 125 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t6_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_hidden(X3,X1)
       => ( X2 = k1_xboole_0
          | r2_hidden(k1_funct_1(X4,X3),k2_relset_1(X1,X2,X4)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

fof(d1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => ( v1_funct_2(X3,X1,X2)
          <=> X1 = k1_relset_1(X1,X2,X3) ) )
        & ( X2 = k1_xboole_0
         => ( X1 = k1_xboole_0
            | ( v1_funct_2(X3,X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t22_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
     => ( ! [X4] :
            ~ ( r2_hidden(X4,X2)
              & ! [X5] : ~ r2_hidden(k4_tarski(X4,X5),X3) )
      <=> k1_relset_1(X2,X1,X3) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t12_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => r2_hidden(k1_funct_1(X2,X1),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( r2_hidden(X3,X1)
         => ( X2 = k1_xboole_0
            | r2_hidden(k1_funct_1(X4,X3),k2_relset_1(X1,X2,X4)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t6_funct_2])).

fof(c_0_9,plain,(
    ! [X25,X26,X27] :
      ( ( ~ v1_funct_2(X27,X25,X26)
        | X25 = k1_relset_1(X25,X26,X27)
        | X26 = k1_xboole_0
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( X25 != k1_relset_1(X25,X26,X27)
        | v1_funct_2(X27,X25,X26)
        | X26 = k1_xboole_0
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( ~ v1_funct_2(X27,X25,X26)
        | X25 = k1_relset_1(X25,X26,X27)
        | X25 != k1_xboole_0
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( X25 != k1_relset_1(X25,X26,X27)
        | v1_funct_2(X27,X25,X26)
        | X25 != k1_xboole_0
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( ~ v1_funct_2(X27,X25,X26)
        | X27 = k1_xboole_0
        | X25 = k1_xboole_0
        | X26 != k1_xboole_0
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( X27 != k1_xboole_0
        | v1_funct_2(X27,X25,X26)
        | X25 = k1_xboole_0
        | X26 != k1_xboole_0
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_10,negated_conjecture,
    ( v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk3_0,esk4_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    & r2_hidden(esk5_0,esk3_0)
    & esk4_0 != k1_xboole_0
    & ~ r2_hidden(k1_funct_1(esk6_0,esk5_0),k2_relset_1(esk3_0,esk4_0,esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_11,plain,(
    ! [X6,X7] :
      ( ~ v1_relat_1(X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | v1_relat_1(X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_12,plain,(
    ! [X8,X9] : v1_relat_1(k2_zfmisc_1(X8,X9)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_13,plain,(
    ! [X18,X19,X20,X22,X23] :
      ( ( r2_hidden(esk1_3(X18,X19,X20),X19)
        | k1_relset_1(X19,X18,X20) = X19
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X19,X18))) )
      & ( ~ r2_hidden(k4_tarski(esk1_3(X18,X19,X20),X22),X20)
        | k1_relset_1(X19,X18,X20) = X19
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X19,X18))) )
      & ( k1_relset_1(X19,X18,X20) != X19
        | ~ r2_hidden(X23,X19)
        | r2_hidden(k4_tarski(X23,esk2_4(X18,X19,X20,X23)),X20)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X19,X18))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_relset_1])])])])])])).

cnf(c_0_14,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( v1_funct_2(esk6_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_20,plain,(
    ! [X12,X13,X14] :
      ( ( r2_hidden(X12,k1_relat_1(X14))
        | ~ r2_hidden(k4_tarski(X12,X13),X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( X13 = k1_funct_1(X14,X12)
        | ~ r2_hidden(k4_tarski(X12,X13),X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( ~ r2_hidden(X12,k1_relat_1(X14))
        | X13 != k1_funct_1(X14,X12)
        | r2_hidden(k4_tarski(X12,X13),X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(X4,esk2_4(X2,X1,X3,X4)),X3)
    | k1_relset_1(X1,X2,X3) != X1
    | ~ r2_hidden(X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( k1_relset_1(esk3_0,esk4_0,esk6_0) = esk3_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_23,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk2_4(esk4_0,esk3_0,esk6_0,X1)),esk6_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_16])])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_27,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( esk2_4(esk4_0,esk3_0,esk6_0,X1) = k1_funct_1(esk6_0,X1)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27])])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_30,plain,(
    ! [X15,X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
      | k2_relset_1(X15,X16,X17) = k2_relat_1(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_31,negated_conjecture,
    ( esk2_4(esk4_0,esk3_0,esk6_0,esk5_0) = k1_funct_1(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_33,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X11)
      | ~ v1_funct_1(X11)
      | ~ r2_hidden(X10,k1_relat_1(X11))
      | r2_hidden(k1_funct_1(X11,X10),k2_relat_1(X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_1])])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_0,k1_funct_1(esk6_0,esk5_0)),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_31]),c_0_29])])).

cnf(c_0_36,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk6_0,esk5_0),k2_relset_1(esk3_0,esk4_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_37,negated_conjecture,
    ( k2_relset_1(esk3_0,esk4_0,esk6_0) = k2_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_16])).

cnf(c_0_38,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk5_0,k1_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_26]),c_0_27])])).

cnf(c_0_40,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk6_0,esk5_0),k2_relat_1(esk6_0)) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_26]),c_0_27])]),c_0_40]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:23:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.18/0.39  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.18/0.39  #
% 0.18/0.39  # Preprocessing time       : 0.045 s
% 0.18/0.39  # Presaturation interreduction done
% 0.18/0.39  
% 0.18/0.39  # Proof found!
% 0.18/0.39  # SZS status Theorem
% 0.18/0.39  # SZS output start CNFRefutation
% 0.18/0.39  fof(t6_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_hidden(X3,X1)=>(X2=k1_xboole_0|r2_hidden(k1_funct_1(X4,X3),k2_relset_1(X1,X2,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 0.18/0.39  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.18/0.39  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.18/0.39  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.18/0.39  fof(t22_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~(r2_hidden(k4_tarski(X4,X5),X3))))<=>k1_relset_1(X2,X1,X3)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relset_1)).
% 0.18/0.39  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 0.18/0.39  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.18/0.39  fof(t12_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r2_hidden(X1,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X1),k2_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 0.18/0.39  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_hidden(X3,X1)=>(X2=k1_xboole_0|r2_hidden(k1_funct_1(X4,X3),k2_relset_1(X1,X2,X4)))))), inference(assume_negation,[status(cth)],[t6_funct_2])).
% 0.18/0.39  fof(c_0_9, plain, ![X25, X26, X27]:((((~v1_funct_2(X27,X25,X26)|X25=k1_relset_1(X25,X26,X27)|X26=k1_xboole_0|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))))&(X25!=k1_relset_1(X25,X26,X27)|v1_funct_2(X27,X25,X26)|X26=k1_xboole_0|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))))&((~v1_funct_2(X27,X25,X26)|X25=k1_relset_1(X25,X26,X27)|X25!=k1_xboole_0|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))))&(X25!=k1_relset_1(X25,X26,X27)|v1_funct_2(X27,X25,X26)|X25!=k1_xboole_0|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))))))&((~v1_funct_2(X27,X25,X26)|X27=k1_xboole_0|X25=k1_xboole_0|X26!=k1_xboole_0|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))))&(X27!=k1_xboole_0|v1_funct_2(X27,X25,X26)|X25=k1_xboole_0|X26!=k1_xboole_0|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.18/0.39  fof(c_0_10, negated_conjecture, (((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk3_0,esk4_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))))&(r2_hidden(esk5_0,esk3_0)&(esk4_0!=k1_xboole_0&~r2_hidden(k1_funct_1(esk6_0,esk5_0),k2_relset_1(esk3_0,esk4_0,esk6_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.18/0.39  fof(c_0_11, plain, ![X6, X7]:(~v1_relat_1(X6)|(~m1_subset_1(X7,k1_zfmisc_1(X6))|v1_relat_1(X7))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.18/0.39  fof(c_0_12, plain, ![X8, X9]:v1_relat_1(k2_zfmisc_1(X8,X9)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.18/0.39  fof(c_0_13, plain, ![X18, X19, X20, X22, X23]:(((r2_hidden(esk1_3(X18,X19,X20),X19)|k1_relset_1(X19,X18,X20)=X19|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X19,X18))))&(~r2_hidden(k4_tarski(esk1_3(X18,X19,X20),X22),X20)|k1_relset_1(X19,X18,X20)=X19|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X19,X18)))))&(k1_relset_1(X19,X18,X20)!=X19|(~r2_hidden(X23,X19)|r2_hidden(k4_tarski(X23,esk2_4(X18,X19,X20,X23)),X20))|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X19,X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_relset_1])])])])])])).
% 0.18/0.39  cnf(c_0_14, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.39  cnf(c_0_15, negated_conjecture, (v1_funct_2(esk6_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.39  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.39  cnf(c_0_17, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.39  cnf(c_0_18, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.39  cnf(c_0_19, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.39  fof(c_0_20, plain, ![X12, X13, X14]:(((r2_hidden(X12,k1_relat_1(X14))|~r2_hidden(k4_tarski(X12,X13),X14)|(~v1_relat_1(X14)|~v1_funct_1(X14)))&(X13=k1_funct_1(X14,X12)|~r2_hidden(k4_tarski(X12,X13),X14)|(~v1_relat_1(X14)|~v1_funct_1(X14))))&(~r2_hidden(X12,k1_relat_1(X14))|X13!=k1_funct_1(X14,X12)|r2_hidden(k4_tarski(X12,X13),X14)|(~v1_relat_1(X14)|~v1_funct_1(X14)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.18/0.39  cnf(c_0_21, plain, (r2_hidden(k4_tarski(X4,esk2_4(X2,X1,X3,X4)),X3)|k1_relset_1(X1,X2,X3)!=X1|~r2_hidden(X4,X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.39  cnf(c_0_22, negated_conjecture, (k1_relset_1(esk3_0,esk4_0,esk6_0)=esk3_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])]), c_0_17])).
% 0.18/0.39  cnf(c_0_23, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.18/0.39  cnf(c_0_24, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.39  cnf(c_0_25, negated_conjecture, (r2_hidden(k4_tarski(X1,esk2_4(esk4_0,esk3_0,esk6_0,X1)),esk6_0)|~r2_hidden(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_16])])).
% 0.18/0.39  cnf(c_0_26, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.39  cnf(c_0_27, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_23, c_0_16])).
% 0.18/0.39  cnf(c_0_28, negated_conjecture, (esk2_4(esk4_0,esk3_0,esk6_0,X1)=k1_funct_1(esk6_0,X1)|~r2_hidden(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27])])).
% 0.18/0.39  cnf(c_0_29, negated_conjecture, (r2_hidden(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.39  fof(c_0_30, plain, ![X15, X16, X17]:(~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))|k2_relset_1(X15,X16,X17)=k2_relat_1(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.18/0.39  cnf(c_0_31, negated_conjecture, (esk2_4(esk4_0,esk3_0,esk6_0,esk5_0)=k1_funct_1(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.18/0.39  cnf(c_0_32, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.18/0.39  fof(c_0_33, plain, ![X10, X11]:(~v1_relat_1(X11)|~v1_funct_1(X11)|(~r2_hidden(X10,k1_relat_1(X11))|r2_hidden(k1_funct_1(X11,X10),k2_relat_1(X11)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_1])])).
% 0.18/0.39  cnf(c_0_34, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.39  cnf(c_0_35, negated_conjecture, (r2_hidden(k4_tarski(esk5_0,k1_funct_1(esk6_0,esk5_0)),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_31]), c_0_29])])).
% 0.18/0.39  cnf(c_0_36, negated_conjecture, (~r2_hidden(k1_funct_1(esk6_0,esk5_0),k2_relset_1(esk3_0,esk4_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.39  cnf(c_0_37, negated_conjecture, (k2_relset_1(esk3_0,esk4_0,esk6_0)=k2_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_32, c_0_16])).
% 0.18/0.39  cnf(c_0_38, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.18/0.39  cnf(c_0_39, negated_conjecture, (r2_hidden(esk5_0,k1_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_26]), c_0_27])])).
% 0.18/0.39  cnf(c_0_40, negated_conjecture, (~r2_hidden(k1_funct_1(esk6_0,esk5_0),k2_relat_1(esk6_0))), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.18/0.39  cnf(c_0_41, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_26]), c_0_27])]), c_0_40]), ['proof']).
% 0.18/0.39  # SZS output end CNFRefutation
% 0.18/0.39  # Proof object total steps             : 42
% 0.18/0.39  # Proof object clause steps            : 25
% 0.18/0.39  # Proof object formula steps           : 17
% 0.18/0.39  # Proof object conjectures             : 19
% 0.18/0.39  # Proof object clause conjectures      : 16
% 0.18/0.39  # Proof object formula conjectures     : 3
% 0.18/0.39  # Proof object initial clauses used    : 14
% 0.18/0.39  # Proof object initial formulas used   : 8
% 0.18/0.39  # Proof object generating inferences   : 10
% 0.18/0.39  # Proof object simplifying inferences  : 18
% 0.18/0.39  # Training examples: 0 positive, 0 negative
% 0.18/0.39  # Parsed axioms                        : 8
% 0.18/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.39  # Initial clauses                      : 22
% 0.18/0.39  # Removed in clause preprocessing      : 0
% 0.18/0.39  # Initial clauses in saturation        : 22
% 0.18/0.39  # Processed clauses                    : 62
% 0.18/0.39  # ...of these trivial                  : 0
% 0.18/0.39  # ...subsumed                          : 0
% 0.18/0.39  # ...remaining for further processing  : 62
% 0.18/0.39  # Other redundant clauses eliminated   : 6
% 0.18/0.39  # Clauses deleted for lack of memory   : 0
% 0.18/0.39  # Backward-subsumed                    : 0
% 0.18/0.39  # Backward-rewritten                   : 1
% 0.18/0.39  # Generated clauses                    : 31
% 0.18/0.39  # ...of the previous two non-trivial   : 27
% 0.18/0.39  # Contextual simplify-reflections      : 0
% 0.18/0.39  # Paramodulations                      : 26
% 0.18/0.39  # Factorizations                       : 0
% 0.18/0.39  # Equation resolutions                 : 6
% 0.18/0.39  # Propositional unsat checks           : 0
% 0.18/0.39  #    Propositional check models        : 0
% 0.18/0.39  #    Propositional check unsatisfiable : 0
% 0.18/0.39  #    Propositional clauses             : 0
% 0.18/0.39  #    Propositional clauses after purity: 0
% 0.18/0.39  #    Propositional unsat core size     : 0
% 0.18/0.39  #    Propositional preprocessing time  : 0.000
% 0.18/0.39  #    Propositional encoding time       : 0.000
% 0.18/0.39  #    Propositional solver time         : 0.000
% 0.18/0.39  #    Success case prop preproc time    : 0.000
% 0.18/0.39  #    Success case prop encoding time   : 0.000
% 0.18/0.39  #    Success case prop solver time     : 0.000
% 0.18/0.39  # Current number of processed clauses  : 34
% 0.18/0.39  #    Positive orientable unit clauses  : 11
% 0.18/0.39  #    Positive unorientable unit clauses: 0
% 0.18/0.39  #    Negative unit clauses             : 2
% 0.18/0.39  #    Non-unit-clauses                  : 21
% 0.18/0.39  # Current number of unprocessed clauses: 9
% 0.18/0.39  # ...number of literals in the above   : 34
% 0.18/0.39  # Current number of archived formulas  : 0
% 0.18/0.39  # Current number of archived clauses   : 23
% 0.18/0.39  # Clause-clause subsumption calls (NU) : 106
% 0.18/0.39  # Rec. Clause-clause subsumption calls : 46
% 0.18/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.18/0.39  # Unit Clause-clause subsumption calls : 0
% 0.18/0.39  # Rewrite failures with RHS unbound    : 0
% 0.18/0.39  # BW rewrite match attempts            : 2
% 0.18/0.39  # BW rewrite match successes           : 1
% 0.18/0.39  # Condensation attempts                : 0
% 0.18/0.39  # Condensation successes               : 0
% 0.18/0.39  # Termbank termtop insertions          : 2311
% 0.18/0.39  
% 0.18/0.39  # -------------------------------------------------
% 0.18/0.39  # User time                : 0.050 s
% 0.18/0.39  # System time              : 0.004 s
% 0.18/0.39  # Total time               : 0.054 s
% 0.18/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
