%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:05:54 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 180 expanded)
%              Number of clauses        :   27 (  63 expanded)
%              Number of leaves         :    7 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :  145 ( 988 expanded)
%              Number of equality atoms :   32 ( 245 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   23 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t85_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ( v2_funct_1(X2)
       => ! [X3,X4] :
            ( ( r2_hidden(X3,X1)
              & r2_hidden(X4,X1)
              & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) )
           => X3 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_2)).

fof(t32_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( v2_funct_1(X4)
          & r2_hidden(X3,X1) )
       => ( X2 = k1_xboole_0
          | k1_funct_1(k2_funct_1(X4),k1_funct_1(X4,X3)) = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(d8_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( r2_hidden(X2,k1_relat_1(X1))
              & r2_hidden(X3,k1_relat_1(X1))
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_funct_2(X2,X1,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
       => ( v2_funct_1(X2)
         => ! [X3,X4] :
              ( ( r2_hidden(X3,X1)
                & r2_hidden(X4,X1)
                & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) )
             => X3 = X4 ) ) ) ),
    inference(assume_negation,[status(cth)],[t85_funct_2])).

fof(c_0_8,plain,(
    ! [X19,X20,X21,X22] :
      ( ~ v1_funct_1(X22)
      | ~ v1_funct_2(X22,X19,X20)
      | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | ~ v2_funct_1(X22)
      | ~ r2_hidden(X21,X19)
      | X20 = k1_xboole_0
      | k1_funct_1(k2_funct_1(X22),k1_funct_1(X22,X21)) = X21 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_funct_2])])).

fof(c_0_9,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk3_0,esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))
    & v2_funct_1(esk4_0)
    & r2_hidden(esk5_0,esk3_0)
    & r2_hidden(esk6_0,esk3_0)
    & k1_funct_1(esk4_0,esk5_0) = k1_funct_1(esk4_0,esk6_0)
    & esk5_0 != esk6_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X6,X7,X8] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | ~ r2_hidden(X8,X7)
      | r2_hidden(X8,X6) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_11,plain,(
    ! [X9,X10] :
      ( ( ~ m1_subset_1(X9,k1_zfmisc_1(X10))
        | r1_tarski(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | m1_subset_1(X9,k1_zfmisc_1(X10)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_12,plain,
    ( X3 = k1_xboole_0
    | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X4)) = X4
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( v1_funct_2(esk4_0,esk3_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( k1_funct_1(k2_funct_1(esk4_0),k1_funct_1(esk4_0,X1)) = X1
    | esk3_0 = k1_xboole_0
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk6_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,negated_conjecture,
    ( k1_funct_1(esk4_0,esk5_0) = k1_funct_1(esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( k1_funct_1(k2_funct_1(esk4_0),k1_funct_1(esk4_0,esk5_0)) = esk6_0
    | esk3_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( k1_funct_1(k2_funct_1(esk4_0),k1_funct_1(esk4_0,esk5_0)) = esk5_0
    | esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_19,c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( esk5_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_27,plain,(
    ! [X5] : r1_tarski(k1_xboole_0,X5) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_28,plain,(
    ! [X11,X12,X13] :
      ( ( ~ v2_funct_1(X11)
        | ~ r2_hidden(X12,k1_relat_1(X11))
        | ~ r2_hidden(X13,k1_relat_1(X11))
        | k1_funct_1(X11,X12) != k1_funct_1(X11,X13)
        | X12 = X13
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( r2_hidden(esk1_1(X11),k1_relat_1(X11))
        | v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( r2_hidden(esk2_1(X11),k1_relat_1(X11))
        | v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( k1_funct_1(X11,esk1_1(X11)) = k1_funct_1(X11,esk2_1(X11))
        | v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( esk1_1(X11) != esk2_1(X11)
        | v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk5_0,X1)
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

cnf(c_0_31,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( X2 = X3
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30]),c_0_31])])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk6_0,X1)
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_20])).

fof(c_0_35,plain,(
    ! [X16,X17,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
      | v1_relat_1(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_36,negated_conjecture,
    ( X1 = esk5_0
    | k1_funct_1(X2,X1) != k1_funct_1(X2,esk5_0)
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_30]),c_0_31])])).

cnf(c_0_38,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( k1_funct_1(X1,esk6_0) != k1_funct_1(X1,esk5_0)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_26])).

cnf(c_0_40,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_13])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_21]),c_0_15]),c_0_16])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:18:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.027 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t85_funct_2, conjecture, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(v2_funct_1(X2)=>![X3, X4]:(((r2_hidden(X3,X1)&r2_hidden(X4,X1))&k1_funct_1(X2,X3)=k1_funct_1(X2,X4))=>X3=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_funct_2)).
% 0.19/0.37  fof(t32_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X4)&r2_hidden(X3,X1))=>(X2=k1_xboole_0|k1_funct_1(k2_funct_1(X4),k1_funct_1(X4,X3))=X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_funct_2)).
% 0.19/0.37  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.19/0.37  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.37  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.37  fof(d8_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)<=>![X2, X3]:(((r2_hidden(X2,k1_relat_1(X1))&r2_hidden(X3,k1_relat_1(X1)))&k1_funct_1(X1,X2)=k1_funct_1(X1,X3))=>X2=X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_funct_1)).
% 0.19/0.37  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.37  fof(c_0_7, negated_conjecture, ~(![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(v2_funct_1(X2)=>![X3, X4]:(((r2_hidden(X3,X1)&r2_hidden(X4,X1))&k1_funct_1(X2,X3)=k1_funct_1(X2,X4))=>X3=X4)))), inference(assume_negation,[status(cth)],[t85_funct_2])).
% 0.19/0.37  fof(c_0_8, plain, ![X19, X20, X21, X22]:(~v1_funct_1(X22)|~v1_funct_2(X22,X19,X20)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))|(~v2_funct_1(X22)|~r2_hidden(X21,X19)|(X20=k1_xboole_0|k1_funct_1(k2_funct_1(X22),k1_funct_1(X22,X21))=X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_funct_2])])).
% 0.19/0.37  fof(c_0_9, negated_conjecture, (((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk3_0,esk3_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))))&(v2_funct_1(esk4_0)&(((r2_hidden(esk5_0,esk3_0)&r2_hidden(esk6_0,esk3_0))&k1_funct_1(esk4_0,esk5_0)=k1_funct_1(esk4_0,esk6_0))&esk5_0!=esk6_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.19/0.37  fof(c_0_10, plain, ![X6, X7, X8]:(~m1_subset_1(X7,k1_zfmisc_1(X6))|(~r2_hidden(X8,X7)|r2_hidden(X8,X6))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.19/0.37  fof(c_0_11, plain, ![X9, X10]:((~m1_subset_1(X9,k1_zfmisc_1(X10))|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|m1_subset_1(X9,k1_zfmisc_1(X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.37  cnf(c_0_12, plain, (X3=k1_xboole_0|k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X4))=X4|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v2_funct_1(X1)|~r2_hidden(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.37  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_14, negated_conjecture, (v1_funct_2(esk4_0,esk3_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_15, negated_conjecture, (v2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_16, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_17, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_18, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.37  cnf(c_0_19, negated_conjecture, (k1_funct_1(k2_funct_1(esk4_0),k1_funct_1(esk4_0,X1))=X1|esk3_0=k1_xboole_0|~r2_hidden(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14]), c_0_15]), c_0_16])])).
% 0.19/0.37  cnf(c_0_20, negated_conjecture, (r2_hidden(esk6_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_21, negated_conjecture, (k1_funct_1(esk4_0,esk5_0)=k1_funct_1(esk4_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_22, negated_conjecture, (r2_hidden(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_23, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.37  cnf(c_0_24, negated_conjecture, (k1_funct_1(k2_funct_1(esk4_0),k1_funct_1(esk4_0,esk5_0))=esk6_0|esk3_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])).
% 0.19/0.37  cnf(c_0_25, negated_conjecture, (k1_funct_1(k2_funct_1(esk4_0),k1_funct_1(esk4_0,esk5_0))=esk5_0|esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_19, c_0_22])).
% 0.19/0.37  cnf(c_0_26, negated_conjecture, (esk5_0!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  fof(c_0_27, plain, ![X5]:r1_tarski(k1_xboole_0,X5), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.37  fof(c_0_28, plain, ![X11, X12, X13]:((~v2_funct_1(X11)|(~r2_hidden(X12,k1_relat_1(X11))|~r2_hidden(X13,k1_relat_1(X11))|k1_funct_1(X11,X12)!=k1_funct_1(X11,X13)|X12=X13)|(~v1_relat_1(X11)|~v1_funct_1(X11)))&((((r2_hidden(esk1_1(X11),k1_relat_1(X11))|v2_funct_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11)))&(r2_hidden(esk2_1(X11),k1_relat_1(X11))|v2_funct_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11))))&(k1_funct_1(X11,esk1_1(X11))=k1_funct_1(X11,esk2_1(X11))|v2_funct_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11))))&(esk1_1(X11)!=esk2_1(X11)|v2_funct_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).
% 0.19/0.37  cnf(c_0_29, negated_conjecture, (r2_hidden(esk5_0,X1)|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_23, c_0_22])).
% 0.19/0.37  cnf(c_0_30, negated_conjecture, (esk3_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])).
% 0.19/0.37  cnf(c_0_31, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.37  cnf(c_0_32, plain, (X2=X3|~v2_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~r2_hidden(X3,k1_relat_1(X1))|k1_funct_1(X1,X2)!=k1_funct_1(X1,X3)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.37  cnf(c_0_33, negated_conjecture, (r2_hidden(esk5_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30]), c_0_31])])).
% 0.19/0.37  cnf(c_0_34, negated_conjecture, (r2_hidden(esk6_0,X1)|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_23, c_0_20])).
% 0.19/0.37  fof(c_0_35, plain, ![X16, X17, X18]:(~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))|v1_relat_1(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.37  cnf(c_0_36, negated_conjecture, (X1=esk5_0|k1_funct_1(X2,X1)!=k1_funct_1(X2,esk5_0)|~v2_funct_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.37  cnf(c_0_37, negated_conjecture, (r2_hidden(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_30]), c_0_31])])).
% 0.19/0.37  cnf(c_0_38, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.37  cnf(c_0_39, negated_conjecture, (k1_funct_1(X1,esk6_0)!=k1_funct_1(X1,esk5_0)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_26])).
% 0.19/0.37  cnf(c_0_40, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_38, c_0_13])).
% 0.19/0.37  cnf(c_0_41, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_21]), c_0_15]), c_0_16])]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 42
% 0.19/0.37  # Proof object clause steps            : 27
% 0.19/0.37  # Proof object formula steps           : 15
% 0.19/0.37  # Proof object conjectures             : 23
% 0.19/0.37  # Proof object clause conjectures      : 20
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 14
% 0.19/0.37  # Proof object initial formulas used   : 7
% 0.19/0.37  # Proof object generating inferences   : 11
% 0.19/0.37  # Proof object simplifying inferences  : 17
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 7
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 19
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 19
% 0.19/0.37  # Processed clauses                    : 65
% 0.19/0.37  # ...of these trivial                  : 3
% 0.19/0.37  # ...subsumed                          : 1
% 0.19/0.37  # ...remaining for further processing  : 61
% 0.19/0.37  # Other redundant clauses eliminated   : 0
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 11
% 0.19/0.37  # Generated clauses                    : 33
% 0.19/0.37  # ...of the previous two non-trivial   : 30
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 33
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 0
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 31
% 0.19/0.37  #    Positive orientable unit clauses  : 12
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 1
% 0.19/0.37  #    Non-unit-clauses                  : 18
% 0.19/0.37  # Current number of unprocessed clauses: 1
% 0.19/0.37  # ...number of literals in the above   : 6
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 30
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 145
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 41
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 1
% 0.19/0.37  # Unit Clause-clause subsumption calls : 2
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 1
% 0.19/0.37  # BW rewrite match successes           : 1
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 2089
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.031 s
% 0.19/0.37  # System time              : 0.003 s
% 0.19/0.37  # Total time               : 0.033 s
% 0.19/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
