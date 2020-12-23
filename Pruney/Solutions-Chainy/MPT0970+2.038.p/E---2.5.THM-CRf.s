%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:01:32 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 199 expanded)
%              Number of clauses        :   28 (  79 expanded)
%              Number of leaves         :    8 (  47 expanded)
%              Depth                    :   12
%              Number of atoms          :  164 (1035 expanded)
%              Number of equality atoms :   56 ( 320 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t16_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ! [X4] :
            ~ ( r2_hidden(X4,X2)
              & ! [X5] :
                  ~ ( r2_hidden(X5,X1)
                    & X4 = k1_funct_1(X3,X5) ) )
       => k2_relset_1(X1,X2,X3) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(t23_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ! [X4] :
            ~ ( r2_hidden(X4,X2)
              & ! [X5] : ~ r2_hidden(k4_tarski(X5,X4),X3) )
      <=> k2_relset_1(X1,X2,X3) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relset_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ! [X4] :
              ~ ( r2_hidden(X4,X2)
                & ! [X5] :
                    ~ ( r2_hidden(X5,X1)
                      & X4 = k1_funct_1(X3,X5) ) )
         => k2_relset_1(X1,X2,X3) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t16_funct_2])).

fof(c_0_9,plain,(
    ! [X12,X13,X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
      | v1_relat_1(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_10,negated_conjecture,(
    ! [X31] :
      ( v1_funct_1(esk5_0)
      & v1_funct_2(esk5_0,esk3_0,esk4_0)
      & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
      & ( r2_hidden(esk6_1(X31),esk3_0)
        | ~ r2_hidden(X31,esk4_0) )
      & ( X31 = k1_funct_1(esk5_0,esk6_1(X31))
        | ~ r2_hidden(X31,esk4_0) )
      & k2_relset_1(esk3_0,esk4_0,esk5_0) != esk4_0 ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])])).

fof(c_0_11,plain,(
    ! [X15,X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
      | k1_relset_1(X15,X16,X17) = k1_relat_1(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_12,plain,(
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

fof(c_0_13,plain,(
    ! [X7,X8,X9] :
      ( ( r2_hidden(X7,k1_relat_1(X9))
        | ~ r2_hidden(k4_tarski(X7,X8),X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( X8 = k1_funct_1(X9,X7)
        | ~ r2_hidden(k4_tarski(X7,X8),X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( ~ r2_hidden(X7,k1_relat_1(X9))
        | X8 != k1_funct_1(X9,X7)
        | r2_hidden(k4_tarski(X7,X8),X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

cnf(c_0_14,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X18,X19,X20,X22,X23] :
      ( ( r2_hidden(esk1_3(X18,X19,X20),X19)
        | k2_relset_1(X18,X19,X20) = X19
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) )
      & ( ~ r2_hidden(k4_tarski(X22,esk1_3(X18,X19,X20)),X20)
        | k2_relset_1(X18,X19,X20) = X19
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) )
      & ( k2_relset_1(X18,X19,X20) != X19
        | ~ r2_hidden(X23,X19)
        | r2_hidden(k4_tarski(esk2_4(X18,X19,X20,X23),X23),X20)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_relset_1])])])])])])).

cnf(c_0_19,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( X1 = k1_funct_1(esk5_0,esk6_1(X1))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_23,plain,
    ( X1 = k1_relat_1(X2)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_2(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_25,plain,
    ( k2_relset_1(X2,X3,X4) = X3
    | ~ r2_hidden(k4_tarski(X1,esk1_3(X2,X3,X4)),X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_1(X1),X1),esk5_0)
    | ~ r2_hidden(esk6_1(X1),k1_relat_1(esk5_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])]),c_0_22])])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk6_1(X1),esk3_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_28,negated_conjecture,
    ( esk3_0 = k1_relat_1(esk5_0)
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_15])])).

cnf(c_0_29,negated_conjecture,
    ( k2_relset_1(X1,X2,esk5_0) = X2
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(esk6_1(esk1_3(X1,X2,esk5_0)),k1_relat_1(esk5_0))
    | ~ r2_hidden(esk1_3(X1,X2,esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(esk6_1(X1),k1_relat_1(esk5_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( k2_relset_1(X1,X2,esk5_0) = X2
    | esk4_0 = k1_xboole_0
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(esk1_3(X1,X2,esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_32,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | k2_relset_1(X1,X2,X3) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_33,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(X10,X11)
      | ~ r1_tarski(X11,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_34,plain,(
    ! [X6] : r1_tarski(k1_xboole_0,X6) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_35,negated_conjecture,
    ( k2_relset_1(esk3_0,esk4_0,esk5_0) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_36,negated_conjecture,
    ( k2_relset_1(X1,esk4_0,esk5_0) = esk4_0
    | esk4_0 = k1_xboole_0
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_15])])).

cnf(c_0_40,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( k2_relset_1(esk3_0,k1_xboole_0,esk5_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_39]),c_0_39])).

cnf(c_0_42,plain,
    ( k2_relset_1(X1,k1_xboole_0,X2) = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_39]),c_0_43]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:57:44 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.34  # Version: 2.5pre002
% 0.19/0.34  # No SInE strategy applied
% 0.19/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.43  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.19/0.43  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.43  #
% 0.19/0.43  # Preprocessing time       : 0.051 s
% 0.19/0.43  # Presaturation interreduction done
% 0.19/0.43  
% 0.19/0.43  # Proof found!
% 0.19/0.43  # SZS status Theorem
% 0.19/0.43  # SZS output start CNFRefutation
% 0.19/0.43  fof(t16_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~((r2_hidden(X5,X1)&X4=k1_funct_1(X3,X5)))))=>k2_relset_1(X1,X2,X3)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_2)).
% 0.19/0.43  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.43  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.43  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.19/0.43  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 0.19/0.43  fof(t23_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~(r2_hidden(k4_tarski(X5,X4),X3))))<=>k2_relset_1(X1,X2,X3)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_relset_1)).
% 0.19/0.43  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.19/0.43  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.43  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~((r2_hidden(X5,X1)&X4=k1_funct_1(X3,X5)))))=>k2_relset_1(X1,X2,X3)=X2))), inference(assume_negation,[status(cth)],[t16_funct_2])).
% 0.19/0.43  fof(c_0_9, plain, ![X12, X13, X14]:(~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))|v1_relat_1(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.43  fof(c_0_10, negated_conjecture, ![X31]:(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk3_0,esk4_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))))&(((r2_hidden(esk6_1(X31),esk3_0)|~r2_hidden(X31,esk4_0))&(X31=k1_funct_1(esk5_0,esk6_1(X31))|~r2_hidden(X31,esk4_0)))&k2_relset_1(esk3_0,esk4_0,esk5_0)!=esk4_0)), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])])).
% 0.19/0.43  fof(c_0_11, plain, ![X15, X16, X17]:(~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))|k1_relset_1(X15,X16,X17)=k1_relat_1(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.43  fof(c_0_12, plain, ![X25, X26, X27]:((((~v1_funct_2(X27,X25,X26)|X25=k1_relset_1(X25,X26,X27)|X26=k1_xboole_0|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))))&(X25!=k1_relset_1(X25,X26,X27)|v1_funct_2(X27,X25,X26)|X26=k1_xboole_0|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))))&((~v1_funct_2(X27,X25,X26)|X25=k1_relset_1(X25,X26,X27)|X25!=k1_xboole_0|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))))&(X25!=k1_relset_1(X25,X26,X27)|v1_funct_2(X27,X25,X26)|X25!=k1_xboole_0|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))))))&((~v1_funct_2(X27,X25,X26)|X27=k1_xboole_0|X25=k1_xboole_0|X26!=k1_xboole_0|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))))&(X27!=k1_xboole_0|v1_funct_2(X27,X25,X26)|X25=k1_xboole_0|X26!=k1_xboole_0|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.19/0.43  fof(c_0_13, plain, ![X7, X8, X9]:(((r2_hidden(X7,k1_relat_1(X9))|~r2_hidden(k4_tarski(X7,X8),X9)|(~v1_relat_1(X9)|~v1_funct_1(X9)))&(X8=k1_funct_1(X9,X7)|~r2_hidden(k4_tarski(X7,X8),X9)|(~v1_relat_1(X9)|~v1_funct_1(X9))))&(~r2_hidden(X7,k1_relat_1(X9))|X8!=k1_funct_1(X9,X7)|r2_hidden(k4_tarski(X7,X8),X9)|(~v1_relat_1(X9)|~v1_funct_1(X9)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.19/0.43  cnf(c_0_14, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.43  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.43  cnf(c_0_16, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.43  cnf(c_0_17, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.43  fof(c_0_18, plain, ![X18, X19, X20, X22, X23]:(((r2_hidden(esk1_3(X18,X19,X20),X19)|k2_relset_1(X18,X19,X20)=X19|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))))&(~r2_hidden(k4_tarski(X22,esk1_3(X18,X19,X20)),X20)|k2_relset_1(X18,X19,X20)=X19|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))))&(k2_relset_1(X18,X19,X20)!=X19|(~r2_hidden(X23,X19)|r2_hidden(k4_tarski(esk2_4(X18,X19,X20,X23),X23),X20))|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_relset_1])])])])])])).
% 0.19/0.43  cnf(c_0_19, plain, (r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.43  cnf(c_0_20, negated_conjecture, (X1=k1_funct_1(esk5_0,esk6_1(X1))|~r2_hidden(X1,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.43  cnf(c_0_21, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.43  cnf(c_0_22, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.43  cnf(c_0_23, plain, (X1=k1_relat_1(X2)|X3=k1_xboole_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.43  cnf(c_0_24, negated_conjecture, (v1_funct_2(esk5_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.43  cnf(c_0_25, plain, (k2_relset_1(X2,X3,X4)=X3|~r2_hidden(k4_tarski(X1,esk1_3(X2,X3,X4)),X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.43  cnf(c_0_26, negated_conjecture, (r2_hidden(k4_tarski(esk6_1(X1),X1),esk5_0)|~r2_hidden(esk6_1(X1),k1_relat_1(esk5_0))|~r2_hidden(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])]), c_0_22])])).
% 0.19/0.43  cnf(c_0_27, negated_conjecture, (r2_hidden(esk6_1(X1),esk3_0)|~r2_hidden(X1,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.43  cnf(c_0_28, negated_conjecture, (esk3_0=k1_relat_1(esk5_0)|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_15])])).
% 0.19/0.43  cnf(c_0_29, negated_conjecture, (k2_relset_1(X1,X2,esk5_0)=X2|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r2_hidden(esk6_1(esk1_3(X1,X2,esk5_0)),k1_relat_1(esk5_0))|~r2_hidden(esk1_3(X1,X2,esk5_0),esk4_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.43  cnf(c_0_30, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(esk6_1(X1),k1_relat_1(esk5_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.43  cnf(c_0_31, negated_conjecture, (k2_relset_1(X1,X2,esk5_0)=X2|esk4_0=k1_xboole_0|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r2_hidden(esk1_3(X1,X2,esk5_0),esk4_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.43  cnf(c_0_32, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|k2_relset_1(X1,X2,X3)=X2|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.43  fof(c_0_33, plain, ![X10, X11]:(~r2_hidden(X10,X11)|~r1_tarski(X11,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.19/0.43  fof(c_0_34, plain, ![X6]:r1_tarski(k1_xboole_0,X6), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.43  cnf(c_0_35, negated_conjecture, (k2_relset_1(esk3_0,esk4_0,esk5_0)!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.43  cnf(c_0_36, negated_conjecture, (k2_relset_1(X1,esk4_0,esk5_0)=esk4_0|esk4_0=k1_xboole_0|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk4_0)))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.43  cnf(c_0_37, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.43  cnf(c_0_38, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.43  cnf(c_0_39, negated_conjecture, (esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_15])])).
% 0.19/0.43  cnf(c_0_40, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.43  cnf(c_0_41, negated_conjecture, (k2_relset_1(esk3_0,k1_xboole_0,esk5_0)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_39]), c_0_39])).
% 0.19/0.43  cnf(c_0_42, plain, (k2_relset_1(X1,k1_xboole_0,X2)=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_40, c_0_32])).
% 0.19/0.43  cnf(c_0_43, negated_conjecture, (~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.43  cnf(c_0_44, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_39]), c_0_43]), ['proof']).
% 0.19/0.43  # SZS output end CNFRefutation
% 0.19/0.43  # Proof object total steps             : 45
% 0.19/0.43  # Proof object clause steps            : 28
% 0.19/0.43  # Proof object formula steps           : 17
% 0.19/0.43  # Proof object conjectures             : 20
% 0.19/0.43  # Proof object clause conjectures      : 17
% 0.19/0.43  # Proof object formula conjectures     : 3
% 0.19/0.43  # Proof object initial clauses used    : 14
% 0.19/0.43  # Proof object initial formulas used   : 8
% 0.19/0.43  # Proof object generating inferences   : 12
% 0.19/0.43  # Proof object simplifying inferences  : 13
% 0.19/0.43  # Training examples: 0 positive, 0 negative
% 0.19/0.43  # Parsed axioms                        : 8
% 0.19/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.43  # Initial clauses                      : 22
% 0.19/0.43  # Removed in clause preprocessing      : 0
% 0.19/0.43  # Initial clauses in saturation        : 22
% 0.19/0.43  # Processed clauses                    : 299
% 0.19/0.43  # ...of these trivial                  : 0
% 0.19/0.43  # ...subsumed                          : 137
% 0.19/0.43  # ...remaining for further processing  : 161
% 0.19/0.43  # Other redundant clauses eliminated   : 6
% 0.19/0.43  # Clauses deleted for lack of memory   : 0
% 0.19/0.43  # Backward-subsumed                    : 2
% 0.19/0.43  # Backward-rewritten                   : 64
% 0.19/0.43  # Generated clauses                    : 501
% 0.19/0.43  # ...of the previous two non-trivial   : 424
% 0.19/0.43  # Contextual simplify-reflections      : 11
% 0.19/0.43  # Paramodulations                      : 488
% 0.19/0.43  # Factorizations                       : 0
% 0.19/0.43  # Equation resolutions                 : 13
% 0.19/0.43  # Propositional unsat checks           : 0
% 0.19/0.43  #    Propositional check models        : 0
% 0.19/0.43  #    Propositional check unsatisfiable : 0
% 0.19/0.43  #    Propositional clauses             : 0
% 0.19/0.43  #    Propositional clauses after purity: 0
% 0.19/0.43  #    Propositional unsat core size     : 0
% 0.19/0.43  #    Propositional preprocessing time  : 0.000
% 0.19/0.43  #    Propositional encoding time       : 0.000
% 0.19/0.43  #    Propositional solver time         : 0.000
% 0.19/0.43  #    Success case prop preproc time    : 0.000
% 0.19/0.43  #    Success case prop encoding time   : 0.000
% 0.19/0.43  #    Success case prop solver time     : 0.000
% 0.19/0.43  # Current number of processed clauses  : 73
% 0.19/0.43  #    Positive orientable unit clauses  : 5
% 0.19/0.43  #    Positive unorientable unit clauses: 0
% 0.19/0.43  #    Negative unit clauses             : 3
% 0.19/0.43  #    Non-unit-clauses                  : 65
% 0.19/0.43  # Current number of unprocessed clauses: 169
% 0.19/0.43  # ...number of literals in the above   : 1006
% 0.19/0.43  # Current number of archived formulas  : 0
% 0.19/0.43  # Current number of archived clauses   : 88
% 0.19/0.43  # Clause-clause subsumption calls (NU) : 5849
% 0.19/0.43  # Rec. Clause-clause subsumption calls : 476
% 0.19/0.43  # Non-unit clause-clause subsumptions  : 140
% 0.19/0.43  # Unit Clause-clause subsumption calls : 66
% 0.19/0.43  # Rewrite failures with RHS unbound    : 0
% 0.19/0.43  # BW rewrite match attempts            : 1
% 0.19/0.43  # BW rewrite match successes           : 1
% 0.19/0.43  # Condensation attempts                : 0
% 0.19/0.43  # Condensation successes               : 0
% 0.19/0.43  # Termbank termtop insertions          : 13944
% 0.19/0.43  
% 0.19/0.43  # -------------------------------------------------
% 0.19/0.43  # User time                : 0.091 s
% 0.19/0.43  # System time              : 0.007 s
% 0.19/0.43  # Total time               : 0.099 s
% 0.19/0.43  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
