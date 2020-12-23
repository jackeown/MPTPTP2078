%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:01:36 EST 2020

% Result     : Theorem 0.37s
% Output     : CNFRefutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 176 expanded)
%              Number of clauses        :   30 (  66 expanded)
%              Number of leaves         :   10 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :  176 ( 876 expanded)
%              Number of equality atoms :   51 ( 250 expanded)
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

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

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

fof(t23_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ! [X4] :
            ~ ( r2_hidden(X4,X2)
              & ! [X5] : ~ r2_hidden(k4_tarski(X5,X4),X3) )
      <=> k2_relset_1(X1,X2,X3) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_10,negated_conjecture,(
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

fof(c_0_11,plain,(
    ! [X13,X14,X15] :
      ( ( r2_hidden(X13,k1_relat_1(X15))
        | ~ r2_hidden(k4_tarski(X13,X14),X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( X14 = k1_funct_1(X15,X13)
        | ~ r2_hidden(k4_tarski(X13,X14),X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( ~ r2_hidden(X13,k1_relat_1(X15))
        | X14 != k1_funct_1(X15,X13)
        | r2_hidden(k4_tarski(X13,X14),X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

fof(c_0_12,plain,(
    ! [X9,X10] :
      ( ~ v1_relat_1(X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | v1_relat_1(X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_13,negated_conjecture,(
    ! [X42] :
      ( v1_funct_1(esk5_0)
      & v1_funct_2(esk5_0,esk3_0,esk4_0)
      & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
      & ( r2_hidden(esk6_1(X42),esk3_0)
        | ~ r2_hidden(X42,esk4_0) )
      & ( X42 = k1_funct_1(esk5_0,esk6_1(X42))
        | ~ r2_hidden(X42,esk4_0) )
      & k2_relset_1(esk3_0,esk4_0,esk5_0) != esk4_0 ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])])).

fof(c_0_14,plain,(
    ! [X11,X12] : v1_relat_1(k2_zfmisc_1(X11,X12)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_15,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X34,X35,X36] :
      ( ( ~ v1_funct_2(X36,X34,X35)
        | X34 = k1_relset_1(X34,X35,X36)
        | X35 = k1_xboole_0
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( X34 != k1_relset_1(X34,X35,X36)
        | v1_funct_2(X36,X34,X35)
        | X35 = k1_xboole_0
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( ~ v1_funct_2(X36,X34,X35)
        | X34 = k1_relset_1(X34,X35,X36)
        | X34 != k1_xboole_0
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( X34 != k1_relset_1(X34,X35,X36)
        | v1_funct_2(X36,X34,X35)
        | X34 != k1_xboole_0
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( ~ v1_funct_2(X36,X34,X35)
        | X36 = k1_xboole_0
        | X34 = k1_xboole_0
        | X35 != k1_xboole_0
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( X36 != k1_xboole_0
        | v1_funct_2(X36,X34,X35)
        | X34 = k1_xboole_0
        | X35 != k1_xboole_0
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_20,plain,(
    ! [X27,X28,X29,X31,X32] :
      ( ( r2_hidden(esk1_3(X27,X28,X29),X28)
        | k2_relset_1(X27,X28,X29) = X28
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) )
      & ( ~ r2_hidden(k4_tarski(X31,esk1_3(X27,X28,X29)),X29)
        | k2_relset_1(X27,X28,X29) = X28
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) )
      & ( k2_relset_1(X27,X28,X29) != X28
        | ~ r2_hidden(X32,X28)
        | r2_hidden(k4_tarski(esk2_4(X27,X28,X29,X32),X32),X29)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_relset_1])])])])])])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( X1 = k1_funct_1(esk5_0,esk6_1(X1))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])])).

fof(c_0_25,plain,(
    ! [X21,X22,X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
      | k1_relset_1(X21,X22,X23) = k1_relat_1(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_26,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_2(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_28,plain,(
    ! [X16,X17] :
      ( ~ r2_hidden(X16,X17)
      | ~ r1_tarski(X17,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_29,plain,(
    ! [X7,X8] :
      ( ( ~ m1_subset_1(X7,k1_zfmisc_1(X8))
        | r1_tarski(X7,X8) )
      & ( ~ r1_tarski(X7,X8)
        | m1_subset_1(X7,k1_zfmisc_1(X8)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_30,plain,
    ( k2_relset_1(X2,X3,X4) = X3
    | ~ r2_hidden(k4_tarski(X1,esk1_3(X2,X3,X4)),X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_1(X1),X1),esk5_0)
    | ~ r2_hidden(esk6_1(X1),k1_relat_1(esk5_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24])])).

cnf(c_0_32,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( k1_relset_1(esk3_0,esk4_0,esk5_0) = esk3_0
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_17]),c_0_27])])).

cnf(c_0_34,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | k2_relset_1(X1,X2,X3) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_37,negated_conjecture,
    ( k2_relset_1(esk3_0,esk4_0,esk5_0) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_38,negated_conjecture,
    ( k2_relset_1(X1,X2,esk5_0) = X2
    | ~ r2_hidden(esk6_1(esk1_3(X1,X2,esk5_0)),k1_relat_1(esk5_0))
    | ~ r2_hidden(esk1_3(X1,X2,esk5_0),esk4_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk3_0
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_17])])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk6_1(X1),esk3_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_41,plain,(
    ! [X6] : r1_tarski(k1_xboole_0,X6) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk1_3(esk3_0,esk4_0,esk5_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_17]),c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( k2_relset_1(X1,X2,esk5_0) = X2
    | esk4_0 = k1_xboole_0
    | ~ r2_hidden(esk1_3(X1,X2,esk5_0),esk4_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_45,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_46,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( ~ m1_subset_1(esk4_0,k1_zfmisc_1(esk1_3(esk3_0,esk4_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_43]),c_0_17])]),c_0_37])).

cnf(c_0_49,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48]),c_0_48]),c_0_49])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:44:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.37/0.61  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.37/0.61  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.37/0.61  #
% 0.37/0.61  # Preprocessing time       : 0.028 s
% 0.37/0.61  # Presaturation interreduction done
% 0.37/0.61  
% 0.37/0.61  # Proof found!
% 0.37/0.61  # SZS status Theorem
% 0.37/0.61  # SZS output start CNFRefutation
% 0.37/0.61  fof(t16_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~((r2_hidden(X5,X1)&X4=k1_funct_1(X3,X5)))))=>k2_relset_1(X1,X2,X3)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_2)).
% 0.37/0.61  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 0.37/0.61  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.37/0.61  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.37/0.61  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.37/0.61  fof(t23_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~(r2_hidden(k4_tarski(X5,X4),X3))))<=>k2_relset_1(X1,X2,X3)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_relset_1)).
% 0.37/0.61  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.37/0.61  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.37/0.61  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.37/0.61  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.37/0.61  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~((r2_hidden(X5,X1)&X4=k1_funct_1(X3,X5)))))=>k2_relset_1(X1,X2,X3)=X2))), inference(assume_negation,[status(cth)],[t16_funct_2])).
% 0.37/0.61  fof(c_0_11, plain, ![X13, X14, X15]:(((r2_hidden(X13,k1_relat_1(X15))|~r2_hidden(k4_tarski(X13,X14),X15)|(~v1_relat_1(X15)|~v1_funct_1(X15)))&(X14=k1_funct_1(X15,X13)|~r2_hidden(k4_tarski(X13,X14),X15)|(~v1_relat_1(X15)|~v1_funct_1(X15))))&(~r2_hidden(X13,k1_relat_1(X15))|X14!=k1_funct_1(X15,X13)|r2_hidden(k4_tarski(X13,X14),X15)|(~v1_relat_1(X15)|~v1_funct_1(X15)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.37/0.61  fof(c_0_12, plain, ![X9, X10]:(~v1_relat_1(X9)|(~m1_subset_1(X10,k1_zfmisc_1(X9))|v1_relat_1(X10))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.37/0.61  fof(c_0_13, negated_conjecture, ![X42]:(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk3_0,esk4_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))))&(((r2_hidden(esk6_1(X42),esk3_0)|~r2_hidden(X42,esk4_0))&(X42=k1_funct_1(esk5_0,esk6_1(X42))|~r2_hidden(X42,esk4_0)))&k2_relset_1(esk3_0,esk4_0,esk5_0)!=esk4_0)), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])])).
% 0.37/0.61  fof(c_0_14, plain, ![X11, X12]:v1_relat_1(k2_zfmisc_1(X11,X12)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.37/0.61  cnf(c_0_15, plain, (r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.37/0.61  cnf(c_0_16, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.37/0.61  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.37/0.61  cnf(c_0_18, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.37/0.61  fof(c_0_19, plain, ![X34, X35, X36]:((((~v1_funct_2(X36,X34,X35)|X34=k1_relset_1(X34,X35,X36)|X35=k1_xboole_0|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))&(X34!=k1_relset_1(X34,X35,X36)|v1_funct_2(X36,X34,X35)|X35=k1_xboole_0|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))))&((~v1_funct_2(X36,X34,X35)|X34=k1_relset_1(X34,X35,X36)|X34!=k1_xboole_0|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))&(X34!=k1_relset_1(X34,X35,X36)|v1_funct_2(X36,X34,X35)|X34!=k1_xboole_0|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))))&((~v1_funct_2(X36,X34,X35)|X36=k1_xboole_0|X34=k1_xboole_0|X35!=k1_xboole_0|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))&(X36!=k1_xboole_0|v1_funct_2(X36,X34,X35)|X34=k1_xboole_0|X35!=k1_xboole_0|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.37/0.61  fof(c_0_20, plain, ![X27, X28, X29, X31, X32]:(((r2_hidden(esk1_3(X27,X28,X29),X28)|k2_relset_1(X27,X28,X29)=X28|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))&(~r2_hidden(k4_tarski(X31,esk1_3(X27,X28,X29)),X29)|k2_relset_1(X27,X28,X29)=X28|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))))&(k2_relset_1(X27,X28,X29)!=X28|(~r2_hidden(X32,X28)|r2_hidden(k4_tarski(esk2_4(X27,X28,X29,X32),X32),X29))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_relset_1])])])])])])).
% 0.37/0.61  cnf(c_0_21, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~r2_hidden(X1,k1_relat_1(X2))|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(er,[status(thm)],[c_0_15])).
% 0.37/0.61  cnf(c_0_22, negated_conjecture, (X1=k1_funct_1(esk5_0,esk6_1(X1))|~r2_hidden(X1,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.37/0.61  cnf(c_0_23, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.37/0.61  cnf(c_0_24, negated_conjecture, (v1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])])).
% 0.37/0.61  fof(c_0_25, plain, ![X21, X22, X23]:(~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))|k1_relset_1(X21,X22,X23)=k1_relat_1(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.37/0.61  cnf(c_0_26, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.37/0.61  cnf(c_0_27, negated_conjecture, (v1_funct_2(esk5_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.37/0.61  fof(c_0_28, plain, ![X16, X17]:(~r2_hidden(X16,X17)|~r1_tarski(X17,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.37/0.61  fof(c_0_29, plain, ![X7, X8]:((~m1_subset_1(X7,k1_zfmisc_1(X8))|r1_tarski(X7,X8))&(~r1_tarski(X7,X8)|m1_subset_1(X7,k1_zfmisc_1(X8)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.37/0.61  cnf(c_0_30, plain, (k2_relset_1(X2,X3,X4)=X3|~r2_hidden(k4_tarski(X1,esk1_3(X2,X3,X4)),X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.37/0.61  cnf(c_0_31, negated_conjecture, (r2_hidden(k4_tarski(esk6_1(X1),X1),esk5_0)|~r2_hidden(esk6_1(X1),k1_relat_1(esk5_0))|~r2_hidden(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24])])).
% 0.37/0.61  cnf(c_0_32, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.37/0.61  cnf(c_0_33, negated_conjecture, (k1_relset_1(esk3_0,esk4_0,esk5_0)=esk3_0|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_17]), c_0_27])])).
% 0.37/0.61  cnf(c_0_34, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.37/0.61  cnf(c_0_35, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.37/0.61  cnf(c_0_36, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|k2_relset_1(X1,X2,X3)=X2|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.37/0.61  cnf(c_0_37, negated_conjecture, (k2_relset_1(esk3_0,esk4_0,esk5_0)!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.37/0.61  cnf(c_0_38, negated_conjecture, (k2_relset_1(X1,X2,esk5_0)=X2|~r2_hidden(esk6_1(esk1_3(X1,X2,esk5_0)),k1_relat_1(esk5_0))|~r2_hidden(esk1_3(X1,X2,esk5_0),esk4_0)|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.37/0.61  cnf(c_0_39, negated_conjecture, (k1_relat_1(esk5_0)=esk3_0|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_17])])).
% 0.37/0.61  cnf(c_0_40, negated_conjecture, (r2_hidden(esk6_1(X1),esk3_0)|~r2_hidden(X1,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.37/0.61  fof(c_0_41, plain, ![X6]:r1_tarski(k1_xboole_0,X6), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.37/0.61  cnf(c_0_42, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.37/0.61  cnf(c_0_43, negated_conjecture, (r2_hidden(esk1_3(esk3_0,esk4_0,esk5_0),esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_17]), c_0_37])).
% 0.37/0.61  cnf(c_0_44, negated_conjecture, (k2_relset_1(X1,X2,esk5_0)=X2|esk4_0=k1_xboole_0|~r2_hidden(esk1_3(X1,X2,esk5_0),esk4_0)|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])).
% 0.37/0.61  cnf(c_0_45, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.37/0.61  cnf(c_0_46, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.37/0.61  cnf(c_0_47, negated_conjecture, (~m1_subset_1(esk4_0,k1_zfmisc_1(esk1_3(esk3_0,esk4_0,esk5_0)))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.37/0.61  cnf(c_0_48, negated_conjecture, (esk4_0=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_43]), c_0_17])]), c_0_37])).
% 0.37/0.61  cnf(c_0_49, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.37/0.61  cnf(c_0_50, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_48]), c_0_48]), c_0_49])]), ['proof']).
% 0.37/0.61  # SZS output end CNFRefutation
% 0.37/0.61  # Proof object total steps             : 51
% 0.37/0.61  # Proof object clause steps            : 30
% 0.37/0.61  # Proof object formula steps           : 21
% 0.37/0.61  # Proof object conjectures             : 19
% 0.37/0.61  # Proof object clause conjectures      : 16
% 0.37/0.61  # Proof object formula conjectures     : 3
% 0.37/0.61  # Proof object initial clauses used    : 17
% 0.37/0.61  # Proof object initial formulas used   : 10
% 0.37/0.61  # Proof object generating inferences   : 11
% 0.37/0.61  # Proof object simplifying inferences  : 19
% 0.37/0.61  # Training examples: 0 positive, 0 negative
% 0.37/0.61  # Parsed axioms                        : 13
% 0.37/0.61  # Removed by relevancy pruning/SinE    : 0
% 0.37/0.61  # Initial clauses                      : 30
% 0.37/0.61  # Removed in clause preprocessing      : 1
% 0.37/0.61  # Initial clauses in saturation        : 29
% 0.37/0.61  # Processed clauses                    : 2636
% 0.37/0.61  # ...of these trivial                  : 5
% 0.37/0.61  # ...subsumed                          : 1822
% 0.37/0.61  # ...remaining for further processing  : 809
% 0.37/0.61  # Other redundant clauses eliminated   : 48
% 0.37/0.61  # Clauses deleted for lack of memory   : 0
% 0.37/0.61  # Backward-subsumed                    : 17
% 0.37/0.61  # Backward-rewritten                   : 484
% 0.37/0.61  # Generated clauses                    : 5375
% 0.37/0.61  # ...of the previous two non-trivial   : 5366
% 0.37/0.61  # Contextual simplify-reflections      : 22
% 0.37/0.61  # Paramodulations                      : 5328
% 0.37/0.61  # Factorizations                       : 0
% 0.37/0.61  # Equation resolutions                 : 48
% 0.37/0.61  # Propositional unsat checks           : 0
% 0.37/0.61  #    Propositional check models        : 0
% 0.37/0.61  #    Propositional check unsatisfiable : 0
% 0.37/0.61  #    Propositional clauses             : 0
% 0.37/0.61  #    Propositional clauses after purity: 0
% 0.37/0.61  #    Propositional unsat core size     : 0
% 0.37/0.61  #    Propositional preprocessing time  : 0.000
% 0.37/0.61  #    Propositional encoding time       : 0.000
% 0.37/0.61  #    Propositional solver time         : 0.000
% 0.37/0.61  #    Success case prop preproc time    : 0.000
% 0.37/0.61  #    Success case prop encoding time   : 0.000
% 0.37/0.61  #    Success case prop solver time     : 0.000
% 0.37/0.61  # Current number of processed clauses  : 274
% 0.37/0.61  #    Positive orientable unit clauses  : 9
% 0.37/0.61  #    Positive unorientable unit clauses: 0
% 0.37/0.61  #    Negative unit clauses             : 1
% 0.37/0.61  #    Non-unit-clauses                  : 264
% 0.37/0.61  # Current number of unprocessed clauses: 2291
% 0.37/0.61  # ...number of literals in the above   : 13455
% 0.37/0.61  # Current number of archived formulas  : 0
% 0.37/0.61  # Current number of archived clauses   : 530
% 0.37/0.61  # Clause-clause subsumption calls (NU) : 77882
% 0.37/0.61  # Rec. Clause-clause subsumption calls : 14252
% 0.37/0.61  # Non-unit clause-clause subsumptions  : 1756
% 0.37/0.61  # Unit Clause-clause subsumption calls : 607
% 0.37/0.61  # Rewrite failures with RHS unbound    : 0
% 0.37/0.61  # BW rewrite match attempts            : 111
% 0.37/0.61  # BW rewrite match successes           : 25
% 0.37/0.61  # Condensation attempts                : 0
% 0.37/0.61  # Condensation successes               : 0
% 0.37/0.61  # Termbank termtop insertions          : 158012
% 0.37/0.61  
% 0.37/0.61  # -------------------------------------------------
% 0.37/0.61  # User time                : 0.250 s
% 0.37/0.61  # System time              : 0.010 s
% 0.37/0.61  # Total time               : 0.261 s
% 0.37/0.61  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
