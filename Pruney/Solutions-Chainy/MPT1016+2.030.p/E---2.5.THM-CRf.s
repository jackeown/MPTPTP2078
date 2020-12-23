%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:05:52 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 739 expanded)
%              Number of clauses        :   33 ( 268 expanded)
%              Number of leaves         :    6 ( 186 expanded)
%              Depth                    :   11
%              Number of atoms          :  159 (4598 expanded)
%              Number of equality atoms :   40 (1064 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   23 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t77_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ( v2_funct_1(X2)
      <=> ! [X3,X4] :
            ( ( r2_hidden(X3,X1)
              & r2_hidden(X4,X1)
              & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) )
           => X3 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_funct_2)).

fof(t67_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => k1_relset_1(X1,X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_funct_2(X2,X1,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
       => ( v2_funct_1(X2)
        <=> ! [X3,X4] :
              ( ( r2_hidden(X3,X1)
                & r2_hidden(X4,X1)
                & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) )
             => X3 = X4 ) ) ) ),
    inference(assume_negation,[status(cth)],[t77_funct_2])).

fof(c_0_7,plain,(
    ! [X17,X18] :
      ( ~ v1_funct_1(X18)
      | ~ v1_funct_2(X18,X17,X17)
      | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X17,X17)))
      | k1_relset_1(X17,X17,X18) = X17 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_funct_2])])).

fof(c_0_8,negated_conjecture,(
    ! [X23,X24] :
      ( v1_funct_1(esk4_0)
      & v1_funct_2(esk4_0,esk3_0,esk3_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))
      & ( r2_hidden(esk5_0,esk3_0)
        | ~ v2_funct_1(esk4_0) )
      & ( r2_hidden(esk6_0,esk3_0)
        | ~ v2_funct_1(esk4_0) )
      & ( k1_funct_1(esk4_0,esk5_0) = k1_funct_1(esk4_0,esk6_0)
        | ~ v2_funct_1(esk4_0) )
      & ( esk5_0 != esk6_0
        | ~ v2_funct_1(esk4_0) )
      & ( v2_funct_1(esk4_0)
        | ~ r2_hidden(X23,esk3_0)
        | ~ r2_hidden(X24,esk3_0)
        | k1_funct_1(esk4_0,X23) != k1_funct_1(esk4_0,X24)
        | X23 = X24 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])])).

fof(c_0_9,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
      | k1_relset_1(X14,X15,X16) = k1_relat_1(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_10,plain,
    ( k1_relset_1(X2,X2,X1) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( v1_funct_2(esk4_0,esk3_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_14,plain,(
    ! [X5,X6] :
      ( ~ v1_relat_1(X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X5))
      | v1_relat_1(X6) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_15,plain,(
    ! [X7,X8] : v1_relat_1(k2_zfmisc_1(X7,X8)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_16,plain,(
    ! [X9,X10,X11] :
      ( ( ~ v2_funct_1(X9)
        | ~ r2_hidden(X10,k1_relat_1(X9))
        | ~ r2_hidden(X11,k1_relat_1(X9))
        | k1_funct_1(X9,X10) != k1_funct_1(X9,X11)
        | X10 = X11
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( r2_hidden(esk1_1(X9),k1_relat_1(X9))
        | v2_funct_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( r2_hidden(esk2_1(X9),k1_relat_1(X9))
        | v2_funct_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( k1_funct_1(X9,esk1_1(X9)) = k1_funct_1(X9,esk2_1(X9))
        | v2_funct_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( esk1_1(X9) != esk2_1(X9)
        | v2_funct_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).

cnf(c_0_17,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,negated_conjecture,
    ( k1_relset_1(esk3_0,esk3_0,esk4_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_13])])).

cnf(c_0_19,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( r2_hidden(esk1_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_13]),c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_13]),c_0_20])])).

cnf(c_0_24,negated_conjecture,
    ( v2_funct_1(esk4_0)
    | X1 = X2
    | ~ r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X2,esk3_0)
    | k1_funct_1(esk4_0,X1) != k1_funct_1(esk4_0,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk1_1(esk4_0),esk3_0)
    | v2_funct_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_12]),c_0_22]),c_0_23])])).

cnf(c_0_26,plain,
    ( r2_hidden(esk2_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( k1_funct_1(X1,esk1_1(X1)) = k1_funct_1(X1,esk2_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,plain,
    ( v2_funct_1(X1)
    | esk1_1(X1) != esk2_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,negated_conjecture,
    ( esk1_1(esk4_0) = X1
    | v2_funct_1(esk4_0)
    | k1_funct_1(esk4_0,esk1_1(esk4_0)) != k1_funct_1(esk4_0,X1)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk2_1(esk4_0),esk3_0)
    | v2_funct_1(esk4_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_12]),c_0_23])]),c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( k1_funct_1(esk4_0,esk2_1(esk4_0)) = k1_funct_1(esk4_0,esk1_1(esk4_0))
    | v2_funct_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_12]),c_0_23])])).

cnf(c_0_32,negated_conjecture,
    ( v2_funct_1(esk4_0)
    | esk2_1(esk4_0) != esk1_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_12]),c_0_23])])).

cnf(c_0_33,plain,
    ( X2 = X3
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_34,negated_conjecture,
    ( v2_funct_1(esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk6_0,esk3_0)
    | ~ v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_36,negated_conjecture,
    ( k1_funct_1(esk4_0,esk5_0) = k1_funct_1(esk4_0,esk6_0)
    | ~ v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_37,negated_conjecture,
    ( X1 = X2
    | k1_funct_1(esk4_0,X1) != k1_funct_1(esk4_0,X2)
    | ~ r2_hidden(X2,esk3_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_12]),c_0_23])]),c_0_22]),c_0_22]),c_0_34])])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk6_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_34])])).

cnf(c_0_39,negated_conjecture,
    ( k1_funct_1(esk4_0,esk6_0) = k1_funct_1(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_34])])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk5_0,esk3_0)
    | ~ v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_41,negated_conjecture,
    ( esk5_0 != esk6_0
    | ~ v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_42,negated_conjecture,
    ( esk6_0 = X1
    | k1_funct_1(esk4_0,esk5_0) != k1_funct_1(esk4_0,X1)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk5_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_34])])).

cnf(c_0_44,negated_conjecture,
    ( esk6_0 != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_34])])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n010.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 12:34:14 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  # Version: 2.5pre002
% 0.14/0.33  # No SInE strategy applied
% 0.14/0.33  # Trying AutoSched0 for 299 seconds
% 0.20/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S002I
% 0.20/0.36  # and selection function SelectNegativeLiterals.
% 0.20/0.36  #
% 0.20/0.36  # Preprocessing time       : 0.027 s
% 0.20/0.36  # Presaturation interreduction done
% 0.20/0.36  
% 0.20/0.36  # Proof found!
% 0.20/0.36  # SZS status Theorem
% 0.20/0.36  # SZS output start CNFRefutation
% 0.20/0.36  fof(t77_funct_2, conjecture, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(v2_funct_1(X2)<=>![X3, X4]:(((r2_hidden(X3,X1)&r2_hidden(X4,X1))&k1_funct_1(X2,X3)=k1_funct_1(X2,X4))=>X3=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_funct_2)).
% 0.20/0.36  fof(t67_funct_2, axiom, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>k1_relset_1(X1,X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 0.20/0.36  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.36  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.20/0.36  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.20/0.36  fof(d8_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)<=>![X2, X3]:(((r2_hidden(X2,k1_relat_1(X1))&r2_hidden(X3,k1_relat_1(X1)))&k1_funct_1(X1,X2)=k1_funct_1(X1,X3))=>X2=X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_funct_1)).
% 0.20/0.36  fof(c_0_6, negated_conjecture, ~(![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(v2_funct_1(X2)<=>![X3, X4]:(((r2_hidden(X3,X1)&r2_hidden(X4,X1))&k1_funct_1(X2,X3)=k1_funct_1(X2,X4))=>X3=X4)))), inference(assume_negation,[status(cth)],[t77_funct_2])).
% 0.20/0.36  fof(c_0_7, plain, ![X17, X18]:(~v1_funct_1(X18)|~v1_funct_2(X18,X17,X17)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X17,X17)))|k1_relset_1(X17,X17,X18)=X17), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_funct_2])])).
% 0.20/0.36  fof(c_0_8, negated_conjecture, ![X23, X24]:(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk3_0,esk3_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))))&(((((r2_hidden(esk5_0,esk3_0)|~v2_funct_1(esk4_0))&(r2_hidden(esk6_0,esk3_0)|~v2_funct_1(esk4_0)))&(k1_funct_1(esk4_0,esk5_0)=k1_funct_1(esk4_0,esk6_0)|~v2_funct_1(esk4_0)))&(esk5_0!=esk6_0|~v2_funct_1(esk4_0)))&(v2_funct_1(esk4_0)|(~r2_hidden(X23,esk3_0)|~r2_hidden(X24,esk3_0)|k1_funct_1(esk4_0,X23)!=k1_funct_1(esk4_0,X24)|X23=X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])])).
% 0.20/0.36  fof(c_0_9, plain, ![X14, X15, X16]:(~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))|k1_relset_1(X14,X15,X16)=k1_relat_1(X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.36  cnf(c_0_10, plain, (k1_relset_1(X2,X2,X1)=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.36  cnf(c_0_11, negated_conjecture, (v1_funct_2(esk4_0,esk3_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.36  cnf(c_0_12, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.36  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.36  fof(c_0_14, plain, ![X5, X6]:(~v1_relat_1(X5)|(~m1_subset_1(X6,k1_zfmisc_1(X5))|v1_relat_1(X6))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.20/0.36  fof(c_0_15, plain, ![X7, X8]:v1_relat_1(k2_zfmisc_1(X7,X8)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.20/0.36  fof(c_0_16, plain, ![X9, X10, X11]:((~v2_funct_1(X9)|(~r2_hidden(X10,k1_relat_1(X9))|~r2_hidden(X11,k1_relat_1(X9))|k1_funct_1(X9,X10)!=k1_funct_1(X9,X11)|X10=X11)|(~v1_relat_1(X9)|~v1_funct_1(X9)))&((((r2_hidden(esk1_1(X9),k1_relat_1(X9))|v2_funct_1(X9)|(~v1_relat_1(X9)|~v1_funct_1(X9)))&(r2_hidden(esk2_1(X9),k1_relat_1(X9))|v2_funct_1(X9)|(~v1_relat_1(X9)|~v1_funct_1(X9))))&(k1_funct_1(X9,esk1_1(X9))=k1_funct_1(X9,esk2_1(X9))|v2_funct_1(X9)|(~v1_relat_1(X9)|~v1_funct_1(X9))))&(esk1_1(X9)!=esk2_1(X9)|v2_funct_1(X9)|(~v1_relat_1(X9)|~v1_funct_1(X9))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).
% 0.20/0.36  cnf(c_0_17, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.36  cnf(c_0_18, negated_conjecture, (k1_relset_1(esk3_0,esk3_0,esk4_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12]), c_0_13])])).
% 0.20/0.36  cnf(c_0_19, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.36  cnf(c_0_20, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.36  cnf(c_0_21, plain, (r2_hidden(esk1_1(X1),k1_relat_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.36  cnf(c_0_22, negated_conjecture, (k1_relat_1(esk4_0)=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_13]), c_0_18])).
% 0.20/0.36  cnf(c_0_23, negated_conjecture, (v1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_13]), c_0_20])])).
% 0.20/0.36  cnf(c_0_24, negated_conjecture, (v2_funct_1(esk4_0)|X1=X2|~r2_hidden(X1,esk3_0)|~r2_hidden(X2,esk3_0)|k1_funct_1(esk4_0,X1)!=k1_funct_1(esk4_0,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.36  cnf(c_0_25, negated_conjecture, (r2_hidden(esk1_1(esk4_0),esk3_0)|v2_funct_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_12]), c_0_22]), c_0_23])])).
% 0.20/0.36  cnf(c_0_26, plain, (r2_hidden(esk2_1(X1),k1_relat_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.36  cnf(c_0_27, plain, (k1_funct_1(X1,esk1_1(X1))=k1_funct_1(X1,esk2_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.36  cnf(c_0_28, plain, (v2_funct_1(X1)|esk1_1(X1)!=esk2_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.36  cnf(c_0_29, negated_conjecture, (esk1_1(esk4_0)=X1|v2_funct_1(esk4_0)|k1_funct_1(esk4_0,esk1_1(esk4_0))!=k1_funct_1(esk4_0,X1)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.36  cnf(c_0_30, negated_conjecture, (r2_hidden(esk2_1(esk4_0),esk3_0)|v2_funct_1(esk4_0)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_12]), c_0_23])]), c_0_22])).
% 0.20/0.36  cnf(c_0_31, negated_conjecture, (k1_funct_1(esk4_0,esk2_1(esk4_0))=k1_funct_1(esk4_0,esk1_1(esk4_0))|v2_funct_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_12]), c_0_23])])).
% 0.20/0.36  cnf(c_0_32, negated_conjecture, (v2_funct_1(esk4_0)|esk2_1(esk4_0)!=esk1_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_12]), c_0_23])])).
% 0.20/0.36  cnf(c_0_33, plain, (X2=X3|~v2_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~r2_hidden(X3,k1_relat_1(X1))|k1_funct_1(X1,X2)!=k1_funct_1(X1,X3)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.36  cnf(c_0_34, negated_conjecture, (v2_funct_1(esk4_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32])).
% 0.20/0.36  cnf(c_0_35, negated_conjecture, (r2_hidden(esk6_0,esk3_0)|~v2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.36  cnf(c_0_36, negated_conjecture, (k1_funct_1(esk4_0,esk5_0)=k1_funct_1(esk4_0,esk6_0)|~v2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.36  cnf(c_0_37, negated_conjecture, (X1=X2|k1_funct_1(esk4_0,X1)!=k1_funct_1(esk4_0,X2)|~r2_hidden(X2,esk3_0)|~r2_hidden(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_12]), c_0_23])]), c_0_22]), c_0_22]), c_0_34])])).
% 0.20/0.36  cnf(c_0_38, negated_conjecture, (r2_hidden(esk6_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_34])])).
% 0.20/0.36  cnf(c_0_39, negated_conjecture, (k1_funct_1(esk4_0,esk6_0)=k1_funct_1(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_34])])).
% 0.20/0.36  cnf(c_0_40, negated_conjecture, (r2_hidden(esk5_0,esk3_0)|~v2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.36  cnf(c_0_41, negated_conjecture, (esk5_0!=esk6_0|~v2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.36  cnf(c_0_42, negated_conjecture, (esk6_0=X1|k1_funct_1(esk4_0,esk5_0)!=k1_funct_1(esk4_0,X1)|~r2_hidden(X1,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])).
% 0.20/0.36  cnf(c_0_43, negated_conjecture, (r2_hidden(esk5_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_34])])).
% 0.20/0.36  cnf(c_0_44, negated_conjecture, (esk6_0!=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_34])])).
% 0.20/0.36  cnf(c_0_45, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), ['proof']).
% 0.20/0.36  # SZS output end CNFRefutation
% 0.20/0.36  # Proof object total steps             : 46
% 0.20/0.36  # Proof object clause steps            : 33
% 0.20/0.36  # Proof object formula steps           : 13
% 0.20/0.36  # Proof object conjectures             : 27
% 0.20/0.36  # Proof object clause conjectures      : 24
% 0.20/0.36  # Proof object formula conjectures     : 3
% 0.20/0.36  # Proof object initial clauses used    : 17
% 0.20/0.36  # Proof object initial formulas used   : 6
% 0.20/0.36  # Proof object generating inferences   : 12
% 0.20/0.36  # Proof object simplifying inferences  : 34
% 0.20/0.36  # Training examples: 0 positive, 0 negative
% 0.20/0.36  # Parsed axioms                        : 6
% 0.20/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.36  # Initial clauses                      : 17
% 0.20/0.36  # Removed in clause preprocessing      : 0
% 0.20/0.36  # Initial clauses in saturation        : 17
% 0.20/0.36  # Processed clauses                    : 50
% 0.20/0.36  # ...of these trivial                  : 0
% 0.20/0.36  # ...subsumed                          : 0
% 0.20/0.36  # ...remaining for further processing  : 50
% 0.20/0.36  # Other redundant clauses eliminated   : 0
% 0.20/0.36  # Clauses deleted for lack of memory   : 0
% 0.20/0.36  # Backward-subsumed                    : 1
% 0.20/0.36  # Backward-rewritten                   : 9
% 0.20/0.36  # Generated clauses                    : 22
% 0.20/0.36  # ...of the previous two non-trivial   : 25
% 0.20/0.36  # Contextual simplify-reflections      : 2
% 0.20/0.36  # Paramodulations                      : 22
% 0.20/0.36  # Factorizations                       : 0
% 0.20/0.36  # Equation resolutions                 : 0
% 0.20/0.36  # Propositional unsat checks           : 0
% 0.20/0.36  #    Propositional check models        : 0
% 0.20/0.36  #    Propositional check unsatisfiable : 0
% 0.20/0.36  #    Propositional clauses             : 0
% 0.20/0.36  #    Propositional clauses after purity: 0
% 0.20/0.36  #    Propositional unsat core size     : 0
% 0.20/0.36  #    Propositional preprocessing time  : 0.000
% 0.20/0.36  #    Propositional encoding time       : 0.000
% 0.20/0.36  #    Propositional solver time         : 0.000
% 0.20/0.36  #    Success case prop preproc time    : 0.000
% 0.20/0.36  #    Success case prop encoding time   : 0.000
% 0.20/0.36  #    Success case prop solver time     : 0.000
% 0.20/0.36  # Current number of processed clauses  : 23
% 0.20/0.36  #    Positive orientable unit clauses  : 11
% 0.20/0.36  #    Positive unorientable unit clauses: 0
% 0.20/0.36  #    Negative unit clauses             : 1
% 0.20/0.36  #    Non-unit-clauses                  : 11
% 0.20/0.36  # Current number of unprocessed clauses: 3
% 0.20/0.36  # ...number of literals in the above   : 9
% 0.20/0.36  # Current number of archived formulas  : 0
% 0.20/0.36  # Current number of archived clauses   : 27
% 0.20/0.36  # Clause-clause subsumption calls (NU) : 117
% 0.20/0.36  # Rec. Clause-clause subsumption calls : 39
% 0.20/0.36  # Non-unit clause-clause subsumptions  : 2
% 0.20/0.36  # Unit Clause-clause subsumption calls : 13
% 0.20/0.36  # Rewrite failures with RHS unbound    : 0
% 0.20/0.36  # BW rewrite match attempts            : 1
% 0.20/0.36  # BW rewrite match successes           : 1
% 0.20/0.36  # Condensation attempts                : 0
% 0.20/0.36  # Condensation successes               : 0
% 0.20/0.36  # Termbank termtop insertions          : 1819
% 0.20/0.36  
% 0.20/0.36  # -------------------------------------------------
% 0.20/0.36  # User time                : 0.028 s
% 0.20/0.36  # System time              : 0.005 s
% 0.20/0.36  # Total time               : 0.033 s
% 0.20/0.36  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
