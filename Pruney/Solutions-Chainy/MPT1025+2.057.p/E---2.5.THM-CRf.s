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
% DateTime   : Thu Dec  3 11:06:43 EST 2020

% Result     : Theorem 0.08s
% Output     : CNFRefutation 0.08s
% Verified   : 
% Statistics : Number of formulae       :   42 (  86 expanded)
%              Number of clauses        :   23 (  34 expanded)
%              Number of leaves         :    9 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :  138 ( 356 expanded)
%              Number of equality atoms :   13 (  34 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t116_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X5] :
          ~ ( r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
            & ! [X6] :
                ( m1_subset_1(X6,X1)
               => ~ ( r2_hidden(X6,X3)
                    & X5 = k1_funct_1(X4,X6) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

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

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X5] :
            ~ ( r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
              & ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ~ ( r2_hidden(X6,X3)
                      & X5 = k1_funct_1(X4,X6) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t116_funct_2])).

fof(c_0_10,plain,(
    ! [X11,X12,X13] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | ~ r2_hidden(X13,X12)
      | r2_hidden(X13,X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_11,negated_conjecture,(
    ! [X37] :
      ( v1_funct_1(esk5_0)
      & v1_funct_2(esk5_0,esk2_0,esk3_0)
      & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
      & r2_hidden(esk6_0,k7_relset_1(esk2_0,esk3_0,esk5_0,esk4_0))
      & ( ~ m1_subset_1(X37,esk2_0)
        | ~ r2_hidden(X37,esk4_0)
        | esk6_0 != k1_funct_1(esk5_0,X37) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).

fof(c_0_12,plain,(
    ! [X25,X26,X27] :
      ( ( r2_hidden(X25,k1_relat_1(X27))
        | ~ r2_hidden(k4_tarski(X25,X26),X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( X26 = k1_funct_1(X27,X25)
        | ~ r2_hidden(k4_tarski(X25,X26),X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( ~ r2_hidden(X25,k1_relat_1(X27))
        | X26 != k1_funct_1(X27,X25)
        | r2_hidden(k4_tarski(X25,X26),X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

fof(c_0_13,plain,(
    ! [X20,X21,X22,X24] :
      ( ( r2_hidden(esk1_3(X20,X21,X22),k1_relat_1(X22))
        | ~ r2_hidden(X20,k9_relat_1(X22,X21))
        | ~ v1_relat_1(X22) )
      & ( r2_hidden(k4_tarski(esk1_3(X20,X21,X22),X20),X22)
        | ~ r2_hidden(X20,k9_relat_1(X22,X21))
        | ~ v1_relat_1(X22) )
      & ( r2_hidden(esk1_3(X20,X21,X22),X21)
        | ~ r2_hidden(X20,k9_relat_1(X22,X21))
        | ~ v1_relat_1(X22) )
      & ( ~ r2_hidden(X24,k1_relat_1(X22))
        | ~ r2_hidden(k4_tarski(X24,X20),X22)
        | ~ r2_hidden(X24,X21)
        | r2_hidden(X20,k9_relat_1(X22,X21))
        | ~ v1_relat_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

fof(c_0_14,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X16)
      | ~ m1_subset_1(X17,k1_zfmisc_1(X16))
      | v1_relat_1(X17) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_15,plain,(
    ! [X18,X19] : v1_relat_1(k2_zfmisc_1(X18,X19)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_16,plain,(
    ! [X7,X8,X9,X10] :
      ( ( r2_hidden(X7,X9)
        | ~ r2_hidden(k4_tarski(X7,X8),k2_zfmisc_1(X9,X10)) )
      & ( r2_hidden(X8,X10)
        | ~ r2_hidden(k4_tarski(X7,X8),k2_zfmisc_1(X9,X10)) )
      & ( ~ r2_hidden(X7,X9)
        | ~ r2_hidden(X8,X10)
        | r2_hidden(k4_tarski(X7,X8),k2_zfmisc_1(X9,X10)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_17,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(esk1_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk2_0,esk3_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_25,plain,(
    ! [X28,X29,X30,X31] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
      | k7_relset_1(X28,X29,X30,X31) = k9_relat_1(X30,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

cnf(c_0_26,negated_conjecture,
    ( ~ m1_subset_1(X1,esk2_0)
    | ~ r2_hidden(X1,esk4_0)
    | esk6_0 != k1_funct_1(esk5_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_27,plain,
    ( k1_funct_1(X1,esk1_3(X2,X3,X1)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_29,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_18]),c_0_22])])).

fof(c_0_30,plain,(
    ! [X14,X15] :
      ( ~ r2_hidden(X14,X15)
      | m1_subset_1(X14,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(k4_tarski(X1,X2),esk5_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( ~ m1_subset_1(esk1_3(esk6_0,X1,esk5_0),esk2_0)
    | ~ r2_hidden(esk1_3(esk6_0,X1,esk5_0),esk4_0)
    | ~ r2_hidden(esk6_0,k9_relat_1(esk5_0,X1)) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])])])).

cnf(c_0_34,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk1_3(X1,X2,esk5_0),esk2_0)
    | ~ r2_hidden(X1,k9_relat_1(esk5_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_20]),c_0_29])])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk6_0,k7_relset_1(esk2_0,esk3_0,esk5_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_37,negated_conjecture,
    ( k7_relset_1(esk2_0,esk3_0,esk5_0,X1) = k9_relat_1(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_18])).

cnf(c_0_38,negated_conjecture,
    ( ~ r2_hidden(esk1_3(esk6_0,X1,esk5_0),esk4_0)
    | ~ r2_hidden(esk6_0,k9_relat_1(esk5_0,X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_39,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk6_0,k9_relat_1(esk5_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_29])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.08/0.27  % Computer   : n022.cluster.edu
% 0.08/0.27  % Model      : x86_64 x86_64
% 0.08/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.27  % Memory     : 8042.1875MB
% 0.08/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.28  % CPULimit   : 60
% 0.08/0.28  % WCLimit    : 600
% 0.08/0.28  % DateTime   : Tue Dec  1 14:19:25 EST 2020
% 0.08/0.28  % CPUTime    : 
% 0.08/0.28  # Version: 2.5pre002
% 0.08/0.28  # No SInE strategy applied
% 0.08/0.28  # Trying AutoSched0 for 299 seconds
% 0.08/0.30  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.08/0.30  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.08/0.30  #
% 0.08/0.30  # Preprocessing time       : 0.020 s
% 0.08/0.30  # Presaturation interreduction done
% 0.08/0.30  
% 0.08/0.30  # Proof found!
% 0.08/0.30  # SZS status Theorem
% 0.08/0.30  # SZS output start CNFRefutation
% 0.08/0.30  fof(t116_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:(m1_subset_1(X6,X1)=>~((r2_hidden(X6,X3)&X5=k1_funct_1(X4,X6))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_funct_2)).
% 0.08/0.30  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.08/0.30  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 0.08/0.30  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 0.08/0.30  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.08/0.30  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.08/0.30  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.08/0.30  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.08/0.30  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.08/0.30  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:(m1_subset_1(X6,X1)=>~((r2_hidden(X6,X3)&X5=k1_funct_1(X4,X6)))))))), inference(assume_negation,[status(cth)],[t116_funct_2])).
% 0.08/0.30  fof(c_0_10, plain, ![X11, X12, X13]:(~m1_subset_1(X12,k1_zfmisc_1(X11))|(~r2_hidden(X13,X12)|r2_hidden(X13,X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.08/0.30  fof(c_0_11, negated_conjecture, ![X37]:(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk2_0,esk3_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))&(r2_hidden(esk6_0,k7_relset_1(esk2_0,esk3_0,esk5_0,esk4_0))&(~m1_subset_1(X37,esk2_0)|(~r2_hidden(X37,esk4_0)|esk6_0!=k1_funct_1(esk5_0,X37))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).
% 0.08/0.30  fof(c_0_12, plain, ![X25, X26, X27]:(((r2_hidden(X25,k1_relat_1(X27))|~r2_hidden(k4_tarski(X25,X26),X27)|(~v1_relat_1(X27)|~v1_funct_1(X27)))&(X26=k1_funct_1(X27,X25)|~r2_hidden(k4_tarski(X25,X26),X27)|(~v1_relat_1(X27)|~v1_funct_1(X27))))&(~r2_hidden(X25,k1_relat_1(X27))|X26!=k1_funct_1(X27,X25)|r2_hidden(k4_tarski(X25,X26),X27)|(~v1_relat_1(X27)|~v1_funct_1(X27)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.08/0.30  fof(c_0_13, plain, ![X20, X21, X22, X24]:((((r2_hidden(esk1_3(X20,X21,X22),k1_relat_1(X22))|~r2_hidden(X20,k9_relat_1(X22,X21))|~v1_relat_1(X22))&(r2_hidden(k4_tarski(esk1_3(X20,X21,X22),X20),X22)|~r2_hidden(X20,k9_relat_1(X22,X21))|~v1_relat_1(X22)))&(r2_hidden(esk1_3(X20,X21,X22),X21)|~r2_hidden(X20,k9_relat_1(X22,X21))|~v1_relat_1(X22)))&(~r2_hidden(X24,k1_relat_1(X22))|~r2_hidden(k4_tarski(X24,X20),X22)|~r2_hidden(X24,X21)|r2_hidden(X20,k9_relat_1(X22,X21))|~v1_relat_1(X22))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.08/0.30  fof(c_0_14, plain, ![X16, X17]:(~v1_relat_1(X16)|(~m1_subset_1(X17,k1_zfmisc_1(X16))|v1_relat_1(X17))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.08/0.30  fof(c_0_15, plain, ![X18, X19]:v1_relat_1(k2_zfmisc_1(X18,X19)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.08/0.30  fof(c_0_16, plain, ![X7, X8, X9, X10]:(((r2_hidden(X7,X9)|~r2_hidden(k4_tarski(X7,X8),k2_zfmisc_1(X9,X10)))&(r2_hidden(X8,X10)|~r2_hidden(k4_tarski(X7,X8),k2_zfmisc_1(X9,X10))))&(~r2_hidden(X7,X9)|~r2_hidden(X8,X10)|r2_hidden(k4_tarski(X7,X8),k2_zfmisc_1(X9,X10)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.08/0.30  cnf(c_0_17, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.08/0.30  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.08/0.30  cnf(c_0_19, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.08/0.30  cnf(c_0_20, plain, (r2_hidden(k4_tarski(esk1_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.08/0.30  cnf(c_0_21, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.08/0.30  cnf(c_0_22, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.08/0.30  cnf(c_0_23, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.08/0.30  cnf(c_0_24, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(esk2_0,esk3_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.08/0.30  fof(c_0_25, plain, ![X28, X29, X30, X31]:(~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|k7_relset_1(X28,X29,X30,X31)=k9_relat_1(X30,X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.08/0.30  cnf(c_0_26, negated_conjecture, (~m1_subset_1(X1,esk2_0)|~r2_hidden(X1,esk4_0)|esk6_0!=k1_funct_1(esk5_0,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.08/0.30  cnf(c_0_27, plain, (k1_funct_1(X1,esk1_3(X2,X3,X1))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(X1,X3))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.08/0.30  cnf(c_0_28, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.08/0.30  cnf(c_0_29, negated_conjecture, (v1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_18]), c_0_22])])).
% 0.08/0.30  fof(c_0_30, plain, ![X14, X15]:(~r2_hidden(X14,X15)|m1_subset_1(X14,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.08/0.30  cnf(c_0_31, negated_conjecture, (r2_hidden(X1,esk2_0)|~r2_hidden(k4_tarski(X1,X2),esk5_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.08/0.30  cnf(c_0_32, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.08/0.30  cnf(c_0_33, negated_conjecture, (~m1_subset_1(esk1_3(esk6_0,X1,esk5_0),esk2_0)|~r2_hidden(esk1_3(esk6_0,X1,esk5_0),esk4_0)|~r2_hidden(esk6_0,k9_relat_1(esk5_0,X1))), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])])])).
% 0.08/0.30  cnf(c_0_34, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.08/0.30  cnf(c_0_35, negated_conjecture, (r2_hidden(esk1_3(X1,X2,esk5_0),esk2_0)|~r2_hidden(X1,k9_relat_1(esk5_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_20]), c_0_29])])).
% 0.08/0.30  cnf(c_0_36, negated_conjecture, (r2_hidden(esk6_0,k7_relset_1(esk2_0,esk3_0,esk5_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.08/0.30  cnf(c_0_37, negated_conjecture, (k7_relset_1(esk2_0,esk3_0,esk5_0,X1)=k9_relat_1(esk5_0,X1)), inference(spm,[status(thm)],[c_0_32, c_0_18])).
% 0.08/0.30  cnf(c_0_38, negated_conjecture, (~r2_hidden(esk1_3(esk6_0,X1,esk5_0),esk4_0)|~r2_hidden(esk6_0,k9_relat_1(esk5_0,X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 0.08/0.30  cnf(c_0_39, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.08/0.30  cnf(c_0_40, negated_conjecture, (r2_hidden(esk6_0,k9_relat_1(esk5_0,esk4_0))), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.08/0.30  cnf(c_0_41, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_29])]), ['proof']).
% 0.08/0.30  # SZS output end CNFRefutation
% 0.08/0.30  # Proof object total steps             : 42
% 0.08/0.30  # Proof object clause steps            : 23
% 0.08/0.30  # Proof object formula steps           : 19
% 0.08/0.30  # Proof object conjectures             : 16
% 0.08/0.30  # Proof object clause conjectures      : 13
% 0.08/0.30  # Proof object formula conjectures     : 3
% 0.08/0.30  # Proof object initial clauses used    : 13
% 0.08/0.30  # Proof object initial formulas used   : 9
% 0.08/0.30  # Proof object generating inferences   : 9
% 0.08/0.30  # Proof object simplifying inferences  : 13
% 0.08/0.30  # Training examples: 0 positive, 0 negative
% 0.08/0.30  # Parsed axioms                        : 9
% 0.08/0.30  # Removed by relevancy pruning/SinE    : 0
% 0.08/0.30  # Initial clauses                      : 20
% 0.08/0.30  # Removed in clause preprocessing      : 0
% 0.08/0.30  # Initial clauses in saturation        : 20
% 0.08/0.30  # Processed clauses                    : 68
% 0.08/0.30  # ...of these trivial                  : 0
% 0.08/0.30  # ...subsumed                          : 1
% 0.08/0.30  # ...remaining for further processing  : 67
% 0.08/0.30  # Other redundant clauses eliminated   : 2
% 0.08/0.30  # Clauses deleted for lack of memory   : 0
% 0.08/0.30  # Backward-subsumed                    : 1
% 0.08/0.30  # Backward-rewritten                   : 1
% 0.08/0.30  # Generated clauses                    : 66
% 0.08/0.30  # ...of the previous two non-trivial   : 62
% 0.08/0.30  # Contextual simplify-reflections      : 1
% 0.08/0.30  # Paramodulations                      : 64
% 0.08/0.30  # Factorizations                       : 0
% 0.08/0.30  # Equation resolutions                 : 2
% 0.08/0.30  # Propositional unsat checks           : 0
% 0.08/0.30  #    Propositional check models        : 0
% 0.08/0.30  #    Propositional check unsatisfiable : 0
% 0.08/0.30  #    Propositional clauses             : 0
% 0.08/0.30  #    Propositional clauses after purity: 0
% 0.08/0.30  #    Propositional unsat core size     : 0
% 0.08/0.30  #    Propositional preprocessing time  : 0.000
% 0.08/0.30  #    Propositional encoding time       : 0.000
% 0.08/0.30  #    Propositional solver time         : 0.000
% 0.08/0.30  #    Success case prop preproc time    : 0.000
% 0.08/0.30  #    Success case prop encoding time   : 0.000
% 0.08/0.30  #    Success case prop solver time     : 0.000
% 0.08/0.30  # Current number of processed clauses  : 44
% 0.08/0.30  #    Positive orientable unit clauses  : 8
% 0.08/0.30  #    Positive unorientable unit clauses: 0
% 0.08/0.30  #    Negative unit clauses             : 0
% 0.08/0.30  #    Non-unit-clauses                  : 36
% 0.08/0.30  # Current number of unprocessed clauses: 34
% 0.08/0.30  # ...number of literals in the above   : 138
% 0.08/0.30  # Current number of archived formulas  : 0
% 0.08/0.30  # Current number of archived clauses   : 22
% 0.08/0.30  # Clause-clause subsumption calls (NU) : 232
% 0.08/0.30  # Rec. Clause-clause subsumption calls : 160
% 0.08/0.30  # Non-unit clause-clause subsumptions  : 3
% 0.08/0.30  # Unit Clause-clause subsumption calls : 0
% 0.08/0.30  # Rewrite failures with RHS unbound    : 0
% 0.08/0.30  # BW rewrite match attempts            : 1
% 0.08/0.30  # BW rewrite match successes           : 1
% 0.08/0.30  # Condensation attempts                : 0
% 0.08/0.30  # Condensation successes               : 0
% 0.08/0.30  # Termbank termtop insertions          : 2991
% 0.08/0.30  
% 0.08/0.30  # -------------------------------------------------
% 0.08/0.30  # User time                : 0.023 s
% 0.08/0.30  # System time              : 0.003 s
% 0.08/0.30  # Total time               : 0.026 s
% 0.08/0.30  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
