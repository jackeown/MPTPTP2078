%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:03:53 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 120 expanded)
%              Number of clauses        :   24 (  43 expanded)
%              Number of leaves         :    7 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :  167 ( 704 expanded)
%              Number of equality atoms :   54 ( 218 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t43_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( X2 != k1_xboole_0
       => ! [X5] :
            ( ? [X6] :
                ( r2_hidden(X6,X1)
                & r2_hidden(X6,X3)
                & X5 = k1_funct_1(X4,X6) )
           => r2_hidden(X5,k7_relset_1(X1,X2,X4,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_2)).

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

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

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

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( X2 != k1_xboole_0
         => ! [X5] :
              ( ? [X6] :
                  ( r2_hidden(X6,X1)
                  & r2_hidden(X6,X3)
                  & X5 = k1_funct_1(X4,X6) )
             => r2_hidden(X5,k7_relset_1(X1,X2,X4,X3)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t43_funct_2])).

fof(c_0_8,plain,(
    ! [X30,X31,X32] :
      ( ( ~ v1_funct_2(X32,X30,X31)
        | X30 = k1_relset_1(X30,X31,X32)
        | X31 = k1_xboole_0
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( X30 != k1_relset_1(X30,X31,X32)
        | v1_funct_2(X32,X30,X31)
        | X31 = k1_xboole_0
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( ~ v1_funct_2(X32,X30,X31)
        | X30 = k1_relset_1(X30,X31,X32)
        | X30 != k1_xboole_0
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( X30 != k1_relset_1(X30,X31,X32)
        | v1_funct_2(X32,X30,X31)
        | X30 != k1_xboole_0
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( ~ v1_funct_2(X32,X30,X31)
        | X32 = k1_xboole_0
        | X30 = k1_xboole_0
        | X31 != k1_xboole_0
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( X32 != k1_xboole_0
        | v1_funct_2(X32,X30,X31)
        | X30 = k1_xboole_0
        | X31 != k1_xboole_0
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_9,negated_conjecture,
    ( v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,esk4_0,esk5_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
    & esk5_0 != k1_xboole_0
    & r2_hidden(esk9_0,esk4_0)
    & r2_hidden(esk9_0,esk6_0)
    & esk8_0 = k1_funct_1(esk7_0,esk9_0)
    & ~ r2_hidden(esk8_0,k7_relset_1(esk4_0,esk5_0,esk7_0,esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X23,X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | k1_relset_1(X23,X24,X25) = k1_relat_1(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_11,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( v1_funct_2(esk7_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( ~ r2_hidden(esk8_0,k7_relset_1(esk4_0,esk5_0,esk7_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( esk8_0 = k1_funct_1(esk7_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( k1_relset_1(esk4_0,esk5_0,esk7_0) = esk4_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk7_0,esk9_0),k7_relset_1(esk4_0,esk5_0,esk7_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( esk4_0 = k1_relat_1(esk7_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_13]),c_0_18])).

fof(c_0_21,plain,(
    ! [X26,X27,X28,X29] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | k7_relset_1(X26,X27,X28,X29) = k9_relat_1(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_22,plain,(
    ! [X11,X12,X13,X14,X16,X17,X18,X19,X21] :
      ( ( r2_hidden(esk1_4(X11,X12,X13,X14),k1_relat_1(X11))
        | ~ r2_hidden(X14,X13)
        | X13 != k9_relat_1(X11,X12)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( r2_hidden(esk1_4(X11,X12,X13,X14),X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k9_relat_1(X11,X12)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( X14 = k1_funct_1(X11,esk1_4(X11,X12,X13,X14))
        | ~ r2_hidden(X14,X13)
        | X13 != k9_relat_1(X11,X12)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( ~ r2_hidden(X17,k1_relat_1(X11))
        | ~ r2_hidden(X17,X12)
        | X16 != k1_funct_1(X11,X17)
        | r2_hidden(X16,X13)
        | X13 != k9_relat_1(X11,X12)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( ~ r2_hidden(esk2_3(X11,X18,X19),X19)
        | ~ r2_hidden(X21,k1_relat_1(X11))
        | ~ r2_hidden(X21,X18)
        | esk2_3(X11,X18,X19) != k1_funct_1(X11,X21)
        | X19 = k9_relat_1(X11,X18)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( r2_hidden(esk3_3(X11,X18,X19),k1_relat_1(X11))
        | r2_hidden(esk2_3(X11,X18,X19),X19)
        | X19 = k9_relat_1(X11,X18)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( r2_hidden(esk3_3(X11,X18,X19),X18)
        | r2_hidden(esk2_3(X11,X18,X19),X19)
        | X19 = k9_relat_1(X11,X18)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( esk2_3(X11,X18,X19) = k1_funct_1(X11,esk3_3(X11,X18,X19))
        | r2_hidden(esk2_3(X11,X18,X19),X19)
        | X19 = k9_relat_1(X11,X18)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).

fof(c_0_23,plain,(
    ! [X7,X8] :
      ( ~ v1_relat_1(X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(X7))
      | v1_relat_1(X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_24,plain,(
    ! [X9,X10] : v1_relat_1(k2_zfmisc_1(X9,X10)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_25,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk7_0,esk9_0),k7_relset_1(k1_relat_1(esk7_0),esk5_0,esk7_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk7_0),esk5_0))) ),
    inference(rw,[status(thm)],[c_0_13,c_0_20])).

cnf(c_0_28,plain,
    ( r2_hidden(X4,X5)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,X3)
    | X4 != k1_funct_1(X2,X1)
    | X5 != k9_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk9_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_30,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk7_0,esk9_0),k9_relat_1(esk7_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

cnf(c_0_33,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k9_relat_1(X1,X3))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_28])])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk9_0,k1_relat_1(esk7_0)) ),
    inference(rw,[status(thm)],[c_0_29,c_0_20])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk9_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_37,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_13]),c_0_31])])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:13:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 0.14/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.028 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t43_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(X2!=k1_xboole_0=>![X5]:(?[X6]:((r2_hidden(X6,X1)&r2_hidden(X6,X3))&X5=k1_funct_1(X4,X6))=>r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_2)).
% 0.14/0.38  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.14/0.38  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.14/0.38  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.14/0.38  fof(d12_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(X3=k9_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((r2_hidden(X5,k1_relat_1(X1))&r2_hidden(X5,X2))&X4=k1_funct_1(X1,X5))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_1)).
% 0.14/0.38  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.14/0.38  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.14/0.38  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(X2!=k1_xboole_0=>![X5]:(?[X6]:((r2_hidden(X6,X1)&r2_hidden(X6,X3))&X5=k1_funct_1(X4,X6))=>r2_hidden(X5,k7_relset_1(X1,X2,X4,X3)))))), inference(assume_negation,[status(cth)],[t43_funct_2])).
% 0.14/0.38  fof(c_0_8, plain, ![X30, X31, X32]:((((~v1_funct_2(X32,X30,X31)|X30=k1_relset_1(X30,X31,X32)|X31=k1_xboole_0|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))&(X30!=k1_relset_1(X30,X31,X32)|v1_funct_2(X32,X30,X31)|X31=k1_xboole_0|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))&((~v1_funct_2(X32,X30,X31)|X30=k1_relset_1(X30,X31,X32)|X30!=k1_xboole_0|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))&(X30!=k1_relset_1(X30,X31,X32)|v1_funct_2(X32,X30,X31)|X30!=k1_xboole_0|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))))&((~v1_funct_2(X32,X30,X31)|X32=k1_xboole_0|X30=k1_xboole_0|X31!=k1_xboole_0|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))&(X32!=k1_xboole_0|v1_funct_2(X32,X30,X31)|X30=k1_xboole_0|X31!=k1_xboole_0|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.14/0.38  fof(c_0_9, negated_conjecture, (((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,esk4_0,esk5_0))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))))&(esk5_0!=k1_xboole_0&(((r2_hidden(esk9_0,esk4_0)&r2_hidden(esk9_0,esk6_0))&esk8_0=k1_funct_1(esk7_0,esk9_0))&~r2_hidden(esk8_0,k7_relset_1(esk4_0,esk5_0,esk7_0,esk6_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.14/0.38  fof(c_0_10, plain, ![X23, X24, X25]:(~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))|k1_relset_1(X23,X24,X25)=k1_relat_1(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.14/0.38  cnf(c_0_11, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_12, negated_conjecture, (v1_funct_2(esk7_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_14, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_15, negated_conjecture, (~r2_hidden(esk8_0,k7_relset_1(esk4_0,esk5_0,esk7_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_16, negated_conjecture, (esk8_0=k1_funct_1(esk7_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_17, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_18, negated_conjecture, (k1_relset_1(esk4_0,esk5_0,esk7_0)=esk4_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13])]), c_0_14])).
% 0.14/0.38  cnf(c_0_19, negated_conjecture, (~r2_hidden(k1_funct_1(esk7_0,esk9_0),k7_relset_1(esk4_0,esk5_0,esk7_0,esk6_0))), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.14/0.38  cnf(c_0_20, negated_conjecture, (esk4_0=k1_relat_1(esk7_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_13]), c_0_18])).
% 0.14/0.38  fof(c_0_21, plain, ![X26, X27, X28, X29]:(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|k7_relset_1(X26,X27,X28,X29)=k9_relat_1(X28,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.14/0.38  fof(c_0_22, plain, ![X11, X12, X13, X14, X16, X17, X18, X19, X21]:(((((r2_hidden(esk1_4(X11,X12,X13,X14),k1_relat_1(X11))|~r2_hidden(X14,X13)|X13!=k9_relat_1(X11,X12)|(~v1_relat_1(X11)|~v1_funct_1(X11)))&(r2_hidden(esk1_4(X11,X12,X13,X14),X12)|~r2_hidden(X14,X13)|X13!=k9_relat_1(X11,X12)|(~v1_relat_1(X11)|~v1_funct_1(X11))))&(X14=k1_funct_1(X11,esk1_4(X11,X12,X13,X14))|~r2_hidden(X14,X13)|X13!=k9_relat_1(X11,X12)|(~v1_relat_1(X11)|~v1_funct_1(X11))))&(~r2_hidden(X17,k1_relat_1(X11))|~r2_hidden(X17,X12)|X16!=k1_funct_1(X11,X17)|r2_hidden(X16,X13)|X13!=k9_relat_1(X11,X12)|(~v1_relat_1(X11)|~v1_funct_1(X11))))&((~r2_hidden(esk2_3(X11,X18,X19),X19)|(~r2_hidden(X21,k1_relat_1(X11))|~r2_hidden(X21,X18)|esk2_3(X11,X18,X19)!=k1_funct_1(X11,X21))|X19=k9_relat_1(X11,X18)|(~v1_relat_1(X11)|~v1_funct_1(X11)))&(((r2_hidden(esk3_3(X11,X18,X19),k1_relat_1(X11))|r2_hidden(esk2_3(X11,X18,X19),X19)|X19=k9_relat_1(X11,X18)|(~v1_relat_1(X11)|~v1_funct_1(X11)))&(r2_hidden(esk3_3(X11,X18,X19),X18)|r2_hidden(esk2_3(X11,X18,X19),X19)|X19=k9_relat_1(X11,X18)|(~v1_relat_1(X11)|~v1_funct_1(X11))))&(esk2_3(X11,X18,X19)=k1_funct_1(X11,esk3_3(X11,X18,X19))|r2_hidden(esk2_3(X11,X18,X19),X19)|X19=k9_relat_1(X11,X18)|(~v1_relat_1(X11)|~v1_funct_1(X11)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).
% 0.14/0.38  fof(c_0_23, plain, ![X7, X8]:(~v1_relat_1(X7)|(~m1_subset_1(X8,k1_zfmisc_1(X7))|v1_relat_1(X8))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.14/0.38  fof(c_0_24, plain, ![X9, X10]:v1_relat_1(k2_zfmisc_1(X9,X10)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.14/0.38  cnf(c_0_25, negated_conjecture, (~r2_hidden(k1_funct_1(esk7_0,esk9_0),k7_relset_1(k1_relat_1(esk7_0),esk5_0,esk7_0,esk6_0))), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.14/0.38  cnf(c_0_26, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.38  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk7_0),esk5_0)))), inference(rw,[status(thm)],[c_0_13, c_0_20])).
% 0.14/0.38  cnf(c_0_28, plain, (r2_hidden(X4,X5)|~r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(X1,X3)|X4!=k1_funct_1(X2,X1)|X5!=k9_relat_1(X2,X3)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.38  cnf(c_0_29, negated_conjecture, (r2_hidden(esk9_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_30, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.38  cnf(c_0_31, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.38  cnf(c_0_32, negated_conjecture, (~r2_hidden(k1_funct_1(esk7_0,esk9_0),k9_relat_1(esk7_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])])).
% 0.14/0.38  cnf(c_0_33, plain, (r2_hidden(k1_funct_1(X1,X2),k9_relat_1(X1,X3))|~r2_hidden(X2,k1_relat_1(X1))|~r2_hidden(X2,X3)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_28])])).
% 0.14/0.38  cnf(c_0_34, negated_conjecture, (r2_hidden(esk9_0,k1_relat_1(esk7_0))), inference(rw,[status(thm)],[c_0_29, c_0_20])).
% 0.14/0.38  cnf(c_0_35, negated_conjecture, (r2_hidden(esk9_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_36, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_37, negated_conjecture, (v1_relat_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_13]), c_0_31])])).
% 0.14/0.38  cnf(c_0_38, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37])]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 39
% 0.14/0.38  # Proof object clause steps            : 24
% 0.14/0.38  # Proof object formula steps           : 15
% 0.14/0.38  # Proof object conjectures             : 20
% 0.14/0.38  # Proof object clause conjectures      : 17
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 14
% 0.14/0.38  # Proof object initial formulas used   : 7
% 0.14/0.38  # Proof object generating inferences   : 5
% 0.14/0.38  # Proof object simplifying inferences  : 19
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 7
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 26
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 26
% 0.14/0.38  # Processed clauses                    : 73
% 0.14/0.38  # ...of these trivial                  : 2
% 0.14/0.38  # ...subsumed                          : 0
% 0.14/0.38  # ...remaining for further processing  : 71
% 0.14/0.38  # Other redundant clauses eliminated   : 10
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 5
% 0.14/0.38  # Generated clauses                    : 27
% 0.14/0.38  # ...of the previous two non-trivial   : 25
% 0.14/0.38  # Contextual simplify-reflections      : 2
% 0.14/0.38  # Paramodulations                      : 19
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 10
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 32
% 0.14/0.38  #    Positive orientable unit clauses  : 10
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 3
% 0.14/0.38  #    Non-unit-clauses                  : 19
% 0.14/0.38  # Current number of unprocessed clauses: 3
% 0.14/0.38  # ...number of literals in the above   : 14
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 31
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 141
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 28
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 2
% 0.14/0.38  # Unit Clause-clause subsumption calls : 1
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 1
% 0.14/0.38  # BW rewrite match successes           : 1
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 2685
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.032 s
% 0.14/0.38  # System time              : 0.003 s
% 0.14/0.38  # Total time               : 0.035 s
% 0.14/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
