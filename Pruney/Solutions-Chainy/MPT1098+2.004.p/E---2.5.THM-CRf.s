%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:08:30 EST 2020

% Result     : Theorem 0.60s
% Output     : CNFRefutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 141 expanded)
%              Number of clauses        :   34 (  59 expanded)
%              Number of leaves         :   12 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :  177 ( 443 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t13_finset_1,axiom,(
    ! [X1,X2] :
      ( ( r1_tarski(X1,X2)
        & v1_finset_1(X2) )
     => v1_finset_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_finset_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(t193_relat_1,axiom,(
    ! [X1,X2] : r1_tarski(k1_relat_1(k2_zfmisc_1(X1,X2)),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t33_finset_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( v1_finset_1(X1)
        & r1_tarski(X1,k2_zfmisc_1(X2,X3))
        & ! [X4] :
            ~ ( v1_finset_1(X4)
              & r1_tarski(X4,X2)
              & r1_tarski(X1,k2_zfmisc_1(X4,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_finset_1)).

fof(t194_relat_1,axiom,(
    ! [X1,X2] : r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t194_relat_1)).

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t32_finset_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( v1_finset_1(X1)
        & r1_tarski(X1,k2_zfmisc_1(X2,X3))
        & ! [X4,X5] :
            ~ ( v1_finset_1(X4)
              & r1_tarski(X4,X2)
              & v1_finset_1(X5)
              & r1_tarski(X5,X3)
              & r1_tarski(X1,k2_zfmisc_1(X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_finset_1)).

fof(c_0_12,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(X13))
      | v1_relat_1(X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_13,plain,(
    ! [X11,X12] :
      ( ( ~ m1_subset_1(X11,k1_zfmisc_1(X12))
        | r1_tarski(X11,X12) )
      & ( ~ r1_tarski(X11,X12)
        | m1_subset_1(X11,k1_zfmisc_1(X12)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_14,plain,(
    ! [X26,X27] :
      ( ~ r1_tarski(X26,X27)
      | ~ v1_finset_1(X27)
      | v1_finset_1(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_finset_1])])).

fof(c_0_15,plain,(
    ! [X21,X22] :
      ( ( r1_tarski(k1_relat_1(X21),k1_relat_1(X22))
        | ~ r1_tarski(X21,X22)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21) )
      & ( r1_tarski(k2_relat_1(X21),k2_relat_1(X22))
        | ~ r1_tarski(X21,X22)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

cnf(c_0_16,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X17,X18] : r1_tarski(k1_relat_1(k2_zfmisc_1(X17,X18)),X17) ),
    inference(variable_rename,[status(thm)],[t193_relat_1])).

cnf(c_0_19,plain,
    ( v1_finset_1(X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_finset_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( r1_tarski(k1_relat_1(k2_zfmisc_1(X1,X2)),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,plain,(
    ! [X15,X16] : v1_relat_1(k2_zfmisc_1(X15,X16)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_24,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(X8,X9)
      | ~ r1_tarski(X9,X10)
      | r1_tarski(X8,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( v1_finset_1(X1)
          & r1_tarski(X1,k2_zfmisc_1(X2,X3))
          & ! [X4] :
              ~ ( v1_finset_1(X4)
                & r1_tarski(X4,X2)
                & r1_tarski(X1,k2_zfmisc_1(X4,X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t33_finset_1])).

fof(c_0_26,plain,(
    ! [X19,X20] : r1_tarski(k2_relat_1(k2_zfmisc_1(X19,X20)),X20) ),
    inference(variable_rename,[status(thm)],[t194_relat_1])).

fof(c_0_27,plain,(
    ! [X23,X24,X25] :
      ( ~ v1_relat_1(X25)
      | ~ r1_tarski(k1_relat_1(X25),X23)
      | ~ r1_tarski(k2_relat_1(X25),X24)
      | m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

fof(c_0_28,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_29,plain,
    ( v1_finset_1(k1_relat_1(X1))
    | ~ v1_finset_1(k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

cnf(c_0_30,plain,
    ( v1_finset_1(k1_relat_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_finset_1(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_22])).

cnf(c_0_31,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_32,plain,(
    ! [X28,X29,X30] :
      ( ( v1_finset_1(esk1_3(X28,X29,X30))
        | ~ v1_finset_1(X28)
        | ~ r1_tarski(X28,k2_zfmisc_1(X29,X30)) )
      & ( r1_tarski(esk1_3(X28,X29,X30),X29)
        | ~ v1_finset_1(X28)
        | ~ r1_tarski(X28,k2_zfmisc_1(X29,X30)) )
      & ( v1_finset_1(esk2_3(X28,X29,X30))
        | ~ v1_finset_1(X28)
        | ~ r1_tarski(X28,k2_zfmisc_1(X29,X30)) )
      & ( r1_tarski(esk2_3(X28,X29,X30),X30)
        | ~ v1_finset_1(X28)
        | ~ r1_tarski(X28,k2_zfmisc_1(X29,X30)) )
      & ( r1_tarski(X28,k2_zfmisc_1(esk1_3(X28,X29,X30),esk2_3(X28,X29,X30)))
        | ~ v1_finset_1(X28)
        | ~ r1_tarski(X28,k2_zfmisc_1(X29,X30)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_finset_1])])])])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_34,negated_conjecture,(
    ! [X36] :
      ( v1_finset_1(esk3_0)
      & r1_tarski(esk3_0,k2_zfmisc_1(esk4_0,esk5_0))
      & ( ~ v1_finset_1(X36)
        | ~ r1_tarski(X36,esk4_0)
        | ~ r1_tarski(esk3_0,k2_zfmisc_1(X36,esk5_0)) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])])).

cnf(c_0_35,plain,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_37,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( v1_finset_1(k1_relat_1(X1))
    | ~ v1_finset_1(X2)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,k2_zfmisc_1(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)))
    | ~ v1_finset_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( v1_finset_1(esk1_3(X1,X2,X3))
    | ~ v1_finset_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_relat_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_22])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(esk3_0,k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k2_relat_1(k2_zfmisc_1(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_35])).

cnf(c_0_45,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_48,plain,
    ( v1_finset_1(k1_relat_1(X1))
    | ~ v1_finset_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( v1_finset_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_50,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_20]),c_0_31])])).

cnf(c_0_51,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_43]),c_0_31])])).

cnf(c_0_52,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X3,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_31])])).

cnf(c_0_53,negated_conjecture,
    ( ~ v1_finset_1(X1)
    | ~ r1_tarski(X1,esk4_0)
    | ~ r1_tarski(esk3_0,k2_zfmisc_1(X1,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( v1_finset_1(k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_43]),c_0_49])])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_43]),c_0_51])])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk3_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_43]),c_0_51])])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),c_0_56]),c_0_51]),c_0_57])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n023.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 19:12:35 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  # Version: 2.5pre002
% 0.12/0.32  # No SInE strategy applied
% 0.12/0.32  # Trying AutoSched0 for 299 seconds
% 0.60/0.79  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.60/0.79  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.60/0.79  #
% 0.60/0.79  # Preprocessing time       : 0.028 s
% 0.60/0.79  # Presaturation interreduction done
% 0.60/0.79  
% 0.60/0.79  # Proof found!
% 0.60/0.79  # SZS status Theorem
% 0.60/0.79  # SZS output start CNFRefutation
% 0.60/0.79  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.60/0.79  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.60/0.79  fof(t13_finset_1, axiom, ![X1, X2]:((r1_tarski(X1,X2)&v1_finset_1(X2))=>v1_finset_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_finset_1)).
% 0.60/0.79  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 0.60/0.79  fof(t193_relat_1, axiom, ![X1, X2]:r1_tarski(k1_relat_1(k2_zfmisc_1(X1,X2)),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t193_relat_1)).
% 0.60/0.79  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.60/0.79  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.60/0.79  fof(t33_finset_1, conjecture, ![X1, X2, X3]:~(((v1_finset_1(X1)&r1_tarski(X1,k2_zfmisc_1(X2,X3)))&![X4]:~(((v1_finset_1(X4)&r1_tarski(X4,X2))&r1_tarski(X1,k2_zfmisc_1(X4,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_finset_1)).
% 0.60/0.79  fof(t194_relat_1, axiom, ![X1, X2]:r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t194_relat_1)).
% 0.60/0.79  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 0.60/0.79  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.60/0.79  fof(t32_finset_1, axiom, ![X1, X2, X3]:~(((v1_finset_1(X1)&r1_tarski(X1,k2_zfmisc_1(X2,X3)))&![X4, X5]:~(((((v1_finset_1(X4)&r1_tarski(X4,X2))&v1_finset_1(X5))&r1_tarski(X5,X3))&r1_tarski(X1,k2_zfmisc_1(X4,X5)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_finset_1)).
% 0.60/0.79  fof(c_0_12, plain, ![X13, X14]:(~v1_relat_1(X13)|(~m1_subset_1(X14,k1_zfmisc_1(X13))|v1_relat_1(X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.60/0.79  fof(c_0_13, plain, ![X11, X12]:((~m1_subset_1(X11,k1_zfmisc_1(X12))|r1_tarski(X11,X12))&(~r1_tarski(X11,X12)|m1_subset_1(X11,k1_zfmisc_1(X12)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.60/0.79  fof(c_0_14, plain, ![X26, X27]:(~r1_tarski(X26,X27)|~v1_finset_1(X27)|v1_finset_1(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_finset_1])])).
% 0.60/0.79  fof(c_0_15, plain, ![X21, X22]:((r1_tarski(k1_relat_1(X21),k1_relat_1(X22))|~r1_tarski(X21,X22)|~v1_relat_1(X22)|~v1_relat_1(X21))&(r1_tarski(k2_relat_1(X21),k2_relat_1(X22))|~r1_tarski(X21,X22)|~v1_relat_1(X22)|~v1_relat_1(X21))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.60/0.79  cnf(c_0_16, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.60/0.79  cnf(c_0_17, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.60/0.79  fof(c_0_18, plain, ![X17, X18]:r1_tarski(k1_relat_1(k2_zfmisc_1(X17,X18)),X17), inference(variable_rename,[status(thm)],[t193_relat_1])).
% 0.60/0.79  cnf(c_0_19, plain, (v1_finset_1(X1)|~r1_tarski(X1,X2)|~v1_finset_1(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.60/0.79  cnf(c_0_20, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.60/0.79  cnf(c_0_21, plain, (v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.60/0.79  cnf(c_0_22, plain, (r1_tarski(k1_relat_1(k2_zfmisc_1(X1,X2)),X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.60/0.79  fof(c_0_23, plain, ![X15, X16]:v1_relat_1(k2_zfmisc_1(X15,X16)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.60/0.79  fof(c_0_24, plain, ![X8, X9, X10]:(~r1_tarski(X8,X9)|~r1_tarski(X9,X10)|r1_tarski(X8,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.60/0.79  fof(c_0_25, negated_conjecture, ~(![X1, X2, X3]:~(((v1_finset_1(X1)&r1_tarski(X1,k2_zfmisc_1(X2,X3)))&![X4]:~(((v1_finset_1(X4)&r1_tarski(X4,X2))&r1_tarski(X1,k2_zfmisc_1(X4,X3))))))), inference(assume_negation,[status(cth)],[t33_finset_1])).
% 0.60/0.79  fof(c_0_26, plain, ![X19, X20]:r1_tarski(k2_relat_1(k2_zfmisc_1(X19,X20)),X20), inference(variable_rename,[status(thm)],[t194_relat_1])).
% 0.60/0.79  fof(c_0_27, plain, ![X23, X24, X25]:(~v1_relat_1(X25)|(~r1_tarski(k1_relat_1(X25),X23)|~r1_tarski(k2_relat_1(X25),X24)|m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 0.60/0.79  fof(c_0_28, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.60/0.79  cnf(c_0_29, plain, (v1_finset_1(k1_relat_1(X1))|~v1_finset_1(k1_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])).
% 0.60/0.79  cnf(c_0_30, plain, (v1_finset_1(k1_relat_1(k2_zfmisc_1(X1,X2)))|~v1_finset_1(X1)), inference(spm,[status(thm)],[c_0_19, c_0_22])).
% 0.60/0.79  cnf(c_0_31, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.60/0.79  fof(c_0_32, plain, ![X28, X29, X30]:(((((v1_finset_1(esk1_3(X28,X29,X30))|(~v1_finset_1(X28)|~r1_tarski(X28,k2_zfmisc_1(X29,X30))))&(r1_tarski(esk1_3(X28,X29,X30),X29)|(~v1_finset_1(X28)|~r1_tarski(X28,k2_zfmisc_1(X29,X30)))))&(v1_finset_1(esk2_3(X28,X29,X30))|(~v1_finset_1(X28)|~r1_tarski(X28,k2_zfmisc_1(X29,X30)))))&(r1_tarski(esk2_3(X28,X29,X30),X30)|(~v1_finset_1(X28)|~r1_tarski(X28,k2_zfmisc_1(X29,X30)))))&(r1_tarski(X28,k2_zfmisc_1(esk1_3(X28,X29,X30),esk2_3(X28,X29,X30)))|(~v1_finset_1(X28)|~r1_tarski(X28,k2_zfmisc_1(X29,X30))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_finset_1])])])])).
% 0.60/0.79  cnf(c_0_33, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.60/0.79  fof(c_0_34, negated_conjecture, ![X36]:((v1_finset_1(esk3_0)&r1_tarski(esk3_0,k2_zfmisc_1(esk4_0,esk5_0)))&(~v1_finset_1(X36)|~r1_tarski(X36,esk4_0)|~r1_tarski(esk3_0,k2_zfmisc_1(X36,esk5_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])])).
% 0.60/0.79  cnf(c_0_35, plain, (r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.60/0.79  cnf(c_0_36, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.60/0.79  cnf(c_0_37, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.60/0.79  cnf(c_0_38, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.60/0.79  cnf(c_0_39, plain, (v1_finset_1(k1_relat_1(X1))|~v1_finset_1(X2)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])])).
% 0.60/0.79  cnf(c_0_40, plain, (r1_tarski(X1,k2_zfmisc_1(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)))|~v1_finset_1(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.60/0.79  cnf(c_0_41, plain, (v1_finset_1(esk1_3(X1,X2,X3))|~v1_finset_1(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.60/0.79  cnf(c_0_42, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_relat_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_33, c_0_22])).
% 0.60/0.79  cnf(c_0_43, negated_conjecture, (r1_tarski(esk3_0,k2_zfmisc_1(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.60/0.79  cnf(c_0_44, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k2_relat_1(k2_zfmisc_1(X3,X2)))), inference(spm,[status(thm)],[c_0_33, c_0_35])).
% 0.60/0.79  cnf(c_0_45, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.60/0.79  cnf(c_0_46, plain, (r1_tarski(X1,k2_zfmisc_1(X2,X3))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.60/0.79  cnf(c_0_47, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_38])).
% 0.60/0.79  cnf(c_0_48, plain, (v1_finset_1(k1_relat_1(X1))|~v1_finset_1(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])).
% 0.60/0.79  cnf(c_0_49, negated_conjecture, (v1_finset_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.60/0.79  cnf(c_0_50, plain, (r1_tarski(k1_relat_1(X1),X2)|~v1_relat_1(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_20]), c_0_31])])).
% 0.60/0.79  cnf(c_0_51, negated_conjecture, (v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_43]), c_0_31])])).
% 0.60/0.79  cnf(c_0_52, plain, (r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~r1_tarski(X1,k2_zfmisc_1(X3,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_31])])).
% 0.60/0.79  cnf(c_0_53, negated_conjecture, (~v1_finset_1(X1)|~r1_tarski(X1,esk4_0)|~r1_tarski(esk3_0,k2_zfmisc_1(X1,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.60/0.79  cnf(c_0_54, plain, (r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),X2))|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.60/0.79  cnf(c_0_55, negated_conjecture, (v1_finset_1(k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_43]), c_0_49])])).
% 0.60/0.79  cnf(c_0_56, negated_conjecture, (r1_tarski(k1_relat_1(esk3_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_43]), c_0_51])])).
% 0.60/0.79  cnf(c_0_57, negated_conjecture, (r1_tarski(k2_relat_1(esk3_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_43]), c_0_51])])).
% 0.60/0.79  cnf(c_0_58, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55]), c_0_56]), c_0_51]), c_0_57])]), ['proof']).
% 0.60/0.79  # SZS output end CNFRefutation
% 0.60/0.79  # Proof object total steps             : 59
% 0.60/0.79  # Proof object clause steps            : 34
% 0.60/0.79  # Proof object formula steps           : 25
% 0.60/0.79  # Proof object conjectures             : 11
% 0.60/0.79  # Proof object clause conjectures      : 8
% 0.60/0.79  # Proof object formula conjectures     : 3
% 0.60/0.79  # Proof object initial clauses used    : 17
% 0.60/0.79  # Proof object initial formulas used   : 12
% 0.60/0.79  # Proof object generating inferences   : 16
% 0.60/0.79  # Proof object simplifying inferences  : 22
% 0.60/0.79  # Training examples: 0 positive, 0 negative
% 0.60/0.79  # Parsed axioms                        : 12
% 0.60/0.79  # Removed by relevancy pruning/SinE    : 0
% 0.60/0.79  # Initial clauses                      : 22
% 0.60/0.79  # Removed in clause preprocessing      : 0
% 0.60/0.79  # Initial clauses in saturation        : 22
% 0.60/0.79  # Processed clauses                    : 2514
% 0.60/0.79  # ...of these trivial                  : 27
% 0.60/0.79  # ...subsumed                          : 1409
% 0.60/0.79  # ...remaining for further processing  : 1078
% 0.60/0.79  # Other redundant clauses eliminated   : 2
% 0.60/0.79  # Clauses deleted for lack of memory   : 0
% 0.60/0.79  # Backward-subsumed                    : 92
% 0.60/0.79  # Backward-rewritten                   : 5
% 0.60/0.79  # Generated clauses                    : 17460
% 0.60/0.79  # ...of the previous two non-trivial   : 16304
% 0.60/0.79  # Contextual simplify-reflections      : 76
% 0.60/0.79  # Paramodulations                      : 17458
% 0.60/0.79  # Factorizations                       : 0
% 0.60/0.79  # Equation resolutions                 : 2
% 0.60/0.79  # Propositional unsat checks           : 0
% 0.60/0.79  #    Propositional check models        : 0
% 0.60/0.79  #    Propositional check unsatisfiable : 0
% 0.60/0.79  #    Propositional clauses             : 0
% 0.60/0.79  #    Propositional clauses after purity: 0
% 0.60/0.79  #    Propositional unsat core size     : 0
% 0.60/0.79  #    Propositional preprocessing time  : 0.000
% 0.60/0.79  #    Propositional encoding time       : 0.000
% 0.60/0.79  #    Propositional solver time         : 0.000
% 0.60/0.79  #    Success case prop preproc time    : 0.000
% 0.60/0.79  #    Success case prop encoding time   : 0.000
% 0.60/0.79  #    Success case prop solver time     : 0.000
% 0.60/0.79  # Current number of processed clauses  : 958
% 0.60/0.79  #    Positive orientable unit clauses  : 92
% 0.60/0.79  #    Positive unorientable unit clauses: 0
% 0.60/0.79  #    Negative unit clauses             : 1
% 0.60/0.79  #    Non-unit-clauses                  : 865
% 0.60/0.79  # Current number of unprocessed clauses: 13735
% 0.60/0.79  # ...number of literals in the above   : 53304
% 0.60/0.79  # Current number of archived formulas  : 0
% 0.60/0.79  # Current number of archived clauses   : 118
% 0.60/0.79  # Clause-clause subsumption calls (NU) : 76595
% 0.60/0.79  # Rec. Clause-clause subsumption calls : 51683
% 0.60/0.79  # Non-unit clause-clause subsumptions  : 1505
% 0.60/0.79  # Unit Clause-clause subsumption calls : 154
% 0.60/0.79  # Rewrite failures with RHS unbound    : 0
% 0.60/0.79  # BW rewrite match attempts            : 222
% 0.60/0.79  # BW rewrite match successes           : 6
% 0.60/0.79  # Condensation attempts                : 0
% 0.60/0.79  # Condensation successes               : 0
% 0.60/0.79  # Termbank termtop insertions          : 308559
% 0.60/0.79  
% 0.60/0.79  # -------------------------------------------------
% 0.60/0.79  # User time                : 0.447 s
% 0.60/0.79  # System time              : 0.028 s
% 0.60/0.79  # Total time               : 0.476 s
% 0.60/0.79  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
