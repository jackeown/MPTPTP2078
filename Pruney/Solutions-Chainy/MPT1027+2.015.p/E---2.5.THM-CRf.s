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
% DateTime   : Thu Dec  3 11:06:48 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 531 expanded)
%              Number of clauses        :   47 ( 212 expanded)
%              Number of leaves         :   17 ( 132 expanded)
%              Depth                    :   14
%              Number of atoms          :  242 (2072 expanded)
%              Number of equality atoms :   78 ( 541 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t130_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( k1_relset_1(X1,X2,X3) = X1
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_funct_2)).

fof(t118_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(X2,k1_relat_1(X3)) )
       => k9_relat_1(X3,k2_tarski(X1,X2)) = k2_tarski(k1_funct_1(X3,X1),k1_funct_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_funct_1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(fc1_grfunc_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => v1_funct_1(k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_grfunc_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(fc8_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k7_relat_1(X1,X2))
        & v1_funct_1(k7_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

fof(t110_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(t150_relat_1,axiom,(
    ! [X1] : k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

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

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(t6_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
     => ~ ( r2_hidden(X1,X4)
          & ! [X5,X6] :
              ~ ( X1 = k4_tarski(X5,X6)
                & r2_hidden(X5,X2)
                & r2_hidden(X6,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(t10_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ~ ( X2 != k1_xboole_0
          & ! [X3] :
              ( m1_subset_1(X3,X1)
             => ~ r2_hidden(X3,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( k1_relset_1(X1,X2,X3) = X1
         => ( v1_funct_1(X3)
            & v1_funct_2(X3,X1,X2)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t130_funct_2])).

fof(c_0_18,plain,(
    ! [X21,X22,X23] :
      ( ~ v1_relat_1(X23)
      | ~ v1_funct_1(X23)
      | ~ r2_hidden(X21,k1_relat_1(X23))
      | ~ r2_hidden(X22,k1_relat_1(X23))
      | k9_relat_1(X23,k2_tarski(X21,X22)) = k2_tarski(k1_funct_1(X23,X21),k1_funct_1(X23,X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_funct_1])])).

fof(c_0_19,plain,(
    ! [X8,X9] : k2_tarski(X8,X9) = k2_xboole_0(k1_tarski(X8),k1_tarski(X9)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_20,plain,(
    ! [X42,X43] :
      ( ~ v1_relat_1(X42)
      | ~ v1_funct_1(X42)
      | v1_funct_1(k3_xboole_0(X42,X43)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_grfunc_1])])).

fof(c_0_21,plain,(
    ! [X7] : k3_xboole_0(X7,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_22,plain,(
    ! [X27,X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | v1_relat_1(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_23,negated_conjecture,
    ( v1_funct_1(esk6_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
    & k1_relset_1(esk4_0,esk5_0,esk6_0) = esk4_0
    & ( ~ v1_funct_1(esk6_0)
      | ~ v1_funct_2(esk6_0,esk4_0,esk5_0)
      | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_24,plain,(
    ! [X19,X20] :
      ( ( v1_relat_1(k7_relat_1(X19,X20))
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( v1_funct_1(k7_relat_1(X19,X20))
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).

fof(c_0_25,plain,(
    ! [X17] :
      ( ~ v1_relat_1(X17)
      | k7_relat_1(X17,k1_xboole_0) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t110_relat_1])])).

fof(c_0_26,plain,(
    ! [X12,X13] : k2_xboole_0(k1_tarski(X12),X13) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

cnf(c_0_27,plain,
    ( k9_relat_1(X1,k2_tarski(X2,X3)) = k2_tarski(k1_funct_1(X1,X2),k1_funct_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( v1_funct_1(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( k7_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( k9_relat_1(X1,k2_xboole_0(k1_tarski(X2),k1_tarski(X3))) = k2_xboole_0(k1_tarski(k1_funct_1(X1,X2)),k1_tarski(k1_funct_1(X1,X3)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_28])).

fof(c_0_37,plain,(
    ! [X18] : k9_relat_1(k1_xboole_0,X18) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t150_relat_1])).

cnf(c_0_38,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_41,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_42,plain,(
    ! [X10,X11] :
      ( ( k2_zfmisc_1(X10,X11) != k1_xboole_0
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0 )
      & ( X10 != k1_xboole_0
        | k2_zfmisc_1(X10,X11) = k1_xboole_0 )
      & ( X11 != k1_xboole_0
        | k2_zfmisc_1(X10,X11) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_43,plain,(
    ! [X39,X40,X41] :
      ( ( ~ v1_funct_2(X41,X39,X40)
        | X39 = k1_relset_1(X39,X40,X41)
        | X40 = k1_xboole_0
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( X39 != k1_relset_1(X39,X40,X41)
        | v1_funct_2(X41,X39,X40)
        | X40 = k1_xboole_0
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( ~ v1_funct_2(X41,X39,X40)
        | X39 = k1_relset_1(X39,X40,X41)
        | X39 != k1_xboole_0
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( X39 != k1_relset_1(X39,X40,X41)
        | v1_funct_2(X41,X39,X40)
        | X39 != k1_xboole_0
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( ~ v1_funct_2(X41,X39,X40)
        | X41 = k1_xboole_0
        | X39 = k1_xboole_0
        | X40 != k1_xboole_0
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( X41 != k1_xboole_0
        | v1_funct_2(X41,X39,X40)
        | X39 = k1_xboole_0
        | X40 != k1_xboole_0
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_44,negated_conjecture,
    ( ~ v1_funct_1(esk6_0)
    | ~ v1_funct_2(esk6_0,esk4_0,esk5_0)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_45,plain,
    ( k9_relat_1(X1,k2_xboole_0(k1_tarski(X2),k1_tarski(X3))) != k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_46,plain,
    ( k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( v1_funct_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])])).

cnf(c_0_48,negated_conjecture,
    ( v1_relat_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_40]),c_0_39])])).

cnf(c_0_49,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

fof(c_0_50,plain,(
    ! [X33,X34,X35,X36] :
      ( ( X33 = k4_tarski(esk2_4(X33,X34,X35,X36),esk3_4(X33,X34,X35,X36))
        | ~ r2_hidden(X33,X36)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( r2_hidden(esk2_4(X33,X34,X35,X36),X34)
        | ~ r2_hidden(X33,X36)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( r2_hidden(esk3_4(X33,X34,X35,X36),X35)
        | ~ r2_hidden(X33,X36)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_relset_1])])])])).

cnf(c_0_51,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,negated_conjecture,
    ( k1_relset_1(esk4_0,esk5_0,esk6_0) = esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_54,negated_conjecture,
    ( ~ v1_funct_2(esk6_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_40]),c_0_32])])).

cnf(c_0_55,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_49])])).

cnf(c_0_56,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X3)
    | ~ r2_hidden(X1,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_57,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_32]),c_0_53])]),c_0_54])).

fof(c_0_59,plain,(
    ! [X30,X31,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      | k1_relset_1(X30,X31,X32) = k1_relat_1(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_60,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_58]),c_0_57])).

fof(c_0_62,plain,(
    ! [X44] :
      ( ( v1_funct_1(X44)
        | ~ v1_relat_1(X44)
        | ~ v1_funct_1(X44) )
      & ( v1_funct_2(X44,k1_relat_1(X44),k2_relat_1(X44))
        | ~ v1_relat_1(X44)
        | ~ v1_funct_1(X44) )
      & ( m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X44),k2_relat_1(X44))))
        | ~ v1_relat_1(X44)
        | ~ v1_funct_1(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

cnf(c_0_63,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X2,esk6_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

fof(c_0_65,plain,(
    ! [X14,X15] :
      ( ( m1_subset_1(esk1_2(X14,X15),X14)
        | X15 = k1_xboole_0
        | ~ m1_subset_1(X15,k1_zfmisc_1(X14)) )
      & ( r2_hidden(esk1_2(X14,X15),X15)
        | X15 = k1_xboole_0
        | ~ m1_subset_1(X15,k1_zfmisc_1(X14)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_subset_1])])])])])).

cnf(c_0_66,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_63]),c_0_32])])).

cnf(c_0_68,negated_conjecture,
    ( ~ r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_56]),c_0_57])).

cnf(c_0_69,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | X2 = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_relat_1(esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_40]),c_0_39])])).

cnf(c_0_71,negated_conjecture,
    ( ~ r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X2,esk6_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_61])).

cnf(c_0_72,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk1_2(k2_zfmisc_1(esk4_0,k2_relat_1(esk6_0)),esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_73,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_74,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_73,c_0_72])).

cnf(c_0_75,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_76,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_77,negated_conjecture,
    ( ~ v1_funct_2(esk6_0,esk4_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_54,c_0_58])).

cnf(c_0_78,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_74]),c_0_49])).

cnf(c_0_79,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_49]),c_0_47])]),c_0_48])])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_74]),c_0_78]),c_0_79])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 21:19:15 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.36  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.020 s
% 0.12/0.36  # Presaturation interreduction done
% 0.12/0.36  
% 0.12/0.36  # Proof found!
% 0.12/0.36  # SZS status Theorem
% 0.12/0.36  # SZS output start CNFRefutation
% 0.12/0.36  fof(t130_funct_2, conjecture, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(k1_relset_1(X1,X2,X3)=X1=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_funct_2)).
% 0.12/0.36  fof(t118_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r2_hidden(X1,k1_relat_1(X3))&r2_hidden(X2,k1_relat_1(X3)))=>k9_relat_1(X3,k2_tarski(X1,X2))=k2_tarski(k1_funct_1(X3,X1),k1_funct_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_funct_1)).
% 0.12/0.36  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 0.12/0.36  fof(fc1_grfunc_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_funct_1(X1))=>v1_funct_1(k3_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_grfunc_1)).
% 0.12/0.36  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.12/0.36  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.12/0.36  fof(fc8_funct_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k7_relat_1(X1,X2))&v1_funct_1(k7_relat_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 0.12/0.36  fof(t110_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_relat_1)).
% 0.12/0.36  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.12/0.36  fof(t150_relat_1, axiom, ![X1]:k9_relat_1(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 0.12/0.36  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.12/0.36  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.12/0.36  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.12/0.36  fof(t6_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))=>~((r2_hidden(X1,X4)&![X5, X6]:~(((X1=k4_tarski(X5,X6)&r2_hidden(X5,X2))&r2_hidden(X6,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_relset_1)).
% 0.12/0.36  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.12/0.36  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 0.12/0.36  fof(t10_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>~((X2!=k1_xboole_0&![X3]:(m1_subset_1(X3,X1)=>~(r2_hidden(X3,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_subset_1)).
% 0.12/0.36  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(k1_relset_1(X1,X2,X3)=X1=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))))), inference(assume_negation,[status(cth)],[t130_funct_2])).
% 0.12/0.36  fof(c_0_18, plain, ![X21, X22, X23]:(~v1_relat_1(X23)|~v1_funct_1(X23)|(~r2_hidden(X21,k1_relat_1(X23))|~r2_hidden(X22,k1_relat_1(X23))|k9_relat_1(X23,k2_tarski(X21,X22))=k2_tarski(k1_funct_1(X23,X21),k1_funct_1(X23,X22)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_funct_1])])).
% 0.12/0.36  fof(c_0_19, plain, ![X8, X9]:k2_tarski(X8,X9)=k2_xboole_0(k1_tarski(X8),k1_tarski(X9)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.12/0.36  fof(c_0_20, plain, ![X42, X43]:(~v1_relat_1(X42)|~v1_funct_1(X42)|v1_funct_1(k3_xboole_0(X42,X43))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_grfunc_1])])).
% 0.12/0.36  fof(c_0_21, plain, ![X7]:k3_xboole_0(X7,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.12/0.36  fof(c_0_22, plain, ![X27, X28, X29]:(~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|v1_relat_1(X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.12/0.36  fof(c_0_23, negated_conjecture, ((v1_funct_1(esk6_0)&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))))&(k1_relset_1(esk4_0,esk5_0,esk6_0)=esk4_0&(~v1_funct_1(esk6_0)|~v1_funct_2(esk6_0,esk4_0,esk5_0)|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.12/0.36  fof(c_0_24, plain, ![X19, X20]:((v1_relat_1(k7_relat_1(X19,X20))|(~v1_relat_1(X19)|~v1_funct_1(X19)))&(v1_funct_1(k7_relat_1(X19,X20))|(~v1_relat_1(X19)|~v1_funct_1(X19)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).
% 0.12/0.36  fof(c_0_25, plain, ![X17]:(~v1_relat_1(X17)|k7_relat_1(X17,k1_xboole_0)=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t110_relat_1])])).
% 0.12/0.36  fof(c_0_26, plain, ![X12, X13]:k2_xboole_0(k1_tarski(X12),X13)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 0.12/0.36  cnf(c_0_27, plain, (k9_relat_1(X1,k2_tarski(X2,X3))=k2_tarski(k1_funct_1(X1,X2),k1_funct_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.36  cnf(c_0_28, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.36  cnf(c_0_29, plain, (v1_funct_1(k3_xboole_0(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.36  cnf(c_0_30, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.36  cnf(c_0_31, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.36  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.36  cnf(c_0_33, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.36  cnf(c_0_34, plain, (k7_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.36  cnf(c_0_35, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.36  cnf(c_0_36, plain, (k9_relat_1(X1,k2_xboole_0(k1_tarski(X2),k1_tarski(X3)))=k2_xboole_0(k1_tarski(k1_funct_1(X1,X2)),k1_tarski(k1_funct_1(X1,X3)))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X3,k1_relat_1(X1))|~r2_hidden(X2,k1_relat_1(X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28]), c_0_28])).
% 0.12/0.36  fof(c_0_37, plain, ![X18]:k9_relat_1(k1_xboole_0,X18)=k1_xboole_0, inference(variable_rename,[status(thm)],[t150_relat_1])).
% 0.12/0.36  cnf(c_0_38, plain, (v1_funct_1(k1_xboole_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.12/0.36  cnf(c_0_39, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.12/0.36  cnf(c_0_40, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.36  cnf(c_0_41, plain, (v1_relat_1(k1_xboole_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.12/0.36  fof(c_0_42, plain, ![X10, X11]:((k2_zfmisc_1(X10,X11)!=k1_xboole_0|(X10=k1_xboole_0|X11=k1_xboole_0))&((X10!=k1_xboole_0|k2_zfmisc_1(X10,X11)=k1_xboole_0)&(X11!=k1_xboole_0|k2_zfmisc_1(X10,X11)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.12/0.36  fof(c_0_43, plain, ![X39, X40, X41]:((((~v1_funct_2(X41,X39,X40)|X39=k1_relset_1(X39,X40,X41)|X40=k1_xboole_0|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))&(X39!=k1_relset_1(X39,X40,X41)|v1_funct_2(X41,X39,X40)|X40=k1_xboole_0|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))))&((~v1_funct_2(X41,X39,X40)|X39=k1_relset_1(X39,X40,X41)|X39!=k1_xboole_0|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))&(X39!=k1_relset_1(X39,X40,X41)|v1_funct_2(X41,X39,X40)|X39!=k1_xboole_0|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))))&((~v1_funct_2(X41,X39,X40)|X41=k1_xboole_0|X39=k1_xboole_0|X40!=k1_xboole_0|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))&(X41!=k1_xboole_0|v1_funct_2(X41,X39,X40)|X39=k1_xboole_0|X40!=k1_xboole_0|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.12/0.36  cnf(c_0_44, negated_conjecture, (~v1_funct_1(esk6_0)|~v1_funct_2(esk6_0,esk4_0,esk5_0)|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.36  cnf(c_0_45, plain, (k9_relat_1(X1,k2_xboole_0(k1_tarski(X2),k1_tarski(X3)))!=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X3,k1_relat_1(X1))|~r2_hidden(X2,k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.12/0.36  cnf(c_0_46, plain, (k9_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.12/0.36  cnf(c_0_47, negated_conjecture, (v1_funct_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])])).
% 0.12/0.36  cnf(c_0_48, negated_conjecture, (v1_relat_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_40]), c_0_39])])).
% 0.12/0.36  cnf(c_0_49, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.12/0.36  fof(c_0_50, plain, ![X33, X34, X35, X36]:(((X33=k4_tarski(esk2_4(X33,X34,X35,X36),esk3_4(X33,X34,X35,X36))|~r2_hidden(X33,X36)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))&(r2_hidden(esk2_4(X33,X34,X35,X36),X34)|~r2_hidden(X33,X36)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))))&(r2_hidden(esk3_4(X33,X34,X35,X36),X35)|~r2_hidden(X33,X36)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_relset_1])])])])).
% 0.12/0.36  cnf(c_0_51, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.12/0.36  cnf(c_0_52, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.12/0.36  cnf(c_0_53, negated_conjecture, (k1_relset_1(esk4_0,esk5_0,esk6_0)=esk4_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.36  cnf(c_0_54, negated_conjecture, (~v1_funct_2(esk6_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_40]), c_0_32])])).
% 0.12/0.36  cnf(c_0_55, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X2,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47]), c_0_48]), c_0_49]), c_0_49])])).
% 0.12/0.36  cnf(c_0_56, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X3)|~r2_hidden(X1,X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.12/0.36  cnf(c_0_57, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_51])).
% 0.12/0.36  cnf(c_0_58, negated_conjecture, (esk5_0=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_32]), c_0_53])]), c_0_54])).
% 0.12/0.36  fof(c_0_59, plain, ![X30, X31, X32]:(~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|k1_relset_1(X30,X31,X32)=k1_relat_1(X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.12/0.36  cnf(c_0_60, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])).
% 0.12/0.36  cnf(c_0_61, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_58]), c_0_57])).
% 0.12/0.36  fof(c_0_62, plain, ![X44]:(((v1_funct_1(X44)|(~v1_relat_1(X44)|~v1_funct_1(X44)))&(v1_funct_2(X44,k1_relat_1(X44),k2_relat_1(X44))|(~v1_relat_1(X44)|~v1_funct_1(X44))))&(m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X44),k2_relat_1(X44))))|(~v1_relat_1(X44)|~v1_funct_1(X44)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.12/0.36  cnf(c_0_63, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.12/0.36  cnf(c_0_64, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X2,esk6_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.12/0.36  fof(c_0_65, plain, ![X14, X15]:((m1_subset_1(esk1_2(X14,X15),X14)|X15=k1_xboole_0|~m1_subset_1(X15,k1_zfmisc_1(X14)))&(r2_hidden(esk1_2(X14,X15),X15)|X15=k1_xboole_0|~m1_subset_1(X15,k1_zfmisc_1(X14)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_subset_1])])])])])).
% 0.12/0.36  cnf(c_0_66, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.12/0.36  cnf(c_0_67, negated_conjecture, (k1_relat_1(esk6_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_63]), c_0_32])])).
% 0.12/0.36  cnf(c_0_68, negated_conjecture, (~r2_hidden(X1,esk6_0)|~r2_hidden(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_56]), c_0_57])).
% 0.12/0.36  cnf(c_0_69, plain, (r2_hidden(esk1_2(X1,X2),X2)|X2=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.12/0.36  cnf(c_0_70, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_relat_1(esk6_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_40]), c_0_39])])).
% 0.12/0.36  cnf(c_0_71, negated_conjecture, (~r2_hidden(X1,esk6_0)|~r2_hidden(X2,esk6_0)), inference(spm,[status(thm)],[c_0_68, c_0_61])).
% 0.12/0.36  cnf(c_0_72, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk1_2(k2_zfmisc_1(esk4_0,k2_relat_1(esk6_0)),esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.12/0.36  cnf(c_0_73, negated_conjecture, (esk6_0=k1_xboole_0|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.12/0.36  cnf(c_0_74, negated_conjecture, (esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_73, c_0_72])).
% 0.12/0.36  cnf(c_0_75, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.12/0.36  cnf(c_0_76, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.12/0.36  cnf(c_0_77, negated_conjecture, (~v1_funct_2(esk6_0,esk4_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_54, c_0_58])).
% 0.12/0.36  cnf(c_0_78, negated_conjecture, (esk4_0=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_74]), c_0_49])).
% 0.12/0.36  cnf(c_0_79, plain, (v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_49]), c_0_47])]), c_0_48])])).
% 0.12/0.36  cnf(c_0_80, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_74]), c_0_78]), c_0_79])]), ['proof']).
% 0.12/0.36  # SZS output end CNFRefutation
% 0.12/0.36  # Proof object total steps             : 81
% 0.12/0.36  # Proof object clause steps            : 47
% 0.12/0.36  # Proof object formula steps           : 34
% 0.12/0.36  # Proof object conjectures             : 24
% 0.12/0.36  # Proof object clause conjectures      : 21
% 0.12/0.36  # Proof object formula conjectures     : 3
% 0.12/0.36  # Proof object initial clauses used    : 22
% 0.12/0.36  # Proof object initial formulas used   : 17
% 0.12/0.36  # Proof object generating inferences   : 18
% 0.12/0.36  # Proof object simplifying inferences  : 39
% 0.12/0.36  # Training examples: 0 positive, 0 negative
% 0.12/0.36  # Parsed axioms                        : 18
% 0.12/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.36  # Initial clauses                      : 37
% 0.12/0.36  # Removed in clause preprocessing      : 2
% 0.12/0.36  # Initial clauses in saturation        : 35
% 0.12/0.36  # Processed clauses                    : 115
% 0.12/0.36  # ...of these trivial                  : 3
% 0.12/0.36  # ...subsumed                          : 6
% 0.12/0.36  # ...remaining for further processing  : 105
% 0.12/0.36  # Other redundant clauses eliminated   : 8
% 0.12/0.36  # Clauses deleted for lack of memory   : 0
% 0.12/0.36  # Backward-subsumed                    : 0
% 0.12/0.36  # Backward-rewritten                   : 22
% 0.12/0.36  # Generated clauses                    : 74
% 0.12/0.36  # ...of the previous two non-trivial   : 76
% 0.12/0.36  # Contextual simplify-reflections      : 0
% 0.12/0.36  # Paramodulations                      : 67
% 0.12/0.36  # Factorizations                       : 0
% 0.12/0.36  # Equation resolutions                 : 8
% 0.12/0.36  # Propositional unsat checks           : 0
% 0.12/0.36  #    Propositional check models        : 0
% 0.12/0.36  #    Propositional check unsatisfiable : 0
% 0.12/0.36  #    Propositional clauses             : 0
% 0.12/0.36  #    Propositional clauses after purity: 0
% 0.12/0.36  #    Propositional unsat core size     : 0
% 0.12/0.36  #    Propositional preprocessing time  : 0.000
% 0.12/0.36  #    Propositional encoding time       : 0.000
% 0.12/0.36  #    Propositional solver time         : 0.000
% 0.12/0.36  #    Success case prop preproc time    : 0.000
% 0.12/0.36  #    Success case prop encoding time   : 0.000
% 0.12/0.36  #    Success case prop solver time     : 0.000
% 0.12/0.36  # Current number of processed clauses  : 41
% 0.12/0.36  #    Positive orientable unit clauses  : 13
% 0.12/0.36  #    Positive unorientable unit clauses: 0
% 0.12/0.36  #    Negative unit clauses             : 1
% 0.12/0.36  #    Non-unit-clauses                  : 27
% 0.12/0.36  # Current number of unprocessed clauses: 28
% 0.12/0.36  # ...number of literals in the above   : 96
% 0.12/0.36  # Current number of archived formulas  : 0
% 0.12/0.36  # Current number of archived clauses   : 58
% 0.12/0.36  # Clause-clause subsumption calls (NU) : 326
% 0.12/0.36  # Rec. Clause-clause subsumption calls : 163
% 0.12/0.36  # Non-unit clause-clause subsumptions  : 6
% 0.12/0.36  # Unit Clause-clause subsumption calls : 5
% 0.12/0.36  # Rewrite failures with RHS unbound    : 0
% 0.12/0.36  # BW rewrite match attempts            : 5
% 0.12/0.36  # BW rewrite match successes           : 4
% 0.12/0.36  # Condensation attempts                : 0
% 0.12/0.36  # Condensation successes               : 0
% 0.12/0.36  # Termbank termtop insertions          : 3869
% 0.12/0.36  
% 0.12/0.36  # -------------------------------------------------
% 0.12/0.36  # User time                : 0.025 s
% 0.12/0.36  # System time              : 0.003 s
% 0.12/0.36  # Total time               : 0.028 s
% 0.12/0.36  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
