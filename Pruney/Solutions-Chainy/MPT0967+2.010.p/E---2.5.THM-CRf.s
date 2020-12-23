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
% DateTime   : Thu Dec  3 11:01:22 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 503 expanded)
%              Number of clauses        :   77 ( 228 expanded)
%              Number of leaves         :   16 ( 121 expanded)
%              Depth                    :   16
%              Number of atoms          :  298 (2128 expanded)
%              Number of equality atoms :   90 ( 623 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t9_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r1_tarski(X2,X3)
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(dt_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t14_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
     => ( r1_tarski(k2_relat_1(X4),X2)
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( r1_tarski(X2,X3)
         => ( ( X2 = k1_xboole_0
              & X1 != k1_xboole_0 )
            | ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t9_funct_2])).

fof(c_0_17,plain,(
    ! [X23,X24] :
      ( ( ~ m1_subset_1(X23,k1_zfmisc_1(X24))
        | r1_tarski(X23,X24) )
      & ( ~ r1_tarski(X23,X24)
        | m1_subset_1(X23,k1_zfmisc_1(X24)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_18,negated_conjecture,
    ( v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk3_0,esk4_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    & r1_tarski(esk4_0,esk5_0)
    & ( esk4_0 != k1_xboole_0
      | esk3_0 = k1_xboole_0 )
    & ( ~ v1_funct_1(esk6_0)
      | ~ v1_funct_2(esk6_0,esk3_0,esk5_0)
      | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk5_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_19,plain,(
    ! [X36,X37,X38] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
      | k1_relset_1(X36,X37,X38) = k1_relat_1(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_20,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_21,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X21,X22] :
      ( ( k2_zfmisc_1(X21,X22) != k1_xboole_0
        | X21 = k1_xboole_0
        | X22 = k1_xboole_0 )
      & ( X21 != k1_xboole_0
        | k2_zfmisc_1(X21,X22) = k1_xboole_0 )
      & ( X22 != k1_xboole_0
        | k2_zfmisc_1(X21,X22) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_25,plain,(
    ! [X33,X34,X35] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | m1_subset_1(k1_relset_1(X33,X34,X35),k1_zfmisc_1(X33)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).

cnf(c_0_26,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_27,plain,(
    ! [X17,X18,X19] :
      ( ~ r1_tarski(X17,X18)
      | ~ r1_tarski(X18,X19)
      | r1_tarski(X17,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_28,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(esk6_0,k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_32,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( k1_relset_1(esk3_0,esk4_0,esk6_0) = k1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_23])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(esk6_0,k2_zfmisc_1(k1_xboole_0,esk4_0))
    | esk4_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_32])).

fof(c_0_39,plain,(
    ! [X15,X16] :
      ( ( r1_tarski(X15,X16)
        | X15 != X16 )
      & ( r1_tarski(X16,X15)
        | X15 != X16 )
      & ( ~ r1_tarski(X15,X16)
        | ~ r1_tarski(X16,X15)
        | X15 = X16 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(k1_relat_1(esk6_0),k1_zfmisc_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_23])])).

cnf(c_0_41,negated_conjecture,
    ( ~ v1_funct_1(esk6_0)
    | ~ v1_funct_2(esk6_0,esk3_0,esk5_0)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_43,plain,(
    ! [X43,X44,X45] :
      ( ( ~ v1_funct_2(X45,X43,X44)
        | X43 = k1_relset_1(X43,X44,X45)
        | X44 = k1_xboole_0
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) )
      & ( X43 != k1_relset_1(X43,X44,X45)
        | v1_funct_2(X45,X43,X44)
        | X44 = k1_xboole_0
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) )
      & ( ~ v1_funct_2(X45,X43,X44)
        | X43 = k1_relset_1(X43,X44,X45)
        | X43 != k1_xboole_0
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) )
      & ( X43 != k1_relset_1(X43,X44,X45)
        | v1_funct_2(X45,X43,X44)
        | X43 != k1_xboole_0
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) )
      & ( ~ v1_funct_2(X45,X43,X44)
        | X45 = k1_xboole_0
        | X43 = k1_xboole_0
        | X44 != k1_xboole_0
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) )
      & ( X45 != k1_xboole_0
        | v1_funct_2(X45,X43,X44)
        | X43 = k1_xboole_0
        | X44 != k1_xboole_0
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_44,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(esk6_0,k1_xboole_0)
    | esk4_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_47,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_48,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk6_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( ~ v1_funct_2(esk6_0,esk3_0,esk5_0)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42])])).

cnf(c_0_51,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,plain,
    ( k1_relset_1(X1,X2,X3) = k1_relat_1(X3)
    | ~ r1_tarski(X3,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(esk6_0,X1)
    | esk4_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])])).

cnf(c_0_54,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_36])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk6_0),k1_xboole_0)
    | esk4_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_31])).

cnf(c_0_56,negated_conjecture,
    ( ~ v1_funct_2(esk6_0,esk3_0,esk5_0)
    | ~ r1_tarski(esk6_0,k2_zfmisc_1(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_44])).

cnf(c_0_57,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | k1_relset_1(k1_xboole_0,X2,X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_51]),c_0_38])).

cnf(c_0_58,negated_conjecture,
    ( k1_relset_1(X1,X2,esk6_0) = k1_relat_1(esk6_0)
    | esk4_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k1_xboole_0))
    | esk4_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_31]),c_0_38])).

cnf(c_0_60,negated_conjecture,
    ( k1_relat_1(esk6_0) = k1_xboole_0
    | esk4_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_47])])).

fof(c_0_61,plain,(
    ! [X27,X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | v1_relat_1(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_62,plain,(
    ! [X39,X40,X41,X42] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X41,X39)))
      | ~ r1_tarski(k2_relat_1(X42),X40)
      | m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X41,X40))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_relset_1])])).

cnf(c_0_63,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_64,negated_conjecture,
    ( v1_funct_2(esk6_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_65,negated_conjecture,
    ( esk4_0 != k1_xboole_0
    | ~ v1_funct_2(esk6_0,k1_xboole_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_31]),c_0_38]),c_0_46])).

cnf(c_0_66,negated_conjecture,
    ( v1_funct_2(esk6_0,k1_xboole_0,X1)
    | esk4_0 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59]),c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_68,plain,(
    ! [X30,X31,X32] :
      ( ( v4_relat_1(X32,X30)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( v5_relat_1(X32,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_69,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_70,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_71,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(k2_relat_1(X1),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_72,negated_conjecture,
    ( k1_relset_1(esk3_0,esk4_0,esk6_0) = esk3_0
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_23]),c_0_64])])).

cnf(c_0_73,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_67])).

fof(c_0_75,plain,(
    ! [X25,X26] :
      ( ( ~ v5_relat_1(X26,X25)
        | r1_tarski(k2_relat_1(X26),X25)
        | ~ v1_relat_1(X26) )
      & ( ~ r1_tarski(k2_relat_1(X26),X25)
        | v5_relat_1(X26,X25)
        | ~ v1_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_76,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

fof(c_0_77,plain,(
    ! [X20] :
      ( ~ r1_tarski(X20,k1_xboole_0)
      | X20 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_78,plain,
    ( v1_relat_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_44])).

cnf(c_0_79,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_70])).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))
    | ~ r1_tarski(k2_relat_1(esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_23])).

cnf(c_0_81,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[c_0_72,c_0_73]),c_0_34])).

cnf(c_0_82,negated_conjecture,
    ( X1 = esk4_0
    | ~ r1_tarski(X1,esk4_0)
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_74])).

cnf(c_0_83,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_84,plain,
    ( v5_relat_1(X1,X2)
    | ~ r1_tarski(X1,k2_zfmisc_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_44])).

cnf(c_0_85,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_86,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_87,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_88,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_89,negated_conjecture,
    ( k1_relset_1(esk3_0,X1,esk6_0) = esk3_0
    | ~ r1_tarski(k2_relat_1(esk6_0),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_80]),c_0_81])).

cnf(c_0_90,negated_conjecture,
    ( v5_relat_1(esk6_0,X1)
    | ~ r1_tarski(k2_relat_1(esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_80])).

cnf(c_0_91,negated_conjecture,
    ( r1_tarski(X1,esk5_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_67])).

cnf(c_0_92,negated_conjecture,
    ( k2_relat_1(X1) = esk4_0
    | ~ v5_relat_1(X1,esk4_0)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_93,plain,
    ( v5_relat_1(k2_zfmisc_1(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_84,c_0_79])).

cnf(c_0_94,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | ~ v5_relat_1(X1,k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_85,c_0_83])).

cnf(c_0_95,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_86])).

cnf(c_0_96,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_38])).

cnf(c_0_97,negated_conjecture,
    ( ~ v1_funct_2(esk6_0,esk3_0,esk5_0)
    | ~ r1_tarski(k2_relat_1(esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_80])).

cnf(c_0_98,negated_conjecture,
    ( X1 = k1_xboole_0
    | v1_funct_2(esk6_0,esk3_0,X1)
    | ~ r1_tarski(k2_relat_1(esk6_0),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_80]),c_0_89])).

cnf(c_0_99,negated_conjecture,
    ( v5_relat_1(esk6_0,esk5_0)
    | ~ r1_tarski(k2_relat_1(esk6_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_100,negated_conjecture,
    ( v5_relat_1(esk6_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_23])).

cnf(c_0_101,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_23])).

cnf(c_0_102,negated_conjecture,
    ( k2_relat_1(k2_zfmisc_1(X1,esk4_0)) = esk4_0
    | ~ v1_xboole_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_87])])).

cnf(c_0_103,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_93]),c_0_95]),c_0_95]),c_0_96])])).

cnf(c_0_104,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | ~ r1_tarski(k2_relat_1(esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_105,negated_conjecture,
    ( v5_relat_1(esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_83]),c_0_100]),c_0_101])])).

cnf(c_0_106,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_38]),c_0_103]),c_0_73])).

cnf(c_0_107,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_83]),c_0_105]),c_0_101])])).

cnf(c_0_108,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106,c_0_107]),c_0_47])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:37:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.44  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.19/0.44  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.44  #
% 0.19/0.44  # Preprocessing time       : 0.028 s
% 0.19/0.44  
% 0.19/0.44  # Proof found!
% 0.19/0.44  # SZS status Theorem
% 0.19/0.44  # SZS output start CNFRefutation
% 0.19/0.44  fof(t9_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X2,X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_2)).
% 0.19/0.44  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.44  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.44  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.44  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.44  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.44  fof(dt_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 0.19/0.44  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.19/0.44  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.44  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.19/0.44  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.44  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.44  fof(t14_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>(r1_tarski(k2_relat_1(X4),X2)=>m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relset_1)).
% 0.19/0.44  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.44  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 0.19/0.44  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.19/0.44  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X2,X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))))))), inference(assume_negation,[status(cth)],[t9_funct_2])).
% 0.19/0.44  fof(c_0_17, plain, ![X23, X24]:((~m1_subset_1(X23,k1_zfmisc_1(X24))|r1_tarski(X23,X24))&(~r1_tarski(X23,X24)|m1_subset_1(X23,k1_zfmisc_1(X24)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.44  fof(c_0_18, negated_conjecture, (((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk3_0,esk4_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))))&(r1_tarski(esk4_0,esk5_0)&((esk4_0!=k1_xboole_0|esk3_0=k1_xboole_0)&(~v1_funct_1(esk6_0)|~v1_funct_2(esk6_0,esk3_0,esk5_0)|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk5_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.19/0.44  fof(c_0_19, plain, ![X36, X37, X38]:(~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))|k1_relset_1(X36,X37,X38)=k1_relat_1(X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.44  fof(c_0_20, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.44  fof(c_0_21, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.44  cnf(c_0_22, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.44  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.44  fof(c_0_24, plain, ![X21, X22]:((k2_zfmisc_1(X21,X22)!=k1_xboole_0|(X21=k1_xboole_0|X22=k1_xboole_0))&((X21!=k1_xboole_0|k2_zfmisc_1(X21,X22)=k1_xboole_0)&(X22!=k1_xboole_0|k2_zfmisc_1(X21,X22)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.19/0.44  fof(c_0_25, plain, ![X33, X34, X35]:(~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|m1_subset_1(k1_relset_1(X33,X34,X35),k1_zfmisc_1(X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).
% 0.19/0.44  cnf(c_0_26, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.44  fof(c_0_27, plain, ![X17, X18, X19]:(~r1_tarski(X17,X18)|~r1_tarski(X18,X19)|r1_tarski(X17,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.19/0.44  cnf(c_0_28, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.44  cnf(c_0_29, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.44  cnf(c_0_30, negated_conjecture, (r1_tarski(esk6_0,k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.44  cnf(c_0_31, negated_conjecture, (esk3_0=k1_xboole_0|esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.44  cnf(c_0_32, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.44  cnf(c_0_33, plain, (m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.44  cnf(c_0_34, negated_conjecture, (k1_relset_1(esk3_0,esk4_0,esk6_0)=k1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_26, c_0_23])).
% 0.19/0.44  cnf(c_0_35, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.44  cnf(c_0_36, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.44  cnf(c_0_37, negated_conjecture, (r1_tarski(esk6_0,k2_zfmisc_1(k1_xboole_0,esk4_0))|esk4_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.44  cnf(c_0_38, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_32])).
% 0.19/0.44  fof(c_0_39, plain, ![X15, X16]:(((r1_tarski(X15,X16)|X15!=X16)&(r1_tarski(X16,X15)|X15!=X16))&(~r1_tarski(X15,X16)|~r1_tarski(X16,X15)|X15=X16)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.44  cnf(c_0_40, negated_conjecture, (m1_subset_1(k1_relat_1(esk6_0),k1_zfmisc_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_23])])).
% 0.19/0.44  cnf(c_0_41, negated_conjecture, (~v1_funct_1(esk6_0)|~v1_funct_2(esk6_0,esk3_0,esk5_0)|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.44  cnf(c_0_42, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.44  fof(c_0_43, plain, ![X43, X44, X45]:((((~v1_funct_2(X45,X43,X44)|X43=k1_relset_1(X43,X44,X45)|X44=k1_xboole_0|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))))&(X43!=k1_relset_1(X43,X44,X45)|v1_funct_2(X45,X43,X44)|X44=k1_xboole_0|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))))&((~v1_funct_2(X45,X43,X44)|X43=k1_relset_1(X43,X44,X45)|X43!=k1_xboole_0|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))))&(X43!=k1_relset_1(X43,X44,X45)|v1_funct_2(X45,X43,X44)|X43!=k1_xboole_0|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))))))&((~v1_funct_2(X45,X43,X44)|X45=k1_xboole_0|X43=k1_xboole_0|X44!=k1_xboole_0|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))))&(X45!=k1_xboole_0|v1_funct_2(X45,X43,X44)|X43=k1_xboole_0|X44!=k1_xboole_0|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.19/0.44  cnf(c_0_44, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.44  cnf(c_0_45, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,X3)|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.44  cnf(c_0_46, negated_conjecture, (r1_tarski(esk6_0,k1_xboole_0)|esk4_0!=k1_xboole_0), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.44  cnf(c_0_47, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.44  cnf(c_0_48, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.44  cnf(c_0_49, negated_conjecture, (r1_tarski(k1_relat_1(esk6_0),esk3_0)), inference(spm,[status(thm)],[c_0_22, c_0_40])).
% 0.19/0.44  cnf(c_0_50, negated_conjecture, (~v1_funct_2(esk6_0,esk3_0,esk5_0)|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42])])).
% 0.19/0.44  cnf(c_0_51, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.44  cnf(c_0_52, plain, (k1_relset_1(X1,X2,X3)=k1_relat_1(X3)|~r1_tarski(X3,k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_26, c_0_44])).
% 0.19/0.44  cnf(c_0_53, negated_conjecture, (r1_tarski(esk6_0,X1)|esk4_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])])).
% 0.19/0.44  cnf(c_0_54, plain, (X1=X2|~r1_tarski(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_48, c_0_36])).
% 0.19/0.44  cnf(c_0_55, negated_conjecture, (r1_tarski(k1_relat_1(esk6_0),k1_xboole_0)|esk4_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_49, c_0_31])).
% 0.19/0.44  cnf(c_0_56, negated_conjecture, (~v1_funct_2(esk6_0,esk3_0,esk5_0)|~r1_tarski(esk6_0,k2_zfmisc_1(esk3_0,esk5_0))), inference(spm,[status(thm)],[c_0_50, c_0_44])).
% 0.19/0.44  cnf(c_0_57, plain, (v1_funct_2(X1,k1_xboole_0,X2)|k1_relset_1(k1_xboole_0,X2,X1)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_51]), c_0_38])).
% 0.19/0.44  cnf(c_0_58, negated_conjecture, (k1_relset_1(X1,X2,esk6_0)=k1_relat_1(esk6_0)|esk4_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.19/0.44  cnf(c_0_59, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k1_xboole_0))|esk4_0!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_31]), c_0_38])).
% 0.19/0.44  cnf(c_0_60, negated_conjecture, (k1_relat_1(esk6_0)=k1_xboole_0|esk4_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_47])])).
% 0.19/0.44  fof(c_0_61, plain, ![X27, X28, X29]:(~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|v1_relat_1(X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.44  fof(c_0_62, plain, ![X39, X40, X41, X42]:(~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X41,X39)))|(~r1_tarski(k2_relat_1(X42),X40)|m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X41,X40))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_relset_1])])).
% 0.19/0.44  cnf(c_0_63, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.44  cnf(c_0_64, negated_conjecture, (v1_funct_2(esk6_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.44  cnf(c_0_65, negated_conjecture, (esk4_0!=k1_xboole_0|~v1_funct_2(esk6_0,k1_xboole_0,esk5_0)), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_31]), c_0_38]), c_0_46])).
% 0.19/0.44  cnf(c_0_66, negated_conjecture, (v1_funct_2(esk6_0,k1_xboole_0,X1)|esk4_0!=k1_xboole_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59]), c_0_60])).
% 0.19/0.44  cnf(c_0_67, negated_conjecture, (r1_tarski(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.44  fof(c_0_68, plain, ![X30, X31, X32]:((v4_relat_1(X32,X30)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))&(v5_relat_1(X32,X31)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.44  cnf(c_0_69, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.44  cnf(c_0_70, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.44  cnf(c_0_71, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(k2_relat_1(X1),X4)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.44  cnf(c_0_72, negated_conjecture, (k1_relset_1(esk3_0,esk4_0,esk6_0)=esk3_0|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_23]), c_0_64])])).
% 0.19/0.44  cnf(c_0_73, negated_conjecture, (esk4_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.19/0.44  cnf(c_0_74, negated_conjecture, (r1_tarski(esk4_0,X1)|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_45, c_0_67])).
% 0.19/0.44  fof(c_0_75, plain, ![X25, X26]:((~v5_relat_1(X26,X25)|r1_tarski(k2_relat_1(X26),X25)|~v1_relat_1(X26))&(~r1_tarski(k2_relat_1(X26),X25)|v5_relat_1(X26,X25)|~v1_relat_1(X26))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.19/0.44  cnf(c_0_76, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.19/0.44  fof(c_0_77, plain, ![X20]:(~r1_tarski(X20,k1_xboole_0)|X20=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.19/0.44  cnf(c_0_78, plain, (v1_relat_1(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_69, c_0_44])).
% 0.19/0.44  cnf(c_0_79, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_70])).
% 0.19/0.44  cnf(c_0_80, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))|~r1_tarski(k2_relat_1(esk6_0),X1)), inference(spm,[status(thm)],[c_0_71, c_0_23])).
% 0.19/0.44  cnf(c_0_81, negated_conjecture, (k1_relat_1(esk6_0)=esk3_0), inference(rw,[status(thm)],[inference(sr,[status(thm)],[c_0_72, c_0_73]), c_0_34])).
% 0.19/0.44  cnf(c_0_82, negated_conjecture, (X1=esk4_0|~r1_tarski(X1,esk4_0)|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_48, c_0_74])).
% 0.19/0.44  cnf(c_0_83, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.19/0.44  cnf(c_0_84, plain, (v5_relat_1(X1,X2)|~r1_tarski(X1,k2_zfmisc_1(X3,X2))), inference(spm,[status(thm)],[c_0_76, c_0_44])).
% 0.19/0.44  cnf(c_0_85, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.19/0.44  cnf(c_0_86, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.44  cnf(c_0_87, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.19/0.44  cnf(c_0_88, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.44  cnf(c_0_89, negated_conjecture, (k1_relset_1(esk3_0,X1,esk6_0)=esk3_0|~r1_tarski(k2_relat_1(esk6_0),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_80]), c_0_81])).
% 0.19/0.44  cnf(c_0_90, negated_conjecture, (v5_relat_1(esk6_0,X1)|~r1_tarski(k2_relat_1(esk6_0),X1)), inference(spm,[status(thm)],[c_0_76, c_0_80])).
% 0.19/0.44  cnf(c_0_91, negated_conjecture, (r1_tarski(X1,esk5_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_35, c_0_67])).
% 0.19/0.44  cnf(c_0_92, negated_conjecture, (k2_relat_1(X1)=esk4_0|~v5_relat_1(X1,esk4_0)|~v1_relat_1(X1)|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.19/0.44  cnf(c_0_93, plain, (v5_relat_1(k2_zfmisc_1(X1,X2),X2)), inference(spm,[status(thm)],[c_0_84, c_0_79])).
% 0.19/0.44  cnf(c_0_94, plain, (k2_relat_1(X1)=k1_xboole_0|~v5_relat_1(X1,k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_85, c_0_83])).
% 0.19/0.44  cnf(c_0_95, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_86])).
% 0.19/0.44  cnf(c_0_96, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_87, c_0_38])).
% 0.19/0.44  cnf(c_0_97, negated_conjecture, (~v1_funct_2(esk6_0,esk3_0,esk5_0)|~r1_tarski(k2_relat_1(esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_50, c_0_80])).
% 0.19/0.44  cnf(c_0_98, negated_conjecture, (X1=k1_xboole_0|v1_funct_2(esk6_0,esk3_0,X1)|~r1_tarski(k2_relat_1(esk6_0),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_80]), c_0_89])).
% 0.19/0.44  cnf(c_0_99, negated_conjecture, (v5_relat_1(esk6_0,esk5_0)|~r1_tarski(k2_relat_1(esk6_0),esk4_0)), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.19/0.44  cnf(c_0_100, negated_conjecture, (v5_relat_1(esk6_0,esk4_0)), inference(spm,[status(thm)],[c_0_76, c_0_23])).
% 0.19/0.44  cnf(c_0_101, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_69, c_0_23])).
% 0.19/0.44  cnf(c_0_102, negated_conjecture, (k2_relat_1(k2_zfmisc_1(X1,esk4_0))=esk4_0|~v1_xboole_0(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_87])])).
% 0.19/0.44  cnf(c_0_103, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_93]), c_0_95]), c_0_95]), c_0_96])])).
% 0.19/0.44  cnf(c_0_104, negated_conjecture, (esk5_0=k1_xboole_0|~r1_tarski(k2_relat_1(esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 0.19/0.44  cnf(c_0_105, negated_conjecture, (v5_relat_1(esk6_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_83]), c_0_100]), c_0_101])])).
% 0.19/0.44  cnf(c_0_106, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_38]), c_0_103]), c_0_73])).
% 0.19/0.44  cnf(c_0_107, negated_conjecture, (esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_83]), c_0_105]), c_0_101])])).
% 0.19/0.44  cnf(c_0_108, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106, c_0_107]), c_0_47])]), ['proof']).
% 0.19/0.44  # SZS output end CNFRefutation
% 0.19/0.44  # Proof object total steps             : 109
% 0.19/0.44  # Proof object clause steps            : 77
% 0.19/0.44  # Proof object formula steps           : 32
% 0.19/0.44  # Proof object conjectures             : 45
% 0.19/0.44  # Proof object clause conjectures      : 42
% 0.19/0.44  # Proof object formula conjectures     : 3
% 0.19/0.44  # Proof object initial clauses used    : 26
% 0.19/0.44  # Proof object initial formulas used   : 16
% 0.19/0.44  # Proof object generating inferences   : 43
% 0.19/0.44  # Proof object simplifying inferences  : 42
% 0.19/0.44  # Training examples: 0 positive, 0 negative
% 0.19/0.44  # Parsed axioms                        : 16
% 0.19/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.44  # Initial clauses                      : 36
% 0.19/0.44  # Removed in clause preprocessing      : 0
% 0.19/0.44  # Initial clauses in saturation        : 36
% 0.19/0.44  # Processed clauses                    : 1625
% 0.19/0.44  # ...of these trivial                  : 24
% 0.19/0.44  # ...subsumed                          : 1139
% 0.19/0.44  # ...remaining for further processing  : 462
% 0.19/0.44  # Other redundant clauses eliminated   : 10
% 0.19/0.44  # Clauses deleted for lack of memory   : 0
% 0.19/0.44  # Backward-subsumed                    : 55
% 0.19/0.44  # Backward-rewritten                   : 111
% 0.19/0.44  # Generated clauses                    : 3700
% 0.19/0.44  # ...of the previous two non-trivial   : 3185
% 0.19/0.44  # Contextual simplify-reflections      : 39
% 0.19/0.44  # Paramodulations                      : 3688
% 0.19/0.44  # Factorizations                       : 0
% 0.19/0.44  # Equation resolutions                 : 10
% 0.19/0.44  # Propositional unsat checks           : 0
% 0.19/0.44  #    Propositional check models        : 0
% 0.19/0.44  #    Propositional check unsatisfiable : 0
% 0.19/0.44  #    Propositional clauses             : 0
% 0.19/0.44  #    Propositional clauses after purity: 0
% 0.19/0.44  #    Propositional unsat core size     : 0
% 0.19/0.44  #    Propositional preprocessing time  : 0.000
% 0.19/0.44  #    Propositional encoding time       : 0.000
% 0.19/0.44  #    Propositional solver time         : 0.000
% 0.19/0.44  #    Success case prop preproc time    : 0.000
% 0.19/0.44  #    Success case prop encoding time   : 0.000
% 0.19/0.44  #    Success case prop solver time     : 0.000
% 0.19/0.44  # Current number of processed clauses  : 285
% 0.19/0.44  #    Positive orientable unit clauses  : 29
% 0.19/0.44  #    Positive unorientable unit clauses: 0
% 0.19/0.44  #    Negative unit clauses             : 1
% 0.19/0.44  #    Non-unit-clauses                  : 255
% 0.19/0.44  # Current number of unprocessed clauses: 1361
% 0.19/0.44  # ...number of literals in the above   : 5139
% 0.19/0.44  # Current number of archived formulas  : 0
% 0.19/0.44  # Current number of archived clauses   : 169
% 0.19/0.44  # Clause-clause subsumption calls (NU) : 19326
% 0.19/0.45  # Rec. Clause-clause subsumption calls : 16405
% 0.19/0.45  # Non-unit clause-clause subsumptions  : 930
% 0.19/0.45  # Unit Clause-clause subsumption calls : 710
% 0.19/0.45  # Rewrite failures with RHS unbound    : 0
% 0.19/0.45  # BW rewrite match attempts            : 62
% 0.19/0.45  # BW rewrite match successes           : 16
% 0.19/0.45  # Condensation attempts                : 0
% 0.19/0.45  # Condensation successes               : 0
% 0.19/0.45  # Termbank termtop insertions          : 44820
% 0.19/0.45  
% 0.19/0.45  # -------------------------------------------------
% 0.19/0.45  # User time                : 0.105 s
% 0.19/0.45  # System time              : 0.004 s
% 0.19/0.45  # Total time               : 0.109 s
% 0.19/0.45  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
