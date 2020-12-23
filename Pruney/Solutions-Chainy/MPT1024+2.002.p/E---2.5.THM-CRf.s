%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:27 EST 2020

% Result     : Theorem 0.39s
% Output     : CNFRefutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 135 expanded)
%              Number of clauses        :   41 (  56 expanded)
%              Number of leaves         :   15 (  34 expanded)
%              Depth                    :   15
%              Number of atoms          :  249 ( 582 expanded)
%              Number of equality atoms :   72 ( 108 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t115_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X5] :
          ~ ( r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
            & ! [X6] :
                ~ ( r2_hidden(X6,X1)
                  & r2_hidden(X6,X3)
                  & X5 = k1_funct_1(X4,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(t99_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(cc1_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X5] :
            ~ ( r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
              & ! [X6] :
                  ~ ( r2_hidden(X6,X1)
                    & r2_hidden(X6,X3)
                    & X5 = k1_funct_1(X4,X6) ) ) ) ),
    inference(assume_negation,[status(cth)],[t115_funct_2])).

fof(c_0_16,plain,(
    ! [X26,X27] :
      ( ~ m1_subset_1(X26,X27)
      | v1_xboole_0(X27)
      | r2_hidden(X26,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_17,negated_conjecture,(
    ! [X55] :
      ( v1_funct_1(esk9_0)
      & v1_funct_2(esk9_0,esk6_0,esk7_0)
      & m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))
      & r2_hidden(esk10_0,k7_relset_1(esk6_0,esk7_0,esk9_0,esk8_0))
      & ( ~ r2_hidden(X55,esk6_0)
        | ~ r2_hidden(X55,esk8_0)
        | esk10_0 != k1_funct_1(esk9_0,X55) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])])).

fof(c_0_18,plain,(
    ! [X25] : ~ v1_xboole_0(k1_zfmisc_1(X25)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_19,plain,(
    ! [X11,X12,X13,X15,X16,X17,X18,X20] :
      ( ( r2_hidden(X13,esk2_3(X11,X12,X13))
        | ~ r2_hidden(X13,X12)
        | X12 != k3_tarski(X11) )
      & ( r2_hidden(esk2_3(X11,X12,X13),X11)
        | ~ r2_hidden(X13,X12)
        | X12 != k3_tarski(X11) )
      & ( ~ r2_hidden(X15,X16)
        | ~ r2_hidden(X16,X11)
        | r2_hidden(X15,X12)
        | X12 != k3_tarski(X11) )
      & ( ~ r2_hidden(esk3_2(X17,X18),X18)
        | ~ r2_hidden(esk3_2(X17,X18),X20)
        | ~ r2_hidden(X20,X17)
        | X18 = k3_tarski(X17) )
      & ( r2_hidden(esk3_2(X17,X18),esk4_2(X17,X18))
        | r2_hidden(esk3_2(X17,X18),X18)
        | X18 = k3_tarski(X17) )
      & ( r2_hidden(esk4_2(X17,X18),X17)
        | r2_hidden(esk3_2(X17,X18),X18)
        | X18 = k3_tarski(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_20,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,plain,(
    ! [X24] : k3_tarski(k1_zfmisc_1(X24)) = X24 ),
    inference(variable_rename,[status(thm)],[t99_zfmisc_1])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | X4 != k3_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_26,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_27,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(X1,X2)
    | X2 != k2_zfmisc_1(esk6_0,esk7_0)
    | ~ r2_hidden(X1,esk9_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

fof(c_0_29,plain,(
    ! [X40,X41,X42] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
      | k1_relset_1(X40,X41,X42) = k1_relat_1(X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_30,plain,(
    ! [X47,X48,X49] :
      ( ( ~ v1_funct_2(X49,X47,X48)
        | X47 = k1_relset_1(X47,X48,X49)
        | X48 = k1_xboole_0
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))) )
      & ( X47 != k1_relset_1(X47,X48,X49)
        | v1_funct_2(X49,X47,X48)
        | X48 = k1_xboole_0
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))) )
      & ( ~ v1_funct_2(X49,X47,X48)
        | X47 = k1_relset_1(X47,X48,X49)
        | X47 != k1_xboole_0
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))) )
      & ( X47 != k1_relset_1(X47,X48,X49)
        | v1_funct_2(X49,X47,X48)
        | X47 != k1_xboole_0
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))) )
      & ( ~ v1_funct_2(X49,X47,X48)
        | X49 = k1_xboole_0
        | X47 = k1_xboole_0
        | X48 != k1_xboole_0
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))) )
      & ( X49 != k1_xboole_0
        | v1_funct_2(X49,X47,X48)
        | X47 = k1_xboole_0
        | X48 != k1_xboole_0
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_31,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk6_0,esk7_0))
    | ~ r2_hidden(X1,esk9_0) ),
    inference(er,[status(thm)],[c_0_28])).

fof(c_0_33,plain,(
    ! [X22,X23] :
      ( ( k2_zfmisc_1(X22,X23) != k1_xboole_0
        | X22 = k1_xboole_0
        | X23 = k1_xboole_0 )
      & ( X22 != k1_xboole_0
        | k2_zfmisc_1(X22,X23) = k1_xboole_0 )
      & ( X23 != k1_xboole_0
        | k2_zfmisc_1(X22,X23) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_34,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_36,plain,(
    ! [X29,X30,X31,X33] :
      ( ( r2_hidden(esk5_3(X29,X30,X31),k1_relat_1(X31))
        | ~ r2_hidden(X29,k9_relat_1(X31,X30))
        | ~ v1_relat_1(X31) )
      & ( r2_hidden(k4_tarski(esk5_3(X29,X30,X31),X29),X31)
        | ~ r2_hidden(X29,k9_relat_1(X31,X30))
        | ~ v1_relat_1(X31) )
      & ( r2_hidden(esk5_3(X29,X30,X31),X30)
        | ~ r2_hidden(X29,k9_relat_1(X31,X30))
        | ~ v1_relat_1(X31) )
      & ( ~ r2_hidden(X33,k1_relat_1(X31))
        | ~ r2_hidden(k4_tarski(X33,X29),X31)
        | ~ r2_hidden(X33,X30)
        | r2_hidden(X29,k9_relat_1(X31,X30))
        | ~ v1_relat_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

fof(c_0_37,plain,(
    ! [X28] :
      ( ~ v1_xboole_0(X28)
      | v1_relat_1(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).

fof(c_0_38,plain,(
    ! [X43,X44,X45,X46] :
      ( ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
      | k7_relset_1(X43,X44,X45,X46) = k9_relat_1(X45,X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

cnf(c_0_39,negated_conjecture,
    ( ~ r2_hidden(X1,esk9_0)
    | ~ v1_xboole_0(k2_zfmisc_1(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_42,plain,
    ( X1 = k1_relat_1(X2)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( v1_funct_2(esk9_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_44,plain,
    ( r2_hidden(k4_tarski(esk5_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk10_0,k7_relset_1(esk6_0,esk7_0,esk9_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_47,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,negated_conjecture,
    ( esk7_0 != k1_xboole_0
    | ~ r2_hidden(X1,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])])).

cnf(c_0_49,negated_conjecture,
    ( esk6_0 = k1_relat_1(esk9_0)
    | esk7_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_21])])).

cnf(c_0_50,plain,
    ( ~ r2_hidden(X1,k9_relat_1(X2,X3))
    | ~ v1_xboole_0(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_44]),c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk10_0,k9_relat_1(esk9_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_21])])).

cnf(c_0_52,negated_conjecture,
    ( esk6_0 = k1_relat_1(esk9_0)
    | ~ r2_hidden(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_53,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_54,negated_conjecture,
    ( ~ v1_xboole_0(esk9_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

fof(c_0_55,plain,(
    ! [X34,X35,X36] :
      ( ( r2_hidden(X34,k1_relat_1(X36))
        | ~ r2_hidden(k4_tarski(X34,X35),X36)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) )
      & ( X35 = k1_funct_1(X36,X34)
        | ~ r2_hidden(k4_tarski(X34,X35),X36)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) )
      & ( ~ r2_hidden(X34,k1_relat_1(X36))
        | X35 != k1_funct_1(X36,X34)
        | r2_hidden(k4_tarski(X34,X35),X36)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

fof(c_0_56,plain,(
    ! [X37,X38,X39] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
      | v1_relat_1(X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_57,negated_conjecture,
    ( ~ r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk8_0)
    | esk10_0 != k1_funct_1(esk9_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_58,negated_conjecture,
    ( esk6_0 = k1_relat_1(esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])).

cnf(c_0_59,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_60,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( esk10_0 != k1_funct_1(esk9_0,X1)
    | ~ r2_hidden(X1,k1_relat_1(esk9_0))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(rw,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,plain,
    ( k1_funct_1(X1,esk5_3(X2,X3,X1)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_44])).

cnf(c_0_63,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_64,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_21])).

cnf(c_0_65,negated_conjecture,
    ( esk10_0 != X1
    | ~ r2_hidden(esk5_3(X1,X2,esk9_0),k1_relat_1(esk9_0))
    | ~ r2_hidden(esk5_3(X1,X2,esk9_0),esk8_0)
    | ~ r2_hidden(X1,k9_relat_1(esk9_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63]),c_0_64])])).

cnf(c_0_66,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_67,negated_conjecture,
    ( esk10_0 != X1
    | ~ r2_hidden(esk5_3(X1,esk8_0,esk9_0),k1_relat_1(esk9_0))
    | ~ r2_hidden(X1,k9_relat_1(esk9_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_64])])).

cnf(c_0_68,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),k1_relat_1(X3))
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_69,negated_conjecture,
    ( esk10_0 != X1
    | ~ r2_hidden(X1,k9_relat_1(esk9_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_64])])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_69,c_0_51]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:58:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.39/0.56  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.39/0.56  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.39/0.56  #
% 0.39/0.56  # Preprocessing time       : 0.029 s
% 0.39/0.56  # Presaturation interreduction done
% 0.39/0.56  
% 0.39/0.56  # Proof found!
% 0.39/0.56  # SZS status Theorem
% 0.39/0.56  # SZS output start CNFRefutation
% 0.39/0.56  fof(t115_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:~(((r2_hidden(X6,X1)&r2_hidden(X6,X3))&X5=k1_funct_1(X4,X6)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_funct_2)).
% 0.39/0.56  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.39/0.56  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.39/0.56  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 0.39/0.56  fof(t99_zfmisc_1, axiom, ![X1]:k3_tarski(k1_zfmisc_1(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 0.39/0.56  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.39/0.56  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.39/0.56  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.39/0.56  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.39/0.56  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 0.39/0.56  fof(cc1_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 0.39/0.56  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.39/0.56  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.39/0.56  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 0.39/0.56  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.39/0.56  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:~(((r2_hidden(X6,X1)&r2_hidden(X6,X3))&X5=k1_funct_1(X4,X6))))))), inference(assume_negation,[status(cth)],[t115_funct_2])).
% 0.39/0.56  fof(c_0_16, plain, ![X26, X27]:(~m1_subset_1(X26,X27)|(v1_xboole_0(X27)|r2_hidden(X26,X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.39/0.56  fof(c_0_17, negated_conjecture, ![X55]:(((v1_funct_1(esk9_0)&v1_funct_2(esk9_0,esk6_0,esk7_0))&m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))))&(r2_hidden(esk10_0,k7_relset_1(esk6_0,esk7_0,esk9_0,esk8_0))&(~r2_hidden(X55,esk6_0)|~r2_hidden(X55,esk8_0)|esk10_0!=k1_funct_1(esk9_0,X55)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])])).
% 0.39/0.56  fof(c_0_18, plain, ![X25]:~v1_xboole_0(k1_zfmisc_1(X25)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.39/0.56  fof(c_0_19, plain, ![X11, X12, X13, X15, X16, X17, X18, X20]:((((r2_hidden(X13,esk2_3(X11,X12,X13))|~r2_hidden(X13,X12)|X12!=k3_tarski(X11))&(r2_hidden(esk2_3(X11,X12,X13),X11)|~r2_hidden(X13,X12)|X12!=k3_tarski(X11)))&(~r2_hidden(X15,X16)|~r2_hidden(X16,X11)|r2_hidden(X15,X12)|X12!=k3_tarski(X11)))&((~r2_hidden(esk3_2(X17,X18),X18)|(~r2_hidden(esk3_2(X17,X18),X20)|~r2_hidden(X20,X17))|X18=k3_tarski(X17))&((r2_hidden(esk3_2(X17,X18),esk4_2(X17,X18))|r2_hidden(esk3_2(X17,X18),X18)|X18=k3_tarski(X17))&(r2_hidden(esk4_2(X17,X18),X17)|r2_hidden(esk3_2(X17,X18),X18)|X18=k3_tarski(X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 0.39/0.56  cnf(c_0_20, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.39/0.56  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.39/0.56  cnf(c_0_22, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.39/0.56  fof(c_0_23, plain, ![X24]:k3_tarski(k1_zfmisc_1(X24))=X24, inference(variable_rename,[status(thm)],[t99_zfmisc_1])).
% 0.39/0.56  cnf(c_0_24, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X2,X3)|X4!=k3_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.39/0.56  cnf(c_0_25, negated_conjecture, (r2_hidden(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 0.39/0.56  cnf(c_0_26, plain, (k3_tarski(k1_zfmisc_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.39/0.56  fof(c_0_27, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.39/0.56  cnf(c_0_28, negated_conjecture, (r2_hidden(X1,X2)|X2!=k2_zfmisc_1(esk6_0,esk7_0)|~r2_hidden(X1,esk9_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])).
% 0.39/0.56  fof(c_0_29, plain, ![X40, X41, X42]:(~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|k1_relset_1(X40,X41,X42)=k1_relat_1(X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.39/0.56  fof(c_0_30, plain, ![X47, X48, X49]:((((~v1_funct_2(X49,X47,X48)|X47=k1_relset_1(X47,X48,X49)|X48=k1_xboole_0|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))))&(X47!=k1_relset_1(X47,X48,X49)|v1_funct_2(X49,X47,X48)|X48=k1_xboole_0|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))))&((~v1_funct_2(X49,X47,X48)|X47=k1_relset_1(X47,X48,X49)|X47!=k1_xboole_0|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))))&(X47!=k1_relset_1(X47,X48,X49)|v1_funct_2(X49,X47,X48)|X47!=k1_xboole_0|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))))))&((~v1_funct_2(X49,X47,X48)|X49=k1_xboole_0|X47=k1_xboole_0|X48!=k1_xboole_0|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))))&(X49!=k1_xboole_0|v1_funct_2(X49,X47,X48)|X47=k1_xboole_0|X48!=k1_xboole_0|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.39/0.56  cnf(c_0_31, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.39/0.56  cnf(c_0_32, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(esk6_0,esk7_0))|~r2_hidden(X1,esk9_0)), inference(er,[status(thm)],[c_0_28])).
% 0.39/0.56  fof(c_0_33, plain, ![X22, X23]:((k2_zfmisc_1(X22,X23)!=k1_xboole_0|(X22=k1_xboole_0|X23=k1_xboole_0))&((X22!=k1_xboole_0|k2_zfmisc_1(X22,X23)=k1_xboole_0)&(X23!=k1_xboole_0|k2_zfmisc_1(X22,X23)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.39/0.56  cnf(c_0_34, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.39/0.56  cnf(c_0_35, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.39/0.56  fof(c_0_36, plain, ![X29, X30, X31, X33]:((((r2_hidden(esk5_3(X29,X30,X31),k1_relat_1(X31))|~r2_hidden(X29,k9_relat_1(X31,X30))|~v1_relat_1(X31))&(r2_hidden(k4_tarski(esk5_3(X29,X30,X31),X29),X31)|~r2_hidden(X29,k9_relat_1(X31,X30))|~v1_relat_1(X31)))&(r2_hidden(esk5_3(X29,X30,X31),X30)|~r2_hidden(X29,k9_relat_1(X31,X30))|~v1_relat_1(X31)))&(~r2_hidden(X33,k1_relat_1(X31))|~r2_hidden(k4_tarski(X33,X29),X31)|~r2_hidden(X33,X30)|r2_hidden(X29,k9_relat_1(X31,X30))|~v1_relat_1(X31))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.39/0.56  fof(c_0_37, plain, ![X28]:(~v1_xboole_0(X28)|v1_relat_1(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).
% 0.39/0.56  fof(c_0_38, plain, ![X43, X44, X45, X46]:(~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))|k7_relset_1(X43,X44,X45,X46)=k9_relat_1(X45,X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.39/0.56  cnf(c_0_39, negated_conjecture, (~r2_hidden(X1,esk9_0)|~v1_xboole_0(k2_zfmisc_1(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.39/0.56  cnf(c_0_40, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.39/0.56  cnf(c_0_41, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.39/0.56  cnf(c_0_42, plain, (X1=k1_relat_1(X2)|X3=k1_xboole_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.39/0.56  cnf(c_0_43, negated_conjecture, (v1_funct_2(esk9_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.39/0.56  cnf(c_0_44, plain, (r2_hidden(k4_tarski(esk5_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.39/0.56  cnf(c_0_45, plain, (v1_relat_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.39/0.56  cnf(c_0_46, negated_conjecture, (r2_hidden(esk10_0,k7_relset_1(esk6_0,esk7_0,esk9_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.39/0.56  cnf(c_0_47, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.39/0.56  cnf(c_0_48, negated_conjecture, (esk7_0!=k1_xboole_0|~r2_hidden(X1,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])])).
% 0.39/0.56  cnf(c_0_49, negated_conjecture, (esk6_0=k1_relat_1(esk9_0)|esk7_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_21])])).
% 0.39/0.56  cnf(c_0_50, plain, (~r2_hidden(X1,k9_relat_1(X2,X3))|~v1_xboole_0(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_44]), c_0_45])).
% 0.39/0.56  cnf(c_0_51, negated_conjecture, (r2_hidden(esk10_0,k9_relat_1(esk9_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_21])])).
% 0.39/0.56  cnf(c_0_52, negated_conjecture, (esk6_0=k1_relat_1(esk9_0)|~r2_hidden(X1,esk9_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.39/0.56  cnf(c_0_53, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.39/0.56  cnf(c_0_54, negated_conjecture, (~v1_xboole_0(esk9_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.39/0.56  fof(c_0_55, plain, ![X34, X35, X36]:(((r2_hidden(X34,k1_relat_1(X36))|~r2_hidden(k4_tarski(X34,X35),X36)|(~v1_relat_1(X36)|~v1_funct_1(X36)))&(X35=k1_funct_1(X36,X34)|~r2_hidden(k4_tarski(X34,X35),X36)|(~v1_relat_1(X36)|~v1_funct_1(X36))))&(~r2_hidden(X34,k1_relat_1(X36))|X35!=k1_funct_1(X36,X34)|r2_hidden(k4_tarski(X34,X35),X36)|(~v1_relat_1(X36)|~v1_funct_1(X36)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.39/0.56  fof(c_0_56, plain, ![X37, X38, X39]:(~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))|v1_relat_1(X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.39/0.56  cnf(c_0_57, negated_conjecture, (~r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk8_0)|esk10_0!=k1_funct_1(esk9_0,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.39/0.56  cnf(c_0_58, negated_conjecture, (esk6_0=k1_relat_1(esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])).
% 0.39/0.56  cnf(c_0_59, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.39/0.56  cnf(c_0_60, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.39/0.56  cnf(c_0_61, negated_conjecture, (esk10_0!=k1_funct_1(esk9_0,X1)|~r2_hidden(X1,k1_relat_1(esk9_0))|~r2_hidden(X1,esk8_0)), inference(rw,[status(thm)],[c_0_57, c_0_58])).
% 0.39/0.56  cnf(c_0_62, plain, (k1_funct_1(X1,esk5_3(X2,X3,X1))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(X1,X3))), inference(spm,[status(thm)],[c_0_59, c_0_44])).
% 0.39/0.56  cnf(c_0_63, negated_conjecture, (v1_funct_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.39/0.56  cnf(c_0_64, negated_conjecture, (v1_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_60, c_0_21])).
% 0.39/0.56  cnf(c_0_65, negated_conjecture, (esk10_0!=X1|~r2_hidden(esk5_3(X1,X2,esk9_0),k1_relat_1(esk9_0))|~r2_hidden(esk5_3(X1,X2,esk9_0),esk8_0)|~r2_hidden(X1,k9_relat_1(esk9_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63]), c_0_64])])).
% 0.39/0.56  cnf(c_0_66, plain, (r2_hidden(esk5_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.39/0.56  cnf(c_0_67, negated_conjecture, (esk10_0!=X1|~r2_hidden(esk5_3(X1,esk8_0,esk9_0),k1_relat_1(esk9_0))|~r2_hidden(X1,k9_relat_1(esk9_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_64])])).
% 0.39/0.56  cnf(c_0_68, plain, (r2_hidden(esk5_3(X1,X2,X3),k1_relat_1(X3))|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.39/0.56  cnf(c_0_69, negated_conjecture, (esk10_0!=X1|~r2_hidden(X1,k9_relat_1(esk9_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_64])])).
% 0.39/0.56  cnf(c_0_70, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_69, c_0_51]), ['proof']).
% 0.39/0.56  # SZS output end CNFRefutation
% 0.39/0.56  # Proof object total steps             : 71
% 0.39/0.56  # Proof object clause steps            : 41
% 0.39/0.56  # Proof object formula steps           : 30
% 0.39/0.56  # Proof object conjectures             : 24
% 0.39/0.56  # Proof object clause conjectures      : 21
% 0.39/0.56  # Proof object formula conjectures     : 3
% 0.39/0.56  # Proof object initial clauses used    : 22
% 0.39/0.56  # Proof object initial formulas used   : 15
% 0.39/0.56  # Proof object generating inferences   : 18
% 0.39/0.56  # Proof object simplifying inferences  : 18
% 0.39/0.56  # Training examples: 0 positive, 0 negative
% 0.39/0.56  # Parsed axioms                        : 15
% 0.39/0.56  # Removed by relevancy pruning/SinE    : 0
% 0.39/0.56  # Initial clauses                      : 37
% 0.39/0.56  # Removed in clause preprocessing      : 0
% 0.39/0.56  # Initial clauses in saturation        : 37
% 0.39/0.56  # Processed clauses                    : 2754
% 0.39/0.56  # ...of these trivial                  : 14
% 0.39/0.56  # ...subsumed                          : 2137
% 0.39/0.56  # ...remaining for further processing  : 603
% 0.39/0.56  # Other redundant clauses eliminated   : 23
% 0.39/0.56  # Clauses deleted for lack of memory   : 0
% 0.39/0.56  # Backward-subsumed                    : 22
% 0.39/0.56  # Backward-rewritten                   : 51
% 0.39/0.56  # Generated clauses                    : 12273
% 0.39/0.56  # ...of the previous two non-trivial   : 10936
% 0.39/0.56  # Contextual simplify-reflections      : 17
% 0.39/0.56  # Paramodulations                      : 12163
% 0.39/0.56  # Factorizations                       : 0
% 0.39/0.56  # Equation resolutions                 : 110
% 0.39/0.56  # Propositional unsat checks           : 0
% 0.39/0.56  #    Propositional check models        : 0
% 0.39/0.56  #    Propositional check unsatisfiable : 0
% 0.39/0.56  #    Propositional clauses             : 0
% 0.39/0.56  #    Propositional clauses after purity: 0
% 0.39/0.56  #    Propositional unsat core size     : 0
% 0.39/0.56  #    Propositional preprocessing time  : 0.000
% 0.39/0.56  #    Propositional encoding time       : 0.000
% 0.39/0.56  #    Propositional solver time         : 0.000
% 0.39/0.56  #    Success case prop preproc time    : 0.000
% 0.39/0.56  #    Success case prop encoding time   : 0.000
% 0.39/0.56  #    Success case prop solver time     : 0.000
% 0.39/0.56  # Current number of processed clauses  : 493
% 0.39/0.56  #    Positive orientable unit clauses  : 13
% 0.39/0.56  #    Positive unorientable unit clauses: 0
% 0.39/0.56  #    Negative unit clauses             : 14
% 0.39/0.56  #    Non-unit-clauses                  : 466
% 0.39/0.56  # Current number of unprocessed clauses: 8076
% 0.39/0.56  # ...number of literals in the above   : 45941
% 0.39/0.56  # Current number of archived formulas  : 0
% 0.39/0.56  # Current number of archived clauses   : 110
% 0.39/0.56  # Clause-clause subsumption calls (NU) : 36602
% 0.39/0.56  # Rec. Clause-clause subsumption calls : 9281
% 0.39/0.56  # Non-unit clause-clause subsumptions  : 693
% 0.39/0.56  # Unit Clause-clause subsumption calls : 138
% 0.39/0.56  # Rewrite failures with RHS unbound    : 0
% 0.39/0.56  # BW rewrite match attempts            : 14
% 0.39/0.56  # BW rewrite match successes           : 5
% 0.39/0.56  # Condensation attempts                : 0
% 0.39/0.56  # Condensation successes               : 0
% 0.39/0.56  # Termbank termtop insertions          : 158720
% 0.39/0.56  
% 0.39/0.56  # -------------------------------------------------
% 0.39/0.56  # User time                : 0.214 s
% 0.39/0.56  # System time              : 0.006 s
% 0.39/0.56  # Total time               : 0.221 s
% 0.39/0.56  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
