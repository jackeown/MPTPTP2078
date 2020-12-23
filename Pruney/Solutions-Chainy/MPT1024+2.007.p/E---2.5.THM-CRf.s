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
% DateTime   : Thu Dec  3 11:06:27 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   84 (1149 expanded)
%              Number of clauses        :   62 ( 461 expanded)
%              Number of leaves         :   11 ( 275 expanded)
%              Depth                    :   19
%              Number of atoms          :  293 (6229 expanded)
%              Number of equality atoms :   88 (1356 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).

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

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(c_0_11,negated_conjecture,(
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

fof(c_0_12,plain,(
    ! [X22,X23,X24,X25,X27,X28,X29,X30,X32] :
      ( ( r2_hidden(esk2_4(X22,X23,X24,X25),k1_relat_1(X22))
        | ~ r2_hidden(X25,X24)
        | X24 != k9_relat_1(X22,X23)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( r2_hidden(esk2_4(X22,X23,X24,X25),X23)
        | ~ r2_hidden(X25,X24)
        | X24 != k9_relat_1(X22,X23)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( X25 = k1_funct_1(X22,esk2_4(X22,X23,X24,X25))
        | ~ r2_hidden(X25,X24)
        | X24 != k9_relat_1(X22,X23)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( ~ r2_hidden(X28,k1_relat_1(X22))
        | ~ r2_hidden(X28,X23)
        | X27 != k1_funct_1(X22,X28)
        | r2_hidden(X27,X24)
        | X24 != k9_relat_1(X22,X23)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( ~ r2_hidden(esk3_3(X22,X29,X30),X30)
        | ~ r2_hidden(X32,k1_relat_1(X22))
        | ~ r2_hidden(X32,X29)
        | esk3_3(X22,X29,X30) != k1_funct_1(X22,X32)
        | X30 = k9_relat_1(X22,X29)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( r2_hidden(esk4_3(X22,X29,X30),k1_relat_1(X22))
        | r2_hidden(esk3_3(X22,X29,X30),X30)
        | X30 = k9_relat_1(X22,X29)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( r2_hidden(esk4_3(X22,X29,X30),X29)
        | r2_hidden(esk3_3(X22,X29,X30),X30)
        | X30 = k9_relat_1(X22,X29)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( esk3_3(X22,X29,X30) = k1_funct_1(X22,esk4_3(X22,X29,X30))
        | r2_hidden(esk3_3(X22,X29,X30),X30)
        | X30 = k9_relat_1(X22,X29)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).

fof(c_0_13,plain,(
    ! [X34,X35,X36] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
      | v1_relat_1(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_14,negated_conjecture,(
    ! [X52] :
      ( v1_funct_1(esk8_0)
      & v1_funct_2(esk8_0,esk5_0,esk6_0)
      & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
      & r2_hidden(esk9_0,k7_relset_1(esk5_0,esk6_0,esk8_0,esk7_0))
      & ( ~ r2_hidden(X52,esk5_0)
        | ~ r2_hidden(X52,esk7_0)
        | esk9_0 != k1_funct_1(esk8_0,X52) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).

fof(c_0_15,plain,(
    ! [X37,X38,X39] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
      | k1_relset_1(X37,X38,X39) = k1_relat_1(X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_16,plain,
    ( X1 = k1_funct_1(X2,esk2_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k9_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X40,X41,X42,X43] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
      | k7_relset_1(X40,X41,X42,X43) = k9_relat_1(X42,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_20,plain,(
    ! [X44,X45,X46] :
      ( ( ~ v1_funct_2(X46,X44,X45)
        | X44 = k1_relset_1(X44,X45,X46)
        | X45 = k1_xboole_0
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) )
      & ( X44 != k1_relset_1(X44,X45,X46)
        | v1_funct_2(X46,X44,X45)
        | X45 = k1_xboole_0
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) )
      & ( ~ v1_funct_2(X46,X44,X45)
        | X44 = k1_relset_1(X44,X45,X46)
        | X44 != k1_xboole_0
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) )
      & ( X44 != k1_relset_1(X44,X45,X46)
        | v1_funct_2(X46,X44,X45)
        | X44 != k1_xboole_0
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) )
      & ( ~ v1_funct_2(X46,X44,X45)
        | X46 = k1_xboole_0
        | X44 = k1_xboole_0
        | X45 != k1_xboole_0
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) )
      & ( X46 != k1_xboole_0
        | v1_funct_2(X46,X44,X45)
        | X44 = k1_xboole_0
        | X45 != k1_xboole_0
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_21,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( ~ r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk7_0)
    | esk9_0 != k1_funct_1(esk8_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k1_funct_1(X1,esk2_4(X1,X2,k9_relat_1(X1,X2),X3)) = X3
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,k9_relat_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_26,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk9_0,k7_relset_1(esk5_0,esk6_0,esk8_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),k1_relat_1(X1))
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_30,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( k1_relset_1(esk5_0,esk6_0,esk8_0) = k1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_18])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_2(esk8_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_33,negated_conjecture,
    ( ~ r2_hidden(esk2_4(esk8_0,X1,k9_relat_1(esk8_0,X1),esk9_0),esk5_0)
    | ~ r2_hidden(esk2_4(esk8_0,X1,k9_relat_1(esk8_0,X1),esk9_0),esk7_0)
    | ~ r2_hidden(esk9_0,k9_relat_1(esk8_0,X1)) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25])])])).

cnf(c_0_34,plain,
    ( r2_hidden(esk2_4(X1,X2,k9_relat_1(X1,X2),X3),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,k9_relat_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk9_0,k9_relat_1(esk8_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_18])])).

cnf(c_0_36,plain,
    ( r2_hidden(esk2_4(X1,X2,k9_relat_1(X1,X2),X3),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,k9_relat_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( k1_relat_1(esk8_0) = esk5_0
    | esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_18]),c_0_31]),c_0_32])])).

cnf(c_0_38,negated_conjecture,
    ( ~ r2_hidden(esk2_4(esk8_0,esk7_0,k9_relat_1(esk8_0,esk7_0),esk9_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_24]),c_0_25])])).

cnf(c_0_39,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk2_4(esk8_0,X1,k9_relat_1(esk8_0,X1),X2),esk5_0)
    | ~ r2_hidden(X2,k9_relat_1(esk8_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_24]),c_0_25])])).

fof(c_0_40,plain,(
    ! [X8,X9] :
      ( ( ~ m1_subset_1(X8,k1_zfmisc_1(X9))
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | m1_subset_1(X8,k1_zfmisc_1(X9)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_41,plain,(
    ! [X7] : r1_tarski(k1_xboole_0,X7) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_43,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_35])])).

fof(c_0_44,plain,(
    ! [X10,X11,X12] :
      ( ~ r2_hidden(X10,X11)
      | ~ m1_subset_1(X11,k1_zfmisc_1(X12))
      | ~ v1_xboole_0(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_45,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,k1_xboole_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_18,c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( v1_funct_2(esk8_0,esk5_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_32,c_0_43])).

cnf(c_0_50,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X2)
    | r2_hidden(esk3_3(X1,X2,X3),X3)
    | X3 = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_53,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_54,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])])).

cnf(c_0_55,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( X1 = k9_relat_1(esk8_0,X2)
    | r2_hidden(esk3_3(esk8_0,X2,X1),X1)
    | r2_hidden(esk4_3(esk8_0,X2,X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_24]),c_0_25])])).

cnf(c_0_57,negated_conjecture,
    ( k1_relset_1(esk5_0,k1_xboole_0,esk8_0) = k1_relat_1(esk8_0) ),
    inference(rw,[status(thm)],[c_0_31,c_0_43])).

cnf(c_0_58,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
    | ~ v1_funct_2(X2,k1_xboole_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(er,[status(thm)],[c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | v1_funct_2(esk8_0,k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( X1 = k9_relat_1(esk8_0,k1_xboole_0)
    | r2_hidden(esk3_3(esk8_0,k1_xboole_0,X1),X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_62,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_63,plain,(
    ! [X17,X18,X19,X21] :
      ( ( r2_hidden(esk1_3(X17,X18,X19),k1_relat_1(X19))
        | ~ r2_hidden(X17,k9_relat_1(X19,X18))
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(k4_tarski(esk1_3(X17,X18,X19),X17),X19)
        | ~ r2_hidden(X17,k9_relat_1(X19,X18))
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(esk1_3(X17,X18,X19),X18)
        | ~ r2_hidden(X17,k9_relat_1(X19,X18))
        | ~ v1_relat_1(X19) )
      & ( ~ r2_hidden(X21,k1_relat_1(X19))
        | ~ r2_hidden(k4_tarski(X21,X17),X19)
        | ~ r2_hidden(X21,X18)
        | r2_hidden(X17,k9_relat_1(X19,X18))
        | ~ v1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

cnf(c_0_64,negated_conjecture,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,esk8_0) = k1_relat_1(esk8_0)
    | esk8_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_54])).

cnf(c_0_65,negated_conjecture,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,esk8_0) = k1_xboole_0
    | esk8_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( X1 = k9_relat_1(esk8_0,k1_xboole_0)
    | r2_hidden(esk3_3(esk8_0,k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_67,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),k1_relat_1(X3))
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( k1_relat_1(esk8_0) = k1_xboole_0
    | esk8_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( k9_relat_1(esk8_0,k1_xboole_0) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_66])).

cnf(c_0_70,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | r2_hidden(esk1_3(X1,X2,esk8_0),k1_xboole_0)
    | ~ r2_hidden(X1,k9_relat_1(esk8_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_25])])).

cnf(c_0_71,plain,
    ( r2_hidden(k4_tarski(esk1_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_72,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_51])).

cnf(c_0_73,negated_conjecture,
    ( k9_relat_1(esk8_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_69,c_0_62])).

cnf(c_0_74,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | ~ r2_hidden(X1,k9_relat_1(esk8_0,X2))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_55,c_0_70])).

cnf(c_0_75,plain,
    ( ~ r2_hidden(X1,k9_relat_1(k1_xboole_0,X2))
    | ~ v1_xboole_0(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_71]),c_0_72])])).

cnf(c_0_76,negated_conjecture,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_3(esk8_0,k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[c_0_66,c_0_73])).

cnf(c_0_77,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_35])).

cnf(c_0_78,negated_conjecture,
    ( k9_relat_1(k1_xboole_0,X1) = k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_79,negated_conjecture,
    ( esk8_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_77,c_0_62])).

cnf(c_0_80,negated_conjecture,
    ( k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_78,c_0_62])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk9_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_79]),c_0_80])).

cnf(c_0_82,negated_conjecture,
    ( ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_81])).

cnf(c_0_83,plain,
    ( $false ),
    inference(sr,[status(thm)],[c_0_62,c_0_82]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:59:10 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.39  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.18/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.18/0.39  #
% 0.18/0.39  # Preprocessing time       : 0.029 s
% 0.18/0.39  
% 0.18/0.39  # Proof found!
% 0.18/0.39  # SZS status Theorem
% 0.18/0.39  # SZS output start CNFRefutation
% 0.18/0.39  fof(t115_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:~(((r2_hidden(X6,X1)&r2_hidden(X6,X3))&X5=k1_funct_1(X4,X6)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_funct_2)).
% 0.18/0.39  fof(d12_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(X3=k9_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((r2_hidden(X5,k1_relat_1(X1))&r2_hidden(X5,X2))&X4=k1_funct_1(X1,X5))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_1)).
% 0.18/0.39  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.18/0.39  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.18/0.39  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.18/0.39  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.18/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.18/0.39  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.18/0.39  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.18/0.39  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.18/0.39  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 0.18/0.39  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:~(((r2_hidden(X6,X1)&r2_hidden(X6,X3))&X5=k1_funct_1(X4,X6))))))), inference(assume_negation,[status(cth)],[t115_funct_2])).
% 0.18/0.39  fof(c_0_12, plain, ![X22, X23, X24, X25, X27, X28, X29, X30, X32]:(((((r2_hidden(esk2_4(X22,X23,X24,X25),k1_relat_1(X22))|~r2_hidden(X25,X24)|X24!=k9_relat_1(X22,X23)|(~v1_relat_1(X22)|~v1_funct_1(X22)))&(r2_hidden(esk2_4(X22,X23,X24,X25),X23)|~r2_hidden(X25,X24)|X24!=k9_relat_1(X22,X23)|(~v1_relat_1(X22)|~v1_funct_1(X22))))&(X25=k1_funct_1(X22,esk2_4(X22,X23,X24,X25))|~r2_hidden(X25,X24)|X24!=k9_relat_1(X22,X23)|(~v1_relat_1(X22)|~v1_funct_1(X22))))&(~r2_hidden(X28,k1_relat_1(X22))|~r2_hidden(X28,X23)|X27!=k1_funct_1(X22,X28)|r2_hidden(X27,X24)|X24!=k9_relat_1(X22,X23)|(~v1_relat_1(X22)|~v1_funct_1(X22))))&((~r2_hidden(esk3_3(X22,X29,X30),X30)|(~r2_hidden(X32,k1_relat_1(X22))|~r2_hidden(X32,X29)|esk3_3(X22,X29,X30)!=k1_funct_1(X22,X32))|X30=k9_relat_1(X22,X29)|(~v1_relat_1(X22)|~v1_funct_1(X22)))&(((r2_hidden(esk4_3(X22,X29,X30),k1_relat_1(X22))|r2_hidden(esk3_3(X22,X29,X30),X30)|X30=k9_relat_1(X22,X29)|(~v1_relat_1(X22)|~v1_funct_1(X22)))&(r2_hidden(esk4_3(X22,X29,X30),X29)|r2_hidden(esk3_3(X22,X29,X30),X30)|X30=k9_relat_1(X22,X29)|(~v1_relat_1(X22)|~v1_funct_1(X22))))&(esk3_3(X22,X29,X30)=k1_funct_1(X22,esk4_3(X22,X29,X30))|r2_hidden(esk3_3(X22,X29,X30),X30)|X30=k9_relat_1(X22,X29)|(~v1_relat_1(X22)|~v1_funct_1(X22)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).
% 0.18/0.39  fof(c_0_13, plain, ![X34, X35, X36]:(~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|v1_relat_1(X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.18/0.39  fof(c_0_14, negated_conjecture, ![X52]:(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,esk5_0,esk6_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))))&(r2_hidden(esk9_0,k7_relset_1(esk5_0,esk6_0,esk8_0,esk7_0))&(~r2_hidden(X52,esk5_0)|~r2_hidden(X52,esk7_0)|esk9_0!=k1_funct_1(esk8_0,X52)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).
% 0.18/0.39  fof(c_0_15, plain, ![X37, X38, X39]:(~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))|k1_relset_1(X37,X38,X39)=k1_relat_1(X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.18/0.39  cnf(c_0_16, plain, (X1=k1_funct_1(X2,esk2_4(X2,X3,X4,X1))|~r2_hidden(X1,X4)|X4!=k9_relat_1(X2,X3)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.39  cnf(c_0_17, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.39  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.39  fof(c_0_19, plain, ![X40, X41, X42, X43]:(~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|k7_relset_1(X40,X41,X42,X43)=k9_relat_1(X42,X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.18/0.39  fof(c_0_20, plain, ![X44, X45, X46]:((((~v1_funct_2(X46,X44,X45)|X44=k1_relset_1(X44,X45,X46)|X45=k1_xboole_0|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))))&(X44!=k1_relset_1(X44,X45,X46)|v1_funct_2(X46,X44,X45)|X45=k1_xboole_0|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))))&((~v1_funct_2(X46,X44,X45)|X44=k1_relset_1(X44,X45,X46)|X44!=k1_xboole_0|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))))&(X44!=k1_relset_1(X44,X45,X46)|v1_funct_2(X46,X44,X45)|X44!=k1_xboole_0|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))))))&((~v1_funct_2(X46,X44,X45)|X46=k1_xboole_0|X44=k1_xboole_0|X45!=k1_xboole_0|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))))&(X46!=k1_xboole_0|v1_funct_2(X46,X44,X45)|X44=k1_xboole_0|X45!=k1_xboole_0|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.18/0.39  cnf(c_0_21, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.39  cnf(c_0_22, negated_conjecture, (~r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk7_0)|esk9_0!=k1_funct_1(esk8_0,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.39  cnf(c_0_23, plain, (k1_funct_1(X1,esk2_4(X1,X2,k9_relat_1(X1,X2),X3))=X3|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X3,k9_relat_1(X1,X2))), inference(er,[status(thm)],[c_0_16])).
% 0.18/0.39  cnf(c_0_24, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.39  cnf(c_0_25, negated_conjecture, (v1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.18/0.39  cnf(c_0_26, plain, (r2_hidden(esk2_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.39  cnf(c_0_27, negated_conjecture, (r2_hidden(esk9_0,k7_relset_1(esk5_0,esk6_0,esk8_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.39  cnf(c_0_28, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.39  cnf(c_0_29, plain, (r2_hidden(esk2_4(X1,X2,X3,X4),k1_relat_1(X1))|~r2_hidden(X4,X3)|X3!=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.39  cnf(c_0_30, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.39  cnf(c_0_31, negated_conjecture, (k1_relset_1(esk5_0,esk6_0,esk8_0)=k1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_21, c_0_18])).
% 0.18/0.39  cnf(c_0_32, negated_conjecture, (v1_funct_2(esk8_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.39  cnf(c_0_33, negated_conjecture, (~r2_hidden(esk2_4(esk8_0,X1,k9_relat_1(esk8_0,X1),esk9_0),esk5_0)|~r2_hidden(esk2_4(esk8_0,X1,k9_relat_1(esk8_0,X1),esk9_0),esk7_0)|~r2_hidden(esk9_0,k9_relat_1(esk8_0,X1))), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25])])])).
% 0.18/0.39  cnf(c_0_34, plain, (r2_hidden(esk2_4(X1,X2,k9_relat_1(X1,X2),X3),X2)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X3,k9_relat_1(X1,X2))), inference(er,[status(thm)],[c_0_26])).
% 0.18/0.39  cnf(c_0_35, negated_conjecture, (r2_hidden(esk9_0,k9_relat_1(esk8_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_18])])).
% 0.18/0.39  cnf(c_0_36, plain, (r2_hidden(esk2_4(X1,X2,k9_relat_1(X1,X2),X3),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X3,k9_relat_1(X1,X2))), inference(er,[status(thm)],[c_0_29])).
% 0.18/0.39  cnf(c_0_37, negated_conjecture, (k1_relat_1(esk8_0)=esk5_0|esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_18]), c_0_31]), c_0_32])])).
% 0.18/0.39  cnf(c_0_38, negated_conjecture, (~r2_hidden(esk2_4(esk8_0,esk7_0,k9_relat_1(esk8_0,esk7_0),esk9_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_24]), c_0_25])])).
% 0.18/0.39  cnf(c_0_39, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk2_4(esk8_0,X1,k9_relat_1(esk8_0,X1),X2),esk5_0)|~r2_hidden(X2,k9_relat_1(esk8_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_24]), c_0_25])])).
% 0.18/0.39  fof(c_0_40, plain, ![X8, X9]:((~m1_subset_1(X8,k1_zfmisc_1(X9))|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|m1_subset_1(X8,k1_zfmisc_1(X9)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.18/0.39  fof(c_0_41, plain, ![X7]:r1_tarski(k1_xboole_0,X7), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.18/0.39  cnf(c_0_42, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X1,X2,X3)|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.39  cnf(c_0_43, negated_conjecture, (esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_35])])).
% 0.18/0.39  fof(c_0_44, plain, ![X10, X11, X12]:(~r2_hidden(X10,X11)|~m1_subset_1(X11,k1_zfmisc_1(X12))|~v1_xboole_0(X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.18/0.39  cnf(c_0_45, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.18/0.39  cnf(c_0_46, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.18/0.39  cnf(c_0_47, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X2,X1,k1_xboole_0)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))), inference(er,[status(thm)],[c_0_42])).
% 0.18/0.39  cnf(c_0_48, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_xboole_0)))), inference(rw,[status(thm)],[c_0_18, c_0_43])).
% 0.18/0.39  cnf(c_0_49, negated_conjecture, (v1_funct_2(esk8_0,esk5_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_32, c_0_43])).
% 0.18/0.39  cnf(c_0_50, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.18/0.39  cnf(c_0_51, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.18/0.39  cnf(c_0_52, plain, (r2_hidden(esk4_3(X1,X2,X3),X2)|r2_hidden(esk3_3(X1,X2,X3),X3)|X3=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.39  cnf(c_0_53, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.39  cnf(c_0_54, negated_conjecture, (esk8_0=k1_xboole_0|esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])])).
% 0.18/0.39  cnf(c_0_55, plain, (~r2_hidden(X1,k1_xboole_0)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.18/0.39  cnf(c_0_56, negated_conjecture, (X1=k9_relat_1(esk8_0,X2)|r2_hidden(esk3_3(esk8_0,X2,X1),X1)|r2_hidden(esk4_3(esk8_0,X2,X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_24]), c_0_25])])).
% 0.18/0.39  cnf(c_0_57, negated_conjecture, (k1_relset_1(esk5_0,k1_xboole_0,esk8_0)=k1_relat_1(esk8_0)), inference(rw,[status(thm)],[c_0_31, c_0_43])).
% 0.18/0.39  cnf(c_0_58, plain, (k1_relset_1(k1_xboole_0,X1,X2)=k1_xboole_0|~v1_funct_2(X2,k1_xboole_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(er,[status(thm)],[c_0_53])).
% 0.18/0.39  cnf(c_0_59, negated_conjecture, (esk8_0=k1_xboole_0|m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_48, c_0_54])).
% 0.18/0.39  cnf(c_0_60, negated_conjecture, (esk8_0=k1_xboole_0|v1_funct_2(esk8_0,k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_49, c_0_54])).
% 0.18/0.39  cnf(c_0_61, negated_conjecture, (X1=k9_relat_1(esk8_0,k1_xboole_0)|r2_hidden(esk3_3(esk8_0,k1_xboole_0,X1),X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.18/0.39  cnf(c_0_62, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.18/0.39  fof(c_0_63, plain, ![X17, X18, X19, X21]:((((r2_hidden(esk1_3(X17,X18,X19),k1_relat_1(X19))|~r2_hidden(X17,k9_relat_1(X19,X18))|~v1_relat_1(X19))&(r2_hidden(k4_tarski(esk1_3(X17,X18,X19),X17),X19)|~r2_hidden(X17,k9_relat_1(X19,X18))|~v1_relat_1(X19)))&(r2_hidden(esk1_3(X17,X18,X19),X18)|~r2_hidden(X17,k9_relat_1(X19,X18))|~v1_relat_1(X19)))&(~r2_hidden(X21,k1_relat_1(X19))|~r2_hidden(k4_tarski(X21,X17),X19)|~r2_hidden(X21,X18)|r2_hidden(X17,k9_relat_1(X19,X18))|~v1_relat_1(X19))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.18/0.39  cnf(c_0_64, negated_conjecture, (k1_relset_1(k1_xboole_0,k1_xboole_0,esk8_0)=k1_relat_1(esk8_0)|esk8_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_57, c_0_54])).
% 0.18/0.39  cnf(c_0_65, negated_conjecture, (k1_relset_1(k1_xboole_0,k1_xboole_0,esk8_0)=k1_xboole_0|esk8_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])).
% 0.18/0.39  cnf(c_0_66, negated_conjecture, (X1=k9_relat_1(esk8_0,k1_xboole_0)|r2_hidden(esk3_3(esk8_0,k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.18/0.39  cnf(c_0_67, plain, (r2_hidden(esk1_3(X1,X2,X3),k1_relat_1(X3))|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.18/0.39  cnf(c_0_68, negated_conjecture, (k1_relat_1(esk8_0)=k1_xboole_0|esk8_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.18/0.39  cnf(c_0_69, negated_conjecture, (k9_relat_1(esk8_0,k1_xboole_0)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_55, c_0_66])).
% 0.18/0.39  cnf(c_0_70, negated_conjecture, (esk8_0=k1_xboole_0|r2_hidden(esk1_3(X1,X2,esk8_0),k1_xboole_0)|~r2_hidden(X1,k9_relat_1(esk8_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_25])])).
% 0.18/0.39  cnf(c_0_71, plain, (r2_hidden(k4_tarski(esk1_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.18/0.39  cnf(c_0_72, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_17, c_0_51])).
% 0.18/0.39  cnf(c_0_73, negated_conjecture, (k9_relat_1(esk8_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_69, c_0_62])).
% 0.18/0.39  cnf(c_0_74, negated_conjecture, (esk8_0=k1_xboole_0|~r2_hidden(X1,k9_relat_1(esk8_0,X2))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_55, c_0_70])).
% 0.18/0.39  cnf(c_0_75, plain, (~r2_hidden(X1,k9_relat_1(k1_xboole_0,X2))|~v1_xboole_0(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_71]), c_0_72])])).
% 0.18/0.39  cnf(c_0_76, negated_conjecture, (X1=k1_xboole_0|r2_hidden(esk3_3(esk8_0,k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[c_0_66, c_0_73])).
% 0.18/0.39  cnf(c_0_77, negated_conjecture, (esk8_0=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_74, c_0_35])).
% 0.18/0.39  cnf(c_0_78, negated_conjecture, (k9_relat_1(k1_xboole_0,X1)=k1_xboole_0|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.18/0.39  cnf(c_0_79, negated_conjecture, (esk8_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_77, c_0_62])).
% 0.18/0.39  cnf(c_0_80, negated_conjecture, (k9_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_78, c_0_62])).
% 0.18/0.39  cnf(c_0_81, negated_conjecture, (r2_hidden(esk9_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_79]), c_0_80])).
% 0.18/0.39  cnf(c_0_82, negated_conjecture, (~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_55, c_0_81])).
% 0.18/0.39  cnf(c_0_83, plain, ($false), inference(sr,[status(thm)],[c_0_62, c_0_82]), ['proof']).
% 0.18/0.39  # SZS output end CNFRefutation
% 0.18/0.39  # Proof object total steps             : 84
% 0.18/0.39  # Proof object clause steps            : 62
% 0.18/0.39  # Proof object formula steps           : 22
% 0.18/0.39  # Proof object conjectures             : 39
% 0.18/0.39  # Proof object clause conjectures      : 36
% 0.18/0.39  # Proof object formula conjectures     : 3
% 0.18/0.39  # Proof object initial clauses used    : 21
% 0.18/0.39  # Proof object initial formulas used   : 11
% 0.18/0.39  # Proof object generating inferences   : 30
% 0.18/0.39  # Proof object simplifying inferences  : 39
% 0.18/0.39  # Training examples: 0 positive, 0 negative
% 0.18/0.39  # Parsed axioms                        : 13
% 0.18/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.39  # Initial clauses                      : 33
% 0.18/0.39  # Removed in clause preprocessing      : 0
% 0.18/0.39  # Initial clauses in saturation        : 33
% 0.18/0.39  # Processed clauses                    : 294
% 0.18/0.39  # ...of these trivial                  : 1
% 0.18/0.39  # ...subsumed                          : 138
% 0.18/0.39  # ...remaining for further processing  : 155
% 0.18/0.39  # Other redundant clauses eliminated   : 17
% 0.18/0.39  # Clauses deleted for lack of memory   : 0
% 0.18/0.39  # Backward-subsumed                    : 16
% 0.18/0.39  # Backward-rewritten                   : 73
% 0.18/0.39  # Generated clauses                    : 782
% 0.18/0.39  # ...of the previous two non-trivial   : 777
% 0.18/0.39  # Contextual simplify-reflections      : 1
% 0.18/0.39  # Paramodulations                      : 766
% 0.18/0.39  # Factorizations                       : 0
% 0.18/0.39  # Equation resolutions                 : 17
% 0.18/0.39  # Propositional unsat checks           : 0
% 0.18/0.39  #    Propositional check models        : 0
% 0.18/0.39  #    Propositional check unsatisfiable : 0
% 0.18/0.39  #    Propositional clauses             : 0
% 0.18/0.39  #    Propositional clauses after purity: 0
% 0.18/0.39  #    Propositional unsat core size     : 0
% 0.18/0.39  #    Propositional preprocessing time  : 0.000
% 0.18/0.39  #    Propositional encoding time       : 0.000
% 0.18/0.39  #    Propositional solver time         : 0.000
% 0.18/0.39  #    Success case prop preproc time    : 0.000
% 0.18/0.39  #    Success case prop encoding time   : 0.000
% 0.18/0.39  #    Success case prop solver time     : 0.000
% 0.18/0.39  # Current number of processed clauses  : 57
% 0.18/0.39  #    Positive orientable unit clauses  : 11
% 0.18/0.39  #    Positive unorientable unit clauses: 0
% 0.18/0.39  #    Negative unit clauses             : 3
% 0.18/0.39  #    Non-unit-clauses                  : 43
% 0.18/0.39  # Current number of unprocessed clauses: 488
% 0.18/0.39  # ...number of literals in the above   : 2675
% 0.18/0.39  # Current number of archived formulas  : 0
% 0.18/0.39  # Current number of archived clauses   : 90
% 0.18/0.39  # Clause-clause subsumption calls (NU) : 1192
% 0.18/0.39  # Rec. Clause-clause subsumption calls : 632
% 0.18/0.39  # Non-unit clause-clause subsumptions  : 155
% 0.18/0.39  # Unit Clause-clause subsumption calls : 51
% 0.18/0.39  # Rewrite failures with RHS unbound    : 0
% 0.18/0.39  # BW rewrite match attempts            : 10
% 0.18/0.39  # BW rewrite match successes           : 8
% 0.18/0.39  # Condensation attempts                : 0
% 0.18/0.39  # Condensation successes               : 0
% 0.18/0.39  # Termbank termtop insertions          : 17942
% 0.18/0.39  
% 0.18/0.39  # -------------------------------------------------
% 0.18/0.39  # User time                : 0.055 s
% 0.18/0.39  # System time              : 0.004 s
% 0.18/0.39  # Total time               : 0.059 s
% 0.18/0.39  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
