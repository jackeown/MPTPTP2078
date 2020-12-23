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
% DateTime   : Thu Dec  3 11:01:34 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  117 (262729 expanded)
%              Number of clauses        :   92 (103913 expanded)
%              Number of leaves         :   12 (65311 expanded)
%              Depth                    :   33
%              Number of atoms          :  388 (1232323 expanded)
%              Number of equality atoms :  112 (318069 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(t12_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => r2_hidden(k1_funct_1(X2,X1),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(d5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( X2 = k2_relat_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                  & X3 = k1_funct_1(X1,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_12,negated_conjecture,(
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

fof(c_0_13,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(X13))
      | v1_relat_1(X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_14,negated_conjecture,(
    ! [X46] :
      ( v1_funct_1(esk7_0)
      & v1_funct_2(esk7_0,esk5_0,esk6_0)
      & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
      & ( r2_hidden(esk8_1(X46),esk5_0)
        | ~ r2_hidden(X46,esk6_0) )
      & ( X46 = k1_funct_1(esk7_0,esk8_1(X46))
        | ~ r2_hidden(X46,esk6_0) )
      & k2_relset_1(esk5_0,esk6_0,esk7_0) != esk6_0 ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])])).

fof(c_0_15,plain,(
    ! [X17,X18] : v1_relat_1(k2_zfmisc_1(X17,X18)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_16,plain,(
    ! [X40,X41,X42] :
      ( ( ~ v1_funct_2(X42,X40,X41)
        | X40 = k1_relset_1(X40,X41,X42)
        | X41 = k1_xboole_0
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) )
      & ( X40 != k1_relset_1(X40,X41,X42)
        | v1_funct_2(X42,X40,X41)
        | X41 = k1_xboole_0
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) )
      & ( ~ v1_funct_2(X42,X40,X41)
        | X40 = k1_relset_1(X40,X41,X42)
        | X40 != k1_xboole_0
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) )
      & ( X40 != k1_relset_1(X40,X41,X42)
        | v1_funct_2(X42,X40,X41)
        | X40 != k1_xboole_0
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) )
      & ( ~ v1_funct_2(X42,X40,X41)
        | X42 = k1_xboole_0
        | X40 = k1_xboole_0
        | X41 != k1_xboole_0
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) )
      & ( X42 != k1_xboole_0
        | v1_funct_2(X42,X40,X41)
        | X40 = k1_xboole_0
        | X41 != k1_xboole_0
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_17,plain,(
    ! [X29,X30] :
      ( ~ v1_relat_1(X30)
      | ~ v1_funct_1(X30)
      | ~ r2_hidden(X29,k1_relat_1(X30))
      | r2_hidden(k1_funct_1(X30,X29),k2_relat_1(X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_1])])).

cnf(c_0_18,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X34,X35,X36] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
      | k1_relset_1(X34,X35,X36) = k1_relat_1(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_22,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_2(esk7_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( X1 = k1_funct_1(esk7_0,esk8_1(X1))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_27,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

cnf(c_0_28,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( k1_relset_1(esk5_0,esk6_0,esk7_0) = esk5_0
    | esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_19]),c_0_23])])).

fof(c_0_30,plain,(
    ! [X19,X20,X21,X23,X24,X25,X27] :
      ( ( r2_hidden(esk2_3(X19,X20,X21),k1_relat_1(X19))
        | ~ r2_hidden(X21,X20)
        | X20 != k2_relat_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( X21 = k1_funct_1(X19,esk2_3(X19,X20,X21))
        | ~ r2_hidden(X21,X20)
        | X20 != k2_relat_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( ~ r2_hidden(X24,k1_relat_1(X19))
        | X23 != k1_funct_1(X19,X24)
        | r2_hidden(X23,X20)
        | X20 != k2_relat_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( ~ r2_hidden(esk3_2(X19,X25),X25)
        | ~ r2_hidden(X27,k1_relat_1(X19))
        | esk3_2(X19,X25) != k1_funct_1(X19,X27)
        | X25 = k2_relat_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( r2_hidden(esk4_2(X19,X25),k1_relat_1(X19))
        | r2_hidden(esk3_2(X19,X25),X25)
        | X25 = k2_relat_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( esk3_2(X19,X25) = k1_funct_1(X19,esk4_2(X19,X25))
        | r2_hidden(esk3_2(X19,X25),X25)
        | X25 = k2_relat_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(X1,k2_relat_1(esk7_0))
    | ~ r2_hidden(esk8_1(X1),k1_relat_1(esk7_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27])])).

cnf(c_0_32,negated_conjecture,
    ( k1_relat_1(esk7_0) = esk5_0
    | esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_19])])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk8_1(X1),esk5_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_34,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_35,plain,
    ( r2_hidden(esk4_2(X1,X2),k1_relat_1(X1))
    | r2_hidden(esk3_2(X1,X2),X2)
    | X2 = k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(X1,k2_relat_1(esk7_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_37,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_38,plain,(
    ! [X37,X38,X39] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
      | k2_relset_1(X37,X38,X39) = k2_relat_1(X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_39,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( X1 = k2_relat_1(esk7_0)
    | r2_hidden(esk4_2(esk7_0,X1),k1_relat_1(esk7_0))
    | r2_hidden(esk3_2(esk7_0,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_26]),c_0_27])])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk1_2(esk6_0,X1),k2_relat_1(esk7_0))
    | r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( k2_relset_1(esk5_0,esk6_0,esk7_0) != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_44,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_45,plain,(
    ! [X15,X16] :
      ( ( ~ v5_relat_1(X16,X15)
        | r1_tarski(k2_relat_1(X16),X15)
        | ~ v1_relat_1(X16) )
      & ( ~ r1_tarski(k2_relat_1(X16),X15)
        | v5_relat_1(X16,X15)
        | ~ v1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

fof(c_0_46,plain,(
    ! [X31,X32,X33] :
      ( ( v4_relat_1(X33,X31)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( v5_relat_1(X33,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_47,negated_conjecture,
    ( X1 = k2_relat_1(esk7_0)
    | r2_hidden(esk4_2(esk7_0,X1),k1_relat_1(esk7_0))
    | r2_hidden(esk3_2(esk7_0,X1),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r1_tarski(esk6_0,k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( k2_relat_1(esk7_0) != esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_19])])).

cnf(c_0_50,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_39,c_0_37])).

cnf(c_0_51,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_39,c_0_24])).

cnf(c_0_54,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk3_2(esk7_0,esk6_0),k2_relat_1(esk7_0))
    | r2_hidden(esk4_2(esk7_0,esk6_0),k1_relat_1(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

cnf(c_0_55,plain,
    ( r2_hidden(esk1_2(k2_relat_1(X1),X2),X3)
    | r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( v5_relat_1(esk7_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_19])).

cnf(c_0_57,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(k1_funct_1(esk7_0,X1),X2)
    | ~ r2_hidden(X1,esk5_0)
    | ~ r1_tarski(k2_relat_1(esk7_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_32]),c_0_26]),c_0_27])])).

cnf(c_0_58,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk3_2(esk7_0,esk6_0),k2_relat_1(esk7_0))
    | r2_hidden(esk4_2(esk7_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_32])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk7_0),X1),esk6_0)
    | r1_tarski(k2_relat_1(esk7_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_27])])).

cnf(c_0_60,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(k1_funct_1(esk7_0,X1),X2)
    | ~ v5_relat_1(esk7_0,X2)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_51]),c_0_27])])).

cnf(c_0_61,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk4_2(esk7_0,esk6_0),esk5_0)
    | r2_hidden(esk3_2(esk7_0,esk6_0),X1)
    | ~ r1_tarski(k2_relat_1(esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk7_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(k1_funct_1(esk7_0,X1),esk6_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk3_2(esk7_0,esk6_0),esk6_0)
    | r2_hidden(esk4_2(esk7_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_65,plain,
    ( esk3_2(X1,X2) = k1_funct_1(X1,esk4_2(X1,X2))
    | r2_hidden(esk3_2(X1,X2),X2)
    | X2 = k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_66,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(k1_funct_1(esk7_0,esk4_2(esk7_0,esk6_0)),esk6_0)
    | r2_hidden(esk3_2(esk7_0,esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_67,negated_conjecture,
    ( k1_funct_1(esk7_0,esk4_2(esk7_0,X1)) = esk3_2(esk7_0,X1)
    | X1 = k2_relat_1(esk7_0)
    | r2_hidden(esk3_2(esk7_0,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_26]),c_0_27])])).

cnf(c_0_68,plain,
    ( X2 = k2_relat_1(X1)
    | ~ r2_hidden(esk3_2(X1,X2),X2)
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | esk3_2(X1,X2) != k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_69,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk3_2(esk7_0,esk6_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_49])).

cnf(c_0_70,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk3_2(esk7_0,esk6_0) != k1_funct_1(esk7_0,X1)
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_26]),c_0_27])]),c_0_49])).

cnf(c_0_71,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk3_2(esk7_0,esk6_0) != k1_funct_1(esk7_0,X1)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_32])).

cnf(c_0_72,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | ~ r2_hidden(esk8_1(esk3_2(esk7_0,esk6_0)),esk5_0) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_25])]),c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk8_1(X1),X2)
    | ~ r2_hidden(X1,esk6_0)
    | ~ r1_tarski(esk5_0,X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_33])).

cnf(c_0_74,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_37])).

fof(c_0_75,plain,(
    ! [X12] : r1_tarski(k1_xboole_0,X12) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk7_0),X1),X2)
    | r1_tarski(k2_relat_1(esk7_0),X1)
    | ~ r1_tarski(esk6_0,X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_59])).

cnf(c_0_77,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74])]),c_0_69])).

cnf(c_0_78,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(k1_funct_1(X1,esk8_1(X2)),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,esk6_0)
    | ~ r1_tarski(esk5_0,k1_relat_1(X1))
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_53,c_0_73])).

cnf(c_0_80,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk7_0),X1),X2)
    | r1_tarski(k2_relat_1(esk7_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_77]),c_0_78])])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,esk6_0)
    | ~ r1_tarski(esk5_0,k1_relat_1(esk7_0))
    | ~ r1_tarski(k2_relat_1(esk7_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_25]),c_0_26]),c_0_27])])).

cnf(c_0_83,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,k1_xboole_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) ),
    inference(er,[status(thm)],[c_0_80])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_19,c_0_77])).

cnf(c_0_85,negated_conjecture,
    ( v1_funct_2(esk7_0,esk5_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_23,c_0_77])).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_81])).

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0)
    | ~ r1_tarski(esk5_0,k1_relat_1(esk7_0))
    | ~ r1_tarski(k2_relat_1(esk7_0),X2) ),
    inference(rw,[status(thm)],[c_0_82,c_0_77])).

cnf(c_0_88,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85])])).

cnf(c_0_89,negated_conjecture,
    ( X1 = k2_relat_1(esk7_0)
    | r2_hidden(k1_funct_1(esk7_0,esk4_2(esk7_0,X1)),X2)
    | r2_hidden(esk3_2(esk7_0,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_40]),c_0_26]),c_0_27])]),c_0_86])])).

cnf(c_0_90,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0)
    | ~ r1_tarski(k2_relat_1(esk7_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_78])])).

cnf(c_0_91,negated_conjecture,
    ( X1 = k2_relat_1(esk7_0)
    | r2_hidden(esk3_2(esk7_0,X1),X1)
    | r2_hidden(esk3_2(esk7_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_89,c_0_67])).

cnf(c_0_92,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_86])])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(esk8_1(X1),X2)
    | ~ r2_hidden(X1,k1_xboole_0)
    | ~ r1_tarski(esk5_0,X2) ),
    inference(rw,[status(thm)],[c_0_73,c_0_77])).

cnf(c_0_94,negated_conjecture,
    ( X1 = k2_relat_1(esk7_0)
    | r2_hidden(esk3_2(esk7_0,X1),X1) ),
    inference(ef,[status(thm)],[c_0_91])).

cnf(c_0_95,negated_conjecture,
    ( k2_relat_1(esk7_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_49,c_0_77])).

cnf(c_0_96,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk8_1(X1),X2)
    | ~ r2_hidden(X1,k1_xboole_0)
    | ~ r1_tarski(esk5_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_97,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk3_2(esk7_0,k1_xboole_0),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_94]),c_0_95])).

cnf(c_0_98,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk8_1(X1),X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_88]),c_0_78])])).

cnf(c_0_99,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk3_2(esk7_0,k1_xboole_0) != k1_funct_1(esk7_0,X1)
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_97]),c_0_26]),c_0_27])]),c_0_95])).

cnf(c_0_100,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk8_1(esk3_2(esk7_0,k1_xboole_0)),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_94]),c_0_95])).

cnf(c_0_101,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | k1_funct_1(esk7_0,esk8_1(esk3_2(esk7_0,k1_xboole_0))) != esk3_2(esk7_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_102,negated_conjecture,
    ( k1_funct_1(esk7_0,esk8_1(X1)) = X1
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_25,c_0_77])).

cnf(c_0_103,negated_conjecture,
    ( esk7_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_97])).

cnf(c_0_104,negated_conjecture,
    ( X1 = k2_relat_1(k1_xboole_0)
    | r2_hidden(esk3_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_103]),c_0_103])).

cnf(c_0_105,negated_conjecture,
    ( X1 = k2_relat_1(k1_xboole_0)
    | r2_hidden(esk3_2(k1_xboole_0,X1),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_104])).

cnf(c_0_106,negated_conjecture,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_95,c_0_103])).

cnf(c_0_107,negated_conjecture,
    ( r2_hidden(esk3_2(k1_xboole_0,k1_xboole_0),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_78]),c_0_106])).

cnf(c_0_108,negated_conjecture,
    ( v1_funct_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_26,c_0_103])).

cnf(c_0_109,negated_conjecture,
    ( v1_relat_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_27,c_0_103])).

cnf(c_0_110,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_111,negated_conjecture,
    ( esk3_2(k1_xboole_0,k1_xboole_0) != k1_funct_1(k1_xboole_0,X1)
    | ~ r2_hidden(X1,k1_relat_1(k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_107]),c_0_108]),c_0_109])]),c_0_106])).

cnf(c_0_112,plain,
    ( r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_110])).

cnf(c_0_113,plain,
    ( X1 = k1_funct_1(X2,esk2_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_114,negated_conjecture,
    ( k1_funct_1(k1_xboole_0,esk2_3(k1_xboole_0,k2_relat_1(k1_xboole_0),X1)) != esk3_2(k1_xboole_0,k1_xboole_0)
    | ~ r2_hidden(X1,k2_relat_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_108]),c_0_109])])).

cnf(c_0_115,plain,
    ( k1_funct_1(X1,esk2_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_113])).

cnf(c_0_116,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_115]),c_0_108]),c_0_109])])]),c_0_107])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:11:30 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.41  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.029 s
% 0.19/0.41  # Presaturation interreduction done
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(t16_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~((r2_hidden(X5,X1)&X4=k1_funct_1(X3,X5)))))=>k2_relset_1(X1,X2,X3)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_2)).
% 0.19/0.41  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.19/0.41  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.19/0.41  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.19/0.41  fof(t12_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r2_hidden(X1,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X1),k2_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 0.19/0.41  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.41  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 0.19/0.41  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.41  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.19/0.41  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.19/0.41  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.41  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.41  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~((r2_hidden(X5,X1)&X4=k1_funct_1(X3,X5)))))=>k2_relset_1(X1,X2,X3)=X2))), inference(assume_negation,[status(cth)],[t16_funct_2])).
% 0.19/0.41  fof(c_0_13, plain, ![X13, X14]:(~v1_relat_1(X13)|(~m1_subset_1(X14,k1_zfmisc_1(X13))|v1_relat_1(X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.19/0.41  fof(c_0_14, negated_conjecture, ![X46]:(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,esk5_0,esk6_0))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))))&(((r2_hidden(esk8_1(X46),esk5_0)|~r2_hidden(X46,esk6_0))&(X46=k1_funct_1(esk7_0,esk8_1(X46))|~r2_hidden(X46,esk6_0)))&k2_relset_1(esk5_0,esk6_0,esk7_0)!=esk6_0)), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])])).
% 0.19/0.41  fof(c_0_15, plain, ![X17, X18]:v1_relat_1(k2_zfmisc_1(X17,X18)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.19/0.41  fof(c_0_16, plain, ![X40, X41, X42]:((((~v1_funct_2(X42,X40,X41)|X40=k1_relset_1(X40,X41,X42)|X41=k1_xboole_0|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))))&(X40!=k1_relset_1(X40,X41,X42)|v1_funct_2(X42,X40,X41)|X41=k1_xboole_0|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))))&((~v1_funct_2(X42,X40,X41)|X40=k1_relset_1(X40,X41,X42)|X40!=k1_xboole_0|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))))&(X40!=k1_relset_1(X40,X41,X42)|v1_funct_2(X42,X40,X41)|X40!=k1_xboole_0|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))))))&((~v1_funct_2(X42,X40,X41)|X42=k1_xboole_0|X40=k1_xboole_0|X41!=k1_xboole_0|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))))&(X42!=k1_xboole_0|v1_funct_2(X42,X40,X41)|X40=k1_xboole_0|X41!=k1_xboole_0|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.19/0.41  fof(c_0_17, plain, ![X29, X30]:(~v1_relat_1(X30)|~v1_funct_1(X30)|(~r2_hidden(X29,k1_relat_1(X30))|r2_hidden(k1_funct_1(X30,X29),k2_relat_1(X30)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_1])])).
% 0.19/0.41  cnf(c_0_18, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.41  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.41  cnf(c_0_20, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.41  fof(c_0_21, plain, ![X34, X35, X36]:(~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|k1_relset_1(X34,X35,X36)=k1_relat_1(X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.41  cnf(c_0_22, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.41  cnf(c_0_23, negated_conjecture, (v1_funct_2(esk7_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.41  cnf(c_0_24, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.41  cnf(c_0_25, negated_conjecture, (X1=k1_funct_1(esk7_0,esk8_1(X1))|~r2_hidden(X1,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.41  cnf(c_0_26, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.41  cnf(c_0_27, negated_conjecture, (v1_relat_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])])).
% 0.19/0.41  cnf(c_0_28, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.41  cnf(c_0_29, negated_conjecture, (k1_relset_1(esk5_0,esk6_0,esk7_0)=esk5_0|esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_19]), c_0_23])])).
% 0.19/0.41  fof(c_0_30, plain, ![X19, X20, X21, X23, X24, X25, X27]:((((r2_hidden(esk2_3(X19,X20,X21),k1_relat_1(X19))|~r2_hidden(X21,X20)|X20!=k2_relat_1(X19)|(~v1_relat_1(X19)|~v1_funct_1(X19)))&(X21=k1_funct_1(X19,esk2_3(X19,X20,X21))|~r2_hidden(X21,X20)|X20!=k2_relat_1(X19)|(~v1_relat_1(X19)|~v1_funct_1(X19))))&(~r2_hidden(X24,k1_relat_1(X19))|X23!=k1_funct_1(X19,X24)|r2_hidden(X23,X20)|X20!=k2_relat_1(X19)|(~v1_relat_1(X19)|~v1_funct_1(X19))))&((~r2_hidden(esk3_2(X19,X25),X25)|(~r2_hidden(X27,k1_relat_1(X19))|esk3_2(X19,X25)!=k1_funct_1(X19,X27))|X25=k2_relat_1(X19)|(~v1_relat_1(X19)|~v1_funct_1(X19)))&((r2_hidden(esk4_2(X19,X25),k1_relat_1(X19))|r2_hidden(esk3_2(X19,X25),X25)|X25=k2_relat_1(X19)|(~v1_relat_1(X19)|~v1_funct_1(X19)))&(esk3_2(X19,X25)=k1_funct_1(X19,esk4_2(X19,X25))|r2_hidden(esk3_2(X19,X25),X25)|X25=k2_relat_1(X19)|(~v1_relat_1(X19)|~v1_funct_1(X19)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.19/0.41  cnf(c_0_31, negated_conjecture, (r2_hidden(X1,k2_relat_1(esk7_0))|~r2_hidden(esk8_1(X1),k1_relat_1(esk7_0))|~r2_hidden(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27])])).
% 0.19/0.41  cnf(c_0_32, negated_conjecture, (k1_relat_1(esk7_0)=esk5_0|esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_19])])).
% 0.19/0.41  cnf(c_0_33, negated_conjecture, (r2_hidden(esk8_1(X1),esk5_0)|~r2_hidden(X1,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.41  fof(c_0_34, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.41  cnf(c_0_35, plain, (r2_hidden(esk4_2(X1,X2),k1_relat_1(X1))|r2_hidden(esk3_2(X1,X2),X2)|X2=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.41  cnf(c_0_36, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(X1,k2_relat_1(esk7_0))|~r2_hidden(X1,esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])).
% 0.19/0.41  cnf(c_0_37, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.41  fof(c_0_38, plain, ![X37, X38, X39]:(~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))|k2_relset_1(X37,X38,X39)=k2_relat_1(X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.19/0.41  cnf(c_0_39, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.41  cnf(c_0_40, negated_conjecture, (X1=k2_relat_1(esk7_0)|r2_hidden(esk4_2(esk7_0,X1),k1_relat_1(esk7_0))|r2_hidden(esk3_2(esk7_0,X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_26]), c_0_27])])).
% 0.19/0.41  cnf(c_0_41, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.41  cnf(c_0_42, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk1_2(esk6_0,X1),k2_relat_1(esk7_0))|r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.41  cnf(c_0_43, negated_conjecture, (k2_relset_1(esk5_0,esk6_0,esk7_0)!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.41  cnf(c_0_44, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.41  fof(c_0_45, plain, ![X15, X16]:((~v5_relat_1(X16,X15)|r1_tarski(k2_relat_1(X16),X15)|~v1_relat_1(X16))&(~r1_tarski(k2_relat_1(X16),X15)|v5_relat_1(X16,X15)|~v1_relat_1(X16))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.19/0.41  fof(c_0_46, plain, ![X31, X32, X33]:((v4_relat_1(X33,X31)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))&(v5_relat_1(X33,X32)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.41  cnf(c_0_47, negated_conjecture, (X1=k2_relat_1(esk7_0)|r2_hidden(esk4_2(esk7_0,X1),k1_relat_1(esk7_0))|r2_hidden(esk3_2(esk7_0,X1),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.41  cnf(c_0_48, negated_conjecture, (esk6_0=k1_xboole_0|r1_tarski(esk6_0,k2_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.41  cnf(c_0_49, negated_conjecture, (k2_relat_1(esk7_0)!=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_19])])).
% 0.19/0.41  cnf(c_0_50, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_39, c_0_37])).
% 0.19/0.41  cnf(c_0_51, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.41  cnf(c_0_52, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.41  cnf(c_0_53, plain, (r2_hidden(k1_funct_1(X1,X2),X3)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~r1_tarski(k2_relat_1(X1),X3)), inference(spm,[status(thm)],[c_0_39, c_0_24])).
% 0.19/0.41  cnf(c_0_54, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk3_2(esk7_0,esk6_0),k2_relat_1(esk7_0))|r2_hidden(esk4_2(esk7_0,esk6_0),k1_relat_1(esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])).
% 0.19/0.41  cnf(c_0_55, plain, (r2_hidden(esk1_2(k2_relat_1(X1),X2),X3)|r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X3)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.19/0.41  cnf(c_0_56, negated_conjecture, (v5_relat_1(esk7_0,esk6_0)), inference(spm,[status(thm)],[c_0_52, c_0_19])).
% 0.19/0.41  cnf(c_0_57, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(k1_funct_1(esk7_0,X1),X2)|~r2_hidden(X1,esk5_0)|~r1_tarski(k2_relat_1(esk7_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_32]), c_0_26]), c_0_27])])).
% 0.19/0.41  cnf(c_0_58, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk3_2(esk7_0,esk6_0),k2_relat_1(esk7_0))|r2_hidden(esk4_2(esk7_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_54, c_0_32])).
% 0.19/0.41  cnf(c_0_59, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk7_0),X1),esk6_0)|r1_tarski(k2_relat_1(esk7_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_27])])).
% 0.19/0.41  cnf(c_0_60, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(k1_funct_1(esk7_0,X1),X2)|~v5_relat_1(esk7_0,X2)|~r2_hidden(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_51]), c_0_27])])).
% 0.19/0.41  cnf(c_0_61, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk4_2(esk7_0,esk6_0),esk5_0)|r2_hidden(esk3_2(esk7_0,esk6_0),X1)|~r1_tarski(k2_relat_1(esk7_0),X1)), inference(spm,[status(thm)],[c_0_39, c_0_58])).
% 0.19/0.41  cnf(c_0_62, negated_conjecture, (r1_tarski(k2_relat_1(esk7_0),esk6_0)), inference(spm,[status(thm)],[c_0_41, c_0_59])).
% 0.19/0.41  cnf(c_0_63, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(k1_funct_1(esk7_0,X1),esk6_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_60, c_0_56])).
% 0.19/0.41  cnf(c_0_64, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk3_2(esk7_0,esk6_0),esk6_0)|r2_hidden(esk4_2(esk7_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.19/0.41  cnf(c_0_65, plain, (esk3_2(X1,X2)=k1_funct_1(X1,esk4_2(X1,X2))|r2_hidden(esk3_2(X1,X2),X2)|X2=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.41  cnf(c_0_66, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(k1_funct_1(esk7_0,esk4_2(esk7_0,esk6_0)),esk6_0)|r2_hidden(esk3_2(esk7_0,esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.19/0.41  cnf(c_0_67, negated_conjecture, (k1_funct_1(esk7_0,esk4_2(esk7_0,X1))=esk3_2(esk7_0,X1)|X1=k2_relat_1(esk7_0)|r2_hidden(esk3_2(esk7_0,X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_26]), c_0_27])])).
% 0.19/0.41  cnf(c_0_68, plain, (X2=k2_relat_1(X1)|~r2_hidden(esk3_2(X1,X2),X2)|~r2_hidden(X3,k1_relat_1(X1))|esk3_2(X1,X2)!=k1_funct_1(X1,X3)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.41  cnf(c_0_69, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk3_2(esk7_0,esk6_0),esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_49])).
% 0.19/0.41  cnf(c_0_70, negated_conjecture, (esk6_0=k1_xboole_0|esk3_2(esk7_0,esk6_0)!=k1_funct_1(esk7_0,X1)|~r2_hidden(X1,k1_relat_1(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_26]), c_0_27])]), c_0_49])).
% 0.19/0.41  cnf(c_0_71, negated_conjecture, (esk6_0=k1_xboole_0|esk3_2(esk7_0,esk6_0)!=k1_funct_1(esk7_0,X1)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_70, c_0_32])).
% 0.19/0.41  cnf(c_0_72, negated_conjecture, (esk6_0=k1_xboole_0|~r2_hidden(esk8_1(esk3_2(esk7_0,esk6_0)),esk5_0)), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_25])]), c_0_69])).
% 0.19/0.41  cnf(c_0_73, negated_conjecture, (r2_hidden(esk8_1(X1),X2)|~r2_hidden(X1,esk6_0)|~r1_tarski(esk5_0,X2)), inference(spm,[status(thm)],[c_0_39, c_0_33])).
% 0.19/0.41  cnf(c_0_74, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_41, c_0_37])).
% 0.19/0.41  fof(c_0_75, plain, ![X12]:r1_tarski(k1_xboole_0,X12), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.41  cnf(c_0_76, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk7_0),X1),X2)|r1_tarski(k2_relat_1(esk7_0),X1)|~r1_tarski(esk6_0,X2)), inference(spm,[status(thm)],[c_0_39, c_0_59])).
% 0.19/0.41  cnf(c_0_77, negated_conjecture, (esk6_0=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_74])]), c_0_69])).
% 0.19/0.41  cnf(c_0_78, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.19/0.41  cnf(c_0_79, negated_conjecture, (r2_hidden(k1_funct_1(X1,esk8_1(X2)),X3)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,esk6_0)|~r1_tarski(esk5_0,k1_relat_1(X1))|~r1_tarski(k2_relat_1(X1),X3)), inference(spm,[status(thm)],[c_0_53, c_0_73])).
% 0.19/0.41  cnf(c_0_80, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X1,X2,X3)|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.41  cnf(c_0_81, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk7_0),X1),X2)|r1_tarski(k2_relat_1(esk7_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_77]), c_0_78])])).
% 0.19/0.41  cnf(c_0_82, negated_conjecture, (r2_hidden(X1,X2)|~r2_hidden(X1,esk6_0)|~r1_tarski(esk5_0,k1_relat_1(esk7_0))|~r1_tarski(k2_relat_1(esk7_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_25]), c_0_26]), c_0_27])])).
% 0.19/0.41  cnf(c_0_83, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X2,X1,k1_xboole_0)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))), inference(er,[status(thm)],[c_0_80])).
% 0.19/0.41  cnf(c_0_84, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_xboole_0)))), inference(rw,[status(thm)],[c_0_19, c_0_77])).
% 0.19/0.41  cnf(c_0_85, negated_conjecture, (v1_funct_2(esk7_0,esk5_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_23, c_0_77])).
% 0.19/0.41  cnf(c_0_86, negated_conjecture, (r1_tarski(k2_relat_1(esk7_0),X1)), inference(spm,[status(thm)],[c_0_41, c_0_81])).
% 0.19/0.41  cnf(c_0_87, negated_conjecture, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_xboole_0)|~r1_tarski(esk5_0,k1_relat_1(esk7_0))|~r1_tarski(k2_relat_1(esk7_0),X2)), inference(rw,[status(thm)],[c_0_82, c_0_77])).
% 0.19/0.41  cnf(c_0_88, negated_conjecture, (esk5_0=k1_xboole_0|esk7_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_85])])).
% 0.19/0.41  cnf(c_0_89, negated_conjecture, (X1=k2_relat_1(esk7_0)|r2_hidden(k1_funct_1(esk7_0,esk4_2(esk7_0,X1)),X2)|r2_hidden(esk3_2(esk7_0,X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_40]), c_0_26]), c_0_27])]), c_0_86])])).
% 0.19/0.41  cnf(c_0_90, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(X1,X2)|~r2_hidden(X1,k1_xboole_0)|~r1_tarski(k2_relat_1(esk7_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_78])])).
% 0.19/0.41  cnf(c_0_91, negated_conjecture, (X1=k2_relat_1(esk7_0)|r2_hidden(esk3_2(esk7_0,X1),X1)|r2_hidden(esk3_2(esk7_0,X1),X2)), inference(spm,[status(thm)],[c_0_89, c_0_67])).
% 0.19/0.41  cnf(c_0_92, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_86])])).
% 0.19/0.41  cnf(c_0_93, negated_conjecture, (r2_hidden(esk8_1(X1),X2)|~r2_hidden(X1,k1_xboole_0)|~r1_tarski(esk5_0,X2)), inference(rw,[status(thm)],[c_0_73, c_0_77])).
% 0.19/0.41  cnf(c_0_94, negated_conjecture, (X1=k2_relat_1(esk7_0)|r2_hidden(esk3_2(esk7_0,X1),X1)), inference(ef,[status(thm)],[c_0_91])).
% 0.19/0.41  cnf(c_0_95, negated_conjecture, (k2_relat_1(esk7_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_49, c_0_77])).
% 0.19/0.41  cnf(c_0_96, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk8_1(X1),X2)|~r2_hidden(X1,k1_xboole_0)|~r1_tarski(esk5_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 0.19/0.41  cnf(c_0_97, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk3_2(esk7_0,k1_xboole_0),X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_94]), c_0_95])).
% 0.19/0.41  cnf(c_0_98, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk8_1(X1),X2)|~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_88]), c_0_78])])).
% 0.19/0.41  cnf(c_0_99, negated_conjecture, (esk7_0=k1_xboole_0|esk3_2(esk7_0,k1_xboole_0)!=k1_funct_1(esk7_0,X1)|~r2_hidden(X1,k1_relat_1(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_97]), c_0_26]), c_0_27])]), c_0_95])).
% 0.19/0.41  cnf(c_0_100, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk8_1(esk3_2(esk7_0,k1_xboole_0)),X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_94]), c_0_95])).
% 0.19/0.41  cnf(c_0_101, negated_conjecture, (esk7_0=k1_xboole_0|k1_funct_1(esk7_0,esk8_1(esk3_2(esk7_0,k1_xboole_0)))!=esk3_2(esk7_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_99, c_0_100])).
% 0.19/0.41  cnf(c_0_102, negated_conjecture, (k1_funct_1(esk7_0,esk8_1(X1))=X1|~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_25, c_0_77])).
% 0.19/0.41  cnf(c_0_103, negated_conjecture, (esk7_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_97])).
% 0.19/0.41  cnf(c_0_104, negated_conjecture, (X1=k2_relat_1(k1_xboole_0)|r2_hidden(esk3_2(k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_103]), c_0_103])).
% 0.19/0.41  cnf(c_0_105, negated_conjecture, (X1=k2_relat_1(k1_xboole_0)|r2_hidden(esk3_2(k1_xboole_0,X1),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_39, c_0_104])).
% 0.19/0.41  cnf(c_0_106, negated_conjecture, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_95, c_0_103])).
% 0.19/0.41  cnf(c_0_107, negated_conjecture, (r2_hidden(esk3_2(k1_xboole_0,k1_xboole_0),X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_78]), c_0_106])).
% 0.19/0.41  cnf(c_0_108, negated_conjecture, (v1_funct_1(k1_xboole_0)), inference(rw,[status(thm)],[c_0_26, c_0_103])).
% 0.19/0.41  cnf(c_0_109, negated_conjecture, (v1_relat_1(k1_xboole_0)), inference(rw,[status(thm)],[c_0_27, c_0_103])).
% 0.19/0.41  cnf(c_0_110, plain, (r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.41  cnf(c_0_111, negated_conjecture, (esk3_2(k1_xboole_0,k1_xboole_0)!=k1_funct_1(k1_xboole_0,X1)|~r2_hidden(X1,k1_relat_1(k1_xboole_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_107]), c_0_108]), c_0_109])]), c_0_106])).
% 0.19/0.41  cnf(c_0_112, plain, (r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_110])).
% 0.19/0.41  cnf(c_0_113, plain, (X1=k1_funct_1(X2,esk2_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.41  cnf(c_0_114, negated_conjecture, (k1_funct_1(k1_xboole_0,esk2_3(k1_xboole_0,k2_relat_1(k1_xboole_0),X1))!=esk3_2(k1_xboole_0,k1_xboole_0)|~r2_hidden(X1,k2_relat_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_108]), c_0_109])])).
% 0.19/0.41  cnf(c_0_115, plain, (k1_funct_1(X1,esk2_3(X1,k2_relat_1(X1),X2))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_113])).
% 0.19/0.41  cnf(c_0_116, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_115]), c_0_108]), c_0_109])])]), c_0_107])]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 117
% 0.19/0.41  # Proof object clause steps            : 92
% 0.19/0.41  # Proof object formula steps           : 25
% 0.19/0.41  # Proof object conjectures             : 70
% 0.19/0.41  # Proof object clause conjectures      : 67
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 24
% 0.19/0.41  # Proof object initial formulas used   : 12
% 0.19/0.41  # Proof object generating inferences   : 53
% 0.19/0.41  # Proof object simplifying inferences  : 88
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 12
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 31
% 0.19/0.41  # Removed in clause preprocessing      : 0
% 0.19/0.41  # Initial clauses in saturation        : 31
% 0.19/0.41  # Processed clauses                    : 448
% 0.19/0.41  # ...of these trivial                  : 2
% 0.19/0.41  # ...subsumed                          : 112
% 0.19/0.41  # ...remaining for further processing  : 334
% 0.19/0.41  # Other redundant clauses eliminated   : 15
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 46
% 0.19/0.41  # Backward-rewritten                   : 174
% 0.19/0.41  # Generated clauses                    : 1325
% 0.19/0.41  # ...of the previous two non-trivial   : 1286
% 0.19/0.41  # Contextual simplify-reflections      : 5
% 0.19/0.41  # Paramodulations                      : 1310
% 0.19/0.41  # Factorizations                       : 2
% 0.19/0.41  # Equation resolutions                 : 15
% 0.19/0.41  # Propositional unsat checks           : 0
% 0.19/0.41  #    Propositional check models        : 0
% 0.19/0.41  #    Propositional check unsatisfiable : 0
% 0.19/0.41  #    Propositional clauses             : 0
% 0.19/0.41  #    Propositional clauses after purity: 0
% 0.19/0.41  #    Propositional unsat core size     : 0
% 0.19/0.41  #    Propositional preprocessing time  : 0.000
% 0.19/0.41  #    Propositional encoding time       : 0.000
% 0.19/0.41  #    Propositional solver time         : 0.000
% 0.19/0.41  #    Success case prop preproc time    : 0.000
% 0.19/0.41  #    Success case prop encoding time   : 0.000
% 0.19/0.41  #    Success case prop solver time     : 0.000
% 0.19/0.41  # Current number of processed clauses  : 77
% 0.19/0.41  #    Positive orientable unit clauses  : 13
% 0.19/0.41  #    Positive unorientable unit clauses: 0
% 0.19/0.41  #    Negative unit clauses             : 4
% 0.19/0.41  #    Non-unit-clauses                  : 60
% 0.19/0.41  # Current number of unprocessed clauses: 628
% 0.19/0.41  # ...number of literals in the above   : 3439
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 250
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 4712
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 1786
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 159
% 0.19/0.41  # Unit Clause-clause subsumption calls : 55
% 0.19/0.41  # Rewrite failures with RHS unbound    : 0
% 0.19/0.41  # BW rewrite match attempts            : 12
% 0.19/0.41  # BW rewrite match successes           : 7
% 0.19/0.41  # Condensation attempts                : 0
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 30768
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.073 s
% 0.19/0.41  # System time              : 0.010 s
% 0.19/0.41  # Total time               : 0.083 s
% 0.19/0.41  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
