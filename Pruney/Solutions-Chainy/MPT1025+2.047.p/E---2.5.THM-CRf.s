%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:41 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   88 (1314 expanded)
%              Number of clauses        :   63 ( 519 expanded)
%              Number of leaves         :   12 ( 323 expanded)
%              Depth                    :   16
%              Number of atoms          :  303 (6703 expanded)
%              Number of equality atoms :   88 (1402 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

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

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(c_0_12,negated_conjecture,(
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

fof(c_0_13,plain,(
    ! [X21,X22,X23,X24,X26,X27,X28,X29,X31] :
      ( ( r2_hidden(esk2_4(X21,X22,X23,X24),k1_relat_1(X21))
        | ~ r2_hidden(X24,X23)
        | X23 != k9_relat_1(X21,X22)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( r2_hidden(esk2_4(X21,X22,X23,X24),X22)
        | ~ r2_hidden(X24,X23)
        | X23 != k9_relat_1(X21,X22)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( X24 = k1_funct_1(X21,esk2_4(X21,X22,X23,X24))
        | ~ r2_hidden(X24,X23)
        | X23 != k9_relat_1(X21,X22)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( ~ r2_hidden(X27,k1_relat_1(X21))
        | ~ r2_hidden(X27,X22)
        | X26 != k1_funct_1(X21,X27)
        | r2_hidden(X26,X23)
        | X23 != k9_relat_1(X21,X22)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( ~ r2_hidden(esk3_3(X21,X28,X29),X29)
        | ~ r2_hidden(X31,k1_relat_1(X21))
        | ~ r2_hidden(X31,X28)
        | esk3_3(X21,X28,X29) != k1_funct_1(X21,X31)
        | X29 = k9_relat_1(X21,X28)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( r2_hidden(esk4_3(X21,X28,X29),k1_relat_1(X21))
        | r2_hidden(esk3_3(X21,X28,X29),X29)
        | X29 = k9_relat_1(X21,X28)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( r2_hidden(esk4_3(X21,X28,X29),X28)
        | r2_hidden(esk3_3(X21,X28,X29),X29)
        | X29 = k9_relat_1(X21,X28)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( esk3_3(X21,X28,X29) = k1_funct_1(X21,esk4_3(X21,X28,X29))
        | r2_hidden(esk3_3(X21,X28,X29),X29)
        | X29 = k9_relat_1(X21,X28)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).

fof(c_0_14,plain,(
    ! [X12,X13] :
      ( ~ v1_relat_1(X12)
      | ~ m1_subset_1(X13,k1_zfmisc_1(X12))
      | v1_relat_1(X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_15,negated_conjecture,(
    ! [X50] :
      ( v1_funct_1(esk8_0)
      & v1_funct_2(esk8_0,esk5_0,esk6_0)
      & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
      & r2_hidden(esk9_0,k7_relset_1(esk5_0,esk6_0,esk8_0,esk7_0))
      & ( ~ m1_subset_1(X50,esk5_0)
        | ~ r2_hidden(X50,esk7_0)
        | esk9_0 != k1_funct_1(esk8_0,X50) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).

fof(c_0_16,plain,(
    ! [X14,X15] : v1_relat_1(k2_zfmisc_1(X14,X15)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_17,plain,
    ( X1 = k1_funct_1(X2,esk2_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k9_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X35,X36,X37] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
      | k1_relset_1(X35,X36,X37) = k1_relat_1(X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_22,negated_conjecture,
    ( ~ m1_subset_1(X1,esk5_0)
    | ~ r2_hidden(X1,esk7_0)
    | esk9_0 != k1_funct_1(esk8_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k1_funct_1(X1,esk2_4(X1,X2,k9_relat_1(X1,X2),X3)) = X3
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,k9_relat_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

fof(c_0_26,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X8,X9)
      | m1_subset_1(X8,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

fof(c_0_27,plain,(
    ! [X38,X39,X40,X41] :
      ( ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
      | k7_relset_1(X38,X39,X40,X41) = k9_relat_1(X40,X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_28,plain,(
    ! [X42,X43,X44] :
      ( ( ~ v1_funct_2(X44,X42,X43)
        | X42 = k1_relset_1(X42,X43,X44)
        | X43 = k1_xboole_0
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) )
      & ( X42 != k1_relset_1(X42,X43,X44)
        | v1_funct_2(X44,X42,X43)
        | X43 = k1_xboole_0
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) )
      & ( ~ v1_funct_2(X44,X42,X43)
        | X42 = k1_relset_1(X42,X43,X44)
        | X42 != k1_xboole_0
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) )
      & ( X42 != k1_relset_1(X42,X43,X44)
        | v1_funct_2(X44,X42,X43)
        | X42 != k1_xboole_0
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) )
      & ( ~ v1_funct_2(X44,X42,X43)
        | X44 = k1_xboole_0
        | X42 = k1_xboole_0
        | X43 != k1_xboole_0
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) )
      & ( X44 != k1_xboole_0
        | v1_funct_2(X44,X42,X43)
        | X42 = k1_xboole_0
        | X43 != k1_xboole_0
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_29,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( ~ m1_subset_1(esk2_4(esk8_0,X1,k9_relat_1(esk8_0,X1),esk9_0),esk5_0)
    | ~ r2_hidden(esk2_4(esk8_0,X1,k9_relat_1(esk8_0,X1),esk9_0),esk7_0)
    | ~ r2_hidden(esk9_0,k9_relat_1(esk8_0,X1)) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25])])])).

cnf(c_0_31,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk9_0,k7_relset_1(esk5_0,esk6_0,esk8_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_34,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),k1_relat_1(X1))
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_36,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( k1_relset_1(esk5_0,esk6_0,esk8_0) = k1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_19])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_2(esk8_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_39,negated_conjecture,
    ( ~ r2_hidden(esk2_4(esk8_0,X1,k9_relat_1(esk8_0,X1),esk9_0),esk7_0)
    | ~ r2_hidden(esk2_4(esk8_0,X1,k9_relat_1(esk8_0,X1),esk9_0),esk5_0)
    | ~ r2_hidden(esk9_0,k9_relat_1(esk8_0,X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_40,plain,
    ( r2_hidden(esk2_4(X1,X2,k9_relat_1(X1,X2),X3),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,k9_relat_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk9_0,k9_relat_1(esk8_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_19])])).

cnf(c_0_42,plain,
    ( r2_hidden(esk2_4(X1,X2,k9_relat_1(X1,X2),X3),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,k9_relat_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( k1_relat_1(esk8_0) = esk5_0
    | esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_19]),c_0_37]),c_0_38])])).

cnf(c_0_44,negated_conjecture,
    ( ~ r2_hidden(esk2_4(esk8_0,esk7_0,k9_relat_1(esk8_0,esk7_0),esk9_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_24]),c_0_25])])).

cnf(c_0_45,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk2_4(esk8_0,X1,k9_relat_1(esk8_0,X1),X2),esk5_0)
    | ~ r2_hidden(X2,k9_relat_1(esk8_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_24]),c_0_25])])).

fof(c_0_46,plain,(
    ! [X33,X34] :
      ( ~ r2_hidden(X33,X34)
      | ~ r1_tarski(X34,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_47,plain,(
    ! [X7] : r1_tarski(k1_xboole_0,X7) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_48,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_49,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_41])])).

cnf(c_0_50,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_51,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_52,plain,(
    ! [X16,X17,X18,X20] :
      ( ( r2_hidden(esk1_3(X16,X17,X18),k1_relat_1(X18))
        | ~ r2_hidden(X16,k9_relat_1(X18,X17))
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(k4_tarski(esk1_3(X16,X17,X18),X16),X18)
        | ~ r2_hidden(X16,k9_relat_1(X18,X17))
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(esk1_3(X16,X17,X18),X17)
        | ~ r2_hidden(X16,k9_relat_1(X18,X17))
        | ~ v1_relat_1(X18) )
      & ( ~ r2_hidden(X20,k1_relat_1(X18))
        | ~ r2_hidden(k4_tarski(X20,X16),X18)
        | ~ r2_hidden(X20,X17)
        | r2_hidden(X16,k9_relat_1(X18,X17))
        | ~ v1_relat_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

cnf(c_0_53,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X2)
    | r2_hidden(esk3_3(X1,X2,X3),X3)
    | X3 = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_54,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,k1_xboole_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_19,c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( v1_funct_2(esk8_0,esk5_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_38,c_0_49])).

fof(c_0_57,plain,(
    ! [X10,X11] :
      ( ( ~ m1_subset_1(X10,k1_zfmisc_1(X11))
        | r1_tarski(X10,X11) )
      & ( ~ r1_tarski(X10,X11)
        | m1_subset_1(X10,k1_zfmisc_1(X11)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_58,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_59,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_60,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),k1_relat_1(X1))
    | r2_hidden(esk3_3(X1,X2,X3),X3)
    | X3 = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_61,negated_conjecture,
    ( X1 = k9_relat_1(esk8_0,X2)
    | r2_hidden(esk3_3(esk8_0,X2,X1),X1)
    | r2_hidden(esk4_3(esk8_0,X2,X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_24]),c_0_25])])).

cnf(c_0_62,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_63,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])])).

cnf(c_0_64,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_65,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( X1 = k9_relat_1(esk8_0,X2)
    | r2_hidden(esk4_3(esk8_0,X2,X1),k1_relat_1(esk8_0))
    | r2_hidden(esk3_3(esk8_0,X2,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_24]),c_0_25])])).

cnf(c_0_67,negated_conjecture,
    ( X1 = k9_relat_1(esk8_0,k1_xboole_0)
    | r2_hidden(esk3_3(esk8_0,k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( k1_relset_1(esk5_0,k1_xboole_0,esk8_0) = k1_relat_1(esk8_0) ),
    inference(rw,[status(thm)],[c_0_37,c_0_49])).

cnf(c_0_69,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
    | ~ v1_funct_2(X2,k1_xboole_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(er,[status(thm)],[c_0_62])).

cnf(c_0_70,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_63])).

cnf(c_0_71,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | v1_funct_2(esk8_0,k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_63])).

cnf(c_0_72,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_51])).

cnf(c_0_73,negated_conjecture,
    ( k9_relat_1(X1,k1_xboole_0) = k9_relat_1(esk8_0,X2)
    | r2_hidden(esk4_3(esk8_0,X2,k9_relat_1(X1,k1_xboole_0)),k1_relat_1(esk8_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_74,negated_conjecture,
    ( k9_relat_1(esk8_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,esk8_0) = k1_relat_1(esk8_0)
    | esk8_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_68,c_0_63])).

cnf(c_0_76,negated_conjecture,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,esk8_0) = k1_xboole_0
    | esk8_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])).

cnf(c_0_77,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_72])).

cnf(c_0_78,negated_conjecture,
    ( k9_relat_1(esk8_0,X1) = k1_xboole_0
    | r2_hidden(esk4_3(esk8_0,X1,k1_xboole_0),k1_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_25])])).

cnf(c_0_79,negated_conjecture,
    ( k1_relat_1(esk8_0) = k1_xboole_0
    | esk8_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_80,plain,
    ( r2_hidden(k4_tarski(esk1_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_81,negated_conjecture,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_25])).

cnf(c_0_82,negated_conjecture,
    ( k9_relat_1(esk8_0,X1) = k1_xboole_0
    | esk8_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_58])).

cnf(c_0_83,plain,
    ( ~ r2_hidden(X1,k9_relat_1(k1_xboole_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_80]),c_0_81])])).

cnf(c_0_84,negated_conjecture,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_3(esk8_0,k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[c_0_67,c_0_74])).

cnf(c_0_85,negated_conjecture,
    ( esk8_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_82]),c_0_58])).

cnf(c_0_86,negated_conjecture,
    ( k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_85]),c_0_86]),c_0_58]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:50:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.20/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.028 s
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t116_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:(m1_subset_1(X6,X1)=>~((r2_hidden(X6,X3)&X5=k1_funct_1(X4,X6))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_funct_2)).
% 0.20/0.39  fof(d12_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(X3=k9_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((r2_hidden(X5,k1_relat_1(X1))&r2_hidden(X5,X2))&X4=k1_funct_1(X1,X5))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_1)).
% 0.20/0.39  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.20/0.39  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.20/0.39  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.39  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.20/0.39  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.20/0.39  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.20/0.39  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.20/0.39  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.39  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 0.20/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.39  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:(m1_subset_1(X6,X1)=>~((r2_hidden(X6,X3)&X5=k1_funct_1(X4,X6)))))))), inference(assume_negation,[status(cth)],[t116_funct_2])).
% 0.20/0.39  fof(c_0_13, plain, ![X21, X22, X23, X24, X26, X27, X28, X29, X31]:(((((r2_hidden(esk2_4(X21,X22,X23,X24),k1_relat_1(X21))|~r2_hidden(X24,X23)|X23!=k9_relat_1(X21,X22)|(~v1_relat_1(X21)|~v1_funct_1(X21)))&(r2_hidden(esk2_4(X21,X22,X23,X24),X22)|~r2_hidden(X24,X23)|X23!=k9_relat_1(X21,X22)|(~v1_relat_1(X21)|~v1_funct_1(X21))))&(X24=k1_funct_1(X21,esk2_4(X21,X22,X23,X24))|~r2_hidden(X24,X23)|X23!=k9_relat_1(X21,X22)|(~v1_relat_1(X21)|~v1_funct_1(X21))))&(~r2_hidden(X27,k1_relat_1(X21))|~r2_hidden(X27,X22)|X26!=k1_funct_1(X21,X27)|r2_hidden(X26,X23)|X23!=k9_relat_1(X21,X22)|(~v1_relat_1(X21)|~v1_funct_1(X21))))&((~r2_hidden(esk3_3(X21,X28,X29),X29)|(~r2_hidden(X31,k1_relat_1(X21))|~r2_hidden(X31,X28)|esk3_3(X21,X28,X29)!=k1_funct_1(X21,X31))|X29=k9_relat_1(X21,X28)|(~v1_relat_1(X21)|~v1_funct_1(X21)))&(((r2_hidden(esk4_3(X21,X28,X29),k1_relat_1(X21))|r2_hidden(esk3_3(X21,X28,X29),X29)|X29=k9_relat_1(X21,X28)|(~v1_relat_1(X21)|~v1_funct_1(X21)))&(r2_hidden(esk4_3(X21,X28,X29),X28)|r2_hidden(esk3_3(X21,X28,X29),X29)|X29=k9_relat_1(X21,X28)|(~v1_relat_1(X21)|~v1_funct_1(X21))))&(esk3_3(X21,X28,X29)=k1_funct_1(X21,esk4_3(X21,X28,X29))|r2_hidden(esk3_3(X21,X28,X29),X29)|X29=k9_relat_1(X21,X28)|(~v1_relat_1(X21)|~v1_funct_1(X21)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).
% 0.20/0.39  fof(c_0_14, plain, ![X12, X13]:(~v1_relat_1(X12)|(~m1_subset_1(X13,k1_zfmisc_1(X12))|v1_relat_1(X13))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.20/0.39  fof(c_0_15, negated_conjecture, ![X50]:(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,esk5_0,esk6_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))))&(r2_hidden(esk9_0,k7_relset_1(esk5_0,esk6_0,esk8_0,esk7_0))&(~m1_subset_1(X50,esk5_0)|(~r2_hidden(X50,esk7_0)|esk9_0!=k1_funct_1(esk8_0,X50))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).
% 0.20/0.39  fof(c_0_16, plain, ![X14, X15]:v1_relat_1(k2_zfmisc_1(X14,X15)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.20/0.39  cnf(c_0_17, plain, (X1=k1_funct_1(X2,esk2_4(X2,X3,X4,X1))|~r2_hidden(X1,X4)|X4!=k9_relat_1(X2,X3)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.39  cnf(c_0_18, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.39  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  cnf(c_0_20, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  fof(c_0_21, plain, ![X35, X36, X37]:(~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|k1_relset_1(X35,X36,X37)=k1_relat_1(X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.39  cnf(c_0_22, negated_conjecture, (~m1_subset_1(X1,esk5_0)|~r2_hidden(X1,esk7_0)|esk9_0!=k1_funct_1(esk8_0,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  cnf(c_0_23, plain, (k1_funct_1(X1,esk2_4(X1,X2,k9_relat_1(X1,X2),X3))=X3|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X3,k9_relat_1(X1,X2))), inference(er,[status(thm)],[c_0_17])).
% 0.20/0.39  cnf(c_0_24, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  cnf(c_0_25, negated_conjecture, (v1_relat_1(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])])).
% 0.20/0.39  fof(c_0_26, plain, ![X8, X9]:(~r2_hidden(X8,X9)|m1_subset_1(X8,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.20/0.39  fof(c_0_27, plain, ![X38, X39, X40, X41]:(~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|k7_relset_1(X38,X39,X40,X41)=k9_relat_1(X40,X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.20/0.39  fof(c_0_28, plain, ![X42, X43, X44]:((((~v1_funct_2(X44,X42,X43)|X42=k1_relset_1(X42,X43,X44)|X43=k1_xboole_0|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))))&(X42!=k1_relset_1(X42,X43,X44)|v1_funct_2(X44,X42,X43)|X43=k1_xboole_0|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))))&((~v1_funct_2(X44,X42,X43)|X42=k1_relset_1(X42,X43,X44)|X42!=k1_xboole_0|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))))&(X42!=k1_relset_1(X42,X43,X44)|v1_funct_2(X44,X42,X43)|X42!=k1_xboole_0|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))))))&((~v1_funct_2(X44,X42,X43)|X44=k1_xboole_0|X42=k1_xboole_0|X43!=k1_xboole_0|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))))&(X44!=k1_xboole_0|v1_funct_2(X44,X42,X43)|X42=k1_xboole_0|X43!=k1_xboole_0|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.20/0.39  cnf(c_0_29, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.39  cnf(c_0_30, negated_conjecture, (~m1_subset_1(esk2_4(esk8_0,X1,k9_relat_1(esk8_0,X1),esk9_0),esk5_0)|~r2_hidden(esk2_4(esk8_0,X1,k9_relat_1(esk8_0,X1),esk9_0),esk7_0)|~r2_hidden(esk9_0,k9_relat_1(esk8_0,X1))), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25])])])).
% 0.20/0.39  cnf(c_0_31, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.39  cnf(c_0_32, plain, (r2_hidden(esk2_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.39  cnf(c_0_33, negated_conjecture, (r2_hidden(esk9_0,k7_relset_1(esk5_0,esk6_0,esk8_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  cnf(c_0_34, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.39  cnf(c_0_35, plain, (r2_hidden(esk2_4(X1,X2,X3,X4),k1_relat_1(X1))|~r2_hidden(X4,X3)|X3!=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.39  cnf(c_0_36, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.39  cnf(c_0_37, negated_conjecture, (k1_relset_1(esk5_0,esk6_0,esk8_0)=k1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_29, c_0_19])).
% 0.20/0.39  cnf(c_0_38, negated_conjecture, (v1_funct_2(esk8_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  cnf(c_0_39, negated_conjecture, (~r2_hidden(esk2_4(esk8_0,X1,k9_relat_1(esk8_0,X1),esk9_0),esk7_0)|~r2_hidden(esk2_4(esk8_0,X1,k9_relat_1(esk8_0,X1),esk9_0),esk5_0)|~r2_hidden(esk9_0,k9_relat_1(esk8_0,X1))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.39  cnf(c_0_40, plain, (r2_hidden(esk2_4(X1,X2,k9_relat_1(X1,X2),X3),X2)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X3,k9_relat_1(X1,X2))), inference(er,[status(thm)],[c_0_32])).
% 0.20/0.39  cnf(c_0_41, negated_conjecture, (r2_hidden(esk9_0,k9_relat_1(esk8_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_19])])).
% 0.20/0.39  cnf(c_0_42, plain, (r2_hidden(esk2_4(X1,X2,k9_relat_1(X1,X2),X3),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X3,k9_relat_1(X1,X2))), inference(er,[status(thm)],[c_0_35])).
% 0.20/0.39  cnf(c_0_43, negated_conjecture, (k1_relat_1(esk8_0)=esk5_0|esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_19]), c_0_37]), c_0_38])])).
% 0.20/0.39  cnf(c_0_44, negated_conjecture, (~r2_hidden(esk2_4(esk8_0,esk7_0,k9_relat_1(esk8_0,esk7_0),esk9_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_24]), c_0_25])])).
% 0.20/0.39  cnf(c_0_45, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk2_4(esk8_0,X1,k9_relat_1(esk8_0,X1),X2),esk5_0)|~r2_hidden(X2,k9_relat_1(esk8_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_24]), c_0_25])])).
% 0.20/0.39  fof(c_0_46, plain, ![X33, X34]:(~r2_hidden(X33,X34)|~r1_tarski(X34,X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.20/0.39  fof(c_0_47, plain, ![X7]:r1_tarski(k1_xboole_0,X7), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.39  cnf(c_0_48, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X1,X2,X3)|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.39  cnf(c_0_49, negated_conjecture, (esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_41])])).
% 0.20/0.39  cnf(c_0_50, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.40  cnf(c_0_51, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.40  fof(c_0_52, plain, ![X16, X17, X18, X20]:((((r2_hidden(esk1_3(X16,X17,X18),k1_relat_1(X18))|~r2_hidden(X16,k9_relat_1(X18,X17))|~v1_relat_1(X18))&(r2_hidden(k4_tarski(esk1_3(X16,X17,X18),X16),X18)|~r2_hidden(X16,k9_relat_1(X18,X17))|~v1_relat_1(X18)))&(r2_hidden(esk1_3(X16,X17,X18),X17)|~r2_hidden(X16,k9_relat_1(X18,X17))|~v1_relat_1(X18)))&(~r2_hidden(X20,k1_relat_1(X18))|~r2_hidden(k4_tarski(X20,X16),X18)|~r2_hidden(X20,X17)|r2_hidden(X16,k9_relat_1(X18,X17))|~v1_relat_1(X18))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.20/0.40  cnf(c_0_53, plain, (r2_hidden(esk4_3(X1,X2,X3),X2)|r2_hidden(esk3_3(X1,X2,X3),X3)|X3=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.40  cnf(c_0_54, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X2,X1,k1_xboole_0)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))), inference(er,[status(thm)],[c_0_48])).
% 0.20/0.40  cnf(c_0_55, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_xboole_0)))), inference(rw,[status(thm)],[c_0_19, c_0_49])).
% 0.20/0.40  cnf(c_0_56, negated_conjecture, (v1_funct_2(esk8_0,esk5_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_38, c_0_49])).
% 0.20/0.40  fof(c_0_57, plain, ![X10, X11]:((~m1_subset_1(X10,k1_zfmisc_1(X11))|r1_tarski(X10,X11))&(~r1_tarski(X10,X11)|m1_subset_1(X10,k1_zfmisc_1(X11)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.40  cnf(c_0_58, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.40  cnf(c_0_59, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.40  cnf(c_0_60, plain, (r2_hidden(esk4_3(X1,X2,X3),k1_relat_1(X1))|r2_hidden(esk3_3(X1,X2,X3),X3)|X3=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.40  cnf(c_0_61, negated_conjecture, (X1=k9_relat_1(esk8_0,X2)|r2_hidden(esk3_3(esk8_0,X2,X1),X1)|r2_hidden(esk4_3(esk8_0,X2,X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_24]), c_0_25])])).
% 0.20/0.40  cnf(c_0_62, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.40  cnf(c_0_63, negated_conjecture, (esk8_0=k1_xboole_0|esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])])).
% 0.20/0.40  cnf(c_0_64, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.20/0.40  cnf(c_0_65, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(X1,k1_xboole_0))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.20/0.40  cnf(c_0_66, negated_conjecture, (X1=k9_relat_1(esk8_0,X2)|r2_hidden(esk4_3(esk8_0,X2,X1),k1_relat_1(esk8_0))|r2_hidden(esk3_3(esk8_0,X2,X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_24]), c_0_25])])).
% 0.20/0.40  cnf(c_0_67, negated_conjecture, (X1=k9_relat_1(esk8_0,k1_xboole_0)|r2_hidden(esk3_3(esk8_0,k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_58, c_0_61])).
% 0.20/0.40  cnf(c_0_68, negated_conjecture, (k1_relset_1(esk5_0,k1_xboole_0,esk8_0)=k1_relat_1(esk8_0)), inference(rw,[status(thm)],[c_0_37, c_0_49])).
% 0.20/0.40  cnf(c_0_69, plain, (k1_relset_1(k1_xboole_0,X1,X2)=k1_xboole_0|~v1_funct_2(X2,k1_xboole_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(er,[status(thm)],[c_0_62])).
% 0.20/0.40  cnf(c_0_70, negated_conjecture, (esk8_0=k1_xboole_0|m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_55, c_0_63])).
% 0.20/0.40  cnf(c_0_71, negated_conjecture, (esk8_0=k1_xboole_0|v1_funct_2(esk8_0,k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_56, c_0_63])).
% 0.20/0.40  cnf(c_0_72, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_64, c_0_51])).
% 0.20/0.40  cnf(c_0_73, negated_conjecture, (k9_relat_1(X1,k1_xboole_0)=k9_relat_1(esk8_0,X2)|r2_hidden(esk4_3(esk8_0,X2,k9_relat_1(X1,k1_xboole_0)),k1_relat_1(esk8_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.20/0.40  cnf(c_0_74, negated_conjecture, (k9_relat_1(esk8_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_58, c_0_67])).
% 0.20/0.40  cnf(c_0_75, negated_conjecture, (k1_relset_1(k1_xboole_0,k1_xboole_0,esk8_0)=k1_relat_1(esk8_0)|esk8_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_68, c_0_63])).
% 0.20/0.40  cnf(c_0_76, negated_conjecture, (k1_relset_1(k1_xboole_0,k1_xboole_0,esk8_0)=k1_xboole_0|esk8_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])).
% 0.20/0.40  cnf(c_0_77, plain, (v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_18, c_0_72])).
% 0.20/0.40  cnf(c_0_78, negated_conjecture, (k9_relat_1(esk8_0,X1)=k1_xboole_0|r2_hidden(esk4_3(esk8_0,X1,k1_xboole_0),k1_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_25])])).
% 0.20/0.40  cnf(c_0_79, negated_conjecture, (k1_relat_1(esk8_0)=k1_xboole_0|esk8_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.20/0.40  cnf(c_0_80, plain, (r2_hidden(k4_tarski(esk1_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.40  cnf(c_0_81, negated_conjecture, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_77, c_0_25])).
% 0.20/0.40  cnf(c_0_82, negated_conjecture, (k9_relat_1(esk8_0,X1)=k1_xboole_0|esk8_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_58])).
% 0.20/0.40  cnf(c_0_83, plain, (~r2_hidden(X1,k9_relat_1(k1_xboole_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_80]), c_0_81])])).
% 0.20/0.40  cnf(c_0_84, negated_conjecture, (X1=k1_xboole_0|r2_hidden(esk3_3(esk8_0,k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[c_0_67, c_0_74])).
% 0.20/0.40  cnf(c_0_85, negated_conjecture, (esk8_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_82]), c_0_58])).
% 0.20/0.40  cnf(c_0_86, negated_conjecture, (k9_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.20/0.40  cnf(c_0_87, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_85]), c_0_86]), c_0_58]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 88
% 0.20/0.40  # Proof object clause steps            : 63
% 0.20/0.40  # Proof object formula steps           : 25
% 0.20/0.40  # Proof object conjectures             : 38
% 0.20/0.40  # Proof object clause conjectures      : 35
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 23
% 0.20/0.40  # Proof object initial formulas used   : 12
% 0.20/0.40  # Proof object generating inferences   : 30
% 0.20/0.40  # Proof object simplifying inferences  : 45
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 12
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 32
% 0.20/0.40  # Removed in clause preprocessing      : 0
% 0.20/0.40  # Initial clauses in saturation        : 32
% 0.20/0.40  # Processed clauses                    : 325
% 0.20/0.40  # ...of these trivial                  : 1
% 0.20/0.40  # ...subsumed                          : 167
% 0.20/0.40  # ...remaining for further processing  : 157
% 0.20/0.40  # Other redundant clauses eliminated   : 13
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 6
% 0.20/0.40  # Backward-rewritten                   : 83
% 0.20/0.40  # Generated clauses                    : 853
% 0.20/0.40  # ...of the previous two non-trivial   : 824
% 0.20/0.40  # Contextual simplify-reflections      : 1
% 0.20/0.40  # Paramodulations                      : 842
% 0.20/0.40  # Factorizations                       : 0
% 0.20/0.40  # Equation resolutions                 : 13
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 60
% 0.20/0.40  #    Positive orientable unit clauses  : 8
% 0.20/0.40  #    Positive unorientable unit clauses: 0
% 0.20/0.40  #    Negative unit clauses             : 1
% 0.20/0.40  #    Non-unit-clauses                  : 51
% 0.20/0.40  # Current number of unprocessed clauses: 467
% 0.20/0.40  # ...number of literals in the above   : 2168
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 89
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 1266
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 731
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 115
% 0.20/0.40  # Unit Clause-clause subsumption calls : 33
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 10
% 0.20/0.40  # BW rewrite match successes           : 8
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 18220
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.056 s
% 0.20/0.40  # System time              : 0.003 s
% 0.20/0.40  # Total time               : 0.059 s
% 0.20/0.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
