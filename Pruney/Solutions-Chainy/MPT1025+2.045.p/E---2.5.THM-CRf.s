%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:41 EST 2020

% Result     : Theorem 13.30s
% Output     : CNFRefutation 13.30s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 382 expanded)
%              Number of clauses        :   45 ( 157 expanded)
%              Number of leaves         :   13 (  97 expanded)
%              Depth                    :   12
%              Number of atoms          :  279 (1680 expanded)
%              Number of equality atoms :   28 ( 165 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(dt_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(t52_relset_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ~ v1_xboole_0(X3)
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                 => ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))
                      <=> ? [X6] :
                            ( m1_subset_1(X6,X3)
                            & r2_hidden(k4_tarski(X6,X5),X4)
                            & r2_hidden(X6,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relset_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t22_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
     => ( ! [X4] :
            ~ ( r2_hidden(X4,X2)
              & ! [X5] : ~ r2_hidden(k4_tarski(X4,X5),X3) )
      <=> k1_relset_1(X2,X1,X3) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(c_0_13,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_14,plain,(
    ! [X20,X21,X22,X24] :
      ( ( r2_hidden(esk2_3(X20,X21,X22),k1_relat_1(X22))
        | ~ r2_hidden(X20,k9_relat_1(X22,X21))
        | ~ v1_relat_1(X22) )
      & ( r2_hidden(k4_tarski(esk2_3(X20,X21,X22),X20),X22)
        | ~ r2_hidden(X20,k9_relat_1(X22,X21))
        | ~ v1_relat_1(X22) )
      & ( r2_hidden(esk2_3(X20,X21,X22),X21)
        | ~ r2_hidden(X20,k9_relat_1(X22,X21))
        | ~ v1_relat_1(X22) )
      & ( ~ r2_hidden(X24,k1_relat_1(X22))
        | ~ r2_hidden(k4_tarski(X24,X20),X22)
        | ~ r2_hidden(X24,X21)
        | r2_hidden(X20,k9_relat_1(X22,X21))
        | ~ v1_relat_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

fof(c_0_15,plain,(
    ! [X13,X14,X15] :
      ( ~ r2_hidden(X13,X14)
      | ~ m1_subset_1(X14,k1_zfmisc_1(X15))
      | m1_subset_1(X13,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_16,plain,(
    ! [X31,X32,X33,X34] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | m1_subset_1(k7_relset_1(X31,X32,X33,X34),k1_zfmisc_1(X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).

cnf(c_0_17,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X38,X39,X40,X41] :
      ( ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
      | k7_relset_1(X38,X39,X40,X41) = k9_relat_1(X40,X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_20,negated_conjecture,(
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

fof(c_0_21,plain,(
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

fof(c_0_22,plain,(
    ! [X49,X50,X51,X52,X53,X55] :
      ( ( m1_subset_1(esk5_5(X49,X50,X51,X52,X53),X51)
        | ~ r2_hidden(X53,k7_relset_1(X51,X49,X52,X50))
        | ~ m1_subset_1(X53,X49)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X51,X49)))
        | v1_xboole_0(X51)
        | v1_xboole_0(X50)
        | v1_xboole_0(X49) )
      & ( r2_hidden(k4_tarski(esk5_5(X49,X50,X51,X52,X53),X53),X52)
        | ~ r2_hidden(X53,k7_relset_1(X51,X49,X52,X50))
        | ~ m1_subset_1(X53,X49)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X51,X49)))
        | v1_xboole_0(X51)
        | v1_xboole_0(X50)
        | v1_xboole_0(X49) )
      & ( r2_hidden(esk5_5(X49,X50,X51,X52,X53),X50)
        | ~ r2_hidden(X53,k7_relset_1(X51,X49,X52,X50))
        | ~ m1_subset_1(X53,X49)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X51,X49)))
        | v1_xboole_0(X51)
        | v1_xboole_0(X50)
        | v1_xboole_0(X49) )
      & ( ~ m1_subset_1(X55,X51)
        | ~ r2_hidden(k4_tarski(X55,X53),X52)
        | ~ r2_hidden(X55,X50)
        | r2_hidden(X53,k7_relset_1(X51,X49,X52,X50))
        | ~ m1_subset_1(X53,X49)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X51,X49)))
        | v1_xboole_0(X51)
        | v1_xboole_0(X50)
        | v1_xboole_0(X49) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t52_relset_1])])])])])])).

cnf(c_0_23,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,X3))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_26,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_27,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X16)
      | ~ m1_subset_1(X17,k1_zfmisc_1(X16))
      | v1_relat_1(X17) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_28,negated_conjecture,(
    ! [X61] :
      ( v1_funct_1(esk9_0)
      & v1_funct_2(esk9_0,esk6_0,esk7_0)
      & m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))
      & r2_hidden(esk10_0,k7_relset_1(esk6_0,esk7_0,esk9_0,esk8_0))
      & ( ~ m1_subset_1(X61,esk6_0)
        | ~ r2_hidden(X61,esk8_0)
        | esk10_0 != k1_funct_1(esk9_0,X61) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])])).

fof(c_0_29,plain,(
    ! [X18,X19] : v1_relat_1(k2_zfmisc_1(X18,X19)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_30,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( r2_hidden(k4_tarski(esk5_5(X1,X2,X3,X4,X5),X5),X4)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))
    | ~ m1_subset_1(X5,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( m1_subset_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ r2_hidden(X1,k7_relset_1(X4,X2,X3,X5)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_33,plain,
    ( ~ v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,k7_relset_1(X2,X3,X1,X5))
    | ~ v1_xboole_0(X5) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( ~ m1_subset_1(X1,esk6_0)
    | ~ r2_hidden(X1,esk8_0)
    | esk10_0 != k1_funct_1(esk9_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( k1_funct_1(X1,esk5_5(X2,X3,X4,X1,X5)) = X5
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ r2_hidden(X5,k7_relset_1(X4,X2,X1,X3)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk10_0,k7_relset_1(esk6_0,esk7_0,esk9_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_42,plain,
    ( k7_relset_1(X1,X2,X3,X4) = k7_relset_1(X5,X6,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_26])).

fof(c_0_43,plain,(
    ! [X42,X43,X44,X46,X47] :
      ( ( r2_hidden(esk3_3(X42,X43,X44),X43)
        | k1_relset_1(X43,X42,X44) = X43
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X43,X42))) )
      & ( ~ r2_hidden(k4_tarski(esk3_3(X42,X43,X44),X46),X44)
        | k1_relset_1(X43,X42,X44) = X43
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X43,X42))) )
      & ( k1_relset_1(X43,X42,X44) != X43
        | ~ r2_hidden(X47,X43)
        | r2_hidden(k4_tarski(X47,esk4_4(X42,X43,X44,X47)),X44)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X43,X42))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_relset_1])])])])])])).

cnf(c_0_44,negated_conjecture,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | esk10_0 != X3
    | ~ m1_subset_1(esk5_5(X2,X4,X1,esk9_0,X3),esk6_0)
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(esk5_5(X2,X4,X1,esk9_0,X3),esk8_0)
    | ~ r2_hidden(X3,k7_relset_1(X1,X2,esk9_0,X4)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40])])).

cnf(c_0_45,plain,
    ( m1_subset_1(esk5_5(X1,X2,X3,X4,X5),X3)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))
    | ~ m1_subset_1(X5,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk10_0,k7_relset_1(X1,X2,esk9_0,esk8_0))
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_35])])).

fof(c_0_47,plain,(
    ! [X35,X36,X37] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
      | k1_relset_1(X35,X36,X37) = k1_relat_1(X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_48,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | k1_relset_1(X2,X1,X3) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_49,plain,(
    ! [X28,X29,X30] :
      ( ~ v1_xboole_0(X28)
      | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X29,X28)))
      | v1_xboole_0(X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

cnf(c_0_50,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | esk10_0 != X3
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,X2)))
    | ~ r2_hidden(esk5_5(X2,X1,esk6_0,esk9_0,X3),esk8_0)
    | ~ r2_hidden(X3,k7_relset_1(esk6_0,X2,esk9_0,X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_32])).

cnf(c_0_51,plain,
    ( r2_hidden(esk5_5(X1,X2,X3,X4,X5),X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))
    | ~ m1_subset_1(X5,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_52,negated_conjecture,
    ( ~ v1_xboole_0(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_41]),c_0_40]),c_0_35])])).

cnf(c_0_53,plain,
    ( r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk10_0,k9_relat_1(esk9_0,esk8_0))
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_26])).

cnf(c_0_55,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_56,plain,
    ( k1_relset_1(X1,X2,X3) = X1
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_48])).

cnf(c_0_57,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_58,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | v1_xboole_0(X1)
    | esk10_0 != X2
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,X1)))
    | ~ r2_hidden(X2,k7_relset_1(esk6_0,X1,esk9_0,esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_32])).

cnf(c_0_59,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,X3))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk10_0,k9_relat_1(esk9_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_35])).

cnf(c_0_61,plain,
    ( X1 = k1_relat_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( v1_xboole_0(esk9_0)
    | ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_35])).

cnf(c_0_63,negated_conjecture,
    ( v1_xboole_0(esk7_0)
    | v1_xboole_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_41]),c_0_35])])).

cnf(c_0_64,negated_conjecture,
    ( ~ v1_xboole_0(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_40])])).

cnf(c_0_65,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X3))
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_66,negated_conjecture,
    ( esk6_0 = k1_relat_1(esk9_0)
    | ~ v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_35])).

cnf(c_0_67,negated_conjecture,
    ( v1_xboole_0(esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])).

cnf(c_0_68,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,X3))
    | ~ v1_xboole_0(k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( esk6_0 = k1_relat_1(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67])])).

cnf(c_0_70,negated_conjecture,
    ( ~ v1_xboole_0(k1_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_60]),c_0_40])])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_69]),c_0_70]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.33  % Computer   : n019.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 10:02:52 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  # Version: 2.5pre002
% 0.11/0.34  # No SInE strategy applied
% 0.11/0.34  # Trying AutoSched0 for 299 seconds
% 13.30/13.50  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 13.30/13.50  # and selection function SelectMaxLComplexAvoidPosPred.
% 13.30/13.50  #
% 13.30/13.50  # Preprocessing time       : 0.029 s
% 13.30/13.50  # Presaturation interreduction done
% 13.30/13.50  
% 13.30/13.50  # Proof found!
% 13.30/13.50  # SZS status Theorem
% 13.30/13.50  # SZS output start CNFRefutation
% 13.30/13.50  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 13.30/13.50  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 13.30/13.50  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 13.30/13.50  fof(dt_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 13.30/13.50  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 13.30/13.50  fof(t116_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:(m1_subset_1(X6,X1)=>~((r2_hidden(X6,X3)&X5=k1_funct_1(X4,X6))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_funct_2)).
% 13.30/13.50  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 13.30/13.50  fof(t52_relset_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))<=>?[X6]:((m1_subset_1(X6,X3)&r2_hidden(k4_tarski(X6,X5),X4))&r2_hidden(X6,X2)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relset_1)).
% 13.30/13.50  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 13.30/13.50  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 13.30/13.50  fof(t22_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~(r2_hidden(k4_tarski(X4,X5),X3))))<=>k1_relset_1(X2,X1,X3)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relset_1)).
% 13.30/13.50  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 13.30/13.50  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 13.30/13.50  fof(c_0_13, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 13.30/13.50  fof(c_0_14, plain, ![X20, X21, X22, X24]:((((r2_hidden(esk2_3(X20,X21,X22),k1_relat_1(X22))|~r2_hidden(X20,k9_relat_1(X22,X21))|~v1_relat_1(X22))&(r2_hidden(k4_tarski(esk2_3(X20,X21,X22),X20),X22)|~r2_hidden(X20,k9_relat_1(X22,X21))|~v1_relat_1(X22)))&(r2_hidden(esk2_3(X20,X21,X22),X21)|~r2_hidden(X20,k9_relat_1(X22,X21))|~v1_relat_1(X22)))&(~r2_hidden(X24,k1_relat_1(X22))|~r2_hidden(k4_tarski(X24,X20),X22)|~r2_hidden(X24,X21)|r2_hidden(X20,k9_relat_1(X22,X21))|~v1_relat_1(X22))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 13.30/13.50  fof(c_0_15, plain, ![X13, X14, X15]:(~r2_hidden(X13,X14)|~m1_subset_1(X14,k1_zfmisc_1(X15))|m1_subset_1(X13,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 13.30/13.50  fof(c_0_16, plain, ![X31, X32, X33, X34]:(~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|m1_subset_1(k7_relset_1(X31,X32,X33,X34),k1_zfmisc_1(X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).
% 13.30/13.50  cnf(c_0_17, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 13.30/13.50  cnf(c_0_18, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 13.30/13.50  fof(c_0_19, plain, ![X38, X39, X40, X41]:(~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|k7_relset_1(X38,X39,X40,X41)=k9_relat_1(X40,X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 13.30/13.50  fof(c_0_20, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:(m1_subset_1(X6,X1)=>~((r2_hidden(X6,X3)&X5=k1_funct_1(X4,X6)))))))), inference(assume_negation,[status(cth)],[t116_funct_2])).
% 13.30/13.50  fof(c_0_21, plain, ![X25, X26, X27]:(((r2_hidden(X25,k1_relat_1(X27))|~r2_hidden(k4_tarski(X25,X26),X27)|(~v1_relat_1(X27)|~v1_funct_1(X27)))&(X26=k1_funct_1(X27,X25)|~r2_hidden(k4_tarski(X25,X26),X27)|(~v1_relat_1(X27)|~v1_funct_1(X27))))&(~r2_hidden(X25,k1_relat_1(X27))|X26!=k1_funct_1(X27,X25)|r2_hidden(k4_tarski(X25,X26),X27)|(~v1_relat_1(X27)|~v1_funct_1(X27)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 13.30/13.50  fof(c_0_22, plain, ![X49, X50, X51, X52, X53, X55]:((((m1_subset_1(esk5_5(X49,X50,X51,X52,X53),X51)|~r2_hidden(X53,k7_relset_1(X51,X49,X52,X50))|~m1_subset_1(X53,X49)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X51,X49)))|v1_xboole_0(X51)|v1_xboole_0(X50)|v1_xboole_0(X49))&(r2_hidden(k4_tarski(esk5_5(X49,X50,X51,X52,X53),X53),X52)|~r2_hidden(X53,k7_relset_1(X51,X49,X52,X50))|~m1_subset_1(X53,X49)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X51,X49)))|v1_xboole_0(X51)|v1_xboole_0(X50)|v1_xboole_0(X49)))&(r2_hidden(esk5_5(X49,X50,X51,X52,X53),X50)|~r2_hidden(X53,k7_relset_1(X51,X49,X52,X50))|~m1_subset_1(X53,X49)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X51,X49)))|v1_xboole_0(X51)|v1_xboole_0(X50)|v1_xboole_0(X49)))&(~m1_subset_1(X55,X51)|~r2_hidden(k4_tarski(X55,X53),X52)|~r2_hidden(X55,X50)|r2_hidden(X53,k7_relset_1(X51,X49,X52,X50))|~m1_subset_1(X53,X49)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X51,X49)))|v1_xboole_0(X51)|v1_xboole_0(X50)|v1_xboole_0(X49))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t52_relset_1])])])])])])).
% 13.30/13.50  cnf(c_0_23, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 13.30/13.50  cnf(c_0_24, plain, (m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 13.30/13.50  cnf(c_0_25, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(X1,X3))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 13.30/13.50  cnf(c_0_26, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 13.30/13.50  fof(c_0_27, plain, ![X16, X17]:(~v1_relat_1(X16)|(~m1_subset_1(X17,k1_zfmisc_1(X16))|v1_relat_1(X17))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 13.30/13.50  fof(c_0_28, negated_conjecture, ![X61]:(((v1_funct_1(esk9_0)&v1_funct_2(esk9_0,esk6_0,esk7_0))&m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))))&(r2_hidden(esk10_0,k7_relset_1(esk6_0,esk7_0,esk9_0,esk8_0))&(~m1_subset_1(X61,esk6_0)|(~r2_hidden(X61,esk8_0)|esk10_0!=k1_funct_1(esk9_0,X61))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])])).
% 13.30/13.50  fof(c_0_29, plain, ![X18, X19]:v1_relat_1(k2_zfmisc_1(X18,X19)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 13.30/13.50  cnf(c_0_30, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 13.30/13.50  cnf(c_0_31, plain, (r2_hidden(k4_tarski(esk5_5(X1,X2,X3,X4,X5),X5),X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|~r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))|~m1_subset_1(X5,X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 13.30/13.50  cnf(c_0_32, plain, (m1_subset_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~r2_hidden(X1,k7_relset_1(X4,X2,X3,X5))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 13.30/13.50  cnf(c_0_33, plain, (~v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,k7_relset_1(X2,X3,X1,X5))|~v1_xboole_0(X5)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 13.30/13.50  cnf(c_0_34, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 13.30/13.50  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 13.30/13.50  cnf(c_0_36, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 13.30/13.50  cnf(c_0_37, negated_conjecture, (~m1_subset_1(X1,esk6_0)|~r2_hidden(X1,esk8_0)|esk10_0!=k1_funct_1(esk9_0,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 13.30/13.50  cnf(c_0_38, plain, (k1_funct_1(X1,esk5_5(X2,X3,X4,X1,X5))=X5|v1_xboole_0(X2)|v1_xboole_0(X4)|~v1_funct_1(X1)|~v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~r2_hidden(X5,k7_relset_1(X4,X2,X1,X3))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33])).
% 13.30/13.50  cnf(c_0_39, negated_conjecture, (v1_funct_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 13.30/13.50  cnf(c_0_40, negated_conjecture, (v1_relat_1(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])])).
% 13.30/13.50  cnf(c_0_41, negated_conjecture, (r2_hidden(esk10_0,k7_relset_1(esk6_0,esk7_0,esk9_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 13.30/13.50  cnf(c_0_42, plain, (k7_relset_1(X1,X2,X3,X4)=k7_relset_1(X5,X6,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(spm,[status(thm)],[c_0_26, c_0_26])).
% 13.30/13.50  fof(c_0_43, plain, ![X42, X43, X44, X46, X47]:(((r2_hidden(esk3_3(X42,X43,X44),X43)|k1_relset_1(X43,X42,X44)=X43|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X43,X42))))&(~r2_hidden(k4_tarski(esk3_3(X42,X43,X44),X46),X44)|k1_relset_1(X43,X42,X44)=X43|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X43,X42)))))&(k1_relset_1(X43,X42,X44)!=X43|(~r2_hidden(X47,X43)|r2_hidden(k4_tarski(X47,esk4_4(X42,X43,X44,X47)),X44))|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X43,X42))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_relset_1])])])])])])).
% 13.30/13.50  cnf(c_0_44, negated_conjecture, (v1_xboole_0(X1)|v1_xboole_0(X2)|esk10_0!=X3|~m1_subset_1(esk5_5(X2,X4,X1,esk9_0,X3),esk6_0)|~m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r2_hidden(esk5_5(X2,X4,X1,esk9_0,X3),esk8_0)|~r2_hidden(X3,k7_relset_1(X1,X2,esk9_0,X4))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_40])])).
% 13.30/13.50  cnf(c_0_45, plain, (m1_subset_1(esk5_5(X1,X2,X3,X4,X5),X3)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|~r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))|~m1_subset_1(X5,X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 13.30/13.50  cnf(c_0_46, negated_conjecture, (r2_hidden(esk10_0,k7_relset_1(X1,X2,esk9_0,esk8_0))|~m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_35])])).
% 13.30/13.50  fof(c_0_47, plain, ![X35, X36, X37]:(~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|k1_relset_1(X35,X36,X37)=k1_relat_1(X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 13.30/13.50  cnf(c_0_48, plain, (r2_hidden(esk3_3(X1,X2,X3),X2)|k1_relset_1(X2,X1,X3)=X2|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 13.30/13.50  fof(c_0_49, plain, ![X28, X29, X30]:(~v1_xboole_0(X28)|(~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X29,X28)))|v1_xboole_0(X30))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 13.30/13.50  cnf(c_0_50, negated_conjecture, (v1_xboole_0(esk6_0)|v1_xboole_0(X1)|v1_xboole_0(X2)|esk10_0!=X3|~m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,X2)))|~r2_hidden(esk5_5(X2,X1,esk6_0,esk9_0,X3),esk8_0)|~r2_hidden(X3,k7_relset_1(esk6_0,X2,esk9_0,X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_32])).
% 13.30/13.50  cnf(c_0_51, plain, (r2_hidden(esk5_5(X1,X2,X3,X4,X5),X2)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|~r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))|~m1_subset_1(X5,X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 13.30/13.50  cnf(c_0_52, negated_conjecture, (~v1_xboole_0(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_41]), c_0_40]), c_0_35])])).
% 13.30/13.50  cnf(c_0_53, plain, (r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 13.30/13.50  cnf(c_0_54, negated_conjecture, (r2_hidden(esk10_0,k9_relat_1(esk9_0,esk8_0))|~m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_46, c_0_26])).
% 13.30/13.50  cnf(c_0_55, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 13.30/13.50  cnf(c_0_56, plain, (k1_relset_1(X1,X2,X3)=X1|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_17, c_0_48])).
% 13.30/13.50  cnf(c_0_57, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 13.30/13.50  cnf(c_0_58, negated_conjecture, (v1_xboole_0(esk6_0)|v1_xboole_0(X1)|esk10_0!=X2|~m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,X1)))|~r2_hidden(X2,k7_relset_1(esk6_0,X1,esk9_0,esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52]), c_0_32])).
% 13.30/13.50  cnf(c_0_59, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(X1,X3))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_17, c_0_53])).
% 13.30/13.50  cnf(c_0_60, negated_conjecture, (r2_hidden(esk10_0,k9_relat_1(esk9_0,esk8_0))), inference(spm,[status(thm)],[c_0_54, c_0_35])).
% 13.30/13.50  cnf(c_0_61, plain, (X1=k1_relat_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 13.30/13.50  cnf(c_0_62, negated_conjecture, (v1_xboole_0(esk9_0)|~v1_xboole_0(esk7_0)), inference(spm,[status(thm)],[c_0_57, c_0_35])).
% 13.30/13.50  cnf(c_0_63, negated_conjecture, (v1_xboole_0(esk7_0)|v1_xboole_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_41]), c_0_35])])).
% 13.30/13.50  cnf(c_0_64, negated_conjecture, (~v1_xboole_0(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_40])])).
% 13.30/13.50  cnf(c_0_65, plain, (r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X3))|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 13.30/13.50  cnf(c_0_66, negated_conjecture, (esk6_0=k1_relat_1(esk9_0)|~v1_xboole_0(esk6_0)), inference(spm,[status(thm)],[c_0_61, c_0_35])).
% 13.30/13.50  cnf(c_0_67, negated_conjecture, (v1_xboole_0(esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])).
% 13.30/13.50  cnf(c_0_68, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(X1,X3))|~v1_xboole_0(k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_17, c_0_65])).
% 13.30/13.50  cnf(c_0_69, negated_conjecture, (esk6_0=k1_relat_1(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_67])])).
% 13.30/13.50  cnf(c_0_70, negated_conjecture, (~v1_xboole_0(k1_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_60]), c_0_40])])).
% 13.30/13.50  cnf(c_0_71, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_69]), c_0_70]), ['proof']).
% 13.30/13.50  # SZS output end CNFRefutation
% 13.30/13.50  # Proof object total steps             : 72
% 13.30/13.50  # Proof object clause steps            : 45
% 13.30/13.50  # Proof object formula steps           : 27
% 13.30/13.50  # Proof object conjectures             : 23
% 13.30/13.50  # Proof object clause conjectures      : 20
% 13.30/13.50  # Proof object formula conjectures     : 3
% 13.30/13.50  # Proof object initial clauses used    : 20
% 13.30/13.50  # Proof object initial formulas used   : 13
% 13.30/13.50  # Proof object generating inferences   : 23
% 13.30/13.50  # Proof object simplifying inferences  : 26
% 13.30/13.50  # Training examples: 0 positive, 0 negative
% 13.30/13.50  # Parsed axioms                        : 14
% 13.30/13.50  # Removed by relevancy pruning/SinE    : 0
% 13.30/13.50  # Initial clauses                      : 29
% 13.30/13.50  # Removed in clause preprocessing      : 0
% 13.30/13.50  # Initial clauses in saturation        : 29
% 13.30/13.50  # Processed clauses                    : 29384
% 13.30/13.50  # ...of these trivial                  : 116
% 13.30/13.50  # ...subsumed                          : 21708
% 13.30/13.50  # ...remaining for further processing  : 7560
% 13.30/13.50  # Other redundant clauses eliminated   : 116
% 13.30/13.50  # Clauses deleted for lack of memory   : 0
% 13.30/13.50  # Backward-subsumed                    : 2282
% 13.30/13.50  # Backward-rewritten                   : 2269
% 13.30/13.50  # Generated clauses                    : 374576
% 13.30/13.50  # ...of the previous two non-trivial   : 373820
% 13.30/13.50  # Contextual simplify-reflections      : 381
% 13.30/13.50  # Paramodulations                      : 374456
% 13.30/13.50  # Factorizations                       : 0
% 13.30/13.50  # Equation resolutions                 : 119
% 13.30/13.50  # Propositional unsat checks           : 0
% 13.30/13.50  #    Propositional check models        : 0
% 13.30/13.50  #    Propositional check unsatisfiable : 0
% 13.30/13.50  #    Propositional clauses             : 0
% 13.30/13.50  #    Propositional clauses after purity: 0
% 13.30/13.50  #    Propositional unsat core size     : 0
% 13.30/13.50  #    Propositional preprocessing time  : 0.000
% 13.30/13.50  #    Propositional encoding time       : 0.000
% 13.30/13.50  #    Propositional solver time         : 0.000
% 13.30/13.50  #    Success case prop preproc time    : 0.000
% 13.30/13.50  #    Success case prop encoding time   : 0.000
% 13.30/13.50  #    Success case prop solver time     : 0.000
% 13.30/13.50  # Current number of processed clauses  : 2979
% 13.30/13.50  #    Positive orientable unit clauses  : 8
% 13.30/13.50  #    Positive unorientable unit clauses: 0
% 13.30/13.50  #    Negative unit clauses             : 5
% 13.30/13.50  #    Non-unit-clauses                  : 2966
% 13.30/13.50  # Current number of unprocessed clauses: 342094
% 13.30/13.50  # ...number of literals in the above   : 3617488
% 13.30/13.50  # Current number of archived formulas  : 0
% 13.30/13.50  # Current number of archived clauses   : 4581
% 13.30/13.50  # Clause-clause subsumption calls (NU) : 11141669
% 13.30/13.50  # Rec. Clause-clause subsumption calls : 267670
% 13.30/13.50  # Non-unit clause-clause subsumptions  : 21327
% 13.30/13.50  # Unit Clause-clause subsumption calls : 2398
% 13.30/13.50  # Rewrite failures with RHS unbound    : 0
% 13.30/13.50  # BW rewrite match attempts            : 3
% 13.30/13.50  # BW rewrite match successes           : 3
% 13.30/13.50  # Condensation attempts                : 0
% 13.30/13.50  # Condensation successes               : 0
% 13.30/13.50  # Termbank termtop insertions          : 18005141
% 13.36/13.53  
% 13.36/13.53  # -------------------------------------------------
% 13.36/13.53  # User time                : 12.973 s
% 13.36/13.53  # System time              : 0.221 s
% 13.36/13.53  # Total time               : 13.194 s
% 13.36/13.53  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
