%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:01:35 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 877 expanded)
%              Number of clauses        :   60 ( 349 expanded)
%              Number of leaves         :   11 ( 210 expanded)
%              Depth                    :   16
%              Number of atoms          :  353 (4848 expanded)
%              Number of equality atoms :  137 (1601 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    3 (   1 average)

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

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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

fof(d4_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( ( r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> r2_hidden(k4_tarski(X2,X3),X1) ) )
          & ( ~ r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

fof(t23_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ! [X4] :
            ~ ( r2_hidden(X4,X2)
              & ! [X5] : ~ r2_hidden(k4_tarski(X5,X4),X3) )
      <=> k2_relset_1(X1,X2,X3) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relset_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(c_0_11,negated_conjecture,(
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

fof(c_0_12,plain,(
    ! [X42,X43,X44] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
      | k1_relset_1(X42,X43,X44) = k1_relat_1(X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_13,plain,(
    ! [X52,X53,X54] :
      ( ( ~ v1_funct_2(X54,X52,X53)
        | X52 = k1_relset_1(X52,X53,X54)
        | X53 = k1_xboole_0
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) )
      & ( X52 != k1_relset_1(X52,X53,X54)
        | v1_funct_2(X54,X52,X53)
        | X53 = k1_xboole_0
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) )
      & ( ~ v1_funct_2(X54,X52,X53)
        | X52 = k1_relset_1(X52,X53,X54)
        | X52 != k1_xboole_0
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) )
      & ( X52 != k1_relset_1(X52,X53,X54)
        | v1_funct_2(X54,X52,X53)
        | X52 != k1_xboole_0
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) )
      & ( ~ v1_funct_2(X54,X52,X53)
        | X54 = k1_xboole_0
        | X52 = k1_xboole_0
        | X53 != k1_xboole_0
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) )
      & ( X54 != k1_xboole_0
        | v1_funct_2(X54,X52,X53)
        | X52 = k1_xboole_0
        | X53 != k1_xboole_0
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_14,plain,(
    ! [X12,X13] :
      ( ~ v1_relat_1(X12)
      | ~ m1_subset_1(X13,k1_zfmisc_1(X12))
      | v1_relat_1(X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_15,negated_conjecture,(
    ! [X58] :
      ( v1_funct_1(esk12_0)
      & v1_funct_2(esk12_0,esk10_0,esk11_0)
      & m1_subset_1(esk12_0,k1_zfmisc_1(k2_zfmisc_1(esk10_0,esk11_0)))
      & ( r2_hidden(esk13_1(X58),esk10_0)
        | ~ r2_hidden(X58,esk11_0) )
      & ( X58 = k1_funct_1(esk12_0,esk13_1(X58))
        | ~ r2_hidden(X58,esk11_0) )
      & k2_relset_1(esk10_0,esk11_0,esk12_0) != esk11_0 ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])])).

fof(c_0_16,plain,(
    ! [X25,X26] : v1_relat_1(k2_zfmisc_1(X25,X26)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_17,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X30,X31,X32,X34,X35,X36,X38] :
      ( ( r2_hidden(esk5_3(X30,X31,X32),k1_relat_1(X30))
        | ~ r2_hidden(X32,X31)
        | X31 != k2_relat_1(X30)
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30) )
      & ( X32 = k1_funct_1(X30,esk5_3(X30,X31,X32))
        | ~ r2_hidden(X32,X31)
        | X31 != k2_relat_1(X30)
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30) )
      & ( ~ r2_hidden(X35,k1_relat_1(X30))
        | X34 != k1_funct_1(X30,X35)
        | r2_hidden(X34,X31)
        | X31 != k2_relat_1(X30)
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30) )
      & ( ~ r2_hidden(esk6_2(X30,X36),X36)
        | ~ r2_hidden(X38,k1_relat_1(X30))
        | esk6_2(X30,X36) != k1_funct_1(X30,X38)
        | X36 = k2_relat_1(X30)
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30) )
      & ( r2_hidden(esk7_2(X30,X36),k1_relat_1(X30))
        | r2_hidden(esk6_2(X30,X36),X36)
        | X36 = k2_relat_1(X30)
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30) )
      & ( esk6_2(X30,X36) = k1_funct_1(X30,esk7_2(X30,X36))
        | r2_hidden(esk6_2(X30,X36),X36)
        | X36 = k2_relat_1(X30)
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

cnf(c_0_20,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk12_0,k1_zfmisc_1(k2_zfmisc_1(esk10_0,esk11_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( X1 = k1_relat_1(X2)
    | X1 != k1_xboole_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_2(esk12_0,esk10_0,esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_26,plain,(
    ! [X27,X28,X29] :
      ( ( X29 != k1_funct_1(X27,X28)
        | r2_hidden(k4_tarski(X28,X29),X27)
        | ~ r2_hidden(X28,k1_relat_1(X27))
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( ~ r2_hidden(k4_tarski(X28,X29),X27)
        | X29 = k1_funct_1(X27,X28)
        | ~ r2_hidden(X28,k1_relat_1(X27))
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( X29 != k1_funct_1(X27,X28)
        | X29 = k1_xboole_0
        | r2_hidden(X28,k1_relat_1(X27))
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( X29 != k1_xboole_0
        | X29 = k1_funct_1(X27,X28)
        | r2_hidden(X28,k1_relat_1(X27))
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).

cnf(c_0_27,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( X1 = k1_funct_1(esk12_0,esk13_1(X1))
    | ~ r2_hidden(X1,esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_1(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_30,negated_conjecture,
    ( v1_relat_1(esk12_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_31,negated_conjecture,
    ( esk10_0 = k1_relat_1(esk12_0)
    | esk10_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_21])])).

cnf(c_0_32,negated_conjecture,
    ( esk12_0 = k1_xboole_0
    | esk10_0 = k1_xboole_0
    | esk11_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_24]),c_0_21])])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk13_1(X1),esk10_0)
    | ~ r2_hidden(X1,esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_34,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X3,k1_relat_1(X2))
    | X1 != k1_funct_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_35,plain,(
    ! [X45,X46,X47,X49,X50] :
      ( ( r2_hidden(esk8_3(X45,X46,X47),X46)
        | k2_relset_1(X45,X46,X47) = X46
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) )
      & ( ~ r2_hidden(k4_tarski(X49,esk8_3(X45,X46,X47)),X47)
        | k2_relset_1(X45,X46,X47) = X46
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) )
      & ( k2_relset_1(X45,X46,X47) != X46
        | ~ r2_hidden(X50,X46)
        | r2_hidden(k4_tarski(esk9_4(X45,X46,X47,X50),X50),X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_relset_1])])])])])])).

fof(c_0_36,plain,(
    ! [X14,X15,X16,X18,X19,X20,X21,X23] :
      ( ( ~ r2_hidden(X16,X15)
        | r2_hidden(k4_tarski(esk2_3(X14,X15,X16),X16),X14)
        | X15 != k2_relat_1(X14) )
      & ( ~ r2_hidden(k4_tarski(X19,X18),X14)
        | r2_hidden(X18,X15)
        | X15 != k2_relat_1(X14) )
      & ( ~ r2_hidden(esk3_2(X20,X21),X21)
        | ~ r2_hidden(k4_tarski(X23,esk3_2(X20,X21)),X20)
        | X21 = k2_relat_1(X20) )
      & ( r2_hidden(esk3_2(X20,X21),X21)
        | r2_hidden(k4_tarski(esk4_2(X20,X21),esk3_2(X20,X21)),X20)
        | X21 = k2_relat_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(X1,X2)
    | X2 != k2_relat_1(esk12_0)
    | ~ r2_hidden(esk13_1(X1),k1_relat_1(esk12_0))
    | ~ r2_hidden(X1,esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])]),c_0_30])])).

cnf(c_0_38,negated_conjecture,
    ( k1_relat_1(esk12_0) = k1_xboole_0
    | esk12_0 = k1_xboole_0
    | esk11_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( esk12_0 = k1_xboole_0
    | r2_hidden(esk13_1(X1),k1_xboole_0)
    | esk11_0 != k1_xboole_0
    | ~ r2_hidden(X1,esk11_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_32])).

cnf(c_0_40,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_41,negated_conjecture,
    ( X1 = k1_xboole_0
    | r2_hidden(esk13_1(X1),k1_relat_1(esk12_0))
    | ~ r2_hidden(X1,esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_28]),c_0_29])])]),c_0_30])])).

fof(c_0_42,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_43,plain,
    ( k2_relset_1(X2,X3,X4) = X3
    | ~ r2_hidden(k4_tarski(X1,esk8_3(X2,X3,X4)),X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( r2_hidden(k4_tarski(esk2_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( esk12_0 = k1_xboole_0
    | r2_hidden(X1,X2)
    | X2 != k2_relat_1(esk12_0)
    | esk11_0 != k1_xboole_0
    | ~ r2_hidden(X1,esk11_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_46,plain,
    ( r2_hidden(esk8_3(X1,X2,X3),X2)
    | k2_relset_1(X1,X2,X3) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_47,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | X1 != k1_funct_1(X2,X3)
    | ~ r2_hidden(X3,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_48,plain,
    ( X1 = k1_relat_1(X2)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( X1 = k1_xboole_0
    | r2_hidden(X1,X2)
    | X2 != k2_relat_1(esk12_0)
    | ~ r2_hidden(X1,esk11_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_41])).

cnf(c_0_50,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_51,plain,
    ( k2_relset_1(X1,X2,X3) = X2
    | X4 != k2_relat_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(esk8_3(X1,X2,X3),X4) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( k2_relset_1(X1,esk11_0,X2) = esk11_0
    | esk12_0 = k1_xboole_0
    | r2_hidden(esk8_3(X1,esk11_0,X2),X3)
    | X3 != k2_relat_1(esk12_0)
    | esk11_0 != k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk11_0))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(k4_tarski(esk13_1(X1),X1),esk12_0)
    | ~ r2_hidden(esk13_1(X1),k1_relat_1(esk12_0))
    | ~ r2_hidden(X1,esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_28]),c_0_29])])]),c_0_30])])).

cnf(c_0_54,negated_conjecture,
    ( esk10_0 = k1_relat_1(esk12_0)
    | esk11_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_24]),c_0_21])])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_56,negated_conjecture,
    ( esk1_2(esk11_0,X1) = k1_xboole_0
    | r2_hidden(esk1_2(esk11_0,X1),X2)
    | r1_tarski(esk11_0,X1)
    | X2 != k2_relat_1(esk12_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( k2_relset_1(X1,esk11_0,X2) = esk11_0
    | esk12_0 = k1_xboole_0
    | X3 != k2_relat_1(esk12_0)
    | X3 != k2_relat_1(X2)
    | esk11_0 != k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk11_0))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( k2_relset_1(X1,X2,esk12_0) = X2
    | ~ m1_subset_1(esk12_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(esk13_1(esk8_3(X1,X2,esk12_0)),k1_relat_1(esk12_0))
    | ~ r2_hidden(esk8_3(X1,X2,esk12_0),esk11_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( esk11_0 = k1_xboole_0
    | r2_hidden(esk13_1(X1),k1_relat_1(esk12_0))
    | ~ r2_hidden(X1,esk11_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( esk1_2(esk11_0,X1) = k1_xboole_0
    | r1_tarski(esk11_0,X1)
    | X1 != k2_relat_1(esk12_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( k2_relset_1(X1,esk11_0,X2) = esk11_0
    | esk12_0 = k1_xboole_0
    | k2_relat_1(esk12_0) != k2_relat_1(X2)
    | esk11_0 != k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk11_0))) ),
    inference(er,[status(thm)],[c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( k2_relset_1(X1,X2,esk12_0) = X2
    | esk11_0 = k1_xboole_0
    | ~ m1_subset_1(esk12_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(esk8_3(X1,X2,esk12_0),esk11_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(k1_xboole_0,esk11_0)
    | r1_tarski(esk11_0,X1)
    | X1 != k2_relat_1(esk12_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_60])).

fof(c_0_64,plain,(
    ! [X40,X41] :
      ( ~ r2_hidden(X40,X41)
      | ~ r1_tarski(X41,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_65,negated_conjecture,
    ( k2_relset_1(esk10_0,esk11_0,esk12_0) != esk11_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_66,negated_conjecture,
    ( k2_relset_1(X1,esk11_0,esk12_0) = esk11_0
    | esk12_0 = k1_xboole_0
    | esk11_0 != k1_xboole_0
    | ~ m1_subset_1(esk12_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk11_0))) ),
    inference(er,[status(thm)],[c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( k2_relset_1(X1,esk11_0,esk12_0) = esk11_0
    | esk11_0 = k1_xboole_0
    | ~ m1_subset_1(esk12_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk11_0))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_46])).

cnf(c_0_68,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(k1_xboole_0,esk11_0)
    | r1_tarski(esk11_0,k2_relat_1(esk12_0)) ),
    inference(er,[status(thm)],[c_0_63])).

cnf(c_0_70,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_50])).

cnf(c_0_72,negated_conjecture,
    ( esk12_0 = k1_xboole_0
    | esk11_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_21])])).

cnf(c_0_73,negated_conjecture,
    ( esk11_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_67]),c_0_21])])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(X1,k2_relat_1(esk12_0))
    | r2_hidden(k1_xboole_0,esk11_0)
    | ~ r2_hidden(X1,esk11_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_75,plain,
    ( ~ r2_hidden(X1,X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_76,negated_conjecture,
    ( esk12_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_73])])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(X1,k2_relat_1(k1_xboole_0))
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_73]),c_0_73]),c_0_75]),c_0_76])).

cnf(c_0_78,negated_conjecture,
    ( k2_relset_1(X1,X2,X3) = X2
    | k2_relat_1(k1_xboole_0) != k2_relat_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(esk8_3(X1,X2,X3),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_77])).

cnf(c_0_79,negated_conjecture,
    ( k2_relset_1(esk10_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_73]),c_0_73]),c_0_76])).

cnf(c_0_80,negated_conjecture,
    ( k2_relset_1(X1,k1_xboole_0,X2) = k1_xboole_0
    | k2_relat_1(k1_xboole_0) != k2_relat_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_78,c_0_46])).

cnf(c_0_81,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(esk10_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_73]),c_0_76])).

cnf(c_0_82,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:21:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.46  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.18/0.46  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.18/0.46  #
% 0.18/0.46  # Preprocessing time       : 0.029 s
% 0.18/0.46  # Presaturation interreduction done
% 0.18/0.46  
% 0.18/0.46  # Proof found!
% 0.18/0.46  # SZS status Theorem
% 0.18/0.46  # SZS output start CNFRefutation
% 0.18/0.46  fof(t16_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~((r2_hidden(X5,X1)&X4=k1_funct_1(X3,X5)))))=>k2_relset_1(X1,X2,X3)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_2)).
% 0.18/0.46  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.18/0.46  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.18/0.46  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.18/0.46  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.18/0.46  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 0.18/0.46  fof(d4_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:((r2_hidden(X2,k1_relat_1(X1))=>(X3=k1_funct_1(X1,X2)<=>r2_hidden(k4_tarski(X2,X3),X1)))&(~(r2_hidden(X2,k1_relat_1(X1)))=>(X3=k1_funct_1(X1,X2)<=>X3=k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 0.18/0.46  fof(t23_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~(r2_hidden(k4_tarski(X5,X4),X3))))<=>k2_relset_1(X1,X2,X3)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_relset_1)).
% 0.18/0.46  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 0.18/0.46  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.18/0.46  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.18/0.46  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~((r2_hidden(X5,X1)&X4=k1_funct_1(X3,X5)))))=>k2_relset_1(X1,X2,X3)=X2))), inference(assume_negation,[status(cth)],[t16_funct_2])).
% 0.18/0.46  fof(c_0_12, plain, ![X42, X43, X44]:(~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))|k1_relset_1(X42,X43,X44)=k1_relat_1(X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.18/0.46  fof(c_0_13, plain, ![X52, X53, X54]:((((~v1_funct_2(X54,X52,X53)|X52=k1_relset_1(X52,X53,X54)|X53=k1_xboole_0|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))))&(X52!=k1_relset_1(X52,X53,X54)|v1_funct_2(X54,X52,X53)|X53=k1_xboole_0|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))))&((~v1_funct_2(X54,X52,X53)|X52=k1_relset_1(X52,X53,X54)|X52!=k1_xboole_0|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))))&(X52!=k1_relset_1(X52,X53,X54)|v1_funct_2(X54,X52,X53)|X52!=k1_xboole_0|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))))))&((~v1_funct_2(X54,X52,X53)|X54=k1_xboole_0|X52=k1_xboole_0|X53!=k1_xboole_0|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))))&(X54!=k1_xboole_0|v1_funct_2(X54,X52,X53)|X52=k1_xboole_0|X53!=k1_xboole_0|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.18/0.46  fof(c_0_14, plain, ![X12, X13]:(~v1_relat_1(X12)|(~m1_subset_1(X13,k1_zfmisc_1(X12))|v1_relat_1(X13))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.18/0.46  fof(c_0_15, negated_conjecture, ![X58]:(((v1_funct_1(esk12_0)&v1_funct_2(esk12_0,esk10_0,esk11_0))&m1_subset_1(esk12_0,k1_zfmisc_1(k2_zfmisc_1(esk10_0,esk11_0))))&(((r2_hidden(esk13_1(X58),esk10_0)|~r2_hidden(X58,esk11_0))&(X58=k1_funct_1(esk12_0,esk13_1(X58))|~r2_hidden(X58,esk11_0)))&k2_relset_1(esk10_0,esk11_0,esk12_0)!=esk11_0)), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])])).
% 0.18/0.46  fof(c_0_16, plain, ![X25, X26]:v1_relat_1(k2_zfmisc_1(X25,X26)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.18/0.46  cnf(c_0_17, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.46  cnf(c_0_18, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.46  fof(c_0_19, plain, ![X30, X31, X32, X34, X35, X36, X38]:((((r2_hidden(esk5_3(X30,X31,X32),k1_relat_1(X30))|~r2_hidden(X32,X31)|X31!=k2_relat_1(X30)|(~v1_relat_1(X30)|~v1_funct_1(X30)))&(X32=k1_funct_1(X30,esk5_3(X30,X31,X32))|~r2_hidden(X32,X31)|X31!=k2_relat_1(X30)|(~v1_relat_1(X30)|~v1_funct_1(X30))))&(~r2_hidden(X35,k1_relat_1(X30))|X34!=k1_funct_1(X30,X35)|r2_hidden(X34,X31)|X31!=k2_relat_1(X30)|(~v1_relat_1(X30)|~v1_funct_1(X30))))&((~r2_hidden(esk6_2(X30,X36),X36)|(~r2_hidden(X38,k1_relat_1(X30))|esk6_2(X30,X36)!=k1_funct_1(X30,X38))|X36=k2_relat_1(X30)|(~v1_relat_1(X30)|~v1_funct_1(X30)))&((r2_hidden(esk7_2(X30,X36),k1_relat_1(X30))|r2_hidden(esk6_2(X30,X36),X36)|X36=k2_relat_1(X30)|(~v1_relat_1(X30)|~v1_funct_1(X30)))&(esk6_2(X30,X36)=k1_funct_1(X30,esk7_2(X30,X36))|r2_hidden(esk6_2(X30,X36),X36)|X36=k2_relat_1(X30)|(~v1_relat_1(X30)|~v1_funct_1(X30)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.18/0.46  cnf(c_0_20, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.46  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk12_0,k1_zfmisc_1(k2_zfmisc_1(esk10_0,esk11_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.46  cnf(c_0_22, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.46  cnf(c_0_23, plain, (X1=k1_relat_1(X2)|X1!=k1_xboole_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.18/0.46  cnf(c_0_24, negated_conjecture, (v1_funct_2(esk12_0,esk10_0,esk11_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.46  cnf(c_0_25, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X1,X2,X3)|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.46  fof(c_0_26, plain, ![X27, X28, X29]:(((X29!=k1_funct_1(X27,X28)|r2_hidden(k4_tarski(X28,X29),X27)|~r2_hidden(X28,k1_relat_1(X27))|(~v1_relat_1(X27)|~v1_funct_1(X27)))&(~r2_hidden(k4_tarski(X28,X29),X27)|X29=k1_funct_1(X27,X28)|~r2_hidden(X28,k1_relat_1(X27))|(~v1_relat_1(X27)|~v1_funct_1(X27))))&((X29!=k1_funct_1(X27,X28)|X29=k1_xboole_0|r2_hidden(X28,k1_relat_1(X27))|(~v1_relat_1(X27)|~v1_funct_1(X27)))&(X29!=k1_xboole_0|X29=k1_funct_1(X27,X28)|r2_hidden(X28,k1_relat_1(X27))|(~v1_relat_1(X27)|~v1_funct_1(X27))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).
% 0.18/0.46  cnf(c_0_27, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.46  cnf(c_0_28, negated_conjecture, (X1=k1_funct_1(esk12_0,esk13_1(X1))|~r2_hidden(X1,esk11_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.46  cnf(c_0_29, negated_conjecture, (v1_funct_1(esk12_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.46  cnf(c_0_30, negated_conjecture, (v1_relat_1(esk12_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])])).
% 0.18/0.46  cnf(c_0_31, negated_conjecture, (esk10_0=k1_relat_1(esk12_0)|esk10_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_21])])).
% 0.18/0.46  cnf(c_0_32, negated_conjecture, (esk12_0=k1_xboole_0|esk10_0=k1_xboole_0|esk11_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_24]), c_0_21])])).
% 0.18/0.46  cnf(c_0_33, negated_conjecture, (r2_hidden(esk13_1(X1),esk10_0)|~r2_hidden(X1,esk11_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.46  cnf(c_0_34, plain, (X1=k1_xboole_0|r2_hidden(X3,k1_relat_1(X2))|X1!=k1_funct_1(X2,X3)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.18/0.46  fof(c_0_35, plain, ![X45, X46, X47, X49, X50]:(((r2_hidden(esk8_3(X45,X46,X47),X46)|k2_relset_1(X45,X46,X47)=X46|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))))&(~r2_hidden(k4_tarski(X49,esk8_3(X45,X46,X47)),X47)|k2_relset_1(X45,X46,X47)=X46|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))))&(k2_relset_1(X45,X46,X47)!=X46|(~r2_hidden(X50,X46)|r2_hidden(k4_tarski(esk9_4(X45,X46,X47,X50),X50),X47))|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_relset_1])])])])])])).
% 0.18/0.46  fof(c_0_36, plain, ![X14, X15, X16, X18, X19, X20, X21, X23]:(((~r2_hidden(X16,X15)|r2_hidden(k4_tarski(esk2_3(X14,X15,X16),X16),X14)|X15!=k2_relat_1(X14))&(~r2_hidden(k4_tarski(X19,X18),X14)|r2_hidden(X18,X15)|X15!=k2_relat_1(X14)))&((~r2_hidden(esk3_2(X20,X21),X21)|~r2_hidden(k4_tarski(X23,esk3_2(X20,X21)),X20)|X21=k2_relat_1(X20))&(r2_hidden(esk3_2(X20,X21),X21)|r2_hidden(k4_tarski(esk4_2(X20,X21),esk3_2(X20,X21)),X20)|X21=k2_relat_1(X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.18/0.46  cnf(c_0_37, negated_conjecture, (r2_hidden(X1,X2)|X2!=k2_relat_1(esk12_0)|~r2_hidden(esk13_1(X1),k1_relat_1(esk12_0))|~r2_hidden(X1,esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])])]), c_0_30])])).
% 0.18/0.46  cnf(c_0_38, negated_conjecture, (k1_relat_1(esk12_0)=k1_xboole_0|esk12_0=k1_xboole_0|esk11_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.18/0.46  cnf(c_0_39, negated_conjecture, (esk12_0=k1_xboole_0|r2_hidden(esk13_1(X1),k1_xboole_0)|esk11_0!=k1_xboole_0|~r2_hidden(X1,esk11_0)), inference(spm,[status(thm)],[c_0_33, c_0_32])).
% 0.18/0.46  cnf(c_0_40, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.46  cnf(c_0_41, negated_conjecture, (X1=k1_xboole_0|r2_hidden(esk13_1(X1),k1_relat_1(esk12_0))|~r2_hidden(X1,esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_28]), c_0_29])])]), c_0_30])])).
% 0.18/0.46  fof(c_0_42, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.18/0.46  cnf(c_0_43, plain, (k2_relset_1(X2,X3,X4)=X3|~r2_hidden(k4_tarski(X1,esk8_3(X2,X3,X4)),X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.18/0.46  cnf(c_0_44, plain, (r2_hidden(k4_tarski(esk2_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.18/0.46  cnf(c_0_45, negated_conjecture, (esk12_0=k1_xboole_0|r2_hidden(X1,X2)|X2!=k2_relat_1(esk12_0)|esk11_0!=k1_xboole_0|~r2_hidden(X1,esk11_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])).
% 0.18/0.46  cnf(c_0_46, plain, (r2_hidden(esk8_3(X1,X2,X3),X2)|k2_relset_1(X1,X2,X3)=X2|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.18/0.46  cnf(c_0_47, plain, (r2_hidden(k4_tarski(X3,X1),X2)|X1!=k1_funct_1(X2,X3)|~r2_hidden(X3,k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.18/0.46  cnf(c_0_48, plain, (X1=k1_relat_1(X2)|X3=k1_xboole_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_17, c_0_40])).
% 0.18/0.46  cnf(c_0_49, negated_conjecture, (X1=k1_xboole_0|r2_hidden(X1,X2)|X2!=k2_relat_1(esk12_0)|~r2_hidden(X1,esk11_0)), inference(spm,[status(thm)],[c_0_37, c_0_41])).
% 0.18/0.46  cnf(c_0_50, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.18/0.46  cnf(c_0_51, plain, (k2_relset_1(X1,X2,X3)=X2|X4!=k2_relat_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r2_hidden(esk8_3(X1,X2,X3),X4)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.18/0.46  cnf(c_0_52, negated_conjecture, (k2_relset_1(X1,esk11_0,X2)=esk11_0|esk12_0=k1_xboole_0|r2_hidden(esk8_3(X1,esk11_0,X2),X3)|X3!=k2_relat_1(esk12_0)|esk11_0!=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk11_0)))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.18/0.46  cnf(c_0_53, negated_conjecture, (r2_hidden(k4_tarski(esk13_1(X1),X1),esk12_0)|~r2_hidden(esk13_1(X1),k1_relat_1(esk12_0))|~r2_hidden(X1,esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_28]), c_0_29])])]), c_0_30])])).
% 0.18/0.46  cnf(c_0_54, negated_conjecture, (esk10_0=k1_relat_1(esk12_0)|esk11_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_24]), c_0_21])])).
% 0.18/0.46  cnf(c_0_55, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.18/0.46  cnf(c_0_56, negated_conjecture, (esk1_2(esk11_0,X1)=k1_xboole_0|r2_hidden(esk1_2(esk11_0,X1),X2)|r1_tarski(esk11_0,X1)|X2!=k2_relat_1(esk12_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.18/0.46  cnf(c_0_57, negated_conjecture, (k2_relset_1(X1,esk11_0,X2)=esk11_0|esk12_0=k1_xboole_0|X3!=k2_relat_1(esk12_0)|X3!=k2_relat_1(X2)|esk11_0!=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk11_0)))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.18/0.46  cnf(c_0_58, negated_conjecture, (k2_relset_1(X1,X2,esk12_0)=X2|~m1_subset_1(esk12_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r2_hidden(esk13_1(esk8_3(X1,X2,esk12_0)),k1_relat_1(esk12_0))|~r2_hidden(esk8_3(X1,X2,esk12_0),esk11_0)), inference(spm,[status(thm)],[c_0_43, c_0_53])).
% 0.18/0.46  cnf(c_0_59, negated_conjecture, (esk11_0=k1_xboole_0|r2_hidden(esk13_1(X1),k1_relat_1(esk12_0))|~r2_hidden(X1,esk11_0)), inference(spm,[status(thm)],[c_0_33, c_0_54])).
% 0.18/0.46  cnf(c_0_60, negated_conjecture, (esk1_2(esk11_0,X1)=k1_xboole_0|r1_tarski(esk11_0,X1)|X1!=k2_relat_1(esk12_0)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.18/0.46  cnf(c_0_61, negated_conjecture, (k2_relset_1(X1,esk11_0,X2)=esk11_0|esk12_0=k1_xboole_0|k2_relat_1(esk12_0)!=k2_relat_1(X2)|esk11_0!=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk11_0)))), inference(er,[status(thm)],[c_0_57])).
% 0.18/0.46  cnf(c_0_62, negated_conjecture, (k2_relset_1(X1,X2,esk12_0)=X2|esk11_0=k1_xboole_0|~m1_subset_1(esk12_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r2_hidden(esk8_3(X1,X2,esk12_0),esk11_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.18/0.46  cnf(c_0_63, negated_conjecture, (r2_hidden(k1_xboole_0,esk11_0)|r1_tarski(esk11_0,X1)|X1!=k2_relat_1(esk12_0)), inference(spm,[status(thm)],[c_0_50, c_0_60])).
% 0.18/0.46  fof(c_0_64, plain, ![X40, X41]:(~r2_hidden(X40,X41)|~r1_tarski(X41,X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.18/0.46  cnf(c_0_65, negated_conjecture, (k2_relset_1(esk10_0,esk11_0,esk12_0)!=esk11_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.46  cnf(c_0_66, negated_conjecture, (k2_relset_1(X1,esk11_0,esk12_0)=esk11_0|esk12_0=k1_xboole_0|esk11_0!=k1_xboole_0|~m1_subset_1(esk12_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk11_0)))), inference(er,[status(thm)],[c_0_61])).
% 0.18/0.46  cnf(c_0_67, negated_conjecture, (k2_relset_1(X1,esk11_0,esk12_0)=esk11_0|esk11_0=k1_xboole_0|~m1_subset_1(esk12_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk11_0)))), inference(spm,[status(thm)],[c_0_62, c_0_46])).
% 0.18/0.46  cnf(c_0_68, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.18/0.46  cnf(c_0_69, negated_conjecture, (r2_hidden(k1_xboole_0,esk11_0)|r1_tarski(esk11_0,k2_relat_1(esk12_0))), inference(er,[status(thm)],[c_0_63])).
% 0.18/0.46  cnf(c_0_70, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.18/0.46  cnf(c_0_71, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_55, c_0_50])).
% 0.18/0.46  cnf(c_0_72, negated_conjecture, (esk12_0=k1_xboole_0|esk11_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_21])])).
% 0.18/0.46  cnf(c_0_73, negated_conjecture, (esk11_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_67]), c_0_21])])).
% 0.18/0.46  cnf(c_0_74, negated_conjecture, (r2_hidden(X1,k2_relat_1(esk12_0))|r2_hidden(k1_xboole_0,esk11_0)|~r2_hidden(X1,esk11_0)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.18/0.46  cnf(c_0_75, plain, (~r2_hidden(X1,X1)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.18/0.46  cnf(c_0_76, negated_conjecture, (esk12_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_73])])).
% 0.18/0.46  cnf(c_0_77, negated_conjecture, (r2_hidden(X1,k2_relat_1(k1_xboole_0))|~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_73]), c_0_73]), c_0_75]), c_0_76])).
% 0.18/0.46  cnf(c_0_78, negated_conjecture, (k2_relset_1(X1,X2,X3)=X2|k2_relat_1(k1_xboole_0)!=k2_relat_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r2_hidden(esk8_3(X1,X2,X3),k1_xboole_0)), inference(spm,[status(thm)],[c_0_51, c_0_77])).
% 0.18/0.46  cnf(c_0_79, negated_conjecture, (k2_relset_1(esk10_0,k1_xboole_0,k1_xboole_0)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_73]), c_0_73]), c_0_76])).
% 0.18/0.46  cnf(c_0_80, negated_conjecture, (k2_relset_1(X1,k1_xboole_0,X2)=k1_xboole_0|k2_relat_1(k1_xboole_0)!=k2_relat_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_78, c_0_46])).
% 0.18/0.46  cnf(c_0_81, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(esk10_0,k1_xboole_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_73]), c_0_76])).
% 0.18/0.46  cnf(c_0_82, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81])]), ['proof']).
% 0.18/0.46  # SZS output end CNFRefutation
% 0.18/0.46  # Proof object total steps             : 83
% 0.18/0.46  # Proof object clause steps            : 60
% 0.18/0.46  # Proof object formula steps           : 23
% 0.18/0.46  # Proof object conjectures             : 42
% 0.18/0.46  # Proof object clause conjectures      : 39
% 0.18/0.46  # Proof object formula conjectures     : 3
% 0.18/0.46  # Proof object initial clauses used    : 22
% 0.18/0.46  # Proof object initial formulas used   : 11
% 0.18/0.46  # Proof object generating inferences   : 34
% 0.18/0.46  # Proof object simplifying inferences  : 41
% 0.18/0.46  # Training examples: 0 positive, 0 negative
% 0.18/0.46  # Parsed axioms                        : 11
% 0.18/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.46  # Initial clauses                      : 36
% 0.18/0.46  # Removed in clause preprocessing      : 0
% 0.18/0.46  # Initial clauses in saturation        : 36
% 0.18/0.46  # Processed clauses                    : 874
% 0.18/0.46  # ...of these trivial                  : 62
% 0.18/0.46  # ...subsumed                          : 317
% 0.18/0.46  # ...remaining for further processing  : 495
% 0.18/0.46  # Other redundant clauses eliminated   : 16
% 0.18/0.46  # Clauses deleted for lack of memory   : 0
% 0.18/0.46  # Backward-subsumed                    : 23
% 0.18/0.46  # Backward-rewritten                   : 188
% 0.18/0.46  # Generated clauses                    : 2075
% 0.18/0.46  # ...of the previous two non-trivial   : 2008
% 0.18/0.46  # Contextual simplify-reflections      : 13
% 0.18/0.46  # Paramodulations                      : 1976
% 0.18/0.46  # Factorizations                       : 0
% 0.18/0.46  # Equation resolutions                 : 99
% 0.18/0.46  # Propositional unsat checks           : 0
% 0.18/0.46  #    Propositional check models        : 0
% 0.18/0.46  #    Propositional check unsatisfiable : 0
% 0.18/0.46  #    Propositional clauses             : 0
% 0.18/0.46  #    Propositional clauses after purity: 0
% 0.18/0.46  #    Propositional unsat core size     : 0
% 0.18/0.46  #    Propositional preprocessing time  : 0.000
% 0.18/0.46  #    Propositional encoding time       : 0.000
% 0.18/0.46  #    Propositional solver time         : 0.000
% 0.18/0.46  #    Success case prop preproc time    : 0.000
% 0.18/0.46  #    Success case prop encoding time   : 0.000
% 0.18/0.46  #    Success case prop solver time     : 0.000
% 0.18/0.46  # Current number of processed clauses  : 248
% 0.18/0.46  #    Positive orientable unit clauses  : 11
% 0.18/0.46  #    Positive unorientable unit clauses: 0
% 0.18/0.46  #    Negative unit clauses             : 20
% 0.18/0.46  #    Non-unit-clauses                  : 217
% 0.18/0.46  # Current number of unprocessed clauses: 1006
% 0.18/0.46  # ...number of literals in the above   : 6389
% 0.18/0.46  # Current number of archived formulas  : 0
% 0.18/0.46  # Current number of archived clauses   : 247
% 0.18/0.46  # Clause-clause subsumption calls (NU) : 25242
% 0.18/0.46  # Rec. Clause-clause subsumption calls : 5823
% 0.18/0.46  # Non-unit clause-clause subsumptions  : 237
% 0.18/0.46  # Unit Clause-clause subsumption calls : 1227
% 0.18/0.46  # Rewrite failures with RHS unbound    : 0
% 0.18/0.46  # BW rewrite match attempts            : 5
% 0.18/0.46  # BW rewrite match successes           : 2
% 0.18/0.46  # Condensation attempts                : 0
% 0.18/0.46  # Condensation successes               : 0
% 0.18/0.46  # Termbank termtop insertions          : 42366
% 0.18/0.46  
% 0.18/0.46  # -------------------------------------------------
% 0.18/0.46  # User time                : 0.116 s
% 0.18/0.46  # System time              : 0.009 s
% 0.18/0.46  # Total time               : 0.125 s
% 0.18/0.46  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
