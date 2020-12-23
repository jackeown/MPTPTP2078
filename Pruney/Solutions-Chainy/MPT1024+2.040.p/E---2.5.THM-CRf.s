%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:32 EST 2020

% Result     : Theorem 4.89s
% Output     : CNFRefutation 4.89s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 222 expanded)
%              Number of clauses        :   37 (  89 expanded)
%              Number of leaves         :   13 (  57 expanded)
%              Depth                    :   11
%              Number of atoms          :  261 ( 984 expanded)
%              Number of equality atoms :   15 (  81 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(dt_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

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

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).

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

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(cc3_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(c_0_13,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_14,plain,(
    ! [X26,X27,X28,X30] :
      ( ( r2_hidden(esk3_3(X26,X27,X28),k1_relat_1(X28))
        | ~ r2_hidden(X26,k9_relat_1(X28,X27))
        | ~ v1_relat_1(X28) )
      & ( r2_hidden(k4_tarski(esk3_3(X26,X27,X28),X26),X28)
        | ~ r2_hidden(X26,k9_relat_1(X28,X27))
        | ~ v1_relat_1(X28) )
      & ( r2_hidden(esk3_3(X26,X27,X28),X27)
        | ~ r2_hidden(X26,k9_relat_1(X28,X27))
        | ~ v1_relat_1(X28) )
      & ( ~ r2_hidden(X30,k1_relat_1(X28))
        | ~ r2_hidden(k4_tarski(X30,X26),X28)
        | ~ r2_hidden(X30,X27)
        | r2_hidden(X26,k9_relat_1(X28,X27))
        | ~ v1_relat_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

fof(c_0_15,plain,(
    ! [X19,X20,X21] :
      ( ~ r2_hidden(X19,X20)
      | ~ m1_subset_1(X20,k1_zfmisc_1(X21))
      | m1_subset_1(X19,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_16,plain,(
    ! [X40,X41,X42,X43] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
      | m1_subset_1(k7_relset_1(X40,X41,X42,X43),k1_zfmisc_1(X41)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).

cnf(c_0_17,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X44,X45,X46,X47] :
      ( ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))
      | k7_relset_1(X44,X45,X46,X47) = k9_relat_1(X46,X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_20,negated_conjecture,(
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

fof(c_0_21,plain,(
    ! [X31,X32,X33] :
      ( ( r2_hidden(X31,k1_relat_1(X33))
        | ~ r2_hidden(k4_tarski(X31,X32),X33)
        | ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33) )
      & ( X32 = k1_funct_1(X33,X31)
        | ~ r2_hidden(k4_tarski(X31,X32),X33)
        | ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33) )
      & ( ~ r2_hidden(X31,k1_relat_1(X33))
        | X32 != k1_funct_1(X33,X31)
        | r2_hidden(k4_tarski(X31,X32),X33)
        | ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

fof(c_0_22,plain,(
    ! [X52,X53,X54,X55,X56,X58] :
      ( ( m1_subset_1(esk4_5(X52,X53,X54,X55,X56),X54)
        | ~ r2_hidden(X56,k7_relset_1(X54,X52,X55,X53))
        | ~ m1_subset_1(X56,X52)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X54,X52)))
        | v1_xboole_0(X54)
        | v1_xboole_0(X53)
        | v1_xboole_0(X52) )
      & ( r2_hidden(k4_tarski(esk4_5(X52,X53,X54,X55,X56),X56),X55)
        | ~ r2_hidden(X56,k7_relset_1(X54,X52,X55,X53))
        | ~ m1_subset_1(X56,X52)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X54,X52)))
        | v1_xboole_0(X54)
        | v1_xboole_0(X53)
        | v1_xboole_0(X52) )
      & ( r2_hidden(esk4_5(X52,X53,X54,X55,X56),X53)
        | ~ r2_hidden(X56,k7_relset_1(X54,X52,X55,X53))
        | ~ m1_subset_1(X56,X52)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X54,X52)))
        | v1_xboole_0(X54)
        | v1_xboole_0(X53)
        | v1_xboole_0(X52) )
      & ( ~ m1_subset_1(X58,X54)
        | ~ r2_hidden(k4_tarski(X58,X56),X55)
        | ~ r2_hidden(X58,X53)
        | r2_hidden(X56,k7_relset_1(X54,X52,X55,X53))
        | ~ m1_subset_1(X56,X52)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X54,X52)))
        | v1_xboole_0(X54)
        | v1_xboole_0(X53)
        | v1_xboole_0(X52) ) ) ),
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
    ! [X22,X23] :
      ( ~ v1_relat_1(X22)
      | ~ m1_subset_1(X23,k1_zfmisc_1(X22))
      | v1_relat_1(X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_28,negated_conjecture,(
    ! [X64] :
      ( v1_funct_1(esk8_0)
      & v1_funct_2(esk8_0,esk5_0,esk6_0)
      & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
      & r2_hidden(esk9_0,k7_relset_1(esk5_0,esk6_0,esk8_0,esk7_0))
      & ( ~ r2_hidden(X64,esk5_0)
        | ~ r2_hidden(X64,esk7_0)
        | esk9_0 != k1_funct_1(esk8_0,X64) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])])).

fof(c_0_29,plain,(
    ! [X24,X25] : v1_relat_1(k2_zfmisc_1(X24,X25)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_30,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( r2_hidden(k4_tarski(esk4_5(X1,X2,X3,X4,X5),X5),X4)
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
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( ~ r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk7_0)
    | esk9_0 != k1_funct_1(esk8_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( k1_funct_1(X1,esk4_5(X2,X3,X4,X1,X5)) = X5
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ r2_hidden(X5,k7_relset_1(X4,X2,X1,X3)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk9_0,k7_relset_1(esk5_0,esk6_0,esk8_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_42,plain,(
    ! [X17,X18] :
      ( ~ m1_subset_1(X17,X18)
      | v1_xboole_0(X18)
      | r2_hidden(X17,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_43,negated_conjecture,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | esk9_0 != X3
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(esk4_5(X2,X4,X1,esk8_0,X3),esk5_0)
    | ~ r2_hidden(esk4_5(X2,X4,X1,esk8_0,X3),esk7_0)
    | ~ r2_hidden(X3,k7_relset_1(X1,X2,esk8_0,X4)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40])])).

cnf(c_0_44,plain,
    ( r2_hidden(esk4_5(X1,X2,X3,X4,X5),X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))
    | ~ m1_subset_1(X5,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_45,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_41]),c_0_40]),c_0_35])])).

cnf(c_0_46,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_47,plain,
    ( m1_subset_1(esk4_5(X1,X2,X3,X4,X5),X3)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))
    | ~ m1_subset_1(X5,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_48,plain,
    ( r2_hidden(k4_tarski(esk3_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_49,plain,(
    ! [X37,X38,X39] :
      ( ~ v1_xboole_0(X37)
      | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X38,X37)))
      | v1_xboole_0(X39) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

cnf(c_0_50,negated_conjecture,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | esk9_0 != X3
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ r2_hidden(esk4_5(X1,esk7_0,X2,esk8_0,X3),esk5_0)
    | ~ r2_hidden(X3,k7_relset_1(X2,X1,esk8_0,esk7_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_32])).

cnf(c_0_51,plain,
    ( r2_hidden(esk4_5(X1,X2,X3,X4,X5),X3)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r2_hidden(X5,k7_relset_1(X3,X1,X4,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_32])).

cnf(c_0_52,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,X3))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_48])).

fof(c_0_53,plain,(
    ! [X34,X35,X36] :
      ( ~ v1_xboole_0(X34)
      | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
      | v1_xboole_0(X36) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).

cnf(c_0_54,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( v1_xboole_0(esk5_0)
    | v1_xboole_0(X1)
    | esk9_0 != X2
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1)))
    | ~ r2_hidden(X2,k7_relset_1(esk5_0,X1,esk8_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_45])).

cnf(c_0_56,plain,
    ( ~ v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,k7_relset_1(X2,X3,X1,X5))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_26])).

cnf(c_0_57,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( v1_xboole_0(esk8_0)
    | ~ v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_35])).

cnf(c_0_59,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | v1_xboole_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_41]),c_0_35])])).

cnf(c_0_60,negated_conjecture,
    ( ~ v1_xboole_0(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_41]),c_0_40]),c_0_35])])).

cnf(c_0_61,negated_conjecture,
    ( v1_xboole_0(esk8_0)
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_35])).

cnf(c_0_62,negated_conjecture,
    ( v1_xboole_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62])]),c_0_60]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:20:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 4.89/5.09  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 4.89/5.09  # and selection function SelectMaxLComplexAvoidPosPred.
% 4.89/5.09  #
% 4.89/5.09  # Preprocessing time       : 0.029 s
% 4.89/5.09  # Presaturation interreduction done
% 4.89/5.09  
% 4.89/5.09  # Proof found!
% 4.89/5.09  # SZS status Theorem
% 4.89/5.09  # SZS output start CNFRefutation
% 4.89/5.09  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.89/5.09  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 4.89/5.09  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 4.89/5.09  fof(dt_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 4.89/5.09  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.89/5.09  fof(t115_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:~(((r2_hidden(X6,X1)&r2_hidden(X6,X3))&X5=k1_funct_1(X4,X6)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_funct_2)).
% 4.89/5.09  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 4.89/5.09  fof(t52_relset_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))<=>?[X6]:((m1_subset_1(X6,X3)&r2_hidden(k4_tarski(X6,X5),X4))&r2_hidden(X6,X2)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relset_1)).
% 4.89/5.09  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.89/5.09  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.89/5.09  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.89/5.09  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 4.89/5.09  fof(cc3_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 4.89/5.09  fof(c_0_13, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 4.89/5.09  fof(c_0_14, plain, ![X26, X27, X28, X30]:((((r2_hidden(esk3_3(X26,X27,X28),k1_relat_1(X28))|~r2_hidden(X26,k9_relat_1(X28,X27))|~v1_relat_1(X28))&(r2_hidden(k4_tarski(esk3_3(X26,X27,X28),X26),X28)|~r2_hidden(X26,k9_relat_1(X28,X27))|~v1_relat_1(X28)))&(r2_hidden(esk3_3(X26,X27,X28),X27)|~r2_hidden(X26,k9_relat_1(X28,X27))|~v1_relat_1(X28)))&(~r2_hidden(X30,k1_relat_1(X28))|~r2_hidden(k4_tarski(X30,X26),X28)|~r2_hidden(X30,X27)|r2_hidden(X26,k9_relat_1(X28,X27))|~v1_relat_1(X28))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 4.89/5.09  fof(c_0_15, plain, ![X19, X20, X21]:(~r2_hidden(X19,X20)|~m1_subset_1(X20,k1_zfmisc_1(X21))|m1_subset_1(X19,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 4.89/5.09  fof(c_0_16, plain, ![X40, X41, X42, X43]:(~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|m1_subset_1(k7_relset_1(X40,X41,X42,X43),k1_zfmisc_1(X41))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).
% 4.89/5.09  cnf(c_0_17, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 4.89/5.09  cnf(c_0_18, plain, (r2_hidden(esk3_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 4.89/5.09  fof(c_0_19, plain, ![X44, X45, X46, X47]:(~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))|k7_relset_1(X44,X45,X46,X47)=k9_relat_1(X46,X47)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 4.89/5.09  fof(c_0_20, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:~(((r2_hidden(X6,X1)&r2_hidden(X6,X3))&X5=k1_funct_1(X4,X6))))))), inference(assume_negation,[status(cth)],[t115_funct_2])).
% 4.89/5.09  fof(c_0_21, plain, ![X31, X32, X33]:(((r2_hidden(X31,k1_relat_1(X33))|~r2_hidden(k4_tarski(X31,X32),X33)|(~v1_relat_1(X33)|~v1_funct_1(X33)))&(X32=k1_funct_1(X33,X31)|~r2_hidden(k4_tarski(X31,X32),X33)|(~v1_relat_1(X33)|~v1_funct_1(X33))))&(~r2_hidden(X31,k1_relat_1(X33))|X32!=k1_funct_1(X33,X31)|r2_hidden(k4_tarski(X31,X32),X33)|(~v1_relat_1(X33)|~v1_funct_1(X33)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 4.89/5.09  fof(c_0_22, plain, ![X52, X53, X54, X55, X56, X58]:((((m1_subset_1(esk4_5(X52,X53,X54,X55,X56),X54)|~r2_hidden(X56,k7_relset_1(X54,X52,X55,X53))|~m1_subset_1(X56,X52)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X54,X52)))|v1_xboole_0(X54)|v1_xboole_0(X53)|v1_xboole_0(X52))&(r2_hidden(k4_tarski(esk4_5(X52,X53,X54,X55,X56),X56),X55)|~r2_hidden(X56,k7_relset_1(X54,X52,X55,X53))|~m1_subset_1(X56,X52)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X54,X52)))|v1_xboole_0(X54)|v1_xboole_0(X53)|v1_xboole_0(X52)))&(r2_hidden(esk4_5(X52,X53,X54,X55,X56),X53)|~r2_hidden(X56,k7_relset_1(X54,X52,X55,X53))|~m1_subset_1(X56,X52)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X54,X52)))|v1_xboole_0(X54)|v1_xboole_0(X53)|v1_xboole_0(X52)))&(~m1_subset_1(X58,X54)|~r2_hidden(k4_tarski(X58,X56),X55)|~r2_hidden(X58,X53)|r2_hidden(X56,k7_relset_1(X54,X52,X55,X53))|~m1_subset_1(X56,X52)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X54,X52)))|v1_xboole_0(X54)|v1_xboole_0(X53)|v1_xboole_0(X52))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t52_relset_1])])])])])])).
% 4.89/5.09  cnf(c_0_23, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 4.89/5.09  cnf(c_0_24, plain, (m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 4.89/5.09  cnf(c_0_25, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(X1,X3))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 4.89/5.09  cnf(c_0_26, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 4.89/5.09  fof(c_0_27, plain, ![X22, X23]:(~v1_relat_1(X22)|(~m1_subset_1(X23,k1_zfmisc_1(X22))|v1_relat_1(X23))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 4.89/5.09  fof(c_0_28, negated_conjecture, ![X64]:(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,esk5_0,esk6_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))))&(r2_hidden(esk9_0,k7_relset_1(esk5_0,esk6_0,esk8_0,esk7_0))&(~r2_hidden(X64,esk5_0)|~r2_hidden(X64,esk7_0)|esk9_0!=k1_funct_1(esk8_0,X64)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])])).
% 4.89/5.09  fof(c_0_29, plain, ![X24, X25]:v1_relat_1(k2_zfmisc_1(X24,X25)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 4.89/5.09  cnf(c_0_30, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.89/5.09  cnf(c_0_31, plain, (r2_hidden(k4_tarski(esk4_5(X1,X2,X3,X4,X5),X5),X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|~r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))|~m1_subset_1(X5,X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 4.89/5.09  cnf(c_0_32, plain, (m1_subset_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~r2_hidden(X1,k7_relset_1(X4,X2,X3,X5))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 4.89/5.09  cnf(c_0_33, plain, (~v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,k7_relset_1(X2,X3,X1,X5))|~v1_xboole_0(X5)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 4.89/5.09  cnf(c_0_34, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 4.89/5.09  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 4.89/5.09  cnf(c_0_36, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 4.89/5.09  cnf(c_0_37, negated_conjecture, (~r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk7_0)|esk9_0!=k1_funct_1(esk8_0,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 4.89/5.09  cnf(c_0_38, plain, (k1_funct_1(X1,esk4_5(X2,X3,X4,X1,X5))=X5|v1_xboole_0(X2)|v1_xboole_0(X4)|~v1_funct_1(X1)|~v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~r2_hidden(X5,k7_relset_1(X4,X2,X1,X3))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33])).
% 4.89/5.09  cnf(c_0_39, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 4.89/5.09  cnf(c_0_40, negated_conjecture, (v1_relat_1(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])])).
% 4.89/5.09  cnf(c_0_41, negated_conjecture, (r2_hidden(esk9_0,k7_relset_1(esk5_0,esk6_0,esk8_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 4.89/5.09  fof(c_0_42, plain, ![X17, X18]:(~m1_subset_1(X17,X18)|(v1_xboole_0(X18)|r2_hidden(X17,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 4.89/5.09  cnf(c_0_43, negated_conjecture, (v1_xboole_0(X1)|v1_xboole_0(X2)|esk9_0!=X3|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r2_hidden(esk4_5(X2,X4,X1,esk8_0,X3),esk5_0)|~r2_hidden(esk4_5(X2,X4,X1,esk8_0,X3),esk7_0)|~r2_hidden(X3,k7_relset_1(X1,X2,esk8_0,X4))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_40])])).
% 4.89/5.09  cnf(c_0_44, plain, (r2_hidden(esk4_5(X1,X2,X3,X4,X5),X2)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|~r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))|~m1_subset_1(X5,X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 4.89/5.09  cnf(c_0_45, negated_conjecture, (~v1_xboole_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_41]), c_0_40]), c_0_35])])).
% 4.89/5.09  cnf(c_0_46, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 4.89/5.09  cnf(c_0_47, plain, (m1_subset_1(esk4_5(X1,X2,X3,X4,X5),X3)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|~r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))|~m1_subset_1(X5,X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 4.89/5.09  cnf(c_0_48, plain, (r2_hidden(k4_tarski(esk3_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 4.89/5.09  fof(c_0_49, plain, ![X37, X38, X39]:(~v1_xboole_0(X37)|(~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X38,X37)))|v1_xboole_0(X39))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 4.89/5.09  cnf(c_0_50, negated_conjecture, (v1_xboole_0(X1)|v1_xboole_0(X2)|esk9_0!=X3|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|~r2_hidden(esk4_5(X1,esk7_0,X2,esk8_0,X3),esk5_0)|~r2_hidden(X3,k7_relset_1(X2,X1,esk8_0,esk7_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_32])).
% 4.89/5.09  cnf(c_0_51, plain, (r2_hidden(esk4_5(X1,X2,X3,X4,X5),X3)|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_32])).
% 4.89/5.09  cnf(c_0_52, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(X1,X3))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_17, c_0_48])).
% 4.89/5.09  fof(c_0_53, plain, ![X34, X35, X36]:(~v1_xboole_0(X34)|(~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|v1_xboole_0(X36))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).
% 4.89/5.09  cnf(c_0_54, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 4.89/5.09  cnf(c_0_55, negated_conjecture, (v1_xboole_0(esk5_0)|v1_xboole_0(X1)|esk9_0!=X2|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1)))|~r2_hidden(X2,k7_relset_1(esk5_0,X1,esk8_0,esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_45])).
% 4.89/5.09  cnf(c_0_56, plain, (~v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,k7_relset_1(X2,X3,X1,X5))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_52, c_0_26])).
% 4.89/5.09  cnf(c_0_57, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 4.89/5.09  cnf(c_0_58, negated_conjecture, (v1_xboole_0(esk8_0)|~v1_xboole_0(esk6_0)), inference(spm,[status(thm)],[c_0_54, c_0_35])).
% 4.89/5.09  cnf(c_0_59, negated_conjecture, (v1_xboole_0(esk6_0)|v1_xboole_0(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_41]), c_0_35])])).
% 4.89/5.09  cnf(c_0_60, negated_conjecture, (~v1_xboole_0(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_41]), c_0_40]), c_0_35])])).
% 4.89/5.09  cnf(c_0_61, negated_conjecture, (v1_xboole_0(esk8_0)|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_57, c_0_35])).
% 4.89/5.09  cnf(c_0_62, negated_conjecture, (v1_xboole_0(esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])).
% 4.89/5.09  cnf(c_0_63, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62])]), c_0_60]), ['proof']).
% 4.89/5.09  # SZS output end CNFRefutation
% 4.89/5.09  # Proof object total steps             : 64
% 4.89/5.09  # Proof object clause steps            : 37
% 4.89/5.09  # Proof object formula steps           : 27
% 4.89/5.09  # Proof object conjectures             : 18
% 4.89/5.09  # Proof object clause conjectures      : 15
% 4.89/5.09  # Proof object formula conjectures     : 3
% 4.89/5.09  # Proof object initial clauses used    : 19
% 4.89/5.09  # Proof object initial formulas used   : 13
% 4.89/5.09  # Proof object generating inferences   : 17
% 4.89/5.09  # Proof object simplifying inferences  : 23
% 4.89/5.09  # Training examples: 0 positive, 0 negative
% 4.89/5.09  # Parsed axioms                        : 15
% 4.89/5.09  # Removed by relevancy pruning/SinE    : 0
% 4.89/5.09  # Initial clauses                      : 30
% 4.89/5.09  # Removed in clause preprocessing      : 0
% 4.89/5.09  # Initial clauses in saturation        : 30
% 4.89/5.09  # Processed clauses                    : 16830
% 4.89/5.09  # ...of these trivial                  : 0
% 4.89/5.09  # ...subsumed                          : 11518
% 4.89/5.09  # ...remaining for further processing  : 5312
% 4.89/5.09  # Other redundant clauses eliminated   : 6
% 4.89/5.09  # Clauses deleted for lack of memory   : 0
% 4.89/5.09  # Backward-subsumed                    : 1095
% 4.89/5.09  # Backward-rewritten                   : 18
% 4.89/5.09  # Generated clauses                    : 189492
% 4.89/5.09  # ...of the previous two non-trivial   : 179950
% 4.89/5.09  # Contextual simplify-reflections      : 670
% 4.89/5.09  # Paramodulations                      : 189475
% 4.89/5.09  # Factorizations                       : 8
% 4.89/5.09  # Equation resolutions                 : 8
% 4.89/5.09  # Propositional unsat checks           : 0
% 4.89/5.09  #    Propositional check models        : 0
% 4.89/5.09  #    Propositional check unsatisfiable : 0
% 4.89/5.09  #    Propositional clauses             : 0
% 4.89/5.09  #    Propositional clauses after purity: 0
% 4.89/5.09  #    Propositional unsat core size     : 0
% 4.89/5.09  #    Propositional preprocessing time  : 0.000
% 4.89/5.09  #    Propositional encoding time       : 0.000
% 4.89/5.09  #    Propositional solver time         : 0.000
% 4.89/5.09  #    Success case prop preproc time    : 0.000
% 4.89/5.09  #    Success case prop encoding time   : 0.000
% 4.89/5.09  #    Success case prop solver time     : 0.000
% 4.89/5.09  # Current number of processed clauses  : 4168
% 4.89/5.09  #    Positive orientable unit clauses  : 12
% 4.89/5.09  #    Positive unorientable unit clauses: 0
% 4.89/5.09  #    Negative unit clauses             : 6
% 4.89/5.09  #    Non-unit-clauses                  : 4150
% 4.89/5.09  # Current number of unprocessed clauses: 161773
% 4.89/5.09  # ...number of literals in the above   : 1191191
% 4.89/5.09  # Current number of archived formulas  : 0
% 4.89/5.09  # Current number of archived clauses   : 1144
% 4.89/5.09  # Clause-clause subsumption calls (NU) : 6676336
% 4.89/5.09  # Rec. Clause-clause subsumption calls : 273535
% 4.89/5.09  # Non-unit clause-clause subsumptions  : 12811
% 4.89/5.09  # Unit Clause-clause subsumption calls : 2505
% 4.89/5.09  # Rewrite failures with RHS unbound    : 0
% 4.89/5.09  # BW rewrite match attempts            : 5
% 4.89/5.09  # BW rewrite match successes           : 2
% 4.89/5.09  # Condensation attempts                : 0
% 4.89/5.09  # Condensation successes               : 0
% 4.89/5.09  # Termbank termtop insertions          : 6185416
% 4.89/5.10  
% 4.89/5.10  # -------------------------------------------------
% 4.89/5.10  # User time                : 4.656 s
% 4.89/5.10  # System time              : 0.105 s
% 4.89/5.10  # Total time               : 4.761 s
% 4.89/5.10  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
