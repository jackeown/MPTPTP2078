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
% DateTime   : Thu Dec  3 11:06:36 EST 2020

% Result     : Theorem 3.08s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 224 expanded)
%              Number of clauses        :   36 (  93 expanded)
%              Number of leaves         :   11 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :  240 ( 918 expanded)
%              Number of equality atoms :   16 (  87 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    3 (   1 average)

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

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

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

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

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

fof(cc3_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(c_0_11,negated_conjecture,(
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

fof(c_0_12,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_13,plain,(
    ! [X18,X19,X20,X22] :
      ( ( r2_hidden(esk3_3(X18,X19,X20),k1_relat_1(X20))
        | ~ r2_hidden(X18,k9_relat_1(X20,X19))
        | ~ v1_relat_1(X20) )
      & ( r2_hidden(k4_tarski(esk3_3(X18,X19,X20),X18),X20)
        | ~ r2_hidden(X18,k9_relat_1(X20,X19))
        | ~ v1_relat_1(X20) )
      & ( r2_hidden(esk3_3(X18,X19,X20),X19)
        | ~ r2_hidden(X18,k9_relat_1(X20,X19))
        | ~ v1_relat_1(X20) )
      & ( ~ r2_hidden(X22,k1_relat_1(X20))
        | ~ r2_hidden(k4_tarski(X22,X18),X20)
        | ~ r2_hidden(X22,X19)
        | r2_hidden(X18,k9_relat_1(X20,X19))
        | ~ v1_relat_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

fof(c_0_14,negated_conjecture,(
    ! [X52] :
      ( v1_funct_1(esk8_0)
      & v1_funct_2(esk8_0,esk5_0,esk6_0)
      & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
      & r2_hidden(esk9_0,k7_relset_1(esk5_0,esk6_0,esk8_0,esk7_0))
      & ( ~ m1_subset_1(X52,esk5_0)
        | ~ r2_hidden(X52,esk7_0)
        | esk9_0 != k1_funct_1(esk8_0,X52) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).

fof(c_0_15,plain,(
    ! [X36,X37,X38,X39] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
      | k7_relset_1(X36,X37,X38,X39) = k9_relat_1(X38,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_16,plain,(
    ! [X15,X16,X17] :
      ( ~ r2_hidden(X15,X16)
      | ~ m1_subset_1(X16,k1_zfmisc_1(X17))
      | m1_subset_1(X15,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_17,plain,(
    ! [X32,X33,X34,X35] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
      | m1_subset_1(k7_relset_1(X32,X33,X34,X35),k1_zfmisc_1(X33)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).

cnf(c_0_18,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_20,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | v1_relat_1(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk9_0,k7_relset_1(esk5_0,esk6_0,esk8_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_23,plain,(
    ! [X13,X14] :
      ( ~ v1_xboole_0(X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(X13))
      | v1_xboole_0(X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

fof(c_0_24,plain,(
    ! [X23,X24,X25] :
      ( ( r2_hidden(X23,k1_relat_1(X25))
        | ~ r2_hidden(k4_tarski(X23,X24),X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( X24 = k1_funct_1(X25,X23)
        | ~ r2_hidden(k4_tarski(X23,X24),X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( ~ r2_hidden(X23,k1_relat_1(X25))
        | X24 != k1_funct_1(X25,X23)
        | r2_hidden(k4_tarski(X23,X24),X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

fof(c_0_25,plain,(
    ! [X40,X41,X42,X43,X44,X46] :
      ( ( m1_subset_1(esk4_5(X40,X41,X42,X43,X44),X42)
        | ~ r2_hidden(X44,k7_relset_1(X42,X40,X43,X41))
        | ~ m1_subset_1(X44,X40)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X42,X40)))
        | v1_xboole_0(X42)
        | v1_xboole_0(X41)
        | v1_xboole_0(X40) )
      & ( r2_hidden(k4_tarski(esk4_5(X40,X41,X42,X43,X44),X44),X43)
        | ~ r2_hidden(X44,k7_relset_1(X42,X40,X43,X41))
        | ~ m1_subset_1(X44,X40)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X42,X40)))
        | v1_xboole_0(X42)
        | v1_xboole_0(X41)
        | v1_xboole_0(X40) )
      & ( r2_hidden(esk4_5(X40,X41,X42,X43,X44),X41)
        | ~ r2_hidden(X44,k7_relset_1(X42,X40,X43,X41))
        | ~ m1_subset_1(X44,X40)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X42,X40)))
        | v1_xboole_0(X42)
        | v1_xboole_0(X41)
        | v1_xboole_0(X40) )
      & ( ~ m1_subset_1(X46,X42)
        | ~ r2_hidden(k4_tarski(X46,X44),X43)
        | ~ r2_hidden(X46,X41)
        | r2_hidden(X44,k7_relset_1(X42,X40,X43,X41))
        | ~ m1_subset_1(X44,X40)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X42,X40)))
        | v1_xboole_0(X42)
        | v1_xboole_0(X41)
        | v1_xboole_0(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t52_relset_1])])])])])])).

cnf(c_0_26,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,X3))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_29,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( ~ v1_xboole_0(k7_relset_1(esk5_0,esk6_0,esk8_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_21])).

cnf(c_0_31,plain,
    ( k7_relset_1(X1,X2,X3,X4) = k7_relset_1(X5,X6,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_33,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( r2_hidden(k4_tarski(esk4_5(X1,X2,X3,X4,X5),X5),X4)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))
    | ~ m1_subset_1(X5,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( m1_subset_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ r2_hidden(X1,k7_relset_1(X4,X2,X3,X5)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_37,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,k7_relset_1(X2,X3,X1,X5))
    | ~ v1_xboole_0(X5) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_22]),c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(k7_relset_1(X1,X2,esk8_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])])).

cnf(c_0_39,plain,
    ( v1_xboole_0(k7_relset_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_27])).

cnf(c_0_40,negated_conjecture,
    ( ~ m1_subset_1(X1,esk5_0)
    | ~ r2_hidden(X1,esk7_0)
    | esk9_0 != k1_funct_1(esk8_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_41,plain,
    ( k1_funct_1(X1,esk4_5(X2,X3,X4,X1,X5)) = X5
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ r2_hidden(X5,k7_relset_1(X4,X2,X1,X3)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_29]),c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_43,negated_conjecture,
    ( ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( v1_xboole_0(X1)
    | esk9_0 != X2
    | ~ m1_subset_1(esk4_5(X3,X4,X1,esk8_0,X2),esk5_0)
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r2_hidden(esk4_5(X3,X4,X1,esk8_0,X2),esk7_0)
    | ~ r2_hidden(X2,k7_relset_1(X1,X3,esk8_0,X4)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])]),c_0_43])).

cnf(c_0_45,plain,
    ( m1_subset_1(esk4_5(X1,X2,X3,X4,X5),X3)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))
    | ~ m1_subset_1(X5,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_46,plain,
    ( r2_hidden(k4_tarski(esk3_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_47,plain,(
    ! [X29,X30,X31] :
      ( ~ v1_xboole_0(X29)
      | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | v1_xboole_0(X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).

cnf(c_0_48,negated_conjecture,
    ( v1_xboole_0(esk5_0)
    | esk9_0 != X1
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X2)))
    | ~ r2_hidden(esk4_5(X2,X3,esk5_0,esk8_0,X1),esk7_0)
    | ~ r2_hidden(X1,k7_relset_1(esk5_0,X2,esk8_0,X3)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_36]),c_0_43]),c_0_37])).

cnf(c_0_49,plain,
    ( r2_hidden(esk4_5(X1,X2,X3,X4,X5),X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))
    | ~ m1_subset_1(X5,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_50,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_21]),c_0_32])])).

cnf(c_0_51,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,X3))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_46])).

cnf(c_0_52,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( v1_xboole_0(esk5_0)
    | esk9_0 != X1
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X2)))
    | ~ r2_hidden(X1,k7_relset_1(esk5_0,X2,esk8_0,esk7_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_36]),c_0_43])).

cnf(c_0_54,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,k7_relset_1(X2,X3,X1,X5))
    | ~ v1_xboole_0(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_22]),c_0_29])).

cnf(c_0_55,negated_conjecture,
    ( v1_xboole_0(esk8_0)
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_32])).

cnf(c_0_56,negated_conjecture,
    ( v1_xboole_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_21]),c_0_32])])).

cnf(c_0_57,negated_conjecture,
    ( ~ v1_xboole_0(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_21]),c_0_32])])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56])]),c_0_57]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:59:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 3.08/3.26  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 3.08/3.26  # and selection function SelectMaxLComplexAvoidPosPred.
% 3.08/3.26  #
% 3.08/3.26  # Preprocessing time       : 0.029 s
% 3.08/3.26  # Presaturation interreduction done
% 3.08/3.26  
% 3.08/3.26  # Proof found!
% 3.08/3.26  # SZS status Theorem
% 3.08/3.26  # SZS output start CNFRefutation
% 3.08/3.26  fof(t116_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:(m1_subset_1(X6,X1)=>~((r2_hidden(X6,X3)&X5=k1_funct_1(X4,X6))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_funct_2)).
% 3.08/3.26  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.08/3.26  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 3.08/3.26  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.08/3.26  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.08/3.26  fof(dt_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 3.08/3.26  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.08/3.26  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.08/3.26  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 3.08/3.26  fof(t52_relset_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))<=>?[X6]:((m1_subset_1(X6,X3)&r2_hidden(k4_tarski(X6,X5),X4))&r2_hidden(X6,X2)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relset_1)).
% 3.08/3.26  fof(cc3_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 3.08/3.26  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:(m1_subset_1(X6,X1)=>~((r2_hidden(X6,X3)&X5=k1_funct_1(X4,X6)))))))), inference(assume_negation,[status(cth)],[t116_funct_2])).
% 3.08/3.26  fof(c_0_12, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 3.08/3.26  fof(c_0_13, plain, ![X18, X19, X20, X22]:((((r2_hidden(esk3_3(X18,X19,X20),k1_relat_1(X20))|~r2_hidden(X18,k9_relat_1(X20,X19))|~v1_relat_1(X20))&(r2_hidden(k4_tarski(esk3_3(X18,X19,X20),X18),X20)|~r2_hidden(X18,k9_relat_1(X20,X19))|~v1_relat_1(X20)))&(r2_hidden(esk3_3(X18,X19,X20),X19)|~r2_hidden(X18,k9_relat_1(X20,X19))|~v1_relat_1(X20)))&(~r2_hidden(X22,k1_relat_1(X20))|~r2_hidden(k4_tarski(X22,X18),X20)|~r2_hidden(X22,X19)|r2_hidden(X18,k9_relat_1(X20,X19))|~v1_relat_1(X20))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 3.08/3.26  fof(c_0_14, negated_conjecture, ![X52]:(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,esk5_0,esk6_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))))&(r2_hidden(esk9_0,k7_relset_1(esk5_0,esk6_0,esk8_0,esk7_0))&(~m1_subset_1(X52,esk5_0)|(~r2_hidden(X52,esk7_0)|esk9_0!=k1_funct_1(esk8_0,X52))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).
% 3.08/3.26  fof(c_0_15, plain, ![X36, X37, X38, X39]:(~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))|k7_relset_1(X36,X37,X38,X39)=k9_relat_1(X38,X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 3.08/3.26  fof(c_0_16, plain, ![X15, X16, X17]:(~r2_hidden(X15,X16)|~m1_subset_1(X16,k1_zfmisc_1(X17))|m1_subset_1(X15,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 3.08/3.26  fof(c_0_17, plain, ![X32, X33, X34, X35]:(~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|m1_subset_1(k7_relset_1(X32,X33,X34,X35),k1_zfmisc_1(X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).
% 3.08/3.26  cnf(c_0_18, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 3.08/3.26  cnf(c_0_19, plain, (r2_hidden(esk3_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 3.08/3.26  fof(c_0_20, plain, ![X26, X27, X28]:(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|v1_relat_1(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 3.08/3.26  cnf(c_0_21, negated_conjecture, (r2_hidden(esk9_0,k7_relset_1(esk5_0,esk6_0,esk8_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.08/3.26  cnf(c_0_22, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 3.08/3.26  fof(c_0_23, plain, ![X13, X14]:(~v1_xboole_0(X13)|(~m1_subset_1(X14,k1_zfmisc_1(X13))|v1_xboole_0(X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 3.08/3.26  fof(c_0_24, plain, ![X23, X24, X25]:(((r2_hidden(X23,k1_relat_1(X25))|~r2_hidden(k4_tarski(X23,X24),X25)|(~v1_relat_1(X25)|~v1_funct_1(X25)))&(X24=k1_funct_1(X25,X23)|~r2_hidden(k4_tarski(X23,X24),X25)|(~v1_relat_1(X25)|~v1_funct_1(X25))))&(~r2_hidden(X23,k1_relat_1(X25))|X24!=k1_funct_1(X25,X23)|r2_hidden(k4_tarski(X23,X24),X25)|(~v1_relat_1(X25)|~v1_funct_1(X25)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 3.08/3.26  fof(c_0_25, plain, ![X40, X41, X42, X43, X44, X46]:((((m1_subset_1(esk4_5(X40,X41,X42,X43,X44),X42)|~r2_hidden(X44,k7_relset_1(X42,X40,X43,X41))|~m1_subset_1(X44,X40)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X42,X40)))|v1_xboole_0(X42)|v1_xboole_0(X41)|v1_xboole_0(X40))&(r2_hidden(k4_tarski(esk4_5(X40,X41,X42,X43,X44),X44),X43)|~r2_hidden(X44,k7_relset_1(X42,X40,X43,X41))|~m1_subset_1(X44,X40)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X42,X40)))|v1_xboole_0(X42)|v1_xboole_0(X41)|v1_xboole_0(X40)))&(r2_hidden(esk4_5(X40,X41,X42,X43,X44),X41)|~r2_hidden(X44,k7_relset_1(X42,X40,X43,X41))|~m1_subset_1(X44,X40)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X42,X40)))|v1_xboole_0(X42)|v1_xboole_0(X41)|v1_xboole_0(X40)))&(~m1_subset_1(X46,X42)|~r2_hidden(k4_tarski(X46,X44),X43)|~r2_hidden(X46,X41)|r2_hidden(X44,k7_relset_1(X42,X40,X43,X41))|~m1_subset_1(X44,X40)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X42,X40)))|v1_xboole_0(X42)|v1_xboole_0(X41)|v1_xboole_0(X40))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t52_relset_1])])])])])])).
% 3.08/3.26  cnf(c_0_26, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 3.08/3.26  cnf(c_0_27, plain, (m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.08/3.26  cnf(c_0_28, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(X1,X3))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 3.08/3.26  cnf(c_0_29, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 3.08/3.26  cnf(c_0_30, negated_conjecture, (~v1_xboole_0(k7_relset_1(esk5_0,esk6_0,esk8_0,esk7_0))), inference(spm,[status(thm)],[c_0_18, c_0_21])).
% 3.08/3.26  cnf(c_0_31, plain, (k7_relset_1(X1,X2,X3,X4)=k7_relset_1(X5,X6,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(spm,[status(thm)],[c_0_22, c_0_22])).
% 3.08/3.26  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.08/3.26  cnf(c_0_33, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 3.08/3.26  cnf(c_0_34, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 3.08/3.26  cnf(c_0_35, plain, (r2_hidden(k4_tarski(esk4_5(X1,X2,X3,X4,X5),X5),X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|~r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))|~m1_subset_1(X5,X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 3.08/3.26  cnf(c_0_36, plain, (m1_subset_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~r2_hidden(X1,k7_relset_1(X4,X2,X3,X5))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 3.08/3.26  cnf(c_0_37, plain, (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,k7_relset_1(X2,X3,X1,X5))|~v1_xboole_0(X5)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_22]), c_0_29])).
% 3.08/3.26  cnf(c_0_38, negated_conjecture, (~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_xboole_0(k7_relset_1(X1,X2,esk8_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])])).
% 3.08/3.26  cnf(c_0_39, plain, (v1_xboole_0(k7_relset_1(X1,X2,X3,X4))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_33, c_0_27])).
% 3.08/3.26  cnf(c_0_40, negated_conjecture, (~m1_subset_1(X1,esk5_0)|~r2_hidden(X1,esk7_0)|esk9_0!=k1_funct_1(esk8_0,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.08/3.26  cnf(c_0_41, plain, (k1_funct_1(X1,esk4_5(X2,X3,X4,X1,X5))=X5|v1_xboole_0(X2)|v1_xboole_0(X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~r2_hidden(X5,k7_relset_1(X4,X2,X1,X3))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_29]), c_0_37])).
% 3.08/3.26  cnf(c_0_42, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.08/3.26  cnf(c_0_43, negated_conjecture, (~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 3.08/3.26  cnf(c_0_44, negated_conjecture, (v1_xboole_0(X1)|esk9_0!=X2|~m1_subset_1(esk4_5(X3,X4,X1,esk8_0,X2),esk5_0)|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~r2_hidden(esk4_5(X3,X4,X1,esk8_0,X2),esk7_0)|~r2_hidden(X2,k7_relset_1(X1,X3,esk8_0,X4))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])]), c_0_43])).
% 3.08/3.26  cnf(c_0_45, plain, (m1_subset_1(esk4_5(X1,X2,X3,X4,X5),X3)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|~r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))|~m1_subset_1(X5,X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 3.08/3.26  cnf(c_0_46, plain, (r2_hidden(k4_tarski(esk3_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 3.08/3.26  fof(c_0_47, plain, ![X29, X30, X31]:(~v1_xboole_0(X29)|(~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|v1_xboole_0(X31))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).
% 3.08/3.26  cnf(c_0_48, negated_conjecture, (v1_xboole_0(esk5_0)|esk9_0!=X1|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X2)))|~r2_hidden(esk4_5(X2,X3,esk5_0,esk8_0,X1),esk7_0)|~r2_hidden(X1,k7_relset_1(esk5_0,X2,esk8_0,X3))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_36]), c_0_43]), c_0_37])).
% 3.08/3.26  cnf(c_0_49, plain, (r2_hidden(esk4_5(X1,X2,X3,X4,X5),X2)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|~r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))|~m1_subset_1(X5,X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 3.08/3.26  cnf(c_0_50, negated_conjecture, (~v1_xboole_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_21]), c_0_32])])).
% 3.08/3.26  cnf(c_0_51, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(X1,X3))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_18, c_0_46])).
% 3.08/3.26  cnf(c_0_52, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 3.08/3.26  cnf(c_0_53, negated_conjecture, (v1_xboole_0(esk5_0)|esk9_0!=X1|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X2)))|~r2_hidden(X1,k7_relset_1(esk5_0,X2,esk8_0,esk7_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_36]), c_0_43])).
% 3.08/3.26  cnf(c_0_54, plain, (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,k7_relset_1(X2,X3,X1,X5))|~v1_xboole_0(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_22]), c_0_29])).
% 3.08/3.26  cnf(c_0_55, negated_conjecture, (v1_xboole_0(esk8_0)|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_52, c_0_32])).
% 3.08/3.26  cnf(c_0_56, negated_conjecture, (v1_xboole_0(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_21]), c_0_32])])).
% 3.08/3.26  cnf(c_0_57, negated_conjecture, (~v1_xboole_0(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_21]), c_0_32])])).
% 3.08/3.26  cnf(c_0_58, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_56])]), c_0_57]), ['proof']).
% 3.08/3.26  # SZS output end CNFRefutation
% 3.08/3.26  # Proof object total steps             : 59
% 3.08/3.26  # Proof object clause steps            : 36
% 3.08/3.26  # Proof object formula steps           : 23
% 3.08/3.26  # Proof object conjectures             : 18
% 3.08/3.26  # Proof object clause conjectures      : 15
% 3.08/3.26  # Proof object formula conjectures     : 3
% 3.08/3.26  # Proof object initial clauses used    : 17
% 3.08/3.26  # Proof object initial formulas used   : 11
% 3.08/3.26  # Proof object generating inferences   : 18
% 3.08/3.26  # Proof object simplifying inferences  : 25
% 3.08/3.26  # Training examples: 0 positive, 0 negative
% 3.08/3.26  # Parsed axioms                        : 12
% 3.08/3.26  # Removed by relevancy pruning/SinE    : 0
% 3.08/3.26  # Initial clauses                      : 26
% 3.08/3.26  # Removed in clause preprocessing      : 0
% 3.08/3.26  # Initial clauses in saturation        : 26
% 3.08/3.26  # Processed clauses                    : 17594
% 3.08/3.26  # ...of these trivial                  : 0
% 3.08/3.26  # ...subsumed                          : 13546
% 3.08/3.26  # ...remaining for further processing  : 4048
% 3.08/3.26  # Other redundant clauses eliminated   : 2
% 3.08/3.26  # Clauses deleted for lack of memory   : 0
% 3.08/3.26  # Backward-subsumed                    : 365
% 3.08/3.26  # Backward-rewritten                   : 5
% 3.08/3.26  # Generated clauses                    : 117332
% 3.08/3.26  # ...of the previous two non-trivial   : 117255
% 3.08/3.26  # Contextual simplify-reflections      : 790
% 3.08/3.26  # Paramodulations                      : 117329
% 3.08/3.26  # Factorizations                       : 0
% 3.08/3.26  # Equation resolutions                 : 3
% 3.08/3.26  # Propositional unsat checks           : 0
% 3.08/3.26  #    Propositional check models        : 0
% 3.08/3.26  #    Propositional check unsatisfiable : 0
% 3.08/3.26  #    Propositional clauses             : 0
% 3.08/3.26  #    Propositional clauses after purity: 0
% 3.08/3.26  #    Propositional unsat core size     : 0
% 3.08/3.26  #    Propositional preprocessing time  : 0.000
% 3.08/3.26  #    Propositional encoding time       : 0.000
% 3.08/3.26  #    Propositional solver time         : 0.000
% 3.08/3.26  #    Success case prop preproc time    : 0.000
% 3.08/3.26  #    Success case prop encoding time   : 0.000
% 3.08/3.26  #    Success case prop solver time     : 0.000
% 3.08/3.26  # Current number of processed clauses  : 3652
% 3.08/3.26  #    Positive orientable unit clauses  : 10
% 3.08/3.26  #    Positive unorientable unit clauses: 0
% 3.08/3.26  #    Negative unit clauses             : 7
% 3.08/3.26  #    Non-unit-clauses                  : 3635
% 3.08/3.26  # Current number of unprocessed clauses: 98186
% 3.08/3.26  # ...number of literals in the above   : 729831
% 3.08/3.26  # Current number of archived formulas  : 0
% 3.08/3.26  # Current number of archived clauses   : 396
% 3.08/3.26  # Clause-clause subsumption calls (NU) : 4023694
% 3.08/3.26  # Rec. Clause-clause subsumption calls : 256819
% 3.08/3.26  # Non-unit clause-clause subsumptions  : 11607
% 3.08/3.26  # Unit Clause-clause subsumption calls : 872
% 3.08/3.26  # Rewrite failures with RHS unbound    : 0
% 3.08/3.26  # BW rewrite match attempts            : 2
% 3.08/3.26  # BW rewrite match successes           : 2
% 3.08/3.26  # Condensation attempts                : 0
% 3.08/3.26  # Condensation successes               : 0
% 3.08/3.26  # Termbank termtop insertions          : 4361292
% 3.08/3.27  
% 3.08/3.27  # -------------------------------------------------
% 3.08/3.27  # User time                : 2.854 s
% 3.08/3.27  # System time              : 0.076 s
% 3.08/3.27  # Total time               : 2.929 s
% 3.08/3.27  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
