%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:01:26 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 420 expanded)
%              Number of clauses        :   85 ( 190 expanded)
%              Number of leaves         :   20 ( 103 expanded)
%              Depth                    :   11
%              Number of atoms          :  380 (1640 expanded)
%              Number of equality atoms :  119 ( 536 expanded)
%              Maximal formula depth    :   25 (   4 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

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

fof(t18_funct_1,axiom,(
    ! [X1,X2] :
      ~ ( ~ ( X1 = k1_xboole_0
            & X2 != k1_xboole_0 )
        & ! [X3] :
            ( ( v1_relat_1(X3)
              & v1_funct_1(X3) )
           => ~ ( X2 = k1_relat_1(X3)
                & r1_tarski(k2_relat_1(X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

fof(t11_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( X2 = k1_xboole_0
         => X1 = k1_xboole_0 )
       => r2_hidden(X3,k1_funct_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_funct_2)).

fof(rc1_relset_1,axiom,(
    ! [X1,X2] :
    ? [X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_xboole_0(X3)
      & v1_relat_1(X3)
      & v4_relat_1(X3,X1)
      & v5_relat_1(X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(dt_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(d2_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k1_funct_2(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5] :
              ( v1_relat_1(X5)
              & v1_funct_1(X5)
              & X4 = X5
              & k1_relat_1(X5) = X1
              & r1_tarski(k2_relat_1(X5),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_funct_2)).

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

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(c_0_20,plain,(
    ! [X35,X36,X37] :
      ( ~ v1_xboole_0(X35)
      | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X36,X35)))
      | v1_xboole_0(X37) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

fof(c_0_21,plain,(
    ! [X21,X22] :
      ( ( ~ m1_subset_1(X21,k1_zfmisc_1(X22))
        | r1_tarski(X21,X22) )
      & ( ~ r1_tarski(X21,X22)
        | m1_subset_1(X21,k1_zfmisc_1(X22)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_22,plain,(
    ! [X19,X20] :
      ( ( k2_zfmisc_1(X19,X20) != k1_xboole_0
        | X19 = k1_xboole_0
        | X20 = k1_xboole_0 )
      & ( X19 != k1_xboole_0
        | k2_zfmisc_1(X19,X20) = k1_xboole_0 )
      & ( X20 != k1_xboole_0
        | k2_zfmisc_1(X19,X20) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_23,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(X16,X17)
        | X16 != X17 )
      & ( r1_tarski(X17,X16)
        | X16 != X17 )
      & ( ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X17,X16)
        | X16 = X17 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_24,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_26,plain,(
    ! [X18] : r1_tarski(k1_xboole_0,X18) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_27,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_28,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( ( ~ r1_tarski(X10,X11)
        | ~ r2_hidden(X12,X10)
        | r2_hidden(X12,X11) )
      & ( r2_hidden(esk2_2(X13,X14),X13)
        | r1_tarski(X13,X14) )
      & ( ~ r2_hidden(esk2_2(X13,X14),X14)
        | r1_tarski(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_29,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_30,plain,(
    ! [X29,X30] :
      ( ( v1_relat_1(esk3_2(X29,X30))
        | X29 = k1_xboole_0 )
      & ( v1_funct_1(esk3_2(X29,X30))
        | X29 = k1_xboole_0 )
      & ( X30 = k1_relat_1(esk3_2(X29,X30))
        | X29 = k1_xboole_0 )
      & ( r1_tarski(k2_relat_1(esk3_2(X29,X30)),X29)
        | X29 = k1_xboole_0 )
      & ( v1_relat_1(esk3_2(X29,X30))
        | X30 != k1_xboole_0 )
      & ( v1_funct_1(esk3_2(X29,X30))
        | X30 != k1_xboole_0 )
      & ( X30 = k1_relat_1(esk3_2(X29,X30))
        | X30 != k1_xboole_0 )
      & ( r1_tarski(k2_relat_1(esk3_2(X29,X30)),X29)
        | X30 != k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_funct_1])])])])).

fof(c_0_31,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => r2_hidden(X3,k1_funct_2(X1,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t11_funct_2])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_34,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_35,plain,(
    ! [X63,X64] :
      ( m1_subset_1(esk7_2(X63,X64),k1_zfmisc_1(k2_zfmisc_1(X63,X64)))
      & v1_xboole_0(esk7_2(X63,X64))
      & v1_relat_1(esk7_2(X63,X64))
      & v4_relat_1(esk7_2(X63,X64),X63)
      & v5_relat_1(esk7_2(X63,X64),X64) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_relset_1])])).

cnf(c_0_36,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_40,plain,
    ( r1_tarski(k2_relat_1(esk3_2(X1,X2)),X1)
    | X2 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_41,plain,(
    ! [X41,X42,X43] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
      | k1_relset_1(X41,X42,X43) = k1_relat_1(X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_42,negated_conjecture,
    ( v1_funct_1(esk10_0)
    & v1_funct_2(esk10_0,esk8_0,esk9_0)
    & m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0)))
    & ( esk9_0 != k1_xboole_0
      | esk8_0 = k1_xboole_0 )
    & ~ r2_hidden(esk10_0,k1_funct_2(esk8_0,esk9_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).

fof(c_0_43,plain,(
    ! [X38,X39,X40] :
      ( ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
      | m1_subset_1(k2_relset_1(X38,X39,X40),k1_zfmisc_1(X39)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).

fof(c_0_44,plain,(
    ! [X44,X45,X46] :
      ( ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))
      | k2_relset_1(X44,X45,X46) = k2_relat_1(X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_46,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_47,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_48,plain,
    ( v1_xboole_0(esk7_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_49,plain,(
    ! [X23,X24] :
      ( ( ~ v4_relat_1(X24,X23)
        | r1_tarski(k1_relat_1(X24),X23)
        | ~ v1_relat_1(X24) )
      & ( ~ r1_tarski(k1_relat_1(X24),X23)
        | v4_relat_1(X24,X23)
        | ~ v1_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_51,plain,(
    ! [X25,X26] :
      ( ( ~ v5_relat_1(X26,X25)
        | r1_tarski(k2_relat_1(X26),X25)
        | ~ v1_relat_1(X26) )
      & ( ~ r1_tarski(k2_relat_1(X26),X25)
        | v5_relat_1(X26,X25)
        | ~ v1_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_52,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_38])).

fof(c_0_53,plain,(
    ! [X66] :
      ( ( v1_funct_1(X66)
        | ~ v1_relat_1(X66)
        | ~ v1_funct_1(X66) )
      & ( v1_funct_2(X66,k1_relat_1(X66),k2_relat_1(X66))
        | ~ v1_relat_1(X66)
        | ~ v1_funct_1(X66) )
      & ( m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X66),k2_relat_1(X66))))
        | ~ v1_relat_1(X66)
        | ~ v1_funct_1(X66) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

cnf(c_0_54,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_34])).

cnf(c_0_55,plain,
    ( r1_tarski(k2_relat_1(esk3_2(X1,k1_xboole_0)),X1) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_56,plain,
    ( X1 = k1_relat_1(esk3_2(X2,X1))
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_57,plain,
    ( v1_funct_1(esk3_2(X1,X2))
    | X2 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_58,plain,
    ( v1_relat_1(esk3_2(X1,X2))
    | X2 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_59,plain,(
    ! [X50,X51,X52,X53,X55,X56,X57,X58,X59,X61] :
      ( ( v1_relat_1(esk4_4(X50,X51,X52,X53))
        | ~ r2_hidden(X53,X52)
        | X52 != k1_funct_2(X50,X51) )
      & ( v1_funct_1(esk4_4(X50,X51,X52,X53))
        | ~ r2_hidden(X53,X52)
        | X52 != k1_funct_2(X50,X51) )
      & ( X53 = esk4_4(X50,X51,X52,X53)
        | ~ r2_hidden(X53,X52)
        | X52 != k1_funct_2(X50,X51) )
      & ( k1_relat_1(esk4_4(X50,X51,X52,X53)) = X50
        | ~ r2_hidden(X53,X52)
        | X52 != k1_funct_2(X50,X51) )
      & ( r1_tarski(k2_relat_1(esk4_4(X50,X51,X52,X53)),X51)
        | ~ r2_hidden(X53,X52)
        | X52 != k1_funct_2(X50,X51) )
      & ( ~ v1_relat_1(X56)
        | ~ v1_funct_1(X56)
        | X55 != X56
        | k1_relat_1(X56) != X50
        | ~ r1_tarski(k2_relat_1(X56),X51)
        | r2_hidden(X55,X52)
        | X52 != k1_funct_2(X50,X51) )
      & ( ~ r2_hidden(esk5_3(X57,X58,X59),X59)
        | ~ v1_relat_1(X61)
        | ~ v1_funct_1(X61)
        | esk5_3(X57,X58,X59) != X61
        | k1_relat_1(X61) != X57
        | ~ r1_tarski(k2_relat_1(X61),X58)
        | X59 = k1_funct_2(X57,X58) )
      & ( v1_relat_1(esk6_3(X57,X58,X59))
        | r2_hidden(esk5_3(X57,X58,X59),X59)
        | X59 = k1_funct_2(X57,X58) )
      & ( v1_funct_1(esk6_3(X57,X58,X59))
        | r2_hidden(esk5_3(X57,X58,X59),X59)
        | X59 = k1_funct_2(X57,X58) )
      & ( esk5_3(X57,X58,X59) = esk6_3(X57,X58,X59)
        | r2_hidden(esk5_3(X57,X58,X59),X59)
        | X59 = k1_funct_2(X57,X58) )
      & ( k1_relat_1(esk6_3(X57,X58,X59)) = X57
        | r2_hidden(esk5_3(X57,X58,X59),X59)
        | X59 = k1_funct_2(X57,X58) )
      & ( r1_tarski(k2_relat_1(esk6_3(X57,X58,X59)),X58)
        | r2_hidden(esk5_3(X57,X58,X59),X59)
        | X59 = k1_funct_2(X57,X58) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).

fof(c_0_60,plain,(
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

cnf(c_0_61,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_63,plain,(
    ! [X32,X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
      | v1_relat_1(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_64,plain,
    ( m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_65,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_66,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_45])).

cnf(c_0_67,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_68,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_69,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_70,plain,
    ( v4_relat_1(esk7_2(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_71,plain,
    ( v1_relat_1(esk7_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_72,plain,
    ( r1_tarski(esk7_2(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_50,c_0_48])).

cnf(c_0_73,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_74,plain,
    ( v5_relat_1(esk7_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_75,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_48])).

cnf(c_0_76,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_77,plain,
    ( k2_relat_1(esk3_2(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_78,plain,
    ( k1_relat_1(esk3_2(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_56])).

cnf(c_0_79,plain,
    ( v1_funct_1(esk3_2(X1,k1_xboole_0)) ),
    inference(er,[status(thm)],[c_0_57])).

cnf(c_0_80,plain,
    ( v1_relat_1(esk3_2(X1,k1_xboole_0)) ),
    inference(er,[status(thm)],[c_0_58])).

cnf(c_0_81,plain,
    ( r2_hidden(X2,X5)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | X2 != X1
    | k1_relat_1(X1) != X3
    | ~ r1_tarski(k2_relat_1(X1),X4)
    | X5 != k1_funct_2(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_82,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_83,negated_conjecture,
    ( k1_relset_1(esk8_0,esk9_0,esk10_0) = k1_relat_1(esk10_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_84,negated_conjecture,
    ( v1_funct_2(esk10_0,esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_85,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_86,plain,
    ( m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_87,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_88,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),X3)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_66])).

cnf(c_0_89,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_67]),c_0_68])])).

cnf(c_0_90,plain,
    ( r1_tarski(k1_relat_1(esk7_2(X1,X2)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])])).

cnf(c_0_91,plain,
    ( esk7_2(X1,X2) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_72])).

fof(c_0_92,plain,(
    ! [X27,X28] : v1_relat_1(k2_zfmisc_1(X27,X28)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_93,plain,
    ( r1_tarski(k2_relat_1(esk7_2(X1,X2)),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_71])])).

cnf(c_0_94,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_75])).

cnf(c_0_95,plain,
    ( m1_subset_1(esk3_2(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78]),c_0_38]),c_0_79]),c_0_80])])).

cnf(c_0_96,plain,
    ( r2_hidden(X1,k1_funct_2(k1_relat_1(X1),X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_81])])])).

cnf(c_0_97,negated_conjecture,
    ( k1_relat_1(esk10_0) = esk8_0
    | esk9_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_62]),c_0_83]),c_0_84])])).

cnf(c_0_98,negated_conjecture,
    ( v1_funct_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_99,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_62])).

cnf(c_0_100,negated_conjecture,
    ( m1_subset_1(k2_relat_1(esk10_0),k1_zfmisc_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_62])).

cnf(c_0_101,negated_conjecture,
    ( r1_tarski(esk10_0,k2_zfmisc_1(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_62])).

cnf(c_0_102,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),X3)
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_103,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X1) ),
    inference(rw,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_104,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_105,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X1) ),
    inference(rw,[status(thm)],[c_0_93,c_0_91])).

cnf(c_0_106,plain,
    ( r1_tarski(esk3_2(k1_xboole_0,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_107,negated_conjecture,
    ( ~ r2_hidden(esk10_0,k1_funct_2(esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_108,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | r2_hidden(esk10_0,k1_funct_2(esk8_0,X1))
    | ~ r1_tarski(k2_relat_1(esk10_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_98]),c_0_99])])).

cnf(c_0_109,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk10_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_100])).

cnf(c_0_110,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk9_0) = esk10_0
    | ~ r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),esk10_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_101])).

cnf(c_0_111,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_102])).

cnf(c_0_112,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_103])).

cnf(c_0_113,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_104,c_0_67])).

cnf(c_0_114,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_105])).

cnf(c_0_115,plain,
    ( esk3_2(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_106])).

cnf(c_0_116,negated_conjecture,
    ( esk9_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_109])])).

cnf(c_0_117,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | ~ r1_tarski(esk9_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_34])])).

cnf(c_0_118,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk9_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_119,plain,
    ( r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,X1))
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_112]),c_0_113]),c_0_114]),c_0_34])])).

cnf(c_0_120,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_115])).

cnf(c_0_121,negated_conjecture,
    ( ~ r2_hidden(esk10_0,k1_funct_2(esk8_0,k1_xboole_0)) ),
    inference(rw,[status(thm)],[c_0_107,c_0_116])).

cnf(c_0_122,negated_conjecture,
    ( esk10_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_117,c_0_116]),c_0_34])])).

cnf(c_0_123,negated_conjecture,
    ( esk8_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_118,c_0_116])])).

cnf(c_0_124,plain,
    ( r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_119,c_0_120])])).

cnf(c_0_125,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_121,c_0_122]),c_0_123]),c_0_124])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:57:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.41  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.21/0.41  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.21/0.41  #
% 0.21/0.41  # Preprocessing time       : 0.030 s
% 0.21/0.41  
% 0.21/0.41  # Proof found!
% 0.21/0.41  # SZS status Theorem
% 0.21/0.41  # SZS output start CNFRefutation
% 0.21/0.41  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 0.21/0.41  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.21/0.41  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.21/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.41  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.21/0.41  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.21/0.41  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.21/0.41  fof(t18_funct_1, axiom, ![X1, X2]:~((~((X1=k1_xboole_0&X2!=k1_xboole_0))&![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>~((X2=k1_relat_1(X3)&r1_tarski(k2_relat_1(X3),X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 0.21/0.41  fof(t11_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0=>X1=k1_xboole_0)=>r2_hidden(X3,k1_funct_2(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_funct_2)).
% 0.21/0.41  fof(rc1_relset_1, axiom, ![X1, X2]:?[X3]:((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&v1_xboole_0(X3))&v1_relat_1(X3))&v4_relat_1(X3,X1))&v5_relat_1(X3,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_relset_1)).
% 0.21/0.41  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.21/0.41  fof(dt_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 0.21/0.41  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.21/0.41  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 0.21/0.41  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 0.21/0.41  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 0.21/0.41  fof(d2_funct_2, axiom, ![X1, X2, X3]:(X3=k1_funct_2(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((((v1_relat_1(X5)&v1_funct_1(X5))&X4=X5)&k1_relat_1(X5)=X1)&r1_tarski(k2_relat_1(X5),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_funct_2)).
% 0.21/0.41  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.21/0.41  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.21/0.41  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.21/0.41  fof(c_0_20, plain, ![X35, X36, X37]:(~v1_xboole_0(X35)|(~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X36,X35)))|v1_xboole_0(X37))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 0.21/0.41  fof(c_0_21, plain, ![X21, X22]:((~m1_subset_1(X21,k1_zfmisc_1(X22))|r1_tarski(X21,X22))&(~r1_tarski(X21,X22)|m1_subset_1(X21,k1_zfmisc_1(X22)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.21/0.41  fof(c_0_22, plain, ![X19, X20]:((k2_zfmisc_1(X19,X20)!=k1_xboole_0|(X19=k1_xboole_0|X20=k1_xboole_0))&((X19!=k1_xboole_0|k2_zfmisc_1(X19,X20)=k1_xboole_0)&(X20!=k1_xboole_0|k2_zfmisc_1(X19,X20)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.21/0.41  fof(c_0_23, plain, ![X16, X17]:(((r1_tarski(X16,X17)|X16!=X17)&(r1_tarski(X17,X16)|X16!=X17))&(~r1_tarski(X16,X17)|~r1_tarski(X17,X16)|X16=X17)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.41  cnf(c_0_24, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.41  cnf(c_0_25, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.41  fof(c_0_26, plain, ![X18]:r1_tarski(k1_xboole_0,X18), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.21/0.41  fof(c_0_27, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.21/0.41  fof(c_0_28, plain, ![X10, X11, X12, X13, X14]:((~r1_tarski(X10,X11)|(~r2_hidden(X12,X10)|r2_hidden(X12,X11)))&((r2_hidden(esk2_2(X13,X14),X13)|r1_tarski(X13,X14))&(~r2_hidden(esk2_2(X13,X14),X14)|r1_tarski(X13,X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.21/0.41  cnf(c_0_29, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.41  fof(c_0_30, plain, ![X29, X30]:((((v1_relat_1(esk3_2(X29,X30))|X29=k1_xboole_0)&(v1_funct_1(esk3_2(X29,X30))|X29=k1_xboole_0))&((X30=k1_relat_1(esk3_2(X29,X30))|X29=k1_xboole_0)&(r1_tarski(k2_relat_1(esk3_2(X29,X30)),X29)|X29=k1_xboole_0)))&(((v1_relat_1(esk3_2(X29,X30))|X30!=k1_xboole_0)&(v1_funct_1(esk3_2(X29,X30))|X30!=k1_xboole_0))&((X30=k1_relat_1(esk3_2(X29,X30))|X30!=k1_xboole_0)&(r1_tarski(k2_relat_1(esk3_2(X29,X30)),X29)|X30!=k1_xboole_0)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_funct_1])])])])).
% 0.21/0.41  fof(c_0_31, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0=>X1=k1_xboole_0)=>r2_hidden(X3,k1_funct_2(X1,X2))))), inference(assume_negation,[status(cth)],[t11_funct_2])).
% 0.21/0.41  cnf(c_0_32, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.41  cnf(c_0_33, plain, (v1_xboole_0(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.21/0.41  cnf(c_0_34, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.41  fof(c_0_35, plain, ![X63, X64]:((((m1_subset_1(esk7_2(X63,X64),k1_zfmisc_1(k2_zfmisc_1(X63,X64)))&v1_xboole_0(esk7_2(X63,X64)))&v1_relat_1(esk7_2(X63,X64)))&v4_relat_1(esk7_2(X63,X64),X63))&v5_relat_1(esk7_2(X63,X64),X64)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_relset_1])])).
% 0.21/0.41  cnf(c_0_36, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.41  cnf(c_0_37, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.41  cnf(c_0_38, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_29])).
% 0.21/0.41  cnf(c_0_39, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.41  cnf(c_0_40, plain, (r1_tarski(k2_relat_1(esk3_2(X1,X2)),X1)|X2!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.41  fof(c_0_41, plain, ![X41, X42, X43]:(~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))|k1_relset_1(X41,X42,X43)=k1_relat_1(X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.21/0.41  fof(c_0_42, negated_conjecture, (((v1_funct_1(esk10_0)&v1_funct_2(esk10_0,esk8_0,esk9_0))&m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0))))&((esk9_0!=k1_xboole_0|esk8_0=k1_xboole_0)&~r2_hidden(esk10_0,k1_funct_2(esk8_0,esk9_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).
% 0.21/0.41  fof(c_0_43, plain, ![X38, X39, X40]:(~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|m1_subset_1(k2_relset_1(X38,X39,X40),k1_zfmisc_1(X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).
% 0.21/0.41  fof(c_0_44, plain, ![X44, X45, X46]:(~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))|k2_relset_1(X44,X45,X46)=k2_relat_1(X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.21/0.41  cnf(c_0_45, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_32])).
% 0.21/0.41  cnf(c_0_46, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.41  cnf(c_0_47, plain, (v1_xboole_0(k1_xboole_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.21/0.41  cnf(c_0_48, plain, (v1_xboole_0(esk7_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.41  fof(c_0_49, plain, ![X23, X24]:((~v4_relat_1(X24,X23)|r1_tarski(k1_relat_1(X24),X23)|~v1_relat_1(X24))&(~r1_tarski(k1_relat_1(X24),X23)|v4_relat_1(X24,X23)|~v1_relat_1(X24))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.21/0.41  cnf(c_0_50, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.21/0.41  fof(c_0_51, plain, ![X25, X26]:((~v5_relat_1(X26,X25)|r1_tarski(k2_relat_1(X26),X25)|~v1_relat_1(X26))&(~r1_tarski(k2_relat_1(X26),X25)|v5_relat_1(X26,X25)|~v1_relat_1(X26))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.21/0.41  cnf(c_0_52, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_24, c_0_38])).
% 0.21/0.41  fof(c_0_53, plain, ![X66]:(((v1_funct_1(X66)|(~v1_relat_1(X66)|~v1_funct_1(X66)))&(v1_funct_2(X66,k1_relat_1(X66),k2_relat_1(X66))|(~v1_relat_1(X66)|~v1_funct_1(X66))))&(m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X66),k2_relat_1(X66))))|(~v1_relat_1(X66)|~v1_funct_1(X66)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.21/0.41  cnf(c_0_54, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_39, c_0_34])).
% 0.21/0.41  cnf(c_0_55, plain, (r1_tarski(k2_relat_1(esk3_2(X1,k1_xboole_0)),X1)), inference(er,[status(thm)],[c_0_40])).
% 0.21/0.41  cnf(c_0_56, plain, (X1=k1_relat_1(esk3_2(X2,X1))|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.41  cnf(c_0_57, plain, (v1_funct_1(esk3_2(X1,X2))|X2!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.41  cnf(c_0_58, plain, (v1_relat_1(esk3_2(X1,X2))|X2!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.41  fof(c_0_59, plain, ![X50, X51, X52, X53, X55, X56, X57, X58, X59, X61]:(((((((v1_relat_1(esk4_4(X50,X51,X52,X53))|~r2_hidden(X53,X52)|X52!=k1_funct_2(X50,X51))&(v1_funct_1(esk4_4(X50,X51,X52,X53))|~r2_hidden(X53,X52)|X52!=k1_funct_2(X50,X51)))&(X53=esk4_4(X50,X51,X52,X53)|~r2_hidden(X53,X52)|X52!=k1_funct_2(X50,X51)))&(k1_relat_1(esk4_4(X50,X51,X52,X53))=X50|~r2_hidden(X53,X52)|X52!=k1_funct_2(X50,X51)))&(r1_tarski(k2_relat_1(esk4_4(X50,X51,X52,X53)),X51)|~r2_hidden(X53,X52)|X52!=k1_funct_2(X50,X51)))&(~v1_relat_1(X56)|~v1_funct_1(X56)|X55!=X56|k1_relat_1(X56)!=X50|~r1_tarski(k2_relat_1(X56),X51)|r2_hidden(X55,X52)|X52!=k1_funct_2(X50,X51)))&((~r2_hidden(esk5_3(X57,X58,X59),X59)|(~v1_relat_1(X61)|~v1_funct_1(X61)|esk5_3(X57,X58,X59)!=X61|k1_relat_1(X61)!=X57|~r1_tarski(k2_relat_1(X61),X58))|X59=k1_funct_2(X57,X58))&(((((v1_relat_1(esk6_3(X57,X58,X59))|r2_hidden(esk5_3(X57,X58,X59),X59)|X59=k1_funct_2(X57,X58))&(v1_funct_1(esk6_3(X57,X58,X59))|r2_hidden(esk5_3(X57,X58,X59),X59)|X59=k1_funct_2(X57,X58)))&(esk5_3(X57,X58,X59)=esk6_3(X57,X58,X59)|r2_hidden(esk5_3(X57,X58,X59),X59)|X59=k1_funct_2(X57,X58)))&(k1_relat_1(esk6_3(X57,X58,X59))=X57|r2_hidden(esk5_3(X57,X58,X59),X59)|X59=k1_funct_2(X57,X58)))&(r1_tarski(k2_relat_1(esk6_3(X57,X58,X59)),X58)|r2_hidden(esk5_3(X57,X58,X59),X59)|X59=k1_funct_2(X57,X58))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).
% 0.21/0.41  fof(c_0_60, plain, ![X47, X48, X49]:((((~v1_funct_2(X49,X47,X48)|X47=k1_relset_1(X47,X48,X49)|X48=k1_xboole_0|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))))&(X47!=k1_relset_1(X47,X48,X49)|v1_funct_2(X49,X47,X48)|X48=k1_xboole_0|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))))&((~v1_funct_2(X49,X47,X48)|X47=k1_relset_1(X47,X48,X49)|X47!=k1_xboole_0|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))))&(X47!=k1_relset_1(X47,X48,X49)|v1_funct_2(X49,X47,X48)|X47!=k1_xboole_0|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))))))&((~v1_funct_2(X49,X47,X48)|X49=k1_xboole_0|X47=k1_xboole_0|X48!=k1_xboole_0|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))))&(X49!=k1_xboole_0|v1_funct_2(X49,X47,X48)|X47=k1_xboole_0|X48!=k1_xboole_0|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.21/0.41  cnf(c_0_61, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.21/0.41  cnf(c_0_62, negated_conjecture, (m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.41  fof(c_0_63, plain, ![X32, X33, X34]:(~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|v1_relat_1(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.21/0.41  cnf(c_0_64, plain, (m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.21/0.41  cnf(c_0_65, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.21/0.41  cnf(c_0_66, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_33, c_0_45])).
% 0.21/0.41  cnf(c_0_67, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_46])).
% 0.21/0.41  cnf(c_0_68, plain, (v1_xboole_0(k1_xboole_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.21/0.41  cnf(c_0_69, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.21/0.41  cnf(c_0_70, plain, (v4_relat_1(esk7_2(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.41  cnf(c_0_71, plain, (v1_relat_1(esk7_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.41  cnf(c_0_72, plain, (r1_tarski(esk7_2(X1,X2),X3)), inference(spm,[status(thm)],[c_0_50, c_0_48])).
% 0.21/0.41  cnf(c_0_73, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.21/0.41  cnf(c_0_74, plain, (v5_relat_1(esk7_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.41  cnf(c_0_75, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_52, c_0_48])).
% 0.21/0.41  cnf(c_0_76, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.21/0.41  cnf(c_0_77, plain, (k2_relat_1(esk3_2(k1_xboole_0,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.21/0.41  cnf(c_0_78, plain, (k1_relat_1(esk3_2(X1,k1_xboole_0))=k1_xboole_0), inference(er,[status(thm)],[c_0_56])).
% 0.21/0.41  cnf(c_0_79, plain, (v1_funct_1(esk3_2(X1,k1_xboole_0))), inference(er,[status(thm)],[c_0_57])).
% 0.21/0.41  cnf(c_0_80, plain, (v1_relat_1(esk3_2(X1,k1_xboole_0))), inference(er,[status(thm)],[c_0_58])).
% 0.21/0.41  cnf(c_0_81, plain, (r2_hidden(X2,X5)|~v1_relat_1(X1)|~v1_funct_1(X1)|X2!=X1|k1_relat_1(X1)!=X3|~r1_tarski(k2_relat_1(X1),X4)|X5!=k1_funct_2(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.21/0.41  cnf(c_0_82, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.21/0.41  cnf(c_0_83, negated_conjecture, (k1_relset_1(esk8_0,esk9_0,esk10_0)=k1_relat_1(esk10_0)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.21/0.41  cnf(c_0_84, negated_conjecture, (v1_funct_2(esk10_0,esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.41  cnf(c_0_85, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.21/0.41  cnf(c_0_86, plain, (m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.21/0.41  cnf(c_0_87, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.41  cnf(c_0_88, plain, (r1_tarski(k2_zfmisc_1(X1,X2),X3)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_50, c_0_66])).
% 0.21/0.41  cnf(c_0_89, plain, (v1_xboole_0(X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_67]), c_0_68])])).
% 0.21/0.41  cnf(c_0_90, plain, (r1_tarski(k1_relat_1(esk7_2(X1,X2)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])])).
% 0.21/0.41  cnf(c_0_91, plain, (esk7_2(X1,X2)=k1_xboole_0), inference(spm,[status(thm)],[c_0_54, c_0_72])).
% 0.21/0.41  fof(c_0_92, plain, ![X27, X28]:v1_relat_1(k2_zfmisc_1(X27,X28)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.21/0.41  cnf(c_0_93, plain, (r1_tarski(k2_relat_1(esk7_2(X1,X2)),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_71])])).
% 0.21/0.41  cnf(c_0_94, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_50, c_0_75])).
% 0.21/0.41  cnf(c_0_95, plain, (m1_subset_1(esk3_2(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78]), c_0_38]), c_0_79]), c_0_80])])).
% 0.21/0.41  cnf(c_0_96, plain, (r2_hidden(X1,k1_funct_2(k1_relat_1(X1),X2))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(er,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_81])])])).
% 0.21/0.41  cnf(c_0_97, negated_conjecture, (k1_relat_1(esk10_0)=esk8_0|esk9_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_62]), c_0_83]), c_0_84])])).
% 0.21/0.41  cnf(c_0_98, negated_conjecture, (v1_funct_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.41  cnf(c_0_99, negated_conjecture, (v1_relat_1(esk10_0)), inference(spm,[status(thm)],[c_0_85, c_0_62])).
% 0.21/0.41  cnf(c_0_100, negated_conjecture, (m1_subset_1(k2_relat_1(esk10_0),k1_zfmisc_1(esk9_0))), inference(spm,[status(thm)],[c_0_86, c_0_62])).
% 0.21/0.41  cnf(c_0_101, negated_conjecture, (r1_tarski(esk10_0,k2_zfmisc_1(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_87, c_0_62])).
% 0.21/0.41  cnf(c_0_102, plain, (r1_tarski(k2_zfmisc_1(X1,X2),X3)|~r1_tarski(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.21/0.41  cnf(c_0_103, plain, (r1_tarski(k1_relat_1(k1_xboole_0),X1)), inference(rw,[status(thm)],[c_0_90, c_0_91])).
% 0.21/0.41  cnf(c_0_104, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_92])).
% 0.21/0.41  cnf(c_0_105, plain, (r1_tarski(k2_relat_1(k1_xboole_0),X1)), inference(rw,[status(thm)],[c_0_93, c_0_91])).
% 0.21/0.41  cnf(c_0_106, plain, (r1_tarski(esk3_2(k1_xboole_0,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.21/0.41  cnf(c_0_107, negated_conjecture, (~r2_hidden(esk10_0,k1_funct_2(esk8_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.41  cnf(c_0_108, negated_conjecture, (esk9_0=k1_xboole_0|r2_hidden(esk10_0,k1_funct_2(esk8_0,X1))|~r1_tarski(k2_relat_1(esk10_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_98]), c_0_99])])).
% 0.21/0.41  cnf(c_0_109, negated_conjecture, (r1_tarski(k2_relat_1(esk10_0),esk9_0)), inference(spm,[status(thm)],[c_0_87, c_0_100])).
% 0.21/0.41  cnf(c_0_110, negated_conjecture, (k2_zfmisc_1(esk8_0,esk9_0)=esk10_0|~r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),esk10_0)), inference(spm,[status(thm)],[c_0_39, c_0_101])).
% 0.21/0.41  cnf(c_0_111, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|~r1_tarski(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_54, c_0_102])).
% 0.21/0.41  cnf(c_0_112, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_54, c_0_103])).
% 0.21/0.41  cnf(c_0_113, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_104, c_0_67])).
% 0.21/0.41  cnf(c_0_114, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_54, c_0_105])).
% 0.21/0.41  cnf(c_0_115, plain, (esk3_2(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_54, c_0_106])).
% 0.21/0.41  cnf(c_0_116, negated_conjecture, (esk9_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_109])])).
% 0.21/0.41  cnf(c_0_117, negated_conjecture, (esk10_0=k1_xboole_0|~r1_tarski(esk9_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_34])])).
% 0.21/0.41  cnf(c_0_118, negated_conjecture, (esk8_0=k1_xboole_0|esk9_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.41  cnf(c_0_119, plain, (r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,X1))|~v1_funct_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_112]), c_0_113]), c_0_114]), c_0_34])])).
% 0.21/0.41  cnf(c_0_120, plain, (v1_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_79, c_0_115])).
% 0.21/0.41  cnf(c_0_121, negated_conjecture, (~r2_hidden(esk10_0,k1_funct_2(esk8_0,k1_xboole_0))), inference(rw,[status(thm)],[c_0_107, c_0_116])).
% 0.21/0.41  cnf(c_0_122, negated_conjecture, (esk10_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_117, c_0_116]), c_0_34])])).
% 0.21/0.41  cnf(c_0_123, negated_conjecture, (esk8_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_118, c_0_116])])).
% 0.21/0.41  cnf(c_0_124, plain, (r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_119, c_0_120])])).
% 0.21/0.41  cnf(c_0_125, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_121, c_0_122]), c_0_123]), c_0_124])]), ['proof']).
% 0.21/0.41  # SZS output end CNFRefutation
% 0.21/0.41  # Proof object total steps             : 126
% 0.21/0.41  # Proof object clause steps            : 85
% 0.21/0.41  # Proof object formula steps           : 41
% 0.21/0.41  # Proof object conjectures             : 22
% 0.21/0.41  # Proof object clause conjectures      : 19
% 0.21/0.41  # Proof object formula conjectures     : 3
% 0.21/0.41  # Proof object initial clauses used    : 33
% 0.21/0.41  # Proof object initial formulas used   : 20
% 0.21/0.41  # Proof object generating inferences   : 37
% 0.21/0.41  # Proof object simplifying inferences  : 49
% 0.21/0.41  # Training examples: 0 positive, 0 negative
% 0.21/0.41  # Parsed axioms                        : 20
% 0.21/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.41  # Initial clauses                      : 63
% 0.21/0.41  # Removed in clause preprocessing      : 1
% 0.21/0.41  # Initial clauses in saturation        : 62
% 0.21/0.41  # Processed clauses                    : 498
% 0.21/0.41  # ...of these trivial                  : 18
% 0.21/0.41  # ...subsumed                          : 189
% 0.21/0.41  # ...remaining for further processing  : 290
% 0.21/0.41  # Other redundant clauses eliminated   : 19
% 0.21/0.41  # Clauses deleted for lack of memory   : 0
% 0.21/0.41  # Backward-subsumed                    : 12
% 0.21/0.41  # Backward-rewritten                   : 146
% 0.21/0.41  # Generated clauses                    : 1362
% 0.21/0.41  # ...of the previous two non-trivial   : 887
% 0.21/0.41  # Contextual simplify-reflections      : 2
% 0.21/0.41  # Paramodulations                      : 1346
% 0.21/0.41  # Factorizations                       : 0
% 0.21/0.41  # Equation resolutions                 : 19
% 0.21/0.41  # Propositional unsat checks           : 0
% 0.21/0.41  #    Propositional check models        : 0
% 0.21/0.41  #    Propositional check unsatisfiable : 0
% 0.21/0.41  #    Propositional clauses             : 0
% 0.21/0.41  #    Propositional clauses after purity: 0
% 0.21/0.41  #    Propositional unsat core size     : 0
% 0.21/0.41  #    Propositional preprocessing time  : 0.000
% 0.21/0.41  #    Propositional encoding time       : 0.000
% 0.21/0.41  #    Propositional solver time         : 0.000
% 0.21/0.41  #    Success case prop preproc time    : 0.000
% 0.21/0.41  #    Success case prop encoding time   : 0.000
% 0.21/0.41  #    Success case prop solver time     : 0.000
% 0.21/0.41  # Current number of processed clauses  : 117
% 0.21/0.41  #    Positive orientable unit clauses  : 21
% 0.21/0.41  #    Positive unorientable unit clauses: 0
% 0.21/0.41  #    Negative unit clauses             : 4
% 0.21/0.41  #    Non-unit-clauses                  : 92
% 0.21/0.41  # Current number of unprocessed clauses: 394
% 0.21/0.41  # ...number of literals in the above   : 1207
% 0.21/0.41  # Current number of archived formulas  : 0
% 0.21/0.41  # Current number of archived clauses   : 158
% 0.21/0.41  # Clause-clause subsumption calls (NU) : 2263
% 0.21/0.41  # Rec. Clause-clause subsumption calls : 1661
% 0.21/0.41  # Non-unit clause-clause subsumptions  : 193
% 0.21/0.41  # Unit Clause-clause subsumption calls : 136
% 0.21/0.41  # Rewrite failures with RHS unbound    : 0
% 0.21/0.41  # BW rewrite match attempts            : 45
% 0.21/0.41  # BW rewrite match successes           : 25
% 0.21/0.41  # Condensation attempts                : 0
% 0.21/0.41  # Condensation successes               : 0
% 0.21/0.41  # Termbank termtop insertions          : 17363
% 0.21/0.41  
% 0.21/0.41  # -------------------------------------------------
% 0.21/0.41  # User time                : 0.057 s
% 0.21/0.41  # System time              : 0.006 s
% 0.21/0.41  # Total time               : 0.063 s
% 0.21/0.41  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
