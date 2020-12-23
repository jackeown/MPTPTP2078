%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:01:07 EST 2020

% Result     : Theorem 0.49s
% Output     : CNFRefutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :  134 (9378 expanded)
%              Number of clauses        :  105 (4048 expanded)
%              Number of leaves         :   14 (2207 expanded)
%              Depth                    :   22
%              Number of atoms          :  389 (46421 expanded)
%              Number of equality atoms :   96 (8315 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( k1_relat_1(X3) = X1
          & ! [X4] :
              ( r2_hidden(X4,X1)
             => r2_hidden(k1_funct_1(X3,X4),X2) ) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(t14_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
     => ( r1_tarski(k2_relat_1(X4),X2)
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t21_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

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

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( ( k1_relat_1(X3) = X1
            & ! [X4] :
                ( r2_hidden(X4,X1)
               => r2_hidden(k1_funct_1(X3,X4),X2) ) )
         => ( v1_funct_1(X3)
            & v1_funct_2(X3,X1,X2)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t5_funct_2])).

fof(c_0_15,plain,(
    ! [X25,X26,X27,X29,X30,X31,X33] :
      ( ( r2_hidden(esk2_3(X25,X26,X27),k1_relat_1(X25))
        | ~ r2_hidden(X27,X26)
        | X26 != k2_relat_1(X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( X27 = k1_funct_1(X25,esk2_3(X25,X26,X27))
        | ~ r2_hidden(X27,X26)
        | X26 != k2_relat_1(X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( ~ r2_hidden(X30,k1_relat_1(X25))
        | X29 != k1_funct_1(X25,X30)
        | r2_hidden(X29,X26)
        | X26 != k2_relat_1(X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( ~ r2_hidden(esk3_2(X25,X31),X31)
        | ~ r2_hidden(X33,k1_relat_1(X25))
        | esk3_2(X25,X31) != k1_funct_1(X25,X33)
        | X31 = k2_relat_1(X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( r2_hidden(esk4_2(X25,X31),k1_relat_1(X25))
        | r2_hidden(esk3_2(X25,X31),X31)
        | X31 = k2_relat_1(X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( esk3_2(X25,X31) = k1_funct_1(X25,esk4_2(X25,X31))
        | r2_hidden(esk3_2(X25,X31),X31)
        | X31 = k2_relat_1(X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_16,negated_conjecture,(
    ! [X53] :
      ( v1_relat_1(esk7_0)
      & v1_funct_1(esk7_0)
      & k1_relat_1(esk7_0) = esk5_0
      & ( ~ r2_hidden(X53,esk5_0)
        | r2_hidden(k1_funct_1(esk7_0,X53),esk6_0) )
      & ( ~ v1_funct_1(esk7_0)
        | ~ v1_funct_2(esk7_0,esk5_0,esk6_0)
        | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])])).

cnf(c_0_17,plain,
    ( X1 = k1_funct_1(X2,esk2_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X43,X44,X45,X46] :
      ( ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X45,X43)))
      | ~ r1_tarski(k2_relat_1(X46),X44)
      | m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X45,X44))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_relset_1])])).

fof(c_0_20,plain,(
    ! [X15,X16] :
      ( ( ~ m1_subset_1(X15,k1_zfmisc_1(X16))
        | r1_tarski(X15,X16) )
      & ( ~ r1_tarski(X15,X16)
        | m1_subset_1(X15,k1_zfmisc_1(X16)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_21,plain,(
    ! [X24] :
      ( ~ v1_relat_1(X24)
      | r1_tarski(X24,k2_zfmisc_1(k1_relat_1(X24),k2_relat_1(X24))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk7_0,X1),esk6_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k1_funct_1(X1,esk2_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( k1_relat_1(esk7_0) = esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_28,plain,(
    ! [X37,X38,X39] :
      ( ( v4_relat_1(X39,X37)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( v5_relat_1(X39,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_29,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_30,plain,(
    ! [X13,X14] :
      ( ( k2_zfmisc_1(X13,X14) != k1_xboole_0
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0 )
      & ( X13 != k1_xboole_0
        | k2_zfmisc_1(X13,X14) = k1_xboole_0 )
      & ( X14 != k1_xboole_0
        | k2_zfmisc_1(X13,X14) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_31,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(k2_relat_1(X1),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(esk2_3(esk7_0,k2_relat_1(esk7_0),X1),esk5_0)
    | ~ r2_hidden(X1,k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25])])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,k2_relat_1(esk7_0),X1),esk5_0)
    | ~ r2_hidden(X1,k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_24]),c_0_25])])).

fof(c_0_36,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_37,plain,(
    ! [X35,X36] :
      ( ~ r2_hidden(X35,X36)
      | ~ r1_tarski(X36,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_38,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_41,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( ~ v1_funct_1(esk7_0)
    | ~ v1_funct_2(esk7_0,esk5_0,esk6_0)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_43,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X4))
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(esk7_0,k2_zfmisc_1(esk5_0,k2_relat_1(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_27]),c_0_25])])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_46,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_47,plain,(
    ! [X40,X41,X42] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
      | k1_relset_1(X40,X41,X42) = k1_relat_1(X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_48,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_49,plain,(
    ! [X17,X18] :
      ( ( ~ v5_relat_1(X18,X17)
        | r1_tarski(k2_relat_1(X18),X17)
        | ~ v1_relat_1(X18) )
      & ( ~ r1_tarski(k2_relat_1(X18),X17)
        | v5_relat_1(X18,X17)
        | ~ v1_relat_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_50,plain,
    ( v5_relat_1(X1,X2)
    | ~ r1_tarski(X1,k2_zfmisc_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_32])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_39])).

fof(c_0_52,plain,(
    ! [X19,X20] : v1_relat_1(k2_zfmisc_1(X19,X20)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_53,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_54,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_40])])).

cnf(c_0_55,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_56,negated_conjecture,
    ( ~ v1_funct_2(esk7_0,esk5_0,esk6_0)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_24])])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1)))
    | ~ r1_tarski(k2_relat_1(esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk7_0),X1),esk6_0)
    | r1_tarski(k2_relat_1(esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

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
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,esk1_2(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_46])).

cnf(c_0_63,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_64,plain,
    ( v5_relat_1(k2_zfmisc_1(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_65,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_66,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_53])).

cnf(c_0_67,plain,
    ( ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r1_tarski(k2_relat_1(X1),k1_funct_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_54])).

cnf(c_0_68,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_55])).

cnf(c_0_69,negated_conjecture,
    ( ~ v1_funct_2(esk7_0,esk5_0,esk6_0)
    | ~ r1_tarski(k2_relat_1(esk7_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk7_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_71,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_72,negated_conjecture,
    ( k1_relset_1(esk5_0,X1,esk7_0) = esk5_0
    | ~ r1_tarski(k2_relat_1(esk7_0),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_57]),c_0_27])).

cnf(c_0_73,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_74,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,esk1_2(k2_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_75,plain,
    ( v5_relat_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_55])).

cnf(c_0_76,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_77,plain,
    ( ~ v1_funct_1(X1)
    | ~ v5_relat_1(X1,k1_funct_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_63])).

cnf(c_0_78,plain,
    ( v5_relat_1(X1,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_32])).

cnf(c_0_79,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k2_relat_1(esk7_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_66])).

cnf(c_0_81,plain,
    ( v5_relat_1(X1,X2)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_82,negated_conjecture,
    ( ~ v1_funct_2(esk7_0,esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_70])])).

cnf(c_0_83,negated_conjecture,
    ( X1 = k1_xboole_0
    | v1_funct_2(esk7_0,esk5_0,X1)
    | ~ r1_tarski(k2_relat_1(esk7_0),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_57]),c_0_72])).

cnf(c_0_84,plain,
    ( X1 = k2_relat_1(X2)
    | ~ v5_relat_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k2_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_63])).

cnf(c_0_85,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76])])).

cnf(c_0_86,plain,
    ( ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(esk7_0,k1_xboole_0)
    | ~ r1_tarski(k2_relat_1(esk7_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_88,negated_conjecture,
    ( v5_relat_1(esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_70]),c_0_25])])).

cnf(c_0_89,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_70])])).

cnf(c_0_90,negated_conjecture,
    ( v5_relat_1(esk7_0,X1)
    | ~ r1_tarski(k2_relat_1(esk7_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_80])).

cnf(c_0_91,plain,
    ( k2_relat_1(k1_xboole_0) = k2_relat_1(X1)
    | ~ v5_relat_1(X1,k2_relat_1(k1_xboole_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_92,plain,
    ( X1 = k2_relat_1(k1_xboole_0)
    | ~ r1_tarski(X1,k2_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_85])).

cnf(c_0_93,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_86,c_0_46])).

cnf(c_0_94,negated_conjecture,
    ( r1_tarski(esk7_0,k1_xboole_0)
    | ~ v5_relat_1(esk7_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_63]),c_0_25])])).

cnf(c_0_95,negated_conjecture,
    ( v5_relat_1(esk7_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_96,negated_conjecture,
    ( v5_relat_1(esk7_0,X1)
    | ~ v5_relat_1(esk7_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_63]),c_0_25])])).

cnf(c_0_97,plain,
    ( k2_relat_1(k2_zfmisc_1(X1,k2_relat_1(k1_xboole_0))) = k2_relat_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_64]),c_0_65])])).

cnf(c_0_98,plain,
    ( k1_relat_1(X1) = k2_relat_1(k1_xboole_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_99,negated_conjecture,
    ( r1_tarski(esk7_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_95])])).

cnf(c_0_100,negated_conjecture,
    ( v5_relat_1(esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_95])])).

cnf(c_0_101,plain,
    ( r1_tarski(k2_zfmisc_1(X1,k2_relat_1(k1_xboole_0)),k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X1,k2_relat_1(k1_xboole_0))),k2_relat_1(k1_xboole_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_97]),c_0_65])])).

cnf(c_0_102,negated_conjecture,
    ( k2_relat_1(k1_xboole_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_27]),c_0_24]),c_0_25])])).

cnf(c_0_103,negated_conjecture,
    ( ~ r2_hidden(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_100]),c_0_24]),c_0_25]),c_0_27])])).

cnf(c_0_104,plain,
    ( r1_tarski(k2_zfmisc_1(X1,esk5_0),k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X1,esk5_0)),esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101,c_0_102]),c_0_102]),c_0_102])).

cnf(c_0_105,plain,
    ( k2_relat_1(k2_zfmisc_1(X1,esk5_0)) = esk5_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97,c_0_102]),c_0_102])).

cnf(c_0_106,negated_conjecture,
    ( r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_103,c_0_46])).

cnf(c_0_107,plain,
    ( r2_hidden(esk4_2(X1,X2),k1_relat_1(X1))
    | r2_hidden(esk3_2(X1,X2),X2)
    | X2 = k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_108,plain,
    ( m1_subset_1(k2_zfmisc_1(X1,esk5_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X1,esk5_0)),X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_104]),c_0_105]),c_0_106])])).

cnf(c_0_109,plain,
    ( m1_subset_1(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_43,c_0_51])).

cnf(c_0_110,negated_conjecture,
    ( ~ r2_hidden(X1,esk5_0)
    | ~ r1_tarski(esk7_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_27]),c_0_24]),c_0_25])])).

cnf(c_0_111,negated_conjecture,
    ( X1 = k2_relat_1(esk7_0)
    | r2_hidden(esk4_2(esk7_0,X1),esk5_0)
    | r2_hidden(esk3_2(esk7_0,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_24]),c_0_27]),c_0_25])])).

cnf(c_0_112,plain,
    ( m1_subset_1(k2_zfmisc_1(X1,esk5_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_108,c_0_66])).

cnf(c_0_113,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_66]),c_0_85])])).

cnf(c_0_114,negated_conjecture,
    ( X1 = k2_relat_1(esk7_0)
    | r2_hidden(esk3_2(esk7_0,X1),X1)
    | ~ r1_tarski(esk7_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_110,c_0_111])).

cnf(c_0_115,plain,
    ( r1_tarski(k2_zfmisc_1(X1,esk5_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_112])).

cnf(c_0_116,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_113])).

cnf(c_0_117,negated_conjecture,
    ( k2_relat_1(esk7_0) = esk5_0
    | ~ r1_tarski(esk7_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_110,c_0_114])).

cnf(c_0_118,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_119,plain,
    ( k2_zfmisc_1(X1,esk5_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_115]),c_0_116])])).

cnf(c_0_120,negated_conjecture,
    ( k2_relat_1(esk7_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_117,c_0_99])])).

cnf(c_0_121,plain,
    ( esk5_0 = k1_xboole_0
    | X1 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_118,c_0_119])).

cnf(c_0_122,negated_conjecture,
    ( r1_tarski(esk7_0,k2_zfmisc_1(esk5_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_44,c_0_120])).

cnf(c_0_123,negated_conjecture,
    ( ~ v1_funct_2(esk7_0,esk5_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_82,c_0_89])).

cnf(c_0_124,plain,
    ( esk5_0 = k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_121])).

cnf(c_0_125,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_126,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_122]),c_0_120]),c_0_106])])).

cnf(c_0_127,negated_conjecture,
    ( ~ v1_funct_2(esk7_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_123,c_0_124])).

cnf(c_0_128,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | k1_relset_1(k1_xboole_0,X2,X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_125]),c_0_55])).

cnf(c_0_129,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_126,c_0_66])).

cnf(c_0_130,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_31,c_0_66])).

cnf(c_0_131,negated_conjecture,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,esk7_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_128]),c_0_129])])).

cnf(c_0_132,plain,
    ( k1_relset_1(X1,X2,X3) = k1_relat_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k2_relat_1(X3),X2) ),
    inference(spm,[status(thm)],[c_0_61,c_0_130])).

cnf(c_0_133,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_132]),c_0_27]),c_0_124]),c_0_129]),c_0_120]),c_0_124]),c_0_51])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:28:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.49/0.67  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.49/0.67  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.49/0.67  #
% 0.49/0.67  # Preprocessing time       : 0.029 s
% 0.49/0.67  
% 0.49/0.67  # Proof found!
% 0.49/0.67  # SZS status Theorem
% 0.49/0.67  # SZS output start CNFRefutation
% 0.49/0.67  fof(t5_funct_2, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X3)=X1&![X4]:(r2_hidden(X4,X1)=>r2_hidden(k1_funct_1(X3,X4),X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_funct_2)).
% 0.49/0.67  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 0.49/0.67  fof(t14_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>(r1_tarski(k2_relat_1(X4),X2)=>m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relset_1)).
% 0.49/0.67  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.49/0.67  fof(t21_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 0.49/0.67  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.49/0.67  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.49/0.67  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.49/0.67  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.49/0.67  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.49/0.67  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.49/0.67  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 0.49/0.67  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.49/0.67  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.49/0.67  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X3)=X1&![X4]:(r2_hidden(X4,X1)=>r2_hidden(k1_funct_1(X3,X4),X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))))), inference(assume_negation,[status(cth)],[t5_funct_2])).
% 0.49/0.67  fof(c_0_15, plain, ![X25, X26, X27, X29, X30, X31, X33]:((((r2_hidden(esk2_3(X25,X26,X27),k1_relat_1(X25))|~r2_hidden(X27,X26)|X26!=k2_relat_1(X25)|(~v1_relat_1(X25)|~v1_funct_1(X25)))&(X27=k1_funct_1(X25,esk2_3(X25,X26,X27))|~r2_hidden(X27,X26)|X26!=k2_relat_1(X25)|(~v1_relat_1(X25)|~v1_funct_1(X25))))&(~r2_hidden(X30,k1_relat_1(X25))|X29!=k1_funct_1(X25,X30)|r2_hidden(X29,X26)|X26!=k2_relat_1(X25)|(~v1_relat_1(X25)|~v1_funct_1(X25))))&((~r2_hidden(esk3_2(X25,X31),X31)|(~r2_hidden(X33,k1_relat_1(X25))|esk3_2(X25,X31)!=k1_funct_1(X25,X33))|X31=k2_relat_1(X25)|(~v1_relat_1(X25)|~v1_funct_1(X25)))&((r2_hidden(esk4_2(X25,X31),k1_relat_1(X25))|r2_hidden(esk3_2(X25,X31),X31)|X31=k2_relat_1(X25)|(~v1_relat_1(X25)|~v1_funct_1(X25)))&(esk3_2(X25,X31)=k1_funct_1(X25,esk4_2(X25,X31))|r2_hidden(esk3_2(X25,X31),X31)|X31=k2_relat_1(X25)|(~v1_relat_1(X25)|~v1_funct_1(X25)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.49/0.67  fof(c_0_16, negated_conjecture, ![X53]:((v1_relat_1(esk7_0)&v1_funct_1(esk7_0))&((k1_relat_1(esk7_0)=esk5_0&(~r2_hidden(X53,esk5_0)|r2_hidden(k1_funct_1(esk7_0,X53),esk6_0)))&(~v1_funct_1(esk7_0)|~v1_funct_2(esk7_0,esk5_0,esk6_0)|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])])).
% 0.49/0.67  cnf(c_0_17, plain, (X1=k1_funct_1(X2,esk2_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.49/0.67  cnf(c_0_18, plain, (r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.49/0.67  fof(c_0_19, plain, ![X43, X44, X45, X46]:(~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X45,X43)))|(~r1_tarski(k2_relat_1(X46),X44)|m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X45,X44))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_relset_1])])).
% 0.49/0.67  fof(c_0_20, plain, ![X15, X16]:((~m1_subset_1(X15,k1_zfmisc_1(X16))|r1_tarski(X15,X16))&(~r1_tarski(X15,X16)|m1_subset_1(X15,k1_zfmisc_1(X16)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.49/0.67  fof(c_0_21, plain, ![X24]:(~v1_relat_1(X24)|r1_tarski(X24,k2_zfmisc_1(k1_relat_1(X24),k2_relat_1(X24)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).
% 0.49/0.67  cnf(c_0_22, negated_conjecture, (r2_hidden(k1_funct_1(esk7_0,X1),esk6_0)|~r2_hidden(X1,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.49/0.67  cnf(c_0_23, plain, (k1_funct_1(X1,esk2_3(X1,k2_relat_1(X1),X2))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_17])).
% 0.49/0.67  cnf(c_0_24, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.49/0.67  cnf(c_0_25, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.49/0.67  cnf(c_0_26, plain, (r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_18])).
% 0.49/0.67  cnf(c_0_27, negated_conjecture, (k1_relat_1(esk7_0)=esk5_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.49/0.67  fof(c_0_28, plain, ![X37, X38, X39]:((v4_relat_1(X39,X37)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))&(v5_relat_1(X39,X38)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.49/0.67  fof(c_0_29, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.49/0.67  fof(c_0_30, plain, ![X13, X14]:((k2_zfmisc_1(X13,X14)!=k1_xboole_0|(X13=k1_xboole_0|X14=k1_xboole_0))&((X13!=k1_xboole_0|k2_zfmisc_1(X13,X14)=k1_xboole_0)&(X14!=k1_xboole_0|k2_zfmisc_1(X13,X14)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.49/0.67  cnf(c_0_31, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(k2_relat_1(X1),X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.49/0.67  cnf(c_0_32, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.49/0.67  cnf(c_0_33, plain, (r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.49/0.67  cnf(c_0_34, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(esk2_3(esk7_0,k2_relat_1(esk7_0),X1),esk5_0)|~r2_hidden(X1,k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25])])).
% 0.49/0.67  cnf(c_0_35, negated_conjecture, (r2_hidden(esk2_3(esk7_0,k2_relat_1(esk7_0),X1),esk5_0)|~r2_hidden(X1,k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_24]), c_0_25])])).
% 0.49/0.67  fof(c_0_36, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.49/0.67  fof(c_0_37, plain, ![X35, X36]:(~r2_hidden(X35,X36)|~r1_tarski(X36,X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.49/0.67  cnf(c_0_38, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.49/0.67  cnf(c_0_39, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.49/0.67  cnf(c_0_40, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.49/0.67  cnf(c_0_41, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.49/0.67  cnf(c_0_42, negated_conjecture, (~v1_funct_1(esk7_0)|~v1_funct_2(esk7_0,esk5_0,esk6_0)|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.49/0.67  cnf(c_0_43, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(X1,k2_zfmisc_1(X2,X4))|~r1_tarski(k2_relat_1(X1),X3)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.49/0.67  cnf(c_0_44, negated_conjecture, (r1_tarski(esk7_0,k2_zfmisc_1(esk5_0,k2_relat_1(esk7_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_27]), c_0_25])])).
% 0.49/0.67  cnf(c_0_45, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(X1,k2_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.49/0.67  cnf(c_0_46, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.49/0.67  fof(c_0_47, plain, ![X40, X41, X42]:(~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|k1_relset_1(X40,X41,X42)=k1_relat_1(X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.49/0.67  cnf(c_0_48, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.49/0.67  fof(c_0_49, plain, ![X17, X18]:((~v5_relat_1(X18,X17)|r1_tarski(k2_relat_1(X18),X17)|~v1_relat_1(X18))&(~r1_tarski(k2_relat_1(X18),X17)|v5_relat_1(X18,X17)|~v1_relat_1(X18))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.49/0.67  cnf(c_0_50, plain, (v5_relat_1(X1,X2)|~r1_tarski(X1,k2_zfmisc_1(X3,X2))), inference(spm,[status(thm)],[c_0_38, c_0_32])).
% 0.49/0.67  cnf(c_0_51, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_39])).
% 0.49/0.67  fof(c_0_52, plain, ![X19, X20]:v1_relat_1(k2_zfmisc_1(X19,X20)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.49/0.67  cnf(c_0_53, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.49/0.67  cnf(c_0_54, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_40])])).
% 0.49/0.67  cnf(c_0_55, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_41])).
% 0.49/0.67  cnf(c_0_56, negated_conjecture, (~v1_funct_2(esk7_0,esk5_0,esk6_0)|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_24])])).
% 0.49/0.67  cnf(c_0_57, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1)))|~r1_tarski(k2_relat_1(esk7_0),X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.49/0.67  cnf(c_0_58, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.49/0.67  cnf(c_0_59, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk7_0),X1),esk6_0)|r1_tarski(k2_relat_1(esk7_0),X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.49/0.67  fof(c_0_60, plain, ![X47, X48, X49]:((((~v1_funct_2(X49,X47,X48)|X47=k1_relset_1(X47,X48,X49)|X48=k1_xboole_0|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))))&(X47!=k1_relset_1(X47,X48,X49)|v1_funct_2(X49,X47,X48)|X48=k1_xboole_0|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))))&((~v1_funct_2(X49,X47,X48)|X47=k1_relset_1(X47,X48,X49)|X47!=k1_xboole_0|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))))&(X47!=k1_relset_1(X47,X48,X49)|v1_funct_2(X49,X47,X48)|X47!=k1_xboole_0|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))))))&((~v1_funct_2(X49,X47,X48)|X49=k1_xboole_0|X47=k1_xboole_0|X48!=k1_xboole_0|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))))&(X49!=k1_xboole_0|v1_funct_2(X49,X47,X48)|X47=k1_xboole_0|X48!=k1_xboole_0|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.49/0.67  cnf(c_0_61, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.49/0.67  cnf(c_0_62, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,esk1_2(X1,X2))), inference(spm,[status(thm)],[c_0_48, c_0_46])).
% 0.49/0.67  cnf(c_0_63, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.49/0.67  cnf(c_0_64, plain, (v5_relat_1(k2_zfmisc_1(X1,X2),X2)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.49/0.67  cnf(c_0_65, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.49/0.67  cnf(c_0_66, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_53])).
% 0.49/0.67  cnf(c_0_67, plain, (~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~r1_tarski(k2_relat_1(X1),k1_funct_1(X1,X2))), inference(spm,[status(thm)],[c_0_48, c_0_54])).
% 0.49/0.67  cnf(c_0_68, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_38, c_0_55])).
% 0.49/0.67  cnf(c_0_69, negated_conjecture, (~v1_funct_2(esk7_0,esk5_0,esk6_0)|~r1_tarski(k2_relat_1(esk7_0),esk6_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.49/0.67  cnf(c_0_70, negated_conjecture, (r1_tarski(k2_relat_1(esk7_0),esk6_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.49/0.67  cnf(c_0_71, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.49/0.67  cnf(c_0_72, negated_conjecture, (k1_relset_1(esk5_0,X1,esk7_0)=esk5_0|~r1_tarski(k2_relat_1(esk7_0),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_57]), c_0_27])).
% 0.49/0.67  cnf(c_0_73, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.49/0.67  cnf(c_0_74, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,esk1_2(k2_relat_1(X1),X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.49/0.67  cnf(c_0_75, plain, (v5_relat_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_64, c_0_55])).
% 0.49/0.67  cnf(c_0_76, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.49/0.67  cnf(c_0_77, plain, (~v1_funct_1(X1)|~v5_relat_1(X1,k1_funct_1(X1,X2))|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_67, c_0_63])).
% 0.49/0.67  cnf(c_0_78, plain, (v5_relat_1(X1,X2)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_68, c_0_32])).
% 0.49/0.67  cnf(c_0_79, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.49/0.67  cnf(c_0_80, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k1_xboole_0))|~r1_tarski(k2_relat_1(esk7_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_57, c_0_66])).
% 0.49/0.67  cnf(c_0_81, plain, (v5_relat_1(X1,X2)|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.49/0.67  cnf(c_0_82, negated_conjecture, (~v1_funct_2(esk7_0,esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_70])])).
% 0.49/0.67  cnf(c_0_83, negated_conjecture, (X1=k1_xboole_0|v1_funct_2(esk7_0,esk5_0,X1)|~r1_tarski(k2_relat_1(esk7_0),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_57]), c_0_72])).
% 0.49/0.67  cnf(c_0_84, plain, (X1=k2_relat_1(X2)|~v5_relat_1(X2,X1)|~v1_relat_1(X2)|~r1_tarski(X1,k2_relat_1(X2))), inference(spm,[status(thm)],[c_0_73, c_0_63])).
% 0.49/0.67  cnf(c_0_85, plain, (r1_tarski(k2_relat_1(k1_xboole_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76])])).
% 0.49/0.67  cnf(c_0_86, plain, (~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.49/0.67  cnf(c_0_87, negated_conjecture, (r1_tarski(esk7_0,k1_xboole_0)|~r1_tarski(k2_relat_1(esk7_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.49/0.67  cnf(c_0_88, negated_conjecture, (v5_relat_1(esk7_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_70]), c_0_25])])).
% 0.49/0.67  cnf(c_0_89, negated_conjecture, (esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_70])])).
% 0.49/0.67  cnf(c_0_90, negated_conjecture, (v5_relat_1(esk7_0,X1)|~r1_tarski(k2_relat_1(esk7_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_68, c_0_80])).
% 0.49/0.67  cnf(c_0_91, plain, (k2_relat_1(k1_xboole_0)=k2_relat_1(X1)|~v5_relat_1(X1,k2_relat_1(k1_xboole_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.49/0.67  cnf(c_0_92, plain, (X1=k2_relat_1(k1_xboole_0)|~r1_tarski(X1,k2_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_73, c_0_85])).
% 0.49/0.67  cnf(c_0_93, plain, (r1_tarski(k1_relat_1(X1),X2)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_86, c_0_46])).
% 0.49/0.67  cnf(c_0_94, negated_conjecture, (r1_tarski(esk7_0,k1_xboole_0)|~v5_relat_1(esk7_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_63]), c_0_25])])).
% 0.49/0.67  cnf(c_0_95, negated_conjecture, (v5_relat_1(esk7_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_88, c_0_89])).
% 0.49/0.67  cnf(c_0_96, negated_conjecture, (v5_relat_1(esk7_0,X1)|~v5_relat_1(esk7_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_63]), c_0_25])])).
% 0.49/0.67  cnf(c_0_97, plain, (k2_relat_1(k2_zfmisc_1(X1,k2_relat_1(k1_xboole_0)))=k2_relat_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_64]), c_0_65])])).
% 0.49/0.67  cnf(c_0_98, plain, (k1_relat_1(X1)=k2_relat_1(k1_xboole_0)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 0.49/0.67  cnf(c_0_99, negated_conjecture, (r1_tarski(esk7_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_95])])).
% 0.49/0.67  cnf(c_0_100, negated_conjecture, (v5_relat_1(esk7_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_95])])).
% 0.49/0.67  cnf(c_0_101, plain, (r1_tarski(k2_zfmisc_1(X1,k2_relat_1(k1_xboole_0)),k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X1,k2_relat_1(k1_xboole_0))),k2_relat_1(k1_xboole_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_97]), c_0_65])])).
% 0.49/0.67  cnf(c_0_102, negated_conjecture, (k2_relat_1(k1_xboole_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_27]), c_0_24]), c_0_25])])).
% 0.49/0.67  cnf(c_0_103, negated_conjecture, (~r2_hidden(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_100]), c_0_24]), c_0_25]), c_0_27])])).
% 0.49/0.67  cnf(c_0_104, plain, (r1_tarski(k2_zfmisc_1(X1,esk5_0),k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X1,esk5_0)),esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101, c_0_102]), c_0_102]), c_0_102])).
% 0.49/0.67  cnf(c_0_105, plain, (k2_relat_1(k2_zfmisc_1(X1,esk5_0))=esk5_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97, c_0_102]), c_0_102])).
% 0.49/0.67  cnf(c_0_106, negated_conjecture, (r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_103, c_0_46])).
% 0.49/0.67  cnf(c_0_107, plain, (r2_hidden(esk4_2(X1,X2),k1_relat_1(X1))|r2_hidden(esk3_2(X1,X2),X2)|X2=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.49/0.67  cnf(c_0_108, plain, (m1_subset_1(k2_zfmisc_1(X1,esk5_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X1,esk5_0)),X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_104]), c_0_105]), c_0_106])])).
% 0.49/0.67  cnf(c_0_109, plain, (m1_subset_1(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X3)), inference(spm,[status(thm)],[c_0_43, c_0_51])).
% 0.49/0.67  cnf(c_0_110, negated_conjecture, (~r2_hidden(X1,esk5_0)|~r1_tarski(esk7_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_27]), c_0_24]), c_0_25])])).
% 0.49/0.67  cnf(c_0_111, negated_conjecture, (X1=k2_relat_1(esk7_0)|r2_hidden(esk4_2(esk7_0,X1),esk5_0)|r2_hidden(esk3_2(esk7_0,X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_24]), c_0_27]), c_0_25])])).
% 0.49/0.67  cnf(c_0_112, plain, (m1_subset_1(k2_zfmisc_1(X1,esk5_0),k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_108, c_0_66])).
% 0.49/0.67  cnf(c_0_113, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_66]), c_0_85])])).
% 0.49/0.67  cnf(c_0_114, negated_conjecture, (X1=k2_relat_1(esk7_0)|r2_hidden(esk3_2(esk7_0,X1),X1)|~r1_tarski(esk7_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_110, c_0_111])).
% 0.49/0.67  cnf(c_0_115, plain, (r1_tarski(k2_zfmisc_1(X1,esk5_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_79, c_0_112])).
% 0.49/0.67  cnf(c_0_116, plain, (r1_tarski(k1_xboole_0,k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_79, c_0_113])).
% 0.49/0.67  cnf(c_0_117, negated_conjecture, (k2_relat_1(esk7_0)=esk5_0|~r1_tarski(esk7_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_110, c_0_114])).
% 0.49/0.67  cnf(c_0_118, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.49/0.67  cnf(c_0_119, plain, (k2_zfmisc_1(X1,esk5_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_115]), c_0_116])])).
% 0.49/0.67  cnf(c_0_120, negated_conjecture, (k2_relat_1(esk7_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_117, c_0_99])])).
% 0.49/0.67  cnf(c_0_121, plain, (esk5_0=k1_xboole_0|X1=k1_xboole_0), inference(spm,[status(thm)],[c_0_118, c_0_119])).
% 0.49/0.67  cnf(c_0_122, negated_conjecture, (r1_tarski(esk7_0,k2_zfmisc_1(esk5_0,esk5_0))), inference(rw,[status(thm)],[c_0_44, c_0_120])).
% 0.49/0.67  cnf(c_0_123, negated_conjecture, (~v1_funct_2(esk7_0,esk5_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_82, c_0_89])).
% 0.49/0.67  cnf(c_0_124, plain, (esk5_0=k1_xboole_0), inference(ef,[status(thm)],[c_0_121])).
% 0.49/0.67  cnf(c_0_125, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.49/0.67  cnf(c_0_126, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_122]), c_0_120]), c_0_106])])).
% 0.49/0.67  cnf(c_0_127, negated_conjecture, (~v1_funct_2(esk7_0,k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_123, c_0_124])).
% 0.49/0.67  cnf(c_0_128, plain, (v1_funct_2(X1,k1_xboole_0,X2)|k1_relset_1(k1_xboole_0,X2,X1)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_125]), c_0_55])).
% 0.49/0.67  cnf(c_0_129, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_126, c_0_66])).
% 0.49/0.67  cnf(c_0_130, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))|~r1_tarski(k2_relat_1(X1),X3)), inference(spm,[status(thm)],[c_0_31, c_0_66])).
% 0.49/0.67  cnf(c_0_131, negated_conjecture, (k1_relset_1(k1_xboole_0,k1_xboole_0,esk7_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_128]), c_0_129])])).
% 0.49/0.67  cnf(c_0_132, plain, (k1_relset_1(X1,X2,X3)=k1_relat_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))|~r1_tarski(k2_relat_1(X3),X2)), inference(spm,[status(thm)],[c_0_61, c_0_130])).
% 0.49/0.67  cnf(c_0_133, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_132]), c_0_27]), c_0_124]), c_0_129]), c_0_120]), c_0_124]), c_0_51])]), ['proof']).
% 0.49/0.67  # SZS output end CNFRefutation
% 0.49/0.67  # Proof object total steps             : 134
% 0.49/0.67  # Proof object clause steps            : 105
% 0.49/0.67  # Proof object formula steps           : 29
% 0.49/0.67  # Proof object conjectures             : 45
% 0.49/0.67  # Proof object clause conjectures      : 42
% 0.49/0.67  # Proof object formula conjectures     : 3
% 0.49/0.67  # Proof object initial clauses used    : 28
% 0.49/0.67  # Proof object initial formulas used   : 14
% 0.49/0.67  # Proof object generating inferences   : 59
% 0.49/0.67  # Proof object simplifying inferences  : 85
% 0.49/0.67  # Training examples: 0 positive, 0 negative
% 0.49/0.67  # Parsed axioms                        : 15
% 0.49/0.67  # Removed by relevancy pruning/SinE    : 0
% 0.49/0.67  # Initial clauses                      : 38
% 0.49/0.67  # Removed in clause preprocessing      : 0
% 0.49/0.67  # Initial clauses in saturation        : 38
% 0.49/0.67  # Processed clauses                    : 3847
% 0.49/0.67  # ...of these trivial                  : 98
% 0.49/0.67  # ...subsumed                          : 2807
% 0.49/0.67  # ...remaining for further processing  : 942
% 0.49/0.67  # Other redundant clauses eliminated   : 82
% 0.49/0.67  # Clauses deleted for lack of memory   : 0
% 0.49/0.67  # Backward-subsumed                    : 64
% 0.49/0.67  # Backward-rewritten                   : 608
% 0.49/0.67  # Generated clauses                    : 12570
% 0.49/0.67  # ...of the previous two non-trivial   : 11994
% 0.49/0.67  # Contextual simplify-reflections      : 10
% 0.49/0.67  # Paramodulations                      : 12485
% 0.49/0.67  # Factorizations                       : 3
% 0.49/0.67  # Equation resolutions                 : 82
% 0.49/0.67  # Propositional unsat checks           : 0
% 0.49/0.67  #    Propositional check models        : 0
% 0.49/0.67  #    Propositional check unsatisfiable : 0
% 0.49/0.67  #    Propositional clauses             : 0
% 0.49/0.67  #    Propositional clauses after purity: 0
% 0.49/0.67  #    Propositional unsat core size     : 0
% 0.49/0.67  #    Propositional preprocessing time  : 0.000
% 0.49/0.67  #    Propositional encoding time       : 0.000
% 0.49/0.67  #    Propositional solver time         : 0.000
% 0.49/0.67  #    Success case prop preproc time    : 0.000
% 0.49/0.67  #    Success case prop encoding time   : 0.000
% 0.49/0.67  #    Success case prop solver time     : 0.000
% 0.49/0.67  # Current number of processed clauses  : 256
% 0.49/0.67  #    Positive orientable unit clauses  : 28
% 0.49/0.67  #    Positive unorientable unit clauses: 0
% 0.49/0.67  #    Negative unit clauses             : 10
% 0.49/0.67  #    Non-unit-clauses                  : 218
% 0.49/0.67  # Current number of unprocessed clauses: 7806
% 0.49/0.67  # ...number of literals in the above   : 43404
% 0.49/0.67  # Current number of archived formulas  : 0
% 0.49/0.67  # Current number of archived clauses   : 674
% 0.49/0.67  # Clause-clause subsumption calls (NU) : 52879
% 0.49/0.67  # Rec. Clause-clause subsumption calls : 15620
% 0.49/0.67  # Non-unit clause-clause subsumptions  : 2434
% 0.49/0.67  # Unit Clause-clause subsumption calls : 1534
% 0.49/0.67  # Rewrite failures with RHS unbound    : 0
% 0.49/0.67  # BW rewrite match attempts            : 132
% 0.49/0.67  # BW rewrite match successes           : 73
% 0.49/0.67  # Condensation attempts                : 0
% 0.49/0.67  # Condensation successes               : 0
% 0.49/0.67  # Termbank termtop insertions          : 217410
% 0.49/0.67  
% 0.49/0.67  # -------------------------------------------------
% 0.49/0.67  # User time                : 0.322 s
% 0.49/0.67  # System time              : 0.008 s
% 0.49/0.67  # Total time               : 0.330 s
% 0.49/0.67  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
