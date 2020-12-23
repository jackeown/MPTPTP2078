%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:58:25 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 154 expanded)
%              Number of clauses        :   35 (  70 expanded)
%              Number of leaves         :   14 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :  166 ( 456 expanded)
%              Number of equality atoms :   30 (  80 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t49_relset_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
             => ~ ( k1_relset_1(X1,X2,X3) != k1_xboole_0
                  & ! [X4] :
                      ( m1_subset_1(X4,X2)
                     => ~ r2_hidden(X4,k2_relset_1(X1,X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

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

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t56_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ! [X2,X3] : ~ r2_hidden(k4_tarski(X2,X3),X1)
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
               => ~ ( k1_relset_1(X1,X2,X3) != k1_xboole_0
                    & ! [X4] :
                        ( m1_subset_1(X4,X2)
                       => ~ r2_hidden(X4,k2_relset_1(X1,X2,X3)) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t49_relset_1])).

fof(c_0_15,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(X21))
      | v1_relat_1(X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_16,plain,(
    ! [X47,X48] : v1_relat_1(k2_zfmisc_1(X47,X48)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_17,plain,(
    ! [X57,X58,X59] :
      ( ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58)))
      | k1_relset_1(X57,X58,X59) = k1_relat_1(X59) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_18,negated_conjecture,(
    ! [X66] :
      ( ~ v1_xboole_0(esk12_0)
      & ~ v1_xboole_0(esk13_0)
      & m1_subset_1(esk14_0,k1_zfmisc_1(k2_zfmisc_1(esk12_0,esk13_0)))
      & k1_relset_1(esk12_0,esk13_0,esk14_0) != k1_xboole_0
      & ( ~ m1_subset_1(X66,esk13_0)
        | ~ r2_hidden(X66,k2_relset_1(esk12_0,esk13_0,esk14_0)) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])])).

cnf(c_0_19,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk14_0,k1_zfmisc_1(k2_zfmisc_1(esk12_0,esk13_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,plain,(
    ! [X49] :
      ( ~ v1_relat_1(X49)
      | r2_hidden(k4_tarski(esk10_1(X49),esk11_1(X49)),X49)
      | X49 = k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t56_relat_1])])])])).

cnf(c_0_24,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_25,plain,(
    ! [X23,X24] :
      ( ( ~ v5_relat_1(X24,X23)
        | r1_tarski(k2_relat_1(X24),X23)
        | ~ v1_relat_1(X24) )
      & ( ~ r1_tarski(k2_relat_1(X24),X23)
        | v5_relat_1(X24,X23)
        | ~ v1_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

fof(c_0_26,plain,(
    ! [X54,X55,X56] :
      ( ( v4_relat_1(X56,X54)
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))) )
      & ( v5_relat_1(X56,X55)
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_27,negated_conjecture,
    ( k1_relset_1(esk12_0,esk13_0,esk14_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( k1_relset_1(esk12_0,esk13_0,esk14_0) = k1_relat_1(esk14_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,plain,
    ( r2_hidden(k4_tarski(esk10_1(X1),esk11_1(X1)),X1)
    | X1 = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( v1_relat_1(esk14_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_22])).

fof(c_0_31,plain,(
    ! [X52,X53] :
      ( ~ r2_hidden(X52,X53)
      | ~ r1_tarski(X53,X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_32,plain,(
    ! [X18] : r1_tarski(k1_xboole_0,X18) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_33,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_35,plain,(
    ! [X36,X37,X38,X40,X41,X42,X43,X45] :
      ( ( ~ r2_hidden(X38,X37)
        | r2_hidden(k4_tarski(esk7_3(X36,X37,X38),X38),X36)
        | X37 != k2_relat_1(X36) )
      & ( ~ r2_hidden(k4_tarski(X41,X40),X36)
        | r2_hidden(X40,X37)
        | X37 != k2_relat_1(X36) )
      & ( ~ r2_hidden(esk8_2(X42,X43),X43)
        | ~ r2_hidden(k4_tarski(X45,esk8_2(X42,X43)),X42)
        | X43 = k2_relat_1(X42) )
      & ( r2_hidden(esk8_2(X42,X43),X43)
        | r2_hidden(k4_tarski(esk9_2(X42,X43),esk8_2(X42,X43)),X42)
        | X43 = k2_relat_1(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_36,negated_conjecture,
    ( k1_relat_1(esk14_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( esk14_0 = k1_xboole_0
    | r2_hidden(k4_tarski(esk10_1(esk14_0),esk11_1(esk14_0)),esk14_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_38,plain,(
    ! [X25,X26,X27,X29,X30,X31,X32,X34] :
      ( ( ~ r2_hidden(X27,X26)
        | r2_hidden(k4_tarski(X27,esk4_3(X25,X26,X27)),X25)
        | X26 != k1_relat_1(X25) )
      & ( ~ r2_hidden(k4_tarski(X29,X30),X25)
        | r2_hidden(X29,X26)
        | X26 != k1_relat_1(X25) )
      & ( ~ r2_hidden(esk5_2(X31,X32),X32)
        | ~ r2_hidden(k4_tarski(esk5_2(X31,X32),X34),X31)
        | X32 = k1_relat_1(X31) )
      & ( r2_hidden(esk5_2(X31,X32),X32)
        | r2_hidden(k4_tarski(esk5_2(X31,X32),esk6_2(X31,X32)),X31)
        | X32 = k1_relat_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_39,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_41,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk14_0),X1)
    | ~ v5_relat_1(esk14_0,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_30])).

cnf(c_0_43,negated_conjecture,
    ( v5_relat_1(esk14_0,esk13_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_22])).

cnf(c_0_44,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(k4_tarski(esk10_1(esk14_0),esk11_1(esk14_0)),esk14_0)
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_46,plain,
    ( r2_hidden(esk5_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk5_2(X1,X2),esk6_2(X1,X2)),X1)
    | X2 = k1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

fof(c_0_48,plain,(
    ! [X60,X61,X62] :
      ( ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))
      | k2_relset_1(X60,X61,X62) = k2_relat_1(X62) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_49,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk14_0),esk13_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(k4_tarski(esk10_1(esk14_0),esk11_1(esk14_0)),esk14_0) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])]),c_0_47])).

cnf(c_0_53,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_54,plain,(
    ! [X19,X20] :
      ( ~ r2_hidden(X19,X20)
      | m1_subset_1(X19,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(X1,esk13_0)
    | ~ r2_hidden(X1,k2_relat_1(esk14_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk11_1(esk14_0),k2_relat_1(esk14_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( ~ m1_subset_1(X1,esk13_0)
    | ~ r2_hidden(X1,k2_relset_1(esk12_0,esk13_0,esk14_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_58,negated_conjecture,
    ( k2_relset_1(esk12_0,esk13_0,esk14_0) = k2_relat_1(esk14_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_22])).

cnf(c_0_59,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk11_1(esk14_0),esk13_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( ~ m1_subset_1(X1,esk13_0)
    | ~ r2_hidden(X1,k2_relat_1(esk14_0)) ),
    inference(rw,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(esk11_1(esk14_0),esk13_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_56])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:34:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S074A
% 0.14/0.39  # and selection function SelectCQIArEqFirst.
% 0.14/0.39  #
% 0.14/0.39  # Preprocessing time       : 0.029 s
% 0.14/0.39  # Presaturation interreduction done
% 0.14/0.39  
% 0.14/0.39  # Proof found!
% 0.14/0.39  # SZS status Theorem
% 0.14/0.39  # SZS output start CNFRefutation
% 0.14/0.39  fof(t49_relset_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>~((k1_relset_1(X1,X2,X3)!=k1_xboole_0&![X4]:(m1_subset_1(X4,X2)=>~(r2_hidden(X4,k2_relset_1(X1,X2,X3))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 0.14/0.39  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.14/0.39  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.14/0.39  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.14/0.39  fof(t56_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(![X2, X3]:~(r2_hidden(k4_tarski(X2,X3),X1))=>X1=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_relat_1)).
% 0.14/0.39  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 0.14/0.39  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.14/0.39  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.14/0.39  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.14/0.39  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 0.14/0.39  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 0.14/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.14/0.39  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.14/0.39  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.14/0.39  fof(c_0_14, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>~((k1_relset_1(X1,X2,X3)!=k1_xboole_0&![X4]:(m1_subset_1(X4,X2)=>~(r2_hidden(X4,k2_relset_1(X1,X2,X3)))))))))), inference(assume_negation,[status(cth)],[t49_relset_1])).
% 0.14/0.39  fof(c_0_15, plain, ![X21, X22]:(~v1_relat_1(X21)|(~m1_subset_1(X22,k1_zfmisc_1(X21))|v1_relat_1(X22))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.14/0.39  fof(c_0_16, plain, ![X47, X48]:v1_relat_1(k2_zfmisc_1(X47,X48)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.14/0.39  fof(c_0_17, plain, ![X57, X58, X59]:(~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58)))|k1_relset_1(X57,X58,X59)=k1_relat_1(X59)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.14/0.39  fof(c_0_18, negated_conjecture, ![X66]:(~v1_xboole_0(esk12_0)&(~v1_xboole_0(esk13_0)&(m1_subset_1(esk14_0,k1_zfmisc_1(k2_zfmisc_1(esk12_0,esk13_0)))&(k1_relset_1(esk12_0,esk13_0,esk14_0)!=k1_xboole_0&(~m1_subset_1(X66,esk13_0)|~r2_hidden(X66,k2_relset_1(esk12_0,esk13_0,esk14_0))))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])])).
% 0.14/0.39  cnf(c_0_19, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.39  cnf(c_0_20, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.39  cnf(c_0_21, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.39  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk14_0,k1_zfmisc_1(k2_zfmisc_1(esk12_0,esk13_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.39  fof(c_0_23, plain, ![X49]:(~v1_relat_1(X49)|(r2_hidden(k4_tarski(esk10_1(X49),esk11_1(X49)),X49)|X49=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t56_relat_1])])])])).
% 0.14/0.39  cnf(c_0_24, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.14/0.39  fof(c_0_25, plain, ![X23, X24]:((~v5_relat_1(X24,X23)|r1_tarski(k2_relat_1(X24),X23)|~v1_relat_1(X24))&(~r1_tarski(k2_relat_1(X24),X23)|v5_relat_1(X24,X23)|~v1_relat_1(X24))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.14/0.39  fof(c_0_26, plain, ![X54, X55, X56]:((v4_relat_1(X56,X54)|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))))&(v5_relat_1(X56,X55)|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.14/0.39  cnf(c_0_27, negated_conjecture, (k1_relset_1(esk12_0,esk13_0,esk14_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.39  cnf(c_0_28, negated_conjecture, (k1_relset_1(esk12_0,esk13_0,esk14_0)=k1_relat_1(esk14_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.14/0.39  cnf(c_0_29, plain, (r2_hidden(k4_tarski(esk10_1(X1),esk11_1(X1)),X1)|X1=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.39  cnf(c_0_30, negated_conjecture, (v1_relat_1(esk14_0)), inference(spm,[status(thm)],[c_0_24, c_0_22])).
% 0.14/0.39  fof(c_0_31, plain, ![X52, X53]:(~r2_hidden(X52,X53)|~r1_tarski(X53,X52)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.14/0.39  fof(c_0_32, plain, ![X18]:r1_tarski(k1_xboole_0,X18), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.14/0.39  cnf(c_0_33, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.14/0.39  cnf(c_0_34, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.14/0.39  fof(c_0_35, plain, ![X36, X37, X38, X40, X41, X42, X43, X45]:(((~r2_hidden(X38,X37)|r2_hidden(k4_tarski(esk7_3(X36,X37,X38),X38),X36)|X37!=k2_relat_1(X36))&(~r2_hidden(k4_tarski(X41,X40),X36)|r2_hidden(X40,X37)|X37!=k2_relat_1(X36)))&((~r2_hidden(esk8_2(X42,X43),X43)|~r2_hidden(k4_tarski(X45,esk8_2(X42,X43)),X42)|X43=k2_relat_1(X42))&(r2_hidden(esk8_2(X42,X43),X43)|r2_hidden(k4_tarski(esk9_2(X42,X43),esk8_2(X42,X43)),X42)|X43=k2_relat_1(X42)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.14/0.39  cnf(c_0_36, negated_conjecture, (k1_relat_1(esk14_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.14/0.39  cnf(c_0_37, negated_conjecture, (esk14_0=k1_xboole_0|r2_hidden(k4_tarski(esk10_1(esk14_0),esk11_1(esk14_0)),esk14_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.14/0.39  fof(c_0_38, plain, ![X25, X26, X27, X29, X30, X31, X32, X34]:(((~r2_hidden(X27,X26)|r2_hidden(k4_tarski(X27,esk4_3(X25,X26,X27)),X25)|X26!=k1_relat_1(X25))&(~r2_hidden(k4_tarski(X29,X30),X25)|r2_hidden(X29,X26)|X26!=k1_relat_1(X25)))&((~r2_hidden(esk5_2(X31,X32),X32)|~r2_hidden(k4_tarski(esk5_2(X31,X32),X34),X31)|X32=k1_relat_1(X31))&(r2_hidden(esk5_2(X31,X32),X32)|r2_hidden(k4_tarski(esk5_2(X31,X32),esk6_2(X31,X32)),X31)|X32=k1_relat_1(X31)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.14/0.39  cnf(c_0_39, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.39  cnf(c_0_40, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.14/0.39  fof(c_0_41, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.14/0.39  cnf(c_0_42, negated_conjecture, (r1_tarski(k2_relat_1(esk14_0),X1)|~v5_relat_1(esk14_0,X1)), inference(spm,[status(thm)],[c_0_33, c_0_30])).
% 0.14/0.39  cnf(c_0_43, negated_conjecture, (v5_relat_1(esk14_0,esk13_0)), inference(spm,[status(thm)],[c_0_34, c_0_22])).
% 0.14/0.39  cnf(c_0_44, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.14/0.39  cnf(c_0_45, negated_conjecture, (r2_hidden(k4_tarski(esk10_1(esk14_0),esk11_1(esk14_0)),esk14_0)|k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.14/0.39  cnf(c_0_46, plain, (r2_hidden(esk5_2(X1,X2),X2)|r2_hidden(k4_tarski(esk5_2(X1,X2),esk6_2(X1,X2)),X1)|X2=k1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.14/0.39  cnf(c_0_47, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.14/0.39  fof(c_0_48, plain, ![X60, X61, X62]:(~m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))|k2_relset_1(X60,X61,X62)=k2_relat_1(X62)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.14/0.39  cnf(c_0_49, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.14/0.39  cnf(c_0_50, negated_conjecture, (r1_tarski(k2_relat_1(esk14_0),esk13_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.14/0.39  cnf(c_0_51, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)), inference(er,[status(thm)],[c_0_44])).
% 0.14/0.39  cnf(c_0_52, negated_conjecture, (r2_hidden(k4_tarski(esk10_1(esk14_0),esk11_1(esk14_0)),esk14_0)), inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])]), c_0_47])).
% 0.14/0.39  cnf(c_0_53, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.14/0.39  fof(c_0_54, plain, ![X19, X20]:(~r2_hidden(X19,X20)|m1_subset_1(X19,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.14/0.39  cnf(c_0_55, negated_conjecture, (r2_hidden(X1,esk13_0)|~r2_hidden(X1,k2_relat_1(esk14_0))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.14/0.39  cnf(c_0_56, negated_conjecture, (r2_hidden(esk11_1(esk14_0),k2_relat_1(esk14_0))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.14/0.39  cnf(c_0_57, negated_conjecture, (~m1_subset_1(X1,esk13_0)|~r2_hidden(X1,k2_relset_1(esk12_0,esk13_0,esk14_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.39  cnf(c_0_58, negated_conjecture, (k2_relset_1(esk12_0,esk13_0,esk14_0)=k2_relat_1(esk14_0)), inference(spm,[status(thm)],[c_0_53, c_0_22])).
% 0.14/0.39  cnf(c_0_59, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.14/0.39  cnf(c_0_60, negated_conjecture, (r2_hidden(esk11_1(esk14_0),esk13_0)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.14/0.39  cnf(c_0_61, negated_conjecture, (~m1_subset_1(X1,esk13_0)|~r2_hidden(X1,k2_relat_1(esk14_0))), inference(rw,[status(thm)],[c_0_57, c_0_58])).
% 0.14/0.39  cnf(c_0_62, negated_conjecture, (m1_subset_1(esk11_1(esk14_0),esk13_0)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.14/0.39  cnf(c_0_63, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_56])]), ['proof']).
% 0.14/0.39  # SZS output end CNFRefutation
% 0.14/0.39  # Proof object total steps             : 64
% 0.14/0.39  # Proof object clause steps            : 35
% 0.14/0.39  # Proof object formula steps           : 29
% 0.14/0.39  # Proof object conjectures             : 22
% 0.14/0.39  # Proof object clause conjectures      : 19
% 0.14/0.39  # Proof object formula conjectures     : 3
% 0.14/0.39  # Proof object initial clauses used    : 16
% 0.14/0.39  # Proof object initial formulas used   : 14
% 0.14/0.39  # Proof object generating inferences   : 16
% 0.14/0.39  # Proof object simplifying inferences  : 8
% 0.14/0.39  # Training examples: 0 positive, 0 negative
% 0.14/0.39  # Parsed axioms                        : 16
% 0.14/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.39  # Initial clauses                      : 32
% 0.14/0.39  # Removed in clause preprocessing      : 0
% 0.14/0.39  # Initial clauses in saturation        : 32
% 0.14/0.39  # Processed clauses                    : 180
% 0.14/0.39  # ...of these trivial                  : 11
% 0.14/0.39  # ...subsumed                          : 12
% 0.14/0.39  # ...remaining for further processing  : 157
% 0.14/0.39  # Other redundant clauses eliminated   : 10
% 0.14/0.39  # Clauses deleted for lack of memory   : 0
% 0.14/0.39  # Backward-subsumed                    : 0
% 0.14/0.39  # Backward-rewritten                   : 8
% 0.14/0.39  # Generated clauses                    : 1234
% 0.14/0.39  # ...of the previous two non-trivial   : 1171
% 0.14/0.39  # Contextual simplify-reflections      : 1
% 0.14/0.39  # Paramodulations                      : 1224
% 0.14/0.39  # Factorizations                       : 0
% 0.14/0.39  # Equation resolutions                 : 10
% 0.14/0.39  # Propositional unsat checks           : 0
% 0.14/0.39  #    Propositional check models        : 0
% 0.14/0.39  #    Propositional check unsatisfiable : 0
% 0.14/0.39  #    Propositional clauses             : 0
% 0.14/0.39  #    Propositional clauses after purity: 0
% 0.14/0.39  #    Propositional unsat core size     : 0
% 0.14/0.39  #    Propositional preprocessing time  : 0.000
% 0.14/0.39  #    Propositional encoding time       : 0.000
% 0.14/0.39  #    Propositional solver time         : 0.000
% 0.14/0.39  #    Success case prop preproc time    : 0.000
% 0.14/0.39  #    Success case prop encoding time   : 0.000
% 0.14/0.39  #    Success case prop solver time     : 0.000
% 0.14/0.39  # Current number of processed clauses  : 113
% 0.14/0.39  #    Positive orientable unit clauses  : 56
% 0.14/0.39  #    Positive unorientable unit clauses: 0
% 0.14/0.39  #    Negative unit clauses             : 11
% 0.14/0.39  #    Non-unit-clauses                  : 46
% 0.14/0.39  # Current number of unprocessed clauses: 1054
% 0.14/0.39  # ...number of literals in the above   : 3278
% 0.14/0.39  # Current number of archived formulas  : 0
% 0.14/0.39  # Current number of archived clauses   : 40
% 0.14/0.39  # Clause-clause subsumption calls (NU) : 342
% 0.14/0.39  # Rec. Clause-clause subsumption calls : 315
% 0.14/0.39  # Non-unit clause-clause subsumptions  : 7
% 0.14/0.39  # Unit Clause-clause subsumption calls : 102
% 0.14/0.39  # Rewrite failures with RHS unbound    : 0
% 0.14/0.39  # BW rewrite match attempts            : 7
% 0.14/0.39  # BW rewrite match successes           : 3
% 0.14/0.39  # Condensation attempts                : 0
% 0.14/0.39  # Condensation successes               : 0
% 0.14/0.39  # Termbank termtop insertions          : 15606
% 0.14/0.40  
% 0.14/0.40  # -------------------------------------------------
% 0.14/0.40  # User time                : 0.046 s
% 0.14/0.40  # System time              : 0.006 s
% 0.14/0.40  # Total time               : 0.052 s
% 0.14/0.40  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
