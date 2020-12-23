%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:57:01 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 198 expanded)
%              Number of clauses        :   40 (  91 expanded)
%              Number of leaves         :   10 (  47 expanded)
%              Depth                    :   15
%              Number of atoms          :  177 ( 672 expanded)
%              Number of equality atoms :   20 (  64 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t6_relset_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
     => ~ ( r2_hidden(X1,X4)
          & ! [X5,X6] :
              ~ ( X1 = k4_tarski(X5,X6)
                & r2_hidden(X5,X2)
                & r2_hidden(X6,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(l139_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
        & ! [X4,X5] : k4_tarski(X4,X5) != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
       => ~ ( r2_hidden(X1,X4)
            & ! [X5,X6] :
                ~ ( X1 = k4_tarski(X5,X6)
                  & r2_hidden(X5,X2)
                  & r2_hidden(X6,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t6_relset_1])).

fof(c_0_11,plain,(
    ! [X18,X19,X20] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(X18))
      | ~ r2_hidden(X20,X19)
      | r2_hidden(X20,X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_12,negated_conjecture,(
    ! [X57,X58] :
      ( m1_subset_1(esk13_0,k1_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0)))
      & r2_hidden(esk10_0,esk13_0)
      & ( esk10_0 != k4_tarski(X57,X58)
        | ~ r2_hidden(X57,esk11_0)
        | ~ r2_hidden(X58,esk12_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).

fof(c_0_13,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_14,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk13_0,k1_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk10_0,esk13_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk11_0,esk12_0))
    | ~ r2_hidden(X1,esk13_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk10_0,X1)
    | ~ r1_tarski(esk13_0,X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(X1,k2_zfmisc_1(esk11_0,esk12_0))
    | ~ r2_hidden(esk1_2(X1,k2_zfmisc_1(esk11_0,esk12_0)),esk13_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_22,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk10_0,X1)
    | ~ r1_tarski(esk13_0,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk13_0,k2_zfmisc_1(esk11_0,esk12_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_25,plain,(
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

fof(c_0_26,plain,(
    ! [X13,X14,X15] :
      ( ~ r2_hidden(X13,k2_zfmisc_1(X14,X15))
      | k4_tarski(esk2_1(X13),esk3_1(X13)) = X13 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk10_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(esk11_0,esk12_0),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_22])).

cnf(c_0_29,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( k4_tarski(esk2_1(X1),esk3_1(X1)) = X1
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk10_0,k2_zfmisc_1(esk11_0,esk12_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_32,plain,(
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

cnf(c_0_33,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( k4_tarski(esk2_1(esk10_0),esk3_1(esk10_0)) = esk10_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk3_1(esk10_0),k2_relat_1(X1))
    | ~ r2_hidden(esk10_0,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_37,plain,(
    ! [X23,X24] :
      ( ( ~ v5_relat_1(X24,X23)
        | r1_tarski(k2_relat_1(X24),X23)
        | ~ v1_relat_1(X24) )
      & ( ~ r1_tarski(k2_relat_1(X24),X23)
        | v5_relat_1(X24,X23)
        | ~ v1_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

fof(c_0_38,plain,(
    ! [X47,X48,X49] :
      ( ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
      | v1_relat_1(X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk3_1(esk10_0),X1)
    | ~ r2_hidden(esk10_0,X2)
    | ~ r1_tarski(k2_relat_1(X2),X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_36])).

cnf(c_0_41,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_42,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_43,plain,(
    ! [X50,X51,X52] :
      ( ( v4_relat_1(X52,X50)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))) )
      & ( v5_relat_1(X52,X51)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk2_1(esk10_0),k1_relat_1(X1))
    | ~ r2_hidden(esk10_0,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_34])).

fof(c_0_45,plain,(
    ! [X21,X22] :
      ( ( ~ v4_relat_1(X22,X21)
        | r1_tarski(k1_relat_1(X22),X21)
        | ~ v1_relat_1(X22) )
      & ( ~ r1_tarski(k1_relat_1(X22),X21)
        | v4_relat_1(X22,X21)
        | ~ v1_relat_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_46,negated_conjecture,
    ( esk10_0 != k4_tarski(X1,X2)
    | ~ r2_hidden(X1,esk11_0)
    | ~ r2_hidden(X2,esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk3_1(esk10_0),X1)
    | ~ v5_relat_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(esk10_0,X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( v1_relat_1(esk13_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_15])).

cnf(c_0_49,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk2_1(esk10_0),X1)
    | ~ r2_hidden(esk10_0,X2)
    | ~ r1_tarski(k1_relat_1(X2),X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_44])).

cnf(c_0_51,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( ~ r2_hidden(esk3_1(esk10_0),esk12_0)
    | ~ r2_hidden(esk2_1(esk10_0),esk11_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_34])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk3_1(esk10_0),X1)
    | ~ v5_relat_1(esk13_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_17]),c_0_48])])).

cnf(c_0_54,negated_conjecture,
    ( v5_relat_1(esk13_0,esk12_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_15])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk2_1(esk10_0),X1)
    | ~ v4_relat_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(esk10_0,X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_57,negated_conjecture,
    ( ~ r2_hidden(esk2_1(esk10_0),esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk2_1(esk10_0),X1)
    | ~ v4_relat_1(esk13_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_17]),c_0_48])])).

cnf(c_0_59,negated_conjecture,
    ( v4_relat_1(esk13_0,esk11_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_15])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:52:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C02CMA_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.028 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t6_relset_1, conjecture, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))=>~((r2_hidden(X1,X4)&![X5, X6]:~(((X1=k4_tarski(X5,X6)&r2_hidden(X5,X2))&r2_hidden(X6,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_relset_1)).
% 0.12/0.37  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.12/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.12/0.37  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 0.12/0.37  fof(l139_zfmisc_1, axiom, ![X1, X2, X3]:~((r2_hidden(X1,k2_zfmisc_1(X2,X3))&![X4, X5]:k4_tarski(X4,X5)!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 0.12/0.37  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 0.12/0.37  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 0.12/0.37  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.12/0.37  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.12/0.37  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 0.12/0.37  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))=>~((r2_hidden(X1,X4)&![X5, X6]:~(((X1=k4_tarski(X5,X6)&r2_hidden(X5,X2))&r2_hidden(X6,X3))))))), inference(assume_negation,[status(cth)],[t6_relset_1])).
% 0.12/0.37  fof(c_0_11, plain, ![X18, X19, X20]:(~m1_subset_1(X19,k1_zfmisc_1(X18))|(~r2_hidden(X20,X19)|r2_hidden(X20,X18))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.12/0.37  fof(c_0_12, negated_conjecture, ![X57, X58]:(m1_subset_1(esk13_0,k1_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0)))&(r2_hidden(esk10_0,esk13_0)&(esk10_0!=k4_tarski(X57,X58)|~r2_hidden(X57,esk11_0)|~r2_hidden(X58,esk12_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).
% 0.12/0.37  fof(c_0_13, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.12/0.37  cnf(c_0_14, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk13_0,k1_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_16, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_17, negated_conjecture, (r2_hidden(esk10_0,esk13_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_18, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_19, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(esk11_0,esk12_0))|~r2_hidden(X1,esk13_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.12/0.37  cnf(c_0_20, negated_conjecture, (r2_hidden(esk10_0,X1)|~r1_tarski(esk13_0,X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.12/0.37  cnf(c_0_21, negated_conjecture, (r1_tarski(X1,k2_zfmisc_1(esk11_0,esk12_0))|~r2_hidden(esk1_2(X1,k2_zfmisc_1(esk11_0,esk12_0)),esk13_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.12/0.37  cnf(c_0_22, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_23, negated_conjecture, (r2_hidden(esk10_0,X1)|~r1_tarski(esk13_0,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_16, c_0_20])).
% 0.12/0.37  cnf(c_0_24, negated_conjecture, (r1_tarski(esk13_0,k2_zfmisc_1(esk11_0,esk12_0))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.12/0.37  fof(c_0_25, plain, ![X36, X37, X38, X40, X41, X42, X43, X45]:(((~r2_hidden(X38,X37)|r2_hidden(k4_tarski(esk7_3(X36,X37,X38),X38),X36)|X37!=k2_relat_1(X36))&(~r2_hidden(k4_tarski(X41,X40),X36)|r2_hidden(X40,X37)|X37!=k2_relat_1(X36)))&((~r2_hidden(esk8_2(X42,X43),X43)|~r2_hidden(k4_tarski(X45,esk8_2(X42,X43)),X42)|X43=k2_relat_1(X42))&(r2_hidden(esk8_2(X42,X43),X43)|r2_hidden(k4_tarski(esk9_2(X42,X43),esk8_2(X42,X43)),X42)|X43=k2_relat_1(X42)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.12/0.37  fof(c_0_26, plain, ![X13, X14, X15]:(~r2_hidden(X13,k2_zfmisc_1(X14,X15))|k4_tarski(esk2_1(X13),esk3_1(X13))=X13), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).
% 0.12/0.37  cnf(c_0_27, negated_conjecture, (r2_hidden(esk10_0,X1)|~r1_tarski(k2_zfmisc_1(esk11_0,esk12_0),X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.12/0.37  cnf(c_0_28, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_18, c_0_22])).
% 0.12/0.37  cnf(c_0_29, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.37  cnf(c_0_30, plain, (k4_tarski(esk2_1(X1),esk3_1(X1))=X1|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.37  cnf(c_0_31, negated_conjecture, (r2_hidden(esk10_0,k2_zfmisc_1(esk11_0,esk12_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.12/0.37  fof(c_0_32, plain, ![X25, X26, X27, X29, X30, X31, X32, X34]:(((~r2_hidden(X27,X26)|r2_hidden(k4_tarski(X27,esk4_3(X25,X26,X27)),X25)|X26!=k1_relat_1(X25))&(~r2_hidden(k4_tarski(X29,X30),X25)|r2_hidden(X29,X26)|X26!=k1_relat_1(X25)))&((~r2_hidden(esk5_2(X31,X32),X32)|~r2_hidden(k4_tarski(esk5_2(X31,X32),X34),X31)|X32=k1_relat_1(X31))&(r2_hidden(esk5_2(X31,X32),X32)|r2_hidden(k4_tarski(esk5_2(X31,X32),esk6_2(X31,X32)),X31)|X32=k1_relat_1(X31)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.12/0.37  cnf(c_0_33, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)), inference(er,[status(thm)],[c_0_29])).
% 0.12/0.37  cnf(c_0_34, negated_conjecture, (k4_tarski(esk2_1(esk10_0),esk3_1(esk10_0))=esk10_0), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.12/0.37  cnf(c_0_35, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.37  cnf(c_0_36, negated_conjecture, (r2_hidden(esk3_1(esk10_0),k2_relat_1(X1))|~r2_hidden(esk10_0,X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.12/0.37  fof(c_0_37, plain, ![X23, X24]:((~v5_relat_1(X24,X23)|r1_tarski(k2_relat_1(X24),X23)|~v1_relat_1(X24))&(~r1_tarski(k2_relat_1(X24),X23)|v5_relat_1(X24,X23)|~v1_relat_1(X24))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.12/0.37  fof(c_0_38, plain, ![X47, X48, X49]:(~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))|v1_relat_1(X49)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.12/0.37  cnf(c_0_39, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_35])).
% 0.12/0.37  cnf(c_0_40, negated_conjecture, (r2_hidden(esk3_1(esk10_0),X1)|~r2_hidden(esk10_0,X2)|~r1_tarski(k2_relat_1(X2),X1)), inference(spm,[status(thm)],[c_0_16, c_0_36])).
% 0.12/0.37  cnf(c_0_41, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.12/0.37  cnf(c_0_42, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.12/0.37  fof(c_0_43, plain, ![X50, X51, X52]:((v4_relat_1(X52,X50)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))))&(v5_relat_1(X52,X51)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.12/0.37  cnf(c_0_44, negated_conjecture, (r2_hidden(esk2_1(esk10_0),k1_relat_1(X1))|~r2_hidden(esk10_0,X1)), inference(spm,[status(thm)],[c_0_39, c_0_34])).
% 0.12/0.37  fof(c_0_45, plain, ![X21, X22]:((~v4_relat_1(X22,X21)|r1_tarski(k1_relat_1(X22),X21)|~v1_relat_1(X22))&(~r1_tarski(k1_relat_1(X22),X21)|v4_relat_1(X22,X21)|~v1_relat_1(X22))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.12/0.37  cnf(c_0_46, negated_conjecture, (esk10_0!=k4_tarski(X1,X2)|~r2_hidden(X1,esk11_0)|~r2_hidden(X2,esk12_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_47, negated_conjecture, (r2_hidden(esk3_1(esk10_0),X1)|~v5_relat_1(X2,X1)|~v1_relat_1(X2)|~r2_hidden(esk10_0,X2)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.12/0.37  cnf(c_0_48, negated_conjecture, (v1_relat_1(esk13_0)), inference(spm,[status(thm)],[c_0_42, c_0_15])).
% 0.12/0.37  cnf(c_0_49, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.12/0.37  cnf(c_0_50, negated_conjecture, (r2_hidden(esk2_1(esk10_0),X1)|~r2_hidden(esk10_0,X2)|~r1_tarski(k1_relat_1(X2),X1)), inference(spm,[status(thm)],[c_0_16, c_0_44])).
% 0.12/0.37  cnf(c_0_51, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.12/0.37  cnf(c_0_52, negated_conjecture, (~r2_hidden(esk3_1(esk10_0),esk12_0)|~r2_hidden(esk2_1(esk10_0),esk11_0)), inference(spm,[status(thm)],[c_0_46, c_0_34])).
% 0.12/0.37  cnf(c_0_53, negated_conjecture, (r2_hidden(esk3_1(esk10_0),X1)|~v5_relat_1(esk13_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_17]), c_0_48])])).
% 0.12/0.37  cnf(c_0_54, negated_conjecture, (v5_relat_1(esk13_0,esk12_0)), inference(spm,[status(thm)],[c_0_49, c_0_15])).
% 0.12/0.37  cnf(c_0_55, negated_conjecture, (r2_hidden(esk2_1(esk10_0),X1)|~v4_relat_1(X2,X1)|~v1_relat_1(X2)|~r2_hidden(esk10_0,X2)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.12/0.37  cnf(c_0_56, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.12/0.37  cnf(c_0_57, negated_conjecture, (~r2_hidden(esk2_1(esk10_0),esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])])).
% 0.12/0.37  cnf(c_0_58, negated_conjecture, (r2_hidden(esk2_1(esk10_0),X1)|~v4_relat_1(esk13_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_17]), c_0_48])])).
% 0.12/0.37  cnf(c_0_59, negated_conjecture, (v4_relat_1(esk13_0,esk11_0)), inference(spm,[status(thm)],[c_0_56, c_0_15])).
% 0.12/0.37  cnf(c_0_60, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 61
% 0.12/0.37  # Proof object clause steps            : 40
% 0.12/0.37  # Proof object formula steps           : 21
% 0.12/0.37  # Proof object conjectures             : 28
% 0.12/0.37  # Proof object clause conjectures      : 25
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 15
% 0.12/0.37  # Proof object initial formulas used   : 10
% 0.12/0.37  # Proof object generating inferences   : 23
% 0.12/0.37  # Proof object simplifying inferences  : 10
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 10
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 23
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 23
% 0.12/0.37  # Processed clauses                    : 120
% 0.12/0.37  # ...of these trivial                  : 1
% 0.12/0.37  # ...subsumed                          : 16
% 0.12/0.37  # ...remaining for further processing  : 103
% 0.12/0.37  # Other redundant clauses eliminated   : 5
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 0
% 0.12/0.37  # Generated clauses                    : 157
% 0.12/0.37  # ...of the previous two non-trivial   : 144
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 152
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 5
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 76
% 0.12/0.37  #    Positive orientable unit clauses  : 11
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 1
% 0.12/0.37  #    Non-unit-clauses                  : 64
% 0.12/0.37  # Current number of unprocessed clauses: 68
% 0.12/0.37  # ...number of literals in the above   : 196
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 23
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 624
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 517
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 13
% 0.12/0.37  # Unit Clause-clause subsumption calls : 6
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 5
% 0.12/0.37  # BW rewrite match successes           : 0
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 4639
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.036 s
% 0.12/0.37  # System time              : 0.003 s
% 0.12/0.37  # Total time               : 0.039 s
% 0.12/0.37  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
