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
% DateTime   : Thu Dec  3 10:58:36 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 172 expanded)
%              Number of clauses        :   41 (  82 expanded)
%              Number of leaves         :   16 (  41 expanded)
%              Depth                    :   12
%              Number of atoms          :  177 ( 446 expanded)
%              Number of equality atoms :   31 (  84 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

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

fof(t50_relset_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
             => ~ ( k2_relset_1(X2,X1,X3) != k1_xboole_0
                  & ! [X4] :
                      ( m1_subset_1(X4,X2)
                     => ~ r2_hidden(X4,k1_relset_1(X2,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t56_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ! [X2,X3] : ~ r2_hidden(k4_tarski(X2,X3),X1)
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

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

fof(c_0_16,plain,(
    ! [X45,X46,X47] :
      ( ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))
      | m1_subset_1(k2_relset_1(X45,X46,X47),k1_zfmisc_1(X46)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).

fof(c_0_17,plain,(
    ! [X14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X14)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_18,plain,(
    ! [X51,X52,X53] :
      ( ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
      | k2_relset_1(X51,X52,X53) = k2_relat_1(X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_19,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X22)
      | ~ m1_subset_1(X23,k1_zfmisc_1(X22))
      | v1_relat_1(X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_20,plain,(
    ! [X37,X38] : v1_relat_1(k2_zfmisc_1(X37,X38)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
               => ~ ( k2_relset_1(X2,X1,X3) != k1_xboole_0
                    & ! [X4] :
                        ( m1_subset_1(X4,X2)
                       => ~ r2_hidden(X4,k1_relset_1(X2,X1,X3)) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t50_relset_1])).

cnf(c_0_22,plain,
    ( m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,negated_conjecture,(
    ! [X57] :
      ( ~ v1_xboole_0(esk7_0)
      & ~ v1_xboole_0(esk8_0)
      & m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk7_0)))
      & k2_relset_1(esk8_0,esk7_0,esk9_0) != k1_xboole_0
      & ( ~ m1_subset_1(X57,esk8_0)
        | ~ r2_hidden(X57,k1_relset_1(esk8_0,esk7_0,esk9_0)) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])])).

fof(c_0_28,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_29,plain,(
    ! [X13] : r1_tarski(k1_xboole_0,X13) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_30,plain,(
    ! [X17,X18] :
      ( ( ~ m1_subset_1(X17,k1_zfmisc_1(X18))
        | r1_tarski(X17,X18) )
      & ( ~ r1_tarski(X17,X18)
        | m1_subset_1(X17,k1_zfmisc_1(X18)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_31,plain,
    ( m1_subset_1(k2_relset_1(X1,X2,k1_xboole_0),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_32,plain,
    ( k2_relset_1(X1,X2,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_23])).

fof(c_0_33,plain,(
    ! [X39] :
      ( ~ v1_relat_1(X39)
      | r2_hidden(k4_tarski(esk5_1(X39),esk6_1(X39)),X39)
      | X39 = k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t56_relat_1])])])])).

cnf(c_0_34,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_40,plain,(
    ! [X24,X25] :
      ( ( ~ v4_relat_1(X25,X24)
        | r1_tarski(k1_relat_1(X25),X24)
        | ~ v1_relat_1(X25) )
      & ( ~ r1_tarski(k1_relat_1(X25),X24)
        | v4_relat_1(X25,X24)
        | ~ v1_relat_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

fof(c_0_41,plain,(
    ! [X42,X43,X44] :
      ( ( v4_relat_1(X44,X42)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) )
      & ( v5_relat_1(X44,X43)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_42,plain,
    ( r2_hidden(k4_tarski(esk5_1(X1),esk6_1(X1)),X1)
    | X1 = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_44,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_45,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_48,plain,(
    ! [X26,X27,X28,X30,X31,X32,X33,X35] :
      ( ( ~ r2_hidden(X28,X27)
        | r2_hidden(k4_tarski(X28,esk2_3(X26,X27,X28)),X26)
        | X27 != k1_relat_1(X26) )
      & ( ~ r2_hidden(k4_tarski(X30,X31),X26)
        | r2_hidden(X30,X27)
        | X27 != k1_relat_1(X26) )
      & ( ~ r2_hidden(esk3_2(X32,X33),X33)
        | ~ r2_hidden(k4_tarski(esk3_2(X32,X33),X35),X32)
        | X33 = k1_relat_1(X32) )
      & ( r2_hidden(esk3_2(X32,X33),X33)
        | r2_hidden(k4_tarski(esk3_2(X32,X33),esk4_2(X32,X33)),X32)
        | X33 = k1_relat_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_49,negated_conjecture,
    ( k2_relset_1(esk8_0,esk7_0,esk9_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_50,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | r2_hidden(k4_tarski(esk5_1(esk9_0),esk6_1(esk9_0)),esk9_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_51,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

fof(c_0_52,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk9_0),X1)
    | ~ v4_relat_1(esk9_0,X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_43])).

cnf(c_0_54,negated_conjecture,
    ( v4_relat_1(esk9_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_35])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_1(esk9_0),esk6_1(esk9_0)),esk9_0)
    | k2_relset_1(esk8_0,esk7_0,k1_xboole_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,plain,
    ( k2_relset_1(X1,X2,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_32,c_0_51])).

fof(c_0_58,plain,(
    ! [X48,X49,X50] :
      ( ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))
      | k1_relset_1(X48,X49,X50) = k1_relat_1(X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_59,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk9_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_1(esk9_0),esk6_1(esk9_0)),esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57])])).

cnf(c_0_63,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_64,plain,(
    ! [X15,X16] :
      ( ~ r2_hidden(X15,X16)
      | m1_subset_1(X15,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | ~ r2_hidden(X1,k1_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk5_1(esk9_0),k1_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( ~ m1_subset_1(X1,esk8_0)
    | ~ r2_hidden(X1,k1_relset_1(esk8_0,esk7_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_68,negated_conjecture,
    ( k1_relset_1(esk8_0,esk7_0,esk9_0) = k1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_35])).

cnf(c_0_69,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk5_1(esk9_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( ~ m1_subset_1(X1,esk8_0)
    | ~ r2_hidden(X1,k1_relat_1(esk9_0)) ),
    inference(rw,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(esk5_1(esk9_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_66])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:28:56 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  # Version: 2.5pre002
% 0.19/0.35  # No SInE strategy applied
% 0.19/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.50  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S074A
% 0.19/0.50  # and selection function SelectCQIArEqFirst.
% 0.19/0.50  #
% 0.19/0.50  # Preprocessing time       : 0.043 s
% 0.19/0.50  # Presaturation interreduction done
% 0.19/0.50  
% 0.19/0.50  # Proof found!
% 0.19/0.50  # SZS status Theorem
% 0.19/0.50  # SZS output start CNFRefutation
% 0.19/0.50  fof(dt_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 0.19/0.50  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.19/0.50  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.19/0.50  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.19/0.50  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.19/0.50  fof(t50_relset_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>~((k2_relset_1(X2,X1,X3)!=k1_xboole_0&![X4]:(m1_subset_1(X4,X2)=>~(r2_hidden(X4,k1_relset_1(X2,X1,X3))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relset_1)).
% 0.19/0.50  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.50  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.50  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.50  fof(t56_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(![X2, X3]:~(r2_hidden(k4_tarski(X2,X3),X1))=>X1=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_relat_1)).
% 0.19/0.50  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 0.19/0.50  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.50  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 0.19/0.50  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.50  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.50  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.19/0.50  fof(c_0_16, plain, ![X45, X46, X47]:(~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))|m1_subset_1(k2_relset_1(X45,X46,X47),k1_zfmisc_1(X46))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).
% 0.19/0.50  fof(c_0_17, plain, ![X14]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X14)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.19/0.50  fof(c_0_18, plain, ![X51, X52, X53]:(~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))|k2_relset_1(X51,X52,X53)=k2_relat_1(X53)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.19/0.50  fof(c_0_19, plain, ![X22, X23]:(~v1_relat_1(X22)|(~m1_subset_1(X23,k1_zfmisc_1(X22))|v1_relat_1(X23))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.19/0.50  fof(c_0_20, plain, ![X37, X38]:v1_relat_1(k2_zfmisc_1(X37,X38)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.19/0.50  fof(c_0_21, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>~((k2_relset_1(X2,X1,X3)!=k1_xboole_0&![X4]:(m1_subset_1(X4,X2)=>~(r2_hidden(X4,k1_relset_1(X2,X1,X3)))))))))), inference(assume_negation,[status(cth)],[t50_relset_1])).
% 0.19/0.50  cnf(c_0_22, plain, (m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.50  cnf(c_0_23, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.50  cnf(c_0_24, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.50  cnf(c_0_25, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.50  cnf(c_0_26, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.50  fof(c_0_27, negated_conjecture, ![X57]:(~v1_xboole_0(esk7_0)&(~v1_xboole_0(esk8_0)&(m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk7_0)))&(k2_relset_1(esk8_0,esk7_0,esk9_0)!=k1_xboole_0&(~m1_subset_1(X57,esk8_0)|~r2_hidden(X57,k1_relset_1(esk8_0,esk7_0,esk9_0))))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])])).
% 0.19/0.50  fof(c_0_28, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.50  fof(c_0_29, plain, ![X13]:r1_tarski(k1_xboole_0,X13), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.50  fof(c_0_30, plain, ![X17, X18]:((~m1_subset_1(X17,k1_zfmisc_1(X18))|r1_tarski(X17,X18))&(~r1_tarski(X17,X18)|m1_subset_1(X17,k1_zfmisc_1(X18)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.50  cnf(c_0_31, plain, (m1_subset_1(k2_relset_1(X1,X2,k1_xboole_0),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.50  cnf(c_0_32, plain, (k2_relset_1(X1,X2,k1_xboole_0)=k2_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_24, c_0_23])).
% 0.19/0.50  fof(c_0_33, plain, ![X39]:(~v1_relat_1(X39)|(r2_hidden(k4_tarski(esk5_1(X39),esk6_1(X39)),X39)|X39=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t56_relat_1])])])])).
% 0.19/0.50  cnf(c_0_34, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.50  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.50  cnf(c_0_36, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.50  cnf(c_0_37, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.50  cnf(c_0_38, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.50  cnf(c_0_39, plain, (m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.50  fof(c_0_40, plain, ![X24, X25]:((~v4_relat_1(X25,X24)|r1_tarski(k1_relat_1(X25),X24)|~v1_relat_1(X25))&(~r1_tarski(k1_relat_1(X25),X24)|v4_relat_1(X25,X24)|~v1_relat_1(X25))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.19/0.50  fof(c_0_41, plain, ![X42, X43, X44]:((v4_relat_1(X44,X42)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))))&(v5_relat_1(X44,X43)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.50  cnf(c_0_42, plain, (r2_hidden(k4_tarski(esk5_1(X1),esk6_1(X1)),X1)|X1=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.50  cnf(c_0_43, negated_conjecture, (v1_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.50  cnf(c_0_44, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.50  cnf(c_0_45, plain, (r1_tarski(k2_relat_1(k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.50  cnf(c_0_46, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.50  cnf(c_0_47, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.50  fof(c_0_48, plain, ![X26, X27, X28, X30, X31, X32, X33, X35]:(((~r2_hidden(X28,X27)|r2_hidden(k4_tarski(X28,esk2_3(X26,X27,X28)),X26)|X27!=k1_relat_1(X26))&(~r2_hidden(k4_tarski(X30,X31),X26)|r2_hidden(X30,X27)|X27!=k1_relat_1(X26)))&((~r2_hidden(esk3_2(X32,X33),X33)|~r2_hidden(k4_tarski(esk3_2(X32,X33),X35),X32)|X33=k1_relat_1(X32))&(r2_hidden(esk3_2(X32,X33),X33)|r2_hidden(k4_tarski(esk3_2(X32,X33),esk4_2(X32,X33)),X32)|X33=k1_relat_1(X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.19/0.50  cnf(c_0_49, negated_conjecture, (k2_relset_1(esk8_0,esk7_0,esk9_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.50  cnf(c_0_50, negated_conjecture, (esk9_0=k1_xboole_0|r2_hidden(k4_tarski(esk5_1(esk9_0),esk6_1(esk9_0)),esk9_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.50  cnf(c_0_51, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.50  fof(c_0_52, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.50  cnf(c_0_53, negated_conjecture, (r1_tarski(k1_relat_1(esk9_0),X1)|~v4_relat_1(esk9_0,X1)), inference(spm,[status(thm)],[c_0_46, c_0_43])).
% 0.19/0.50  cnf(c_0_54, negated_conjecture, (v4_relat_1(esk9_0,esk8_0)), inference(spm,[status(thm)],[c_0_47, c_0_35])).
% 0.19/0.50  cnf(c_0_55, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.50  cnf(c_0_56, negated_conjecture, (r2_hidden(k4_tarski(esk5_1(esk9_0),esk6_1(esk9_0)),esk9_0)|k2_relset_1(esk8_0,esk7_0,k1_xboole_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.50  cnf(c_0_57, plain, (k2_relset_1(X1,X2,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_32, c_0_51])).
% 0.19/0.50  fof(c_0_58, plain, ![X48, X49, X50]:(~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))|k1_relset_1(X48,X49,X50)=k1_relat_1(X50)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.50  cnf(c_0_59, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.50  cnf(c_0_60, negated_conjecture, (r1_tarski(k1_relat_1(esk9_0),esk8_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.19/0.50  cnf(c_0_61, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_55])).
% 0.19/0.50  cnf(c_0_62, negated_conjecture, (r2_hidden(k4_tarski(esk5_1(esk9_0),esk6_1(esk9_0)),esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57])])).
% 0.19/0.50  cnf(c_0_63, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.50  fof(c_0_64, plain, ![X15, X16]:(~r2_hidden(X15,X16)|m1_subset_1(X15,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.19/0.50  cnf(c_0_65, negated_conjecture, (r2_hidden(X1,esk8_0)|~r2_hidden(X1,k1_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.19/0.50  cnf(c_0_66, negated_conjecture, (r2_hidden(esk5_1(esk9_0),k1_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.19/0.50  cnf(c_0_67, negated_conjecture, (~m1_subset_1(X1,esk8_0)|~r2_hidden(X1,k1_relset_1(esk8_0,esk7_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.50  cnf(c_0_68, negated_conjecture, (k1_relset_1(esk8_0,esk7_0,esk9_0)=k1_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_63, c_0_35])).
% 0.19/0.50  cnf(c_0_69, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.19/0.50  cnf(c_0_70, negated_conjecture, (r2_hidden(esk5_1(esk9_0),esk8_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.19/0.50  cnf(c_0_71, negated_conjecture, (~m1_subset_1(X1,esk8_0)|~r2_hidden(X1,k1_relat_1(esk9_0))), inference(rw,[status(thm)],[c_0_67, c_0_68])).
% 0.19/0.50  cnf(c_0_72, negated_conjecture, (m1_subset_1(esk5_1(esk9_0),esk8_0)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.19/0.50  cnf(c_0_73, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_66])]), ['proof']).
% 0.19/0.50  # SZS output end CNFRefutation
% 0.19/0.50  # Proof object total steps             : 74
% 0.19/0.50  # Proof object clause steps            : 41
% 0.19/0.50  # Proof object formula steps           : 33
% 0.19/0.50  # Proof object conjectures             : 20
% 0.19/0.50  # Proof object clause conjectures      : 17
% 0.19/0.50  # Proof object formula conjectures     : 3
% 0.19/0.50  # Proof object initial clauses used    : 18
% 0.19/0.50  # Proof object initial formulas used   : 16
% 0.19/0.50  # Proof object generating inferences   : 19
% 0.19/0.50  # Proof object simplifying inferences  : 7
% 0.19/0.50  # Training examples: 0 positive, 0 negative
% 0.19/0.50  # Parsed axioms                        : 17
% 0.19/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.50  # Initial clauses                      : 31
% 0.19/0.50  # Removed in clause preprocessing      : 0
% 0.19/0.50  # Initial clauses in saturation        : 31
% 0.19/0.50  # Processed clauses                    : 403
% 0.19/0.50  # ...of these trivial                  : 30
% 0.19/0.50  # ...subsumed                          : 68
% 0.19/0.50  # ...remaining for further processing  : 305
% 0.19/0.50  # Other redundant clauses eliminated   : 28
% 0.19/0.50  # Clauses deleted for lack of memory   : 0
% 0.19/0.50  # Backward-subsumed                    : 7
% 0.19/0.50  # Backward-rewritten                   : 56
% 0.19/0.50  # Generated clauses                    : 4003
% 0.19/0.50  # ...of the previous two non-trivial   : 3466
% 0.19/0.50  # Contextual simplify-reflections      : 4
% 0.19/0.50  # Paramodulations                      : 3975
% 0.19/0.50  # Factorizations                       : 0
% 0.19/0.50  # Equation resolutions                 : 28
% 0.19/0.50  # Propositional unsat checks           : 0
% 0.19/0.50  #    Propositional check models        : 0
% 0.19/0.50  #    Propositional check unsatisfiable : 0
% 0.19/0.50  #    Propositional clauses             : 0
% 0.19/0.50  #    Propositional clauses after purity: 0
% 0.19/0.50  #    Propositional unsat core size     : 0
% 0.19/0.50  #    Propositional preprocessing time  : 0.000
% 0.19/0.50  #    Propositional encoding time       : 0.000
% 0.19/0.50  #    Propositional solver time         : 0.000
% 0.19/0.50  #    Success case prop preproc time    : 0.000
% 0.19/0.50  #    Success case prop encoding time   : 0.000
% 0.19/0.50  #    Success case prop solver time     : 0.000
% 0.19/0.50  # Current number of processed clauses  : 208
% 0.19/0.50  #    Positive orientable unit clauses  : 55
% 0.19/0.50  #    Positive unorientable unit clauses: 1
% 0.19/0.50  #    Negative unit clauses             : 4
% 0.19/0.50  #    Non-unit-clauses                  : 148
% 0.19/0.50  # Current number of unprocessed clauses: 3090
% 0.19/0.50  # ...number of literals in the above   : 14115
% 0.19/0.50  # Current number of archived formulas  : 0
% 0.19/0.50  # Current number of archived clauses   : 93
% 0.19/0.50  # Clause-clause subsumption calls (NU) : 3068
% 0.19/0.50  # Rec. Clause-clause subsumption calls : 1874
% 0.19/0.50  # Non-unit clause-clause subsumptions  : 76
% 0.19/0.50  # Unit Clause-clause subsumption calls : 1213
% 0.19/0.50  # Rewrite failures with RHS unbound    : 2
% 0.19/0.50  # BW rewrite match attempts            : 60
% 0.19/0.50  # BW rewrite match successes           : 18
% 0.19/0.50  # Condensation attempts                : 0
% 0.19/0.50  # Condensation successes               : 0
% 0.19/0.50  # Termbank termtop insertions          : 73632
% 0.19/0.50  
% 0.19/0.50  # -------------------------------------------------
% 0.19/0.50  # User time                : 0.149 s
% 0.19/0.50  # System time              : 0.004 s
% 0.19/0.50  # Total time               : 0.153 s
% 0.19/0.50  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
