%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:58:24 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 329 expanded)
%              Number of clauses        :   58 ( 151 expanded)
%              Number of leaves         :   18 (  78 expanded)
%              Depth                    :   18
%              Number of atoms          :  225 ( 979 expanded)
%              Number of equality atoms :   35 ( 129 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(t69_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(t151_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k9_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

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

fof(c_0_18,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(X26))
      | v1_relat_1(X27) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_19,plain,(
    ! [X32,X33] : v1_relat_1(k2_zfmisc_1(X32,X33)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_20,negated_conjecture,(
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

cnf(c_0_21,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,negated_conjecture,(
    ! [X52] :
      ( ~ v1_xboole_0(esk4_0)
      & ~ v1_xboole_0(esk5_0)
      & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
      & k1_relset_1(esk4_0,esk5_0,esk6_0) != k1_xboole_0
      & ( ~ m1_subset_1(X52,esk5_0)
        | ~ r2_hidden(X52,k2_relset_1(esk4_0,esk5_0,esk6_0)) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])])).

fof(c_0_24,plain,(
    ! [X30,X31] :
      ( ( ~ v5_relat_1(X31,X30)
        | r1_tarski(k2_relat_1(X31),X30)
        | ~ v1_relat_1(X31) )
      & ( ~ r1_tarski(k2_relat_1(X31),X30)
        | v5_relat_1(X31,X30)
        | ~ v1_relat_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_25,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_27,plain,(
    ! [X40,X41,X42] :
      ( ( v4_relat_1(X42,X40)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) )
      & ( v5_relat_1(X42,X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_28,plain,(
    ! [X38,X39] :
      ( ~ v1_relat_1(X39)
      | ~ v4_relat_1(X39,X38)
      | X39 = k7_relat_1(X39,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_29,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_32,plain,(
    ! [X34,X35] :
      ( ~ v1_relat_1(X35)
      | k2_relat_1(k7_relat_1(X35,X34)) = k9_relat_1(X35,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_33,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_35,plain,(
    ! [X18,X19] :
      ( v1_xboole_0(X19)
      | ~ r1_tarski(X19,X18)
      | ~ r1_xboole_0(X19,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk6_0),X1)
    | ~ v5_relat_1(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( v5_relat_1(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_26])).

cnf(c_0_38,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( k7_relat_1(esk6_0,X1) = esk6_0
    | ~ v4_relat_1(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( v4_relat_1(esk6_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_26])).

cnf(c_0_41,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_43,plain,(
    ! [X12,X13,X15,X16,X17] :
      ( ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_xboole_0(X12,X13) )
      & ( r2_hidden(esk2_2(X12,X13),X13)
        | r1_xboole_0(X12,X13) )
      & ( ~ r2_hidden(X17,X15)
        | ~ r2_hidden(X17,X16)
        | ~ r1_xboole_0(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_44,plain,(
    ! [X28,X29] :
      ( ( ~ v4_relat_1(X29,X28)
        | r1_tarski(k1_relat_1(X29),X28)
        | ~ v1_relat_1(X29) )
      & ( ~ r1_tarski(k1_relat_1(X29),X28)
        | v4_relat_1(X29,X28)
        | ~ v1_relat_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

fof(c_0_45,plain,(
    ! [X36,X37] :
      ( ( k9_relat_1(X37,X36) != k1_xboole_0
        | r1_xboole_0(k1_relat_1(X37),X36)
        | ~ v1_relat_1(X37) )
      & ( ~ r1_xboole_0(k1_relat_1(X37),X36)
        | k9_relat_1(X37,X36) = k1_xboole_0
        | ~ v1_relat_1(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t151_relat_1])])])).

cnf(c_0_46,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk6_0,X1)) = k9_relat_1(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_30])).

cnf(c_0_47,negated_conjecture,
    ( k7_relat_1(esk6_0,esk4_0) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

fof(c_0_48,plain,(
    ! [X11] :
      ( ~ v1_xboole_0(X11)
      | X11 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_49,negated_conjecture,
    ( v1_xboole_0(k2_relat_1(esk6_0))
    | ~ r1_xboole_0(k2_relat_1(esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_52,plain,(
    ! [X43,X44,X45] :
      ( ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
      | k1_relset_1(X43,X44,X45) = k1_relat_1(X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_53,plain,(
    ! [X24,X25] :
      ( ~ m1_subset_1(X24,X25)
      | v1_xboole_0(X25)
      | r2_hidden(X24,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_54,plain,(
    ! [X20] : m1_subset_1(esk3_1(X20),X20) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_55,plain,
    ( r1_xboole_0(k1_relat_1(X1),X2)
    | k9_relat_1(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,negated_conjecture,
    ( k9_relat_1(esk6_0,esk4_0) = k2_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_57,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_58,negated_conjecture,
    ( v1_xboole_0(k2_relat_1(esk6_0))
    | r2_hidden(esk2_2(k2_relat_1(esk6_0),esk5_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

fof(c_0_59,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk6_0),X1)
    | ~ v4_relat_1(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_30])).

cnf(c_0_61,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_62,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_63,plain,
    ( m1_subset_1(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_64,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(esk6_0),esk4_0)
    | k2_relat_1(esk6_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_30])])).

cnf(c_0_65,negated_conjecture,
    ( k2_relat_1(esk6_0) = k1_xboole_0
    | r2_hidden(esk2_2(k2_relat_1(esk6_0),esk5_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_66,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk6_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_40])).

cnf(c_0_68,negated_conjecture,
    ( k1_relset_1(esk4_0,esk5_0,esk6_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_69,negated_conjecture,
    ( k1_relset_1(esk4_0,esk5_0,esk6_0) = k1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_26])).

cnf(c_0_70,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk3_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

fof(c_0_71,plain,(
    ! [X46,X47,X48] :
      ( ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))
      | k2_relset_1(X46,X47,X48) = k2_relat_1(X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_72,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_73,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(esk6_0),esk4_0)
    | r2_hidden(esk2_2(k2_relat_1(esk6_0),esk5_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( k1_relat_1(esk6_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_76,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_70])).

cnf(c_0_77,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

fof(c_0_78,plain,(
    ! [X22,X23] :
      ( ~ r2_hidden(X22,X23)
      | m1_subset_1(X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(esk2_2(k2_relat_1(esk6_0),esk5_0),esk5_0)
    | ~ r2_hidden(X1,k1_relat_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(esk3_1(k1_relat_1(esk6_0)),k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_81,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_82,negated_conjecture,
    ( ~ m1_subset_1(X1,esk5_0)
    | ~ r2_hidden(X1,k2_relset_1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_83,negated_conjecture,
    ( k2_relset_1(esk4_0,esk5_0,esk6_0) = k2_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_26])).

cnf(c_0_84,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(esk2_2(k2_relat_1(esk6_0),esk5_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_86,negated_conjecture,
    ( v1_xboole_0(k2_relat_1(esk6_0))
    | r2_hidden(esk2_2(k2_relat_1(esk6_0),esk5_0),k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_81])).

cnf(c_0_87,negated_conjecture,
    ( ~ m1_subset_1(X1,esk5_0)
    | ~ r2_hidden(X1,k2_relat_1(esk6_0)) ),
    inference(rw,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(esk2_2(k2_relat_1(esk6_0),esk5_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_89,negated_conjecture,
    ( k2_relat_1(esk6_0) = k1_xboole_0
    | r2_hidden(esk2_2(k2_relat_1(esk6_0),esk5_0),k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_86])).

cnf(c_0_90,negated_conjecture,
    ( ~ r2_hidden(esk2_2(k2_relat_1(esk6_0),esk5_0),k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_91,negated_conjecture,
    ( k2_relat_1(esk6_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_92,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(esk6_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_91])])).

cnf(c_0_93,negated_conjecture,
    ( ~ r2_hidden(X1,k1_relat_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_92]),c_0_74])).

cnf(c_0_94,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_80,c_0_93]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:31:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.44  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S074A
% 0.20/0.44  # and selection function SelectCQIArEqFirst.
% 0.20/0.44  #
% 0.20/0.44  # Preprocessing time       : 0.028 s
% 0.20/0.44  # Presaturation interreduction done
% 0.20/0.44  
% 0.20/0.44  # Proof found!
% 0.20/0.44  # SZS status Theorem
% 0.20/0.44  # SZS output start CNFRefutation
% 0.20/0.44  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.20/0.44  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.20/0.44  fof(t49_relset_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>~((k1_relset_1(X1,X2,X3)!=k1_xboole_0&![X4]:(m1_subset_1(X4,X2)=>~(r2_hidden(X4,k2_relset_1(X1,X2,X3))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 0.20/0.44  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 0.20/0.44  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.20/0.44  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 0.20/0.44  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.20/0.44  fof(t69_xboole_1, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>~((r1_tarski(X2,X1)&r1_xboole_0(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 0.20/0.44  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.20/0.44  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 0.20/0.44  fof(t151_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(k9_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 0.20/0.44  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.20/0.44  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.44  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.20/0.44  fof(existence_m1_subset_1, axiom, ![X1]:?[X2]:m1_subset_1(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 0.20/0.44  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.44  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.20/0.44  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.20/0.44  fof(c_0_18, plain, ![X26, X27]:(~v1_relat_1(X26)|(~m1_subset_1(X27,k1_zfmisc_1(X26))|v1_relat_1(X27))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.20/0.44  fof(c_0_19, plain, ![X32, X33]:v1_relat_1(k2_zfmisc_1(X32,X33)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.20/0.44  fof(c_0_20, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>~((k1_relset_1(X1,X2,X3)!=k1_xboole_0&![X4]:(m1_subset_1(X4,X2)=>~(r2_hidden(X4,k2_relset_1(X1,X2,X3)))))))))), inference(assume_negation,[status(cth)],[t49_relset_1])).
% 0.20/0.44  cnf(c_0_21, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.44  cnf(c_0_22, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.44  fof(c_0_23, negated_conjecture, ![X52]:(~v1_xboole_0(esk4_0)&(~v1_xboole_0(esk5_0)&(m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))&(k1_relset_1(esk4_0,esk5_0,esk6_0)!=k1_xboole_0&(~m1_subset_1(X52,esk5_0)|~r2_hidden(X52,k2_relset_1(esk4_0,esk5_0,esk6_0))))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])])).
% 0.20/0.44  fof(c_0_24, plain, ![X30, X31]:((~v5_relat_1(X31,X30)|r1_tarski(k2_relat_1(X31),X30)|~v1_relat_1(X31))&(~r1_tarski(k2_relat_1(X31),X30)|v5_relat_1(X31,X30)|~v1_relat_1(X31))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.20/0.44  cnf(c_0_25, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.44  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.44  fof(c_0_27, plain, ![X40, X41, X42]:((v4_relat_1(X42,X40)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))))&(v5_relat_1(X42,X41)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.20/0.44  fof(c_0_28, plain, ![X38, X39]:(~v1_relat_1(X39)|~v4_relat_1(X39,X38)|X39=k7_relat_1(X39,X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.20/0.44  cnf(c_0_29, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.44  cnf(c_0_30, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.44  cnf(c_0_31, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.44  fof(c_0_32, plain, ![X34, X35]:(~v1_relat_1(X35)|k2_relat_1(k7_relat_1(X35,X34))=k9_relat_1(X35,X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.20/0.44  cnf(c_0_33, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.44  cnf(c_0_34, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.44  fof(c_0_35, plain, ![X18, X19]:(v1_xboole_0(X19)|(~r1_tarski(X19,X18)|~r1_xboole_0(X19,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).
% 0.20/0.44  cnf(c_0_36, negated_conjecture, (r1_tarski(k2_relat_1(esk6_0),X1)|~v5_relat_1(esk6_0,X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.44  cnf(c_0_37, negated_conjecture, (v5_relat_1(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_31, c_0_26])).
% 0.20/0.44  cnf(c_0_38, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.44  cnf(c_0_39, negated_conjecture, (k7_relat_1(esk6_0,X1)=esk6_0|~v4_relat_1(esk6_0,X1)), inference(spm,[status(thm)],[c_0_33, c_0_30])).
% 0.20/0.44  cnf(c_0_40, negated_conjecture, (v4_relat_1(esk6_0,esk4_0)), inference(spm,[status(thm)],[c_0_34, c_0_26])).
% 0.20/0.44  cnf(c_0_41, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.44  cnf(c_0_42, negated_conjecture, (r1_tarski(k2_relat_1(esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.44  fof(c_0_43, plain, ![X12, X13, X15, X16, X17]:(((r2_hidden(esk2_2(X12,X13),X12)|r1_xboole_0(X12,X13))&(r2_hidden(esk2_2(X12,X13),X13)|r1_xboole_0(X12,X13)))&(~r2_hidden(X17,X15)|~r2_hidden(X17,X16)|~r1_xboole_0(X15,X16))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.20/0.44  fof(c_0_44, plain, ![X28, X29]:((~v4_relat_1(X29,X28)|r1_tarski(k1_relat_1(X29),X28)|~v1_relat_1(X29))&(~r1_tarski(k1_relat_1(X29),X28)|v4_relat_1(X29,X28)|~v1_relat_1(X29))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.20/0.44  fof(c_0_45, plain, ![X36, X37]:((k9_relat_1(X37,X36)!=k1_xboole_0|r1_xboole_0(k1_relat_1(X37),X36)|~v1_relat_1(X37))&(~r1_xboole_0(k1_relat_1(X37),X36)|k9_relat_1(X37,X36)=k1_xboole_0|~v1_relat_1(X37))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t151_relat_1])])])).
% 0.20/0.44  cnf(c_0_46, negated_conjecture, (k2_relat_1(k7_relat_1(esk6_0,X1))=k9_relat_1(esk6_0,X1)), inference(spm,[status(thm)],[c_0_38, c_0_30])).
% 0.20/0.44  cnf(c_0_47, negated_conjecture, (k7_relat_1(esk6_0,esk4_0)=esk6_0), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.44  fof(c_0_48, plain, ![X11]:(~v1_xboole_0(X11)|X11=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.20/0.44  cnf(c_0_49, negated_conjecture, (v1_xboole_0(k2_relat_1(esk6_0))|~r1_xboole_0(k2_relat_1(esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.44  cnf(c_0_50, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.44  cnf(c_0_51, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.44  fof(c_0_52, plain, ![X43, X44, X45]:(~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))|k1_relset_1(X43,X44,X45)=k1_relat_1(X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.44  fof(c_0_53, plain, ![X24, X25]:(~m1_subset_1(X24,X25)|(v1_xboole_0(X25)|r2_hidden(X24,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.20/0.44  fof(c_0_54, plain, ![X20]:m1_subset_1(esk3_1(X20),X20), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).
% 0.20/0.44  cnf(c_0_55, plain, (r1_xboole_0(k1_relat_1(X1),X2)|k9_relat_1(X1,X2)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.44  cnf(c_0_56, negated_conjecture, (k9_relat_1(esk6_0,esk4_0)=k2_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.44  cnf(c_0_57, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.44  cnf(c_0_58, negated_conjecture, (v1_xboole_0(k2_relat_1(esk6_0))|r2_hidden(esk2_2(k2_relat_1(esk6_0),esk5_0),esk5_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.20/0.44  fof(c_0_59, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.44  cnf(c_0_60, negated_conjecture, (r1_tarski(k1_relat_1(esk6_0),X1)|~v4_relat_1(esk6_0,X1)), inference(spm,[status(thm)],[c_0_51, c_0_30])).
% 0.20/0.44  cnf(c_0_61, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.44  cnf(c_0_62, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.20/0.44  cnf(c_0_63, plain, (m1_subset_1(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.44  cnf(c_0_64, negated_conjecture, (r1_xboole_0(k1_relat_1(esk6_0),esk4_0)|k2_relat_1(esk6_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_30])])).
% 0.20/0.44  cnf(c_0_65, negated_conjecture, (k2_relat_1(esk6_0)=k1_xboole_0|r2_hidden(esk2_2(k2_relat_1(esk6_0),esk5_0),esk5_0)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.20/0.44  cnf(c_0_66, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.44  cnf(c_0_67, negated_conjecture, (r1_tarski(k1_relat_1(esk6_0),esk4_0)), inference(spm,[status(thm)],[c_0_60, c_0_40])).
% 0.20/0.44  cnf(c_0_68, negated_conjecture, (k1_relset_1(esk4_0,esk5_0,esk6_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.44  cnf(c_0_69, negated_conjecture, (k1_relset_1(esk4_0,esk5_0,esk6_0)=k1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_61, c_0_26])).
% 0.20/0.44  cnf(c_0_70, plain, (v1_xboole_0(X1)|r2_hidden(esk3_1(X1),X1)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.20/0.44  fof(c_0_71, plain, ![X46, X47, X48]:(~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))|k2_relset_1(X46,X47,X48)=k2_relat_1(X48)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.20/0.44  cnf(c_0_72, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.44  cnf(c_0_73, negated_conjecture, (r1_xboole_0(k1_relat_1(esk6_0),esk4_0)|r2_hidden(esk2_2(k2_relat_1(esk6_0),esk5_0),esk5_0)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.20/0.44  cnf(c_0_74, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,k1_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.20/0.44  cnf(c_0_75, negated_conjecture, (k1_relat_1(esk6_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_68, c_0_69])).
% 0.20/0.44  cnf(c_0_76, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(spm,[status(thm)],[c_0_57, c_0_70])).
% 0.20/0.44  cnf(c_0_77, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.20/0.44  fof(c_0_78, plain, ![X22, X23]:(~r2_hidden(X22,X23)|m1_subset_1(X22,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.20/0.44  cnf(c_0_79, negated_conjecture, (r2_hidden(esk2_2(k2_relat_1(esk6_0),esk5_0),esk5_0)|~r2_hidden(X1,k1_relat_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_74])).
% 0.20/0.44  cnf(c_0_80, negated_conjecture, (r2_hidden(esk3_1(k1_relat_1(esk6_0)),k1_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.20/0.44  cnf(c_0_81, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.44  cnf(c_0_82, negated_conjecture, (~m1_subset_1(X1,esk5_0)|~r2_hidden(X1,k2_relset_1(esk4_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.44  cnf(c_0_83, negated_conjecture, (k2_relset_1(esk4_0,esk5_0,esk6_0)=k2_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_77, c_0_26])).
% 0.20/0.44  cnf(c_0_84, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.20/0.44  cnf(c_0_85, negated_conjecture, (r2_hidden(esk2_2(k2_relat_1(esk6_0),esk5_0),esk5_0)), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.20/0.44  cnf(c_0_86, negated_conjecture, (v1_xboole_0(k2_relat_1(esk6_0))|r2_hidden(esk2_2(k2_relat_1(esk6_0),esk5_0),k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_49, c_0_81])).
% 0.20/0.44  cnf(c_0_87, negated_conjecture, (~m1_subset_1(X1,esk5_0)|~r2_hidden(X1,k2_relat_1(esk6_0))), inference(rw,[status(thm)],[c_0_82, c_0_83])).
% 0.20/0.44  cnf(c_0_88, negated_conjecture, (m1_subset_1(esk2_2(k2_relat_1(esk6_0),esk5_0),esk5_0)), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.20/0.44  cnf(c_0_89, negated_conjecture, (k2_relat_1(esk6_0)=k1_xboole_0|r2_hidden(esk2_2(k2_relat_1(esk6_0),esk5_0),k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_57, c_0_86])).
% 0.20/0.44  cnf(c_0_90, negated_conjecture, (~r2_hidden(esk2_2(k2_relat_1(esk6_0),esk5_0),k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.20/0.44  cnf(c_0_91, negated_conjecture, (k2_relat_1(esk6_0)=k1_xboole_0), inference(sr,[status(thm)],[c_0_89, c_0_90])).
% 0.20/0.44  cnf(c_0_92, negated_conjecture, (r1_xboole_0(k1_relat_1(esk6_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_91])])).
% 0.20/0.44  cnf(c_0_93, negated_conjecture, (~r2_hidden(X1,k1_relat_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_92]), c_0_74])).
% 0.20/0.44  cnf(c_0_94, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_80, c_0_93]), ['proof']).
% 0.20/0.44  # SZS output end CNFRefutation
% 0.20/0.44  # Proof object total steps             : 95
% 0.20/0.44  # Proof object clause steps            : 58
% 0.20/0.44  # Proof object formula steps           : 37
% 0.20/0.44  # Proof object conjectures             : 38
% 0.20/0.44  # Proof object clause conjectures      : 35
% 0.20/0.44  # Proof object formula conjectures     : 3
% 0.20/0.44  # Proof object initial clauses used    : 23
% 0.20/0.44  # Proof object initial formulas used   : 18
% 0.20/0.44  # Proof object generating inferences   : 30
% 0.20/0.44  # Proof object simplifying inferences  : 10
% 0.20/0.44  # Training examples: 0 positive, 0 negative
% 0.20/0.44  # Parsed axioms                        : 18
% 0.20/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.44  # Initial clauses                      : 30
% 0.20/0.44  # Removed in clause preprocessing      : 0
% 0.20/0.44  # Initial clauses in saturation        : 30
% 0.20/0.44  # Processed clauses                    : 525
% 0.20/0.44  # ...of these trivial                  : 9
% 0.20/0.44  # ...subsumed                          : 141
% 0.20/0.44  # ...remaining for further processing  : 375
% 0.20/0.44  # Other redundant clauses eliminated   : 18
% 0.20/0.44  # Clauses deleted for lack of memory   : 0
% 0.20/0.44  # Backward-subsumed                    : 11
% 0.20/0.44  # Backward-rewritten                   : 59
% 0.20/0.44  # Generated clauses                    : 3955
% 0.20/0.44  # ...of the previous two non-trivial   : 2822
% 0.20/0.44  # Contextual simplify-reflections      : 2
% 0.20/0.44  # Paramodulations                      : 3930
% 0.20/0.44  # Factorizations                       : 0
% 0.20/0.44  # Equation resolutions                 : 18
% 0.20/0.44  # Propositional unsat checks           : 0
% 0.20/0.44  #    Propositional check models        : 0
% 0.20/0.44  #    Propositional check unsatisfiable : 0
% 0.20/0.44  #    Propositional clauses             : 0
% 0.20/0.44  #    Propositional clauses after purity: 0
% 0.20/0.44  #    Propositional unsat core size     : 0
% 0.20/0.44  #    Propositional preprocessing time  : 0.000
% 0.20/0.44  #    Propositional encoding time       : 0.000
% 0.20/0.44  #    Propositional solver time         : 0.000
% 0.20/0.44  #    Success case prop preproc time    : 0.000
% 0.20/0.44  #    Success case prop encoding time   : 0.000
% 0.20/0.44  #    Success case prop solver time     : 0.000
% 0.20/0.44  # Current number of processed clauses  : 268
% 0.20/0.44  #    Positive orientable unit clauses  : 42
% 0.20/0.44  #    Positive unorientable unit clauses: 0
% 0.20/0.44  #    Negative unit clauses             : 8
% 0.20/0.44  #    Non-unit-clauses                  : 218
% 0.20/0.44  # Current number of unprocessed clauses: 2346
% 0.20/0.44  # ...number of literals in the above   : 8231
% 0.20/0.44  # Current number of archived formulas  : 0
% 0.20/0.44  # Current number of archived clauses   : 107
% 0.20/0.44  # Clause-clause subsumption calls (NU) : 6139
% 0.20/0.44  # Rec. Clause-clause subsumption calls : 2450
% 0.20/0.44  # Non-unit clause-clause subsumptions  : 133
% 0.20/0.44  # Unit Clause-clause subsumption calls : 834
% 0.20/0.44  # Rewrite failures with RHS unbound    : 0
% 0.20/0.44  # BW rewrite match attempts            : 14
% 0.20/0.44  # BW rewrite match successes           : 6
% 0.20/0.44  # Condensation attempts                : 0
% 0.20/0.44  # Condensation successes               : 0
% 0.20/0.44  # Termbank termtop insertions          : 52151
% 0.20/0.44  
% 0.20/0.44  # -------------------------------------------------
% 0.20/0.44  # User time                : 0.095 s
% 0.20/0.44  # System time              : 0.004 s
% 0.20/0.44  # Total time               : 0.099 s
% 0.20/0.44  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
