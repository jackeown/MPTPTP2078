%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:05:02 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  121 (1845 expanded)
%              Number of clauses        :   74 ( 775 expanded)
%              Number of leaves         :   23 ( 504 expanded)
%              Depth                    :   18
%              Number of atoms          :  306 (3927 expanded)
%              Number of equality atoms :   78 (1385 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   30 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t64_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,k1_tarski(X1),X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
     => ( X2 != k1_xboole_0
       => r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

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

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(d16_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t5_funct_2,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(t117_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => k11_relat_1(X2,X1) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

fof(t144_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,X1),k2_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

fof(dt_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,k1_tarski(X1),X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
       => ( X2 != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1))) ) ) ),
    inference(assume_negation,[status(cth)],[t64_funct_2])).

fof(c_0_24,negated_conjecture,
    ( v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,k1_tarski(esk4_0),esk5_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk4_0),esk5_0)))
    & esk5_0 != k1_xboole_0
    & ~ r1_tarski(k7_relset_1(k1_tarski(esk4_0),esk5_0,esk7_0,esk6_0),k1_tarski(k1_funct_1(esk7_0,esk4_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

fof(c_0_25,plain,(
    ! [X20] : k2_tarski(X20,X20) = k1_tarski(X20) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_26,plain,(
    ! [X21,X22] : k1_enumset1(X21,X21,X22) = k2_tarski(X21,X22) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_27,plain,(
    ! [X23,X24,X25] : k2_enumset1(X23,X23,X24,X25) = k1_enumset1(X23,X24,X25) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_28,plain,(
    ! [X52,X53,X54] :
      ( ( v4_relat_1(X54,X52)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) )
      & ( v5_relat_1(X54,X53)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk4_0),esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_33,plain,(
    ! [X34,X35] :
      ( ~ v1_relat_1(X34)
      | ~ m1_subset_1(X35,k1_zfmisc_1(X34))
      | v1_relat_1(X35) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_34,plain,(
    ! [X40,X41] : v1_relat_1(k2_zfmisc_1(X40,X41)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_35,plain,(
    ! [X13,X14,X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X15,X14)
        | X15 = X13
        | X14 != k1_tarski(X13) )
      & ( X16 != X13
        | r2_hidden(X16,X14)
        | X14 != k1_tarski(X13) )
      & ( ~ r2_hidden(esk2_2(X17,X18),X18)
        | esk2_2(X17,X18) != X17
        | X18 = k1_tarski(X17) )
      & ( r2_hidden(esk2_2(X17,X18),X18)
        | esk2_2(X17,X18) = X17
        | X18 = k1_tarski(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_36,plain,(
    ! [X38,X39] :
      ( ( ~ v4_relat_1(X39,X38)
        | r1_tarski(k1_relat_1(X39),X38)
        | ~ v1_relat_1(X39) )
      & ( ~ r1_tarski(k1_relat_1(X39),X38)
        | v4_relat_1(X39,X38)
        | ~ v1_relat_1(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_37,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_39,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_42,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_43,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( v4_relat_1(esk7_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_38]),c_0_40])])).

cnf(c_0_46,plain,
    ( X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_47,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk7_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])])).

fof(c_0_49,plain,(
    ! [X26,X27] :
      ( ( k2_zfmisc_1(X26,X27) != k1_xboole_0
        | X26 = k1_xboole_0
        | X27 = k1_xboole_0 )
      & ( X26 != k1_xboole_0
        | k2_zfmisc_1(X26,X27) = k1_xboole_0 )
      & ( X27 != k1_xboole_0
        | k2_zfmisc_1(X26,X27) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_50,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(X1,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

fof(c_0_52,plain,(
    ! [X44,X45] :
      ( ~ v1_relat_1(X45)
      | k2_relat_1(k7_relat_1(X45,X44)) = k9_relat_1(X45,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_53,plain,(
    ! [X46,X47] :
      ( ~ v1_relat_1(X47)
      | ~ v4_relat_1(X47,X46)
      | X47 = k7_relat_1(X47,X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

fof(c_0_54,plain,(
    ! [X28] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X28)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_55,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( X1 = esk4_0
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_57,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_58,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_59,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_60,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_61,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_55])).

fof(c_0_62,plain,(
    ! [X36,X37] :
      ( ~ v1_relat_1(X36)
      | k11_relat_1(X36,X37) = k9_relat_1(X36,k1_tarski(X37)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).

fof(c_0_63,plain,(
    ! [X50,X51] :
      ( ~ r2_hidden(X50,X51)
      | ~ r1_tarski(X51,X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_64,negated_conjecture,
    ( esk1_2(k1_relat_1(esk7_0),X1) = esk4_0
    | r1_tarski(k1_relat_1(esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

fof(c_0_65,plain,(
    ! [X63,X64,X65] :
      ( ( v1_funct_1(X65)
        | r2_hidden(esk3_3(X63,X64,X65),X63)
        | k1_relat_1(X65) != X63
        | ~ v1_relat_1(X65)
        | ~ v1_funct_1(X65) )
      & ( v1_funct_2(X65,X63,X64)
        | r2_hidden(esk3_3(X63,X64,X65),X63)
        | k1_relat_1(X65) != X63
        | ~ v1_relat_1(X65)
        | ~ v1_funct_1(X65) )
      & ( m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64)))
        | r2_hidden(esk3_3(X63,X64,X65),X63)
        | k1_relat_1(X65) != X63
        | ~ v1_relat_1(X65)
        | ~ v1_funct_1(X65) )
      & ( v1_funct_1(X65)
        | ~ r2_hidden(k1_funct_1(X65,esk3_3(X63,X64,X65)),X64)
        | k1_relat_1(X65) != X63
        | ~ v1_relat_1(X65)
        | ~ v1_funct_1(X65) )
      & ( v1_funct_2(X65,X63,X64)
        | ~ r2_hidden(k1_funct_1(X65,esk3_3(X63,X64,X65)),X64)
        | k1_relat_1(X65) != X63
        | ~ v1_relat_1(X65)
        | ~ v1_funct_1(X65) )
      & ( m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64)))
        | ~ r2_hidden(k1_funct_1(X65,esk3_3(X63,X64,X65)),X64)
        | k1_relat_1(X65) != X63
        | ~ v1_relat_1(X65)
        | ~ v1_funct_1(X65) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_funct_2])])])])).

cnf(c_0_66,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(esk4_0),esk5_0,esk7_0,esk6_0),k1_tarski(k1_funct_1(esk7_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_67,plain,(
    ! [X59,X60,X61,X62] :
      ( ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))
      | k7_relset_1(X59,X60,X61,X62) = k9_relat_1(X61,X62) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_68,plain,(
    ! [X48,X49] :
      ( ~ v1_relat_1(X49)
      | ~ v1_funct_1(X49)
      | ~ r2_hidden(X48,k1_relat_1(X49))
      | k11_relat_1(X49,X48) = k1_tarski(k1_funct_1(X49,X48)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t117_funct_1])])).

fof(c_0_69,plain,(
    ! [X42,X43] :
      ( ~ v1_relat_1(X43)
      | r1_tarski(k9_relat_1(X43,X42),k2_relat_1(X43)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t144_relat_1])])).

cnf(c_0_70,plain,
    ( k2_relat_1(X1) = k9_relat_1(X1,X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_71,plain,
    ( v4_relat_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_60])).

cnf(c_0_72,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_61])).

cnf(c_0_73,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_74,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk4_0,k1_relat_1(esk7_0))
    | r1_tarski(k1_relat_1(esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_64])).

cnf(c_0_76,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | r2_hidden(esk3_3(X2,X3,X1),X2)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_77,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0,esk7_0,esk6_0),k2_enumset1(k1_funct_1(esk7_0,esk4_0),k1_funct_1(esk7_0,esk4_0),k1_funct_1(esk7_0,esk4_0),k1_funct_1(esk7_0,esk4_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_32]),c_0_32])).

cnf(c_0_78,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_79,plain,
    ( k11_relat_1(X1,X2) = k1_tarski(k1_funct_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_80,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_81,plain,
    ( k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72])])).

cnf(c_0_82,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k2_enumset1(X2,X2,X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_30]),c_0_31]),c_0_32])).

fof(c_0_83,plain,(
    ! [X55,X56,X57,X58] :
      ( ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56)))
      | m1_subset_1(k7_relset_1(X55,X56,X57,X58),k1_zfmisc_1(X56)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).

fof(c_0_84,plain,(
    ! [X29,X30] :
      ( ( ~ m1_subset_1(X29,k1_zfmisc_1(X30))
        | r1_tarski(X29,X30) )
      & ( ~ r1_tarski(X29,X30)
        | m1_subset_1(X29,k1_zfmisc_1(X30)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(esk4_0,k1_relat_1(esk7_0))
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_86,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | r2_hidden(esk3_3(k1_relat_1(X1),X2,X1),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_76])).

cnf(c_0_87,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_88,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk7_0,esk6_0),k2_enumset1(k1_funct_1(esk7_0,esk4_0),k1_funct_1(esk7_0,esk4_0),k1_funct_1(esk7_0,esk4_0),k1_funct_1(esk7_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_38])])).

cnf(c_0_89,plain,
    ( k11_relat_1(X1,X2) = k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_90,negated_conjecture,
    ( k9_relat_1(esk7_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) = k2_relat_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_44]),c_0_45])])).

cnf(c_0_91,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,X1),k9_relat_1(k1_xboole_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_72])])).

cnf(c_0_92,plain,
    ( k11_relat_1(k1_xboole_0,X1) = k2_relat_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_81]),c_0_72])])).

cnf(c_0_93,plain,
    ( m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_94,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_95,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk7_0),X1)))
    | r2_hidden(esk4_0,k1_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_87]),c_0_45])])).

cnf(c_0_96,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k1_relat_1(esk7_0))
    | ~ r1_tarski(k9_relat_1(esk7_0,esk6_0),k11_relat_1(esk7_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_87]),c_0_45])])).

cnf(c_0_97,negated_conjecture,
    ( k11_relat_1(esk7_0,esk4_0) = k2_relat_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_90]),c_0_45])])).

cnf(c_0_98,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),k9_relat_1(k1_xboole_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_82]),c_0_92]),c_0_72])])).

cnf(c_0_99,plain,
    ( m1_subset_1(k9_relat_1(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3))) ),
    inference(spm,[status(thm)],[c_0_93,c_0_78])).

cnf(c_0_100,negated_conjecture,
    ( r2_hidden(esk4_0,k1_relat_1(esk7_0))
    | r1_tarski(esk7_0,k2_zfmisc_1(k1_relat_1(esk7_0),X1)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_101,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k1_relat_1(esk7_0))
    | ~ r1_tarski(k9_relat_1(esk7_0,esk6_0),k2_relat_1(esk7_0)) ),
    inference(rw,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_102,plain,
    ( r2_hidden(X1,k9_relat_1(k1_xboole_0,X2))
    | ~ r2_hidden(X1,k2_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_98])).

cnf(c_0_103,plain,
    ( m1_subset_1(k9_relat_1(k1_xboole_0,X1),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_99,c_0_60])).

fof(c_0_104,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_105,negated_conjecture,
    ( r2_hidden(esk4_0,k1_relat_1(esk7_0))
    | r1_tarski(esk7_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_100,c_0_61])).

cnf(c_0_106,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k1_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_80]),c_0_45])])).

cnf(c_0_107,plain,
    ( r2_hidden(esk1_2(k2_relat_1(k1_xboole_0),X1),k9_relat_1(k1_xboole_0,X2))
    | r1_tarski(k2_relat_1(k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_102,c_0_57])).

cnf(c_0_108,plain,
    ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_82]),c_0_92]),c_0_72])])).

cnf(c_0_109,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_104])).

cnf(c_0_110,negated_conjecture,
    ( r1_tarski(esk7_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_111,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_94,c_0_60])).

cnf(c_0_112,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k9_relat_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_80])).

cnf(c_0_113,plain,
    ( r2_hidden(esk1_2(k9_relat_1(k1_xboole_0,X1),X2),k9_relat_1(k1_xboole_0,X3))
    | r1_tarski(k9_relat_1(k1_xboole_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_107,c_0_81])).

cnf(c_0_114,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_94,c_0_108])).

cnf(c_0_115,negated_conjecture,
    ( esk7_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_111])])).

cnf(c_0_116,plain,
    ( r2_hidden(esk1_2(k9_relat_1(k1_xboole_0,X1),X2),k2_relat_1(k1_xboole_0))
    | r1_tarski(k9_relat_1(k1_xboole_0,X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_72])])).

cnf(c_0_117,plain,
    ( ~ r2_hidden(X1,k2_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_114])).

cnf(c_0_118,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(k1_xboole_0,esk6_0),k2_enumset1(k1_funct_1(k1_xboole_0,esk4_0),k1_funct_1(k1_xboole_0,esk4_0),k1_funct_1(k1_xboole_0,esk4_0),k1_funct_1(k1_xboole_0,esk4_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_115]),c_0_115]),c_0_115]),c_0_115]),c_0_115])).

cnf(c_0_119,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,X1),X2) ),
    inference(sr,[status(thm)],[c_0_116,c_0_117])).

cnf(c_0_120,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_118,c_0_119])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.33  % Computer   : n005.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 10:37:47 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.34  # No SInE strategy applied
% 0.11/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.45  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.18/0.45  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.18/0.45  #
% 0.18/0.45  # Preprocessing time       : 0.029 s
% 0.18/0.45  
% 0.18/0.45  # Proof found!
% 0.18/0.45  # SZS status Theorem
% 0.18/0.45  # SZS output start CNFRefutation
% 0.18/0.45  fof(t64_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,k1_tarski(X1),X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 0.18/0.45  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.18/0.45  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.18/0.45  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.18/0.45  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.18/0.45  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.18/0.45  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.18/0.45  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.18/0.45  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 0.18/0.45  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.18/0.45  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.18/0.45  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.18/0.45  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 0.18/0.45  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.18/0.45  fof(d16_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 0.18/0.45  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.18/0.45  fof(t5_funct_2, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X3)=X1&![X4]:(r2_hidden(X4,X1)=>r2_hidden(k1_funct_1(X3,X4),X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_funct_2)).
% 0.18/0.45  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.18/0.45  fof(t117_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r2_hidden(X1,k1_relat_1(X2))=>k11_relat_1(X2,X1)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_funct_1)).
% 0.18/0.45  fof(t144_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k9_relat_1(X2,X1),k2_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 0.18/0.45  fof(dt_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 0.18/0.45  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.18/0.45  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.18/0.45  fof(c_0_23, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,k1_tarski(X1),X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1)))))), inference(assume_negation,[status(cth)],[t64_funct_2])).
% 0.18/0.45  fof(c_0_24, negated_conjecture, (((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,k1_tarski(esk4_0),esk5_0))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk4_0),esk5_0))))&(esk5_0!=k1_xboole_0&~r1_tarski(k7_relset_1(k1_tarski(esk4_0),esk5_0,esk7_0,esk6_0),k1_tarski(k1_funct_1(esk7_0,esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 0.18/0.45  fof(c_0_25, plain, ![X20]:k2_tarski(X20,X20)=k1_tarski(X20), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.18/0.45  fof(c_0_26, plain, ![X21, X22]:k1_enumset1(X21,X21,X22)=k2_tarski(X21,X22), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.18/0.45  fof(c_0_27, plain, ![X23, X24, X25]:k2_enumset1(X23,X23,X24,X25)=k1_enumset1(X23,X24,X25), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.18/0.45  fof(c_0_28, plain, ![X52, X53, X54]:((v4_relat_1(X54,X52)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))))&(v5_relat_1(X54,X53)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.18/0.45  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk4_0),esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.45  cnf(c_0_30, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.18/0.45  cnf(c_0_31, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.18/0.45  cnf(c_0_32, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.18/0.45  fof(c_0_33, plain, ![X34, X35]:(~v1_relat_1(X34)|(~m1_subset_1(X35,k1_zfmisc_1(X34))|v1_relat_1(X35))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.18/0.45  fof(c_0_34, plain, ![X40, X41]:v1_relat_1(k2_zfmisc_1(X40,X41)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.18/0.45  fof(c_0_35, plain, ![X13, X14, X15, X16, X17, X18]:(((~r2_hidden(X15,X14)|X15=X13|X14!=k1_tarski(X13))&(X16!=X13|r2_hidden(X16,X14)|X14!=k1_tarski(X13)))&((~r2_hidden(esk2_2(X17,X18),X18)|esk2_2(X17,X18)!=X17|X18=k1_tarski(X17))&(r2_hidden(esk2_2(X17,X18),X18)|esk2_2(X17,X18)=X17|X18=k1_tarski(X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.18/0.45  fof(c_0_36, plain, ![X38, X39]:((~v4_relat_1(X39,X38)|r1_tarski(k1_relat_1(X39),X38)|~v1_relat_1(X39))&(~r1_tarski(k1_relat_1(X39),X38)|v4_relat_1(X39,X38)|~v1_relat_1(X39))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.18/0.45  cnf(c_0_37, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.45  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32])).
% 0.18/0.45  cnf(c_0_39, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.18/0.45  cnf(c_0_40, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.45  cnf(c_0_41, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.18/0.45  fof(c_0_42, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.18/0.45  cnf(c_0_43, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.18/0.45  cnf(c_0_44, negated_conjecture, (v4_relat_1(esk7_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.18/0.45  cnf(c_0_45, negated_conjecture, (v1_relat_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_38]), c_0_40])])).
% 0.18/0.45  cnf(c_0_46, plain, (X1=X3|X2!=k2_enumset1(X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_30]), c_0_31]), c_0_32])).
% 0.18/0.45  cnf(c_0_47, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.18/0.45  cnf(c_0_48, negated_conjecture, (r1_tarski(k1_relat_1(esk7_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])])).
% 0.18/0.45  fof(c_0_49, plain, ![X26, X27]:((k2_zfmisc_1(X26,X27)!=k1_xboole_0|(X26=k1_xboole_0|X27=k1_xboole_0))&((X26!=k1_xboole_0|k2_zfmisc_1(X26,X27)=k1_xboole_0)&(X27!=k1_xboole_0|k2_zfmisc_1(X26,X27)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.18/0.45  cnf(c_0_50, plain, (X1=X2|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_46])).
% 0.18/0.45  cnf(c_0_51, negated_conjecture, (r2_hidden(X1,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))|~r2_hidden(X1,k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.18/0.45  fof(c_0_52, plain, ![X44, X45]:(~v1_relat_1(X45)|k2_relat_1(k7_relat_1(X45,X44))=k9_relat_1(X45,X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.18/0.45  fof(c_0_53, plain, ![X46, X47]:(~v1_relat_1(X47)|~v4_relat_1(X47,X46)|X47=k7_relat_1(X47,X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.18/0.45  fof(c_0_54, plain, ![X28]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X28)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.18/0.45  cnf(c_0_55, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.18/0.45  cnf(c_0_56, negated_conjecture, (X1=esk4_0|~r2_hidden(X1,k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.18/0.45  cnf(c_0_57, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.18/0.45  cnf(c_0_58, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.18/0.45  cnf(c_0_59, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.18/0.45  cnf(c_0_60, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.18/0.45  cnf(c_0_61, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_55])).
% 0.18/0.45  fof(c_0_62, plain, ![X36, X37]:(~v1_relat_1(X36)|k11_relat_1(X36,X37)=k9_relat_1(X36,k1_tarski(X37))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).
% 0.18/0.45  fof(c_0_63, plain, ![X50, X51]:(~r2_hidden(X50,X51)|~r1_tarski(X51,X50)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.18/0.45  cnf(c_0_64, negated_conjecture, (esk1_2(k1_relat_1(esk7_0),X1)=esk4_0|r1_tarski(k1_relat_1(esk7_0),X1)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.18/0.45  fof(c_0_65, plain, ![X63, X64, X65]:((((v1_funct_1(X65)|(r2_hidden(esk3_3(X63,X64,X65),X63)|k1_relat_1(X65)!=X63)|(~v1_relat_1(X65)|~v1_funct_1(X65)))&(v1_funct_2(X65,X63,X64)|(r2_hidden(esk3_3(X63,X64,X65),X63)|k1_relat_1(X65)!=X63)|(~v1_relat_1(X65)|~v1_funct_1(X65))))&(m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64)))|(r2_hidden(esk3_3(X63,X64,X65),X63)|k1_relat_1(X65)!=X63)|(~v1_relat_1(X65)|~v1_funct_1(X65))))&(((v1_funct_1(X65)|(~r2_hidden(k1_funct_1(X65,esk3_3(X63,X64,X65)),X64)|k1_relat_1(X65)!=X63)|(~v1_relat_1(X65)|~v1_funct_1(X65)))&(v1_funct_2(X65,X63,X64)|(~r2_hidden(k1_funct_1(X65,esk3_3(X63,X64,X65)),X64)|k1_relat_1(X65)!=X63)|(~v1_relat_1(X65)|~v1_funct_1(X65))))&(m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64)))|(~r2_hidden(k1_funct_1(X65,esk3_3(X63,X64,X65)),X64)|k1_relat_1(X65)!=X63)|(~v1_relat_1(X65)|~v1_funct_1(X65))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_funct_2])])])])).
% 0.18/0.45  cnf(c_0_66, negated_conjecture, (~r1_tarski(k7_relset_1(k1_tarski(esk4_0),esk5_0,esk7_0,esk6_0),k1_tarski(k1_funct_1(esk7_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.45  fof(c_0_67, plain, ![X59, X60, X61, X62]:(~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))|k7_relset_1(X59,X60,X61,X62)=k9_relat_1(X61,X62)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.18/0.45  fof(c_0_68, plain, ![X48, X49]:(~v1_relat_1(X49)|~v1_funct_1(X49)|(~r2_hidden(X48,k1_relat_1(X49))|k11_relat_1(X49,X48)=k1_tarski(k1_funct_1(X49,X48)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t117_funct_1])])).
% 0.18/0.45  fof(c_0_69, plain, ![X42, X43]:(~v1_relat_1(X43)|r1_tarski(k9_relat_1(X43,X42),k2_relat_1(X43))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t144_relat_1])])).
% 0.18/0.45  cnf(c_0_70, plain, (k2_relat_1(X1)=k9_relat_1(X1,X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.18/0.45  cnf(c_0_71, plain, (v4_relat_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_37, c_0_60])).
% 0.18/0.45  cnf(c_0_72, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_40, c_0_61])).
% 0.18/0.45  cnf(c_0_73, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.18/0.45  cnf(c_0_74, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.18/0.45  cnf(c_0_75, negated_conjecture, (r2_hidden(esk4_0,k1_relat_1(esk7_0))|r1_tarski(k1_relat_1(esk7_0),X1)), inference(spm,[status(thm)],[c_0_57, c_0_64])).
% 0.18/0.45  cnf(c_0_76, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|r2_hidden(esk3_3(X2,X3,X1),X2)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.18/0.45  cnf(c_0_77, negated_conjecture, (~r1_tarski(k7_relset_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0,esk7_0,esk6_0),k2_enumset1(k1_funct_1(esk7_0,esk4_0),k1_funct_1(esk7_0,esk4_0),k1_funct_1(esk7_0,esk4_0),k1_funct_1(esk7_0,esk4_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_30]), c_0_30]), c_0_31]), c_0_31]), c_0_32]), c_0_32])).
% 0.18/0.45  cnf(c_0_78, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.18/0.45  cnf(c_0_79, plain, (k11_relat_1(X1,X2)=k1_tarski(k1_funct_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.18/0.45  cnf(c_0_80, plain, (r1_tarski(k9_relat_1(X1,X2),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.18/0.45  cnf(c_0_81, plain, (k2_relat_1(k1_xboole_0)=k9_relat_1(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72])])).
% 0.18/0.45  cnf(c_0_82, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k2_enumset1(X2,X2,X2,X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_30]), c_0_31]), c_0_32])).
% 0.18/0.45  fof(c_0_83, plain, ![X55, X56, X57, X58]:(~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56)))|m1_subset_1(k7_relset_1(X55,X56,X57,X58),k1_zfmisc_1(X56))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).
% 0.18/0.45  fof(c_0_84, plain, ![X29, X30]:((~m1_subset_1(X29,k1_zfmisc_1(X30))|r1_tarski(X29,X30))&(~r1_tarski(X29,X30)|m1_subset_1(X29,k1_zfmisc_1(X30)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.18/0.45  cnf(c_0_85, negated_conjecture, (r2_hidden(esk4_0,k1_relat_1(esk7_0))|~r2_hidden(X1,k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.18/0.45  cnf(c_0_86, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|r2_hidden(esk3_3(k1_relat_1(X1),X2,X1),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_76])).
% 0.18/0.45  cnf(c_0_87, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.45  cnf(c_0_88, negated_conjecture, (~r1_tarski(k9_relat_1(esk7_0,esk6_0),k2_enumset1(k1_funct_1(esk7_0,esk4_0),k1_funct_1(esk7_0,esk4_0),k1_funct_1(esk7_0,esk4_0),k1_funct_1(esk7_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_38])])).
% 0.18/0.45  cnf(c_0_89, plain, (k11_relat_1(X1,X2)=k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_30]), c_0_31]), c_0_32])).
% 0.18/0.45  cnf(c_0_90, negated_conjecture, (k9_relat_1(esk7_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))=k2_relat_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_44]), c_0_45])])).
% 0.18/0.45  cnf(c_0_91, plain, (r1_tarski(k9_relat_1(k1_xboole_0,X1),k9_relat_1(k1_xboole_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_72])])).
% 0.18/0.45  cnf(c_0_92, plain, (k11_relat_1(k1_xboole_0,X1)=k2_relat_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_81]), c_0_72])])).
% 0.18/0.45  cnf(c_0_93, plain, (m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.18/0.45  cnf(c_0_94, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.18/0.45  cnf(c_0_95, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk7_0),X1)))|r2_hidden(esk4_0,k1_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_87]), c_0_45])])).
% 0.18/0.45  cnf(c_0_96, negated_conjecture, (~r2_hidden(esk4_0,k1_relat_1(esk7_0))|~r1_tarski(k9_relat_1(esk7_0,esk6_0),k11_relat_1(esk7_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_87]), c_0_45])])).
% 0.18/0.45  cnf(c_0_97, negated_conjecture, (k11_relat_1(esk7_0,esk4_0)=k2_relat_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_90]), c_0_45])])).
% 0.18/0.45  cnf(c_0_98, plain, (r1_tarski(k2_relat_1(k1_xboole_0),k9_relat_1(k1_xboole_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_82]), c_0_92]), c_0_72])])).
% 0.18/0.45  cnf(c_0_99, plain, (m1_subset_1(k9_relat_1(X1,X2),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))), inference(spm,[status(thm)],[c_0_93, c_0_78])).
% 0.18/0.45  cnf(c_0_100, negated_conjecture, (r2_hidden(esk4_0,k1_relat_1(esk7_0))|r1_tarski(esk7_0,k2_zfmisc_1(k1_relat_1(esk7_0),X1))), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.18/0.45  cnf(c_0_101, negated_conjecture, (~r2_hidden(esk4_0,k1_relat_1(esk7_0))|~r1_tarski(k9_relat_1(esk7_0,esk6_0),k2_relat_1(esk7_0))), inference(rw,[status(thm)],[c_0_96, c_0_97])).
% 0.18/0.45  cnf(c_0_102, plain, (r2_hidden(X1,k9_relat_1(k1_xboole_0,X2))|~r2_hidden(X1,k2_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_47, c_0_98])).
% 0.18/0.45  cnf(c_0_103, plain, (m1_subset_1(k9_relat_1(k1_xboole_0,X1),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_99, c_0_60])).
% 0.18/0.45  fof(c_0_104, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.18/0.45  cnf(c_0_105, negated_conjecture, (r2_hidden(esk4_0,k1_relat_1(esk7_0))|r1_tarski(esk7_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_100, c_0_61])).
% 0.18/0.45  cnf(c_0_106, negated_conjecture, (~r2_hidden(esk4_0,k1_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_80]), c_0_45])])).
% 0.18/0.45  cnf(c_0_107, plain, (r2_hidden(esk1_2(k2_relat_1(k1_xboole_0),X1),k9_relat_1(k1_xboole_0,X2))|r1_tarski(k2_relat_1(k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_102, c_0_57])).
% 0.18/0.45  cnf(c_0_108, plain, (m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_82]), c_0_92]), c_0_72])])).
% 0.18/0.45  cnf(c_0_109, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_104])).
% 0.18/0.45  cnf(c_0_110, negated_conjecture, (r1_tarski(esk7_0,k1_xboole_0)), inference(sr,[status(thm)],[c_0_105, c_0_106])).
% 0.18/0.45  cnf(c_0_111, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_94, c_0_60])).
% 0.18/0.45  cnf(c_0_112, plain, (r2_hidden(X1,k2_relat_1(X2))|~v1_relat_1(X2)|~r2_hidden(X1,k9_relat_1(X2,X3))), inference(spm,[status(thm)],[c_0_47, c_0_80])).
% 0.18/0.45  cnf(c_0_113, plain, (r2_hidden(esk1_2(k9_relat_1(k1_xboole_0,X1),X2),k9_relat_1(k1_xboole_0,X3))|r1_tarski(k9_relat_1(k1_xboole_0,X1),X2)), inference(spm,[status(thm)],[c_0_107, c_0_81])).
% 0.18/0.45  cnf(c_0_114, plain, (r1_tarski(k2_relat_1(k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_94, c_0_108])).
% 0.18/0.45  cnf(c_0_115, negated_conjecture, (esk7_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_110]), c_0_111])])).
% 0.18/0.45  cnf(c_0_116, plain, (r2_hidden(esk1_2(k9_relat_1(k1_xboole_0,X1),X2),k2_relat_1(k1_xboole_0))|r1_tarski(k9_relat_1(k1_xboole_0,X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_113]), c_0_72])])).
% 0.18/0.45  cnf(c_0_117, plain, (~r2_hidden(X1,k2_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_74, c_0_114])).
% 0.18/0.45  cnf(c_0_118, negated_conjecture, (~r1_tarski(k9_relat_1(k1_xboole_0,esk6_0),k2_enumset1(k1_funct_1(k1_xboole_0,esk4_0),k1_funct_1(k1_xboole_0,esk4_0),k1_funct_1(k1_xboole_0,esk4_0),k1_funct_1(k1_xboole_0,esk4_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_115]), c_0_115]), c_0_115]), c_0_115]), c_0_115])).
% 0.18/0.45  cnf(c_0_119, plain, (r1_tarski(k9_relat_1(k1_xboole_0,X1),X2)), inference(sr,[status(thm)],[c_0_116, c_0_117])).
% 0.18/0.45  cnf(c_0_120, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_118, c_0_119])]), ['proof']).
% 0.18/0.45  # SZS output end CNFRefutation
% 0.18/0.45  # Proof object total steps             : 121
% 0.18/0.45  # Proof object clause steps            : 74
% 0.18/0.45  # Proof object formula steps           : 47
% 0.18/0.45  # Proof object conjectures             : 29
% 0.18/0.45  # Proof object clause conjectures      : 26
% 0.18/0.45  # Proof object formula conjectures     : 3
% 0.18/0.45  # Proof object initial clauses used    : 26
% 0.18/0.45  # Proof object initial formulas used   : 23
% 0.18/0.45  # Proof object generating inferences   : 35
% 0.18/0.45  # Proof object simplifying inferences  : 65
% 0.18/0.45  # Training examples: 0 positive, 0 negative
% 0.18/0.45  # Parsed axioms                        : 24
% 0.18/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.45  # Initial clauses                      : 45
% 0.18/0.45  # Removed in clause preprocessing      : 5
% 0.18/0.45  # Initial clauses in saturation        : 40
% 0.18/0.45  # Processed clauses                    : 1052
% 0.18/0.45  # ...of these trivial                  : 30
% 0.18/0.45  # ...subsumed                          : 620
% 0.18/0.45  # ...remaining for further processing  : 402
% 0.18/0.45  # Other redundant clauses eliminated   : 12
% 0.18/0.45  # Clauses deleted for lack of memory   : 0
% 0.18/0.45  # Backward-subsumed                    : 15
% 0.18/0.45  # Backward-rewritten                   : 67
% 0.18/0.45  # Generated clauses                    : 3890
% 0.18/0.45  # ...of the previous two non-trivial   : 3134
% 0.18/0.45  # Contextual simplify-reflections      : 6
% 0.18/0.45  # Paramodulations                      : 3860
% 0.18/0.45  # Factorizations                       : 0
% 0.18/0.45  # Equation resolutions                 : 12
% 0.18/0.45  # Propositional unsat checks           : 0
% 0.18/0.45  #    Propositional check models        : 0
% 0.18/0.45  #    Propositional check unsatisfiable : 0
% 0.18/0.45  #    Propositional clauses             : 0
% 0.18/0.45  #    Propositional clauses after purity: 0
% 0.18/0.45  #    Propositional unsat core size     : 0
% 0.18/0.45  #    Propositional preprocessing time  : 0.000
% 0.18/0.45  #    Propositional encoding time       : 0.000
% 0.18/0.45  #    Propositional solver time         : 0.000
% 0.18/0.45  #    Success case prop preproc time    : 0.000
% 0.18/0.45  #    Success case prop encoding time   : 0.000
% 0.18/0.45  #    Success case prop solver time     : 0.000
% 0.18/0.45  # Current number of processed clauses  : 291
% 0.18/0.45  #    Positive orientable unit clauses  : 38
% 0.18/0.45  #    Positive unorientable unit clauses: 3
% 0.18/0.45  #    Negative unit clauses             : 13
% 0.18/0.45  #    Non-unit-clauses                  : 237
% 0.18/0.45  # Current number of unprocessed clauses: 1980
% 0.18/0.45  # ...number of literals in the above   : 7323
% 0.18/0.45  # Current number of archived formulas  : 0
% 0.18/0.45  # Current number of archived clauses   : 104
% 0.18/0.45  # Clause-clause subsumption calls (NU) : 8379
% 0.18/0.45  # Rec. Clause-clause subsumption calls : 5003
% 0.18/0.45  # Non-unit clause-clause subsumptions  : 385
% 0.18/0.45  # Unit Clause-clause subsumption calls : 1348
% 0.18/0.45  # Rewrite failures with RHS unbound    : 34
% 0.18/0.45  # BW rewrite match attempts            : 28
% 0.18/0.45  # BW rewrite match successes           : 17
% 0.18/0.45  # Condensation attempts                : 0
% 0.18/0.45  # Condensation successes               : 0
% 0.18/0.45  # Termbank termtop insertions          : 59608
% 0.18/0.45  
% 0.18/0.45  # -------------------------------------------------
% 0.18/0.45  # User time                : 0.108 s
% 0.18/0.45  # System time              : 0.012 s
% 0.18/0.45  # Total time               : 0.120 s
% 0.18/0.45  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
