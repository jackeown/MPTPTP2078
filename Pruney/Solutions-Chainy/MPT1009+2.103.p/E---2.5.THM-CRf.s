%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:05:02 EST 2020

% Result     : Theorem 1.09s
% Output     : CNFRefutation 1.09s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 753 expanded)
%              Number of clauses        :   86 ( 302 expanded)
%              Number of leaves         :   29 ( 216 expanded)
%              Depth                    :   17
%              Number of atoms          :  426 (1500 expanded)
%              Number of equality atoms :  141 ( 664 expanded)
%              Maximal formula depth    :   32 (   4 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t47_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => r1_tarski(k8_relset_1(X1,X2,X4,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_2)).

fof(t38_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( k7_relset_1(X1,X2,X3,X1) = k2_relset_1(X1,X2,X3)
        & k8_relset_1(X1,X2,X3,X2) = k1_relset_1(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

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

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t13_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
     => ( r1_tarski(k1_relat_1(X4),X2)
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(t14_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
     => ( r1_tarski(k2_relat_1(X4),X2)
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

fof(d12_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( X3 = k9_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(X5,k1_relat_1(X1))
                  & r2_hidden(X5,X2)
                  & X4 = k1_funct_1(X1,X5) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

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

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t14_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( k1_relat_1(X2) = k1_tarski(X1)
       => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(d3_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( X6 = k3_enumset1(X1,X2,X3,X4,X5)
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ~ ( X7 != X1
              & X7 != X2
              & X7 != X3
              & X7 != X4
              & X7 != X5 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(t63_subset_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(c_0_29,plain,(
    ! [X92,X93] :
      ( ~ r2_hidden(X92,X93)
      | ~ r1_tarski(X93,X92) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_30,plain,(
    ! [X119,X120,X121,X122] :
      ( ~ v1_funct_1(X122)
      | ~ m1_subset_1(X122,k1_zfmisc_1(k2_zfmisc_1(X119,X120)))
      | r1_tarski(k8_relset_1(X119,X120,X122,X121),X119) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_funct_2])])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_32,plain,
    ( r1_tarski(k8_relset_1(X2,X3,X1,X4),X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_33,plain,(
    ! [X116,X117,X118] :
      ( ( k7_relset_1(X116,X117,X118,X116) = k2_relset_1(X116,X117,X118)
        | ~ m1_subset_1(X118,k1_zfmisc_1(k2_zfmisc_1(X116,X117))) )
      & ( k8_relset_1(X116,X117,X118,X117) = k1_relset_1(X116,X117,X118)
        | ~ m1_subset_1(X118,k1_zfmisc_1(k2_zfmisc_1(X116,X117))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).

cnf(c_0_34,plain,
    ( ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X2,k8_relset_1(X2,X3,X1,X4)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_35,plain,
    ( k8_relset_1(X1,X2,X3,X2) = k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_36,plain,(
    ! [X101,X102,X103] :
      ( ~ m1_subset_1(X103,k1_zfmisc_1(k2_zfmisc_1(X101,X102)))
      | k1_relset_1(X101,X102,X103) = k1_relat_1(X103) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_37,plain,
    ( ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X2,k1_relset_1(X2,X3,X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_38,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_39,plain,(
    ! [X65,X66] :
      ( ( ~ m1_subset_1(X65,k1_zfmisc_1(X66))
        | r1_tarski(X65,X66) )
      & ( ~ r1_tarski(X65,X66)
        | m1_subset_1(X65,k1_zfmisc_1(X66)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_40,plain,(
    ! [X45,X46] :
      ( ( k2_zfmisc_1(X45,X46) != k1_xboole_0
        | X45 = k1_xboole_0
        | X46 = k1_xboole_0 )
      & ( X45 != k1_xboole_0
        | k2_zfmisc_1(X45,X46) = k1_xboole_0 )
      & ( X46 != k1_xboole_0
        | k2_zfmisc_1(X45,X46) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_41,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,k1_tarski(X1),X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
       => ( X2 != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1))) ) ) ),
    inference(assume_negation,[status(cth)],[t64_funct_2])).

cnf(c_0_42,plain,
    ( ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_45,negated_conjecture,
    ( v1_funct_1(esk9_0)
    & v1_funct_2(esk9_0,k1_tarski(esk6_0),esk7_0)
    & m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk6_0),esk7_0)))
    & esk7_0 != k1_xboole_0
    & ~ r1_tarski(k7_relset_1(k1_tarski(esk6_0),esk7_0,esk9_0,esk8_0),k1_tarski(k1_funct_1(esk9_0,esk6_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_41])])])).

fof(c_0_46,plain,(
    ! [X17] : k2_tarski(X17,X17) = k1_tarski(X17) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_47,plain,(
    ! [X18,X19] : k1_enumset1(X18,X18,X19) = k2_tarski(X18,X19) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_48,plain,(
    ! [X20,X21,X22] : k2_enumset1(X20,X20,X21,X22) = k1_enumset1(X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_49,plain,(
    ! [X23,X24,X25,X26] : k3_enumset1(X23,X23,X24,X25,X26) = k2_enumset1(X23,X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_50,plain,(
    ! [X27,X28,X29,X30,X31] : k4_enumset1(X27,X27,X28,X29,X30,X31) = k3_enumset1(X27,X28,X29,X30,X31) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_51,plain,(
    ! [X32,X33,X34,X35,X36,X37] : k5_enumset1(X32,X32,X33,X34,X35,X36,X37) = k4_enumset1(X32,X33,X34,X35,X36,X37) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_52,plain,(
    ! [X38,X39,X40,X41,X42,X43,X44] : k6_enumset1(X38,X38,X39,X40,X41,X42,X43,X44) = k5_enumset1(X38,X39,X40,X41,X42,X43,X44) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_53,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | X14 != X15 )
      & ( r1_tarski(X15,X14)
        | X14 != X15 )
      & ( ~ r1_tarski(X14,X15)
        | ~ r1_tarski(X15,X14)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_54,plain,(
    ! [X16] : r1_tarski(k1_xboole_0,X16) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_55,plain,
    ( ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_56,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_44])).

fof(c_0_57,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_58,plain,(
    ! [X108,X109,X110,X111] :
      ( ~ m1_subset_1(X111,k1_zfmisc_1(k2_zfmisc_1(X108,X110)))
      | ~ r1_tarski(k1_relat_1(X111),X109)
      | m1_subset_1(X111,k1_zfmisc_1(k2_zfmisc_1(X109,X110))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relset_1])])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk6_0),esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_60,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_61,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_62,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_63,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_64,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_65,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_66,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_67,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_68,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_69,plain,
    ( ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_70,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_71,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(k1_relat_1(X1),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),esk7_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_62]),c_0_63]),c_0_64]),c_0_65]),c_0_66])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_74,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_75,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

fof(c_0_76,plain,(
    ! [X112,X113,X114,X115] :
      ( ~ m1_subset_1(X115,k1_zfmisc_1(k2_zfmisc_1(X114,X112)))
      | ~ r1_tarski(k2_relat_1(X115),X113)
      | m1_subset_1(X115,k1_zfmisc_1(k2_zfmisc_1(X114,X113))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_relset_1])])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk7_0)))
    | ~ r1_tarski(k1_relat_1(esk9_0),X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_78,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_73])).

cnf(c_0_79,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_81,plain,(
    ! [X78,X79,X80,X81,X83,X84,X85,X86,X88] :
      ( ( r2_hidden(esk3_4(X78,X79,X80,X81),k1_relat_1(X78))
        | ~ r2_hidden(X81,X80)
        | X80 != k9_relat_1(X78,X79)
        | ~ v1_relat_1(X78)
        | ~ v1_funct_1(X78) )
      & ( r2_hidden(esk3_4(X78,X79,X80,X81),X79)
        | ~ r2_hidden(X81,X80)
        | X80 != k9_relat_1(X78,X79)
        | ~ v1_relat_1(X78)
        | ~ v1_funct_1(X78) )
      & ( X81 = k1_funct_1(X78,esk3_4(X78,X79,X80,X81))
        | ~ r2_hidden(X81,X80)
        | X80 != k9_relat_1(X78,X79)
        | ~ v1_relat_1(X78)
        | ~ v1_funct_1(X78) )
      & ( ~ r2_hidden(X84,k1_relat_1(X78))
        | ~ r2_hidden(X84,X79)
        | X83 != k1_funct_1(X78,X84)
        | r2_hidden(X83,X80)
        | X80 != k9_relat_1(X78,X79)
        | ~ v1_relat_1(X78)
        | ~ v1_funct_1(X78) )
      & ( ~ r2_hidden(esk4_3(X78,X85,X86),X86)
        | ~ r2_hidden(X88,k1_relat_1(X78))
        | ~ r2_hidden(X88,X85)
        | esk4_3(X78,X85,X86) != k1_funct_1(X78,X88)
        | X86 = k9_relat_1(X78,X85)
        | ~ v1_relat_1(X78)
        | ~ v1_funct_1(X78) )
      & ( r2_hidden(esk5_3(X78,X85,X86),k1_relat_1(X78))
        | r2_hidden(esk4_3(X78,X85,X86),X86)
        | X86 = k9_relat_1(X78,X85)
        | ~ v1_relat_1(X78)
        | ~ v1_funct_1(X78) )
      & ( r2_hidden(esk5_3(X78,X85,X86),X85)
        | r2_hidden(esk4_3(X78,X85,X86),X86)
        | X86 = k9_relat_1(X78,X85)
        | ~ v1_relat_1(X78)
        | ~ v1_funct_1(X78) )
      & ( esk4_3(X78,X85,X86) = k1_funct_1(X78,esk5_3(X78,X85,X86))
        | r2_hidden(esk4_3(X78,X85,X86),X86)
        | X86 = k9_relat_1(X78,X85)
        | ~ v1_relat_1(X78)
        | ~ v1_funct_1(X78) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).

fof(c_0_82,plain,(
    ! [X70,X71] :
      ( ~ v1_relat_1(X70)
      | ~ m1_subset_1(X71,k1_zfmisc_1(X70))
      | v1_relat_1(X71) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_83,plain,(
    ! [X74,X75] : v1_relat_1(k2_zfmisc_1(X74,X75)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_84,plain,(
    ! [X97,X98,X99,X100] :
      ( ~ m1_subset_1(X99,k1_zfmisc_1(k2_zfmisc_1(X97,X98)))
      | m1_subset_1(k7_relset_1(X97,X98,X99,X100),k1_zfmisc_1(X98)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).

fof(c_0_85,plain,(
    ! [X104,X105,X106,X107] :
      ( ~ m1_subset_1(X106,k1_zfmisc_1(k2_zfmisc_1(X104,X105)))
      | k7_relset_1(X104,X105,X106,X107) = k9_relat_1(X106,X107) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

cnf(c_0_86,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(k2_relat_1(X1),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk9_0),esk7_0))) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk7_0)))
    | ~ r1_tarski(esk9_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_79]),c_0_68]),c_0_80])])).

cnf(c_0_89,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),k1_relat_1(X1))
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_90,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_91,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

fof(c_0_92,plain,(
    ! [X94,X95,X96] :
      ( ( v4_relat_1(X96,X94)
        | ~ m1_subset_1(X96,k1_zfmisc_1(k2_zfmisc_1(X94,X95))) )
      & ( v5_relat_1(X96,X95)
        | ~ m1_subset_1(X96,k1_zfmisc_1(k2_zfmisc_1(X94,X95))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_93,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(esk6_0),esk7_0,esk9_0,esk8_0),k1_tarski(k1_funct_1(esk9_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_94,plain,(
    ! [X90,X91] :
      ( ~ v1_relat_1(X91)
      | ~ v1_funct_1(X91)
      | k1_relat_1(X91) != k1_tarski(X90)
      | k2_relat_1(X91) = k1_tarski(k1_funct_1(X91,X90)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_funct_1])])).

cnf(c_0_95,plain,
    ( m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_96,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_97,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk9_0),X1)))
    | ~ r1_tarski(k2_relat_1(esk9_0),X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_98,plain,
    ( ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_56])).

cnf(c_0_99,negated_conjecture,
    ( ~ r2_hidden(X1,k1_relat_1(esk9_0))
    | ~ r1_tarski(esk9_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_88]),c_0_80])])).

cnf(c_0_100,plain,
    ( r2_hidden(esk3_4(X1,X2,k9_relat_1(X1,X2),X3),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,k9_relat_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_89])).

cnf(c_0_101,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_72]),c_0_91])])).

fof(c_0_102,plain,(
    ! [X47,X48,X49,X50,X51,X52,X53,X54,X55,X56,X57,X58,X59,X60] :
      ( ( ~ r2_hidden(X53,X52)
        | X53 = X47
        | X53 = X48
        | X53 = X49
        | X53 = X50
        | X53 = X51
        | X52 != k3_enumset1(X47,X48,X49,X50,X51) )
      & ( X54 != X47
        | r2_hidden(X54,X52)
        | X52 != k3_enumset1(X47,X48,X49,X50,X51) )
      & ( X54 != X48
        | r2_hidden(X54,X52)
        | X52 != k3_enumset1(X47,X48,X49,X50,X51) )
      & ( X54 != X49
        | r2_hidden(X54,X52)
        | X52 != k3_enumset1(X47,X48,X49,X50,X51) )
      & ( X54 != X50
        | r2_hidden(X54,X52)
        | X52 != k3_enumset1(X47,X48,X49,X50,X51) )
      & ( X54 != X51
        | r2_hidden(X54,X52)
        | X52 != k3_enumset1(X47,X48,X49,X50,X51) )
      & ( esk2_6(X55,X56,X57,X58,X59,X60) != X55
        | ~ r2_hidden(esk2_6(X55,X56,X57,X58,X59,X60),X60)
        | X60 = k3_enumset1(X55,X56,X57,X58,X59) )
      & ( esk2_6(X55,X56,X57,X58,X59,X60) != X56
        | ~ r2_hidden(esk2_6(X55,X56,X57,X58,X59,X60),X60)
        | X60 = k3_enumset1(X55,X56,X57,X58,X59) )
      & ( esk2_6(X55,X56,X57,X58,X59,X60) != X57
        | ~ r2_hidden(esk2_6(X55,X56,X57,X58,X59,X60),X60)
        | X60 = k3_enumset1(X55,X56,X57,X58,X59) )
      & ( esk2_6(X55,X56,X57,X58,X59,X60) != X58
        | ~ r2_hidden(esk2_6(X55,X56,X57,X58,X59,X60),X60)
        | X60 = k3_enumset1(X55,X56,X57,X58,X59) )
      & ( esk2_6(X55,X56,X57,X58,X59,X60) != X59
        | ~ r2_hidden(esk2_6(X55,X56,X57,X58,X59,X60),X60)
        | X60 = k3_enumset1(X55,X56,X57,X58,X59) )
      & ( r2_hidden(esk2_6(X55,X56,X57,X58,X59,X60),X60)
        | esk2_6(X55,X56,X57,X58,X59,X60) = X55
        | esk2_6(X55,X56,X57,X58,X59,X60) = X56
        | esk2_6(X55,X56,X57,X58,X59,X60) = X57
        | esk2_6(X55,X56,X57,X58,X59,X60) = X58
        | esk2_6(X55,X56,X57,X58,X59,X60) = X59
        | X60 = k3_enumset1(X55,X56,X57,X58,X59) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_enumset1])])])])])])).

fof(c_0_103,plain,(
    ! [X72,X73] :
      ( ( ~ v4_relat_1(X73,X72)
        | r1_tarski(k1_relat_1(X73),X72)
        | ~ v1_relat_1(X73) )
      & ( ~ r1_tarski(k1_relat_1(X73),X72)
        | v4_relat_1(X73,X72)
        | ~ v1_relat_1(X73) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_104,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

fof(c_0_105,plain,(
    ! [X63,X64] :
      ( ~ r2_hidden(X63,X64)
      | m1_subset_1(k1_tarski(X63),k1_zfmisc_1(X64)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).

cnf(c_0_106,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),esk7_0,esk9_0,esk8_0),k6_enumset1(k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_60]),c_0_60]),c_0_61]),c_0_61]),c_0_62]),c_0_62]),c_0_63]),c_0_63]),c_0_64]),c_0_64]),c_0_65]),c_0_65]),c_0_66]),c_0_66])).

cnf(c_0_107,plain,
    ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_relat_1(X1) != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_108,plain,
    ( m1_subset_1(k9_relat_1(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3))) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_109,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk9_0),k2_relat_1(esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_97,c_0_78])).

cnf(c_0_110,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_98,c_0_70])).

cnf(c_0_111,negated_conjecture,
    ( ~ r2_hidden(X1,k9_relat_1(esk9_0,X2))
    | ~ r1_tarski(esk9_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_80]),c_0_101])])).

cnf(c_0_112,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | X1 = X6
    | X1 = X7
    | ~ r2_hidden(X1,X2)
    | X2 != k3_enumset1(X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_113,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_114,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_115,negated_conjecture,
    ( v4_relat_1(esk9_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_72])).

cnf(c_0_116,plain,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_105])).

cnf(c_0_117,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk9_0,esk8_0),k6_enumset1(k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_96]),c_0_72])])).

cnf(c_0_118,plain,
    ( k2_relat_1(X1) = k6_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2))
    | k1_relat_1(X1) != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_107,c_0_60]),c_0_60]),c_0_61]),c_0_61]),c_0_62]),c_0_62]),c_0_63]),c_0_63]),c_0_64]),c_0_64]),c_0_65]),c_0_65]),c_0_66]),c_0_66])).

cnf(c_0_119,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_120,negated_conjecture,
    ( m1_subset_1(k9_relat_1(esk9_0,X1),k1_zfmisc_1(k2_relat_1(esk9_0))) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_121,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk7_0)))
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_110]),c_0_80])])).

cnf(c_0_122,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_123,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk9_0,X1),X2)
    | ~ r1_tarski(esk9_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_111,c_0_70])).

cnf(c_0_124,plain,
    ( X1 = X7
    | X1 = X6
    | X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X4,X5,X6,X7)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_112,c_0_64]),c_0_65]),c_0_66])).

cnf(c_0_125,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_113,c_0_70])).

cnf(c_0_126,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk9_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_115]),c_0_101])])).

cnf(c_0_127,plain,
    ( m1_subset_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_116,c_0_60]),c_0_61]),c_0_62]),c_0_63]),c_0_64]),c_0_65]),c_0_66])).

cnf(c_0_128,negated_conjecture,
    ( k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) != k1_relat_1(esk9_0)
    | ~ r1_tarski(k9_relat_1(esk9_0,esk8_0),k2_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_118]),c_0_80]),c_0_101])])).

cnf(c_0_129,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk9_0,X1),k2_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_119,c_0_120])).

cnf(c_0_130,negated_conjecture,
    ( r1_tarski(esk9_0,k2_zfmisc_1(X1,esk7_0))
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_119,c_0_121])).

cnf(c_0_131,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_122])).

cnf(c_0_132,negated_conjecture,
    ( ~ r1_tarski(esk9_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_117,c_0_123])).

cnf(c_0_133,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | X1 = X5
    | X1 = X6
    | ~ r2_hidden(X1,k6_enumset1(X6,X6,X6,X6,X5,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_124])).

cnf(c_0_134,negated_conjecture,
    ( r2_hidden(esk1_2(k1_relat_1(esk9_0),X1),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))
    | r1_tarski(k1_relat_1(esk9_0),X1) ),
    inference(spm,[status(thm)],[c_0_125,c_0_126])).

cnf(c_0_135,negated_conjecture,
    ( k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) = k1_relat_1(esk9_0)
    | ~ r1_tarski(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k1_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_126])).

cnf(c_0_136,plain,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_119,c_0_127])).

cnf(c_0_137,negated_conjecture,
    ( k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) != k1_relat_1(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_128,c_0_129])])).

cnf(c_0_138,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk9_0))))
    | ~ r1_tarski(k1_relat_1(esk9_0),X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_109])).

cnf(c_0_139,negated_conjecture,
    ( ~ m1_subset_1(esk9_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_131]),c_0_132])).

cnf(c_0_140,negated_conjecture,
    ( esk1_2(k1_relat_1(esk9_0),X1) = esk6_0
    | r1_tarski(k1_relat_1(esk9_0),X1) ),
    inference(spm,[status(thm)],[c_0_133,c_0_134])).

cnf(c_0_141,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k1_relat_1(esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_136]),c_0_137])).

cnf(c_0_142,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk9_0),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_131]),c_0_139])).

cnf(c_0_143,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk9_0),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_140]),c_0_141])).

cnf(c_0_144,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_142,c_0_143])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:36:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 1.09/1.30  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 1.09/1.30  # and selection function SelectComplexExceptUniqMaxHorn.
% 1.09/1.30  #
% 1.09/1.30  # Preprocessing time       : 0.045 s
% 1.09/1.30  # Presaturation interreduction done
% 1.09/1.30  
% 1.09/1.30  # Proof found!
% 1.09/1.30  # SZS status Theorem
% 1.09/1.30  # SZS output start CNFRefutation
% 1.09/1.30  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 1.09/1.30  fof(t47_funct_2, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X4)&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r1_tarski(k8_relset_1(X1,X2,X4,X3),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_funct_2)).
% 1.09/1.30  fof(t38_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(k7_relset_1(X1,X2,X3,X1)=k2_relset_1(X1,X2,X3)&k8_relset_1(X1,X2,X3,X2)=k1_relset_1(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 1.09/1.30  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 1.09/1.30  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.09/1.30  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.09/1.30  fof(t64_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,k1_tarski(X1),X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 1.09/1.30  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.09/1.30  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.09/1.30  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.09/1.30  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 1.09/1.30  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 1.09/1.30  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 1.09/1.30  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 1.09/1.30  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.09/1.30  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.09/1.30  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.09/1.30  fof(t13_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))=>(r1_tarski(k1_relat_1(X4),X2)=>m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 1.09/1.30  fof(t14_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>(r1_tarski(k2_relat_1(X4),X2)=>m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_relset_1)).
% 1.09/1.30  fof(d12_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(X3=k9_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((r2_hidden(X5,k1_relat_1(X1))&r2_hidden(X5,X2))&X4=k1_funct_1(X1,X5))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_1)).
% 1.09/1.30  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.09/1.30  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.09/1.30  fof(dt_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 1.09/1.30  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 1.09/1.30  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.09/1.30  fof(t14_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 1.09/1.30  fof(d3_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:(X6=k3_enumset1(X1,X2,X3,X4,X5)<=>![X7]:(r2_hidden(X7,X6)<=>~(((((X7!=X1&X7!=X2)&X7!=X3)&X7!=X4)&X7!=X5)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_enumset1)).
% 1.09/1.30  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 1.09/1.30  fof(t63_subset_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 1.09/1.30  fof(c_0_29, plain, ![X92, X93]:(~r2_hidden(X92,X93)|~r1_tarski(X93,X92)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 1.09/1.30  fof(c_0_30, plain, ![X119, X120, X121, X122]:(~v1_funct_1(X122)|~m1_subset_1(X122,k1_zfmisc_1(k2_zfmisc_1(X119,X120)))|r1_tarski(k8_relset_1(X119,X120,X122,X121),X119)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_funct_2])])).
% 1.09/1.30  cnf(c_0_31, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.09/1.30  cnf(c_0_32, plain, (r1_tarski(k8_relset_1(X2,X3,X1,X4),X2)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.09/1.30  fof(c_0_33, plain, ![X116, X117, X118]:((k7_relset_1(X116,X117,X118,X116)=k2_relset_1(X116,X117,X118)|~m1_subset_1(X118,k1_zfmisc_1(k2_zfmisc_1(X116,X117))))&(k8_relset_1(X116,X117,X118,X117)=k1_relset_1(X116,X117,X118)|~m1_subset_1(X118,k1_zfmisc_1(k2_zfmisc_1(X116,X117))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).
% 1.09/1.30  cnf(c_0_34, plain, (~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X2,k8_relset_1(X2,X3,X1,X4))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 1.09/1.30  cnf(c_0_35, plain, (k8_relset_1(X1,X2,X3,X2)=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.09/1.30  fof(c_0_36, plain, ![X101, X102, X103]:(~m1_subset_1(X103,k1_zfmisc_1(k2_zfmisc_1(X101,X102)))|k1_relset_1(X101,X102,X103)=k1_relat_1(X103)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 1.09/1.30  cnf(c_0_37, plain, (~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X2,k1_relset_1(X2,X3,X1))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 1.09/1.30  cnf(c_0_38, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 1.09/1.30  fof(c_0_39, plain, ![X65, X66]:((~m1_subset_1(X65,k1_zfmisc_1(X66))|r1_tarski(X65,X66))&(~r1_tarski(X65,X66)|m1_subset_1(X65,k1_zfmisc_1(X66)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 1.09/1.30  fof(c_0_40, plain, ![X45, X46]:((k2_zfmisc_1(X45,X46)!=k1_xboole_0|(X45=k1_xboole_0|X46=k1_xboole_0))&((X45!=k1_xboole_0|k2_zfmisc_1(X45,X46)=k1_xboole_0)&(X46!=k1_xboole_0|k2_zfmisc_1(X45,X46)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 1.09/1.30  fof(c_0_41, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,k1_tarski(X1),X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1)))))), inference(assume_negation,[status(cth)],[t64_funct_2])).
% 1.09/1.30  cnf(c_0_42, plain, (~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X2,k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 1.09/1.30  cnf(c_0_43, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 1.09/1.30  cnf(c_0_44, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_40])).
% 1.09/1.30  fof(c_0_45, negated_conjecture, (((v1_funct_1(esk9_0)&v1_funct_2(esk9_0,k1_tarski(esk6_0),esk7_0))&m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk6_0),esk7_0))))&(esk7_0!=k1_xboole_0&~r1_tarski(k7_relset_1(k1_tarski(esk6_0),esk7_0,esk9_0,esk8_0),k1_tarski(k1_funct_1(esk9_0,esk6_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_41])])])).
% 1.09/1.30  fof(c_0_46, plain, ![X17]:k2_tarski(X17,X17)=k1_tarski(X17), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 1.09/1.30  fof(c_0_47, plain, ![X18, X19]:k1_enumset1(X18,X18,X19)=k2_tarski(X18,X19), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 1.09/1.30  fof(c_0_48, plain, ![X20, X21, X22]:k2_enumset1(X20,X20,X21,X22)=k1_enumset1(X20,X21,X22), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 1.09/1.30  fof(c_0_49, plain, ![X23, X24, X25, X26]:k3_enumset1(X23,X23,X24,X25,X26)=k2_enumset1(X23,X24,X25,X26), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 1.09/1.30  fof(c_0_50, plain, ![X27, X28, X29, X30, X31]:k4_enumset1(X27,X27,X28,X29,X30,X31)=k3_enumset1(X27,X28,X29,X30,X31), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 1.09/1.30  fof(c_0_51, plain, ![X32, X33, X34, X35, X36, X37]:k5_enumset1(X32,X32,X33,X34,X35,X36,X37)=k4_enumset1(X32,X33,X34,X35,X36,X37), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 1.09/1.30  fof(c_0_52, plain, ![X38, X39, X40, X41, X42, X43, X44]:k6_enumset1(X38,X38,X39,X40,X41,X42,X43,X44)=k5_enumset1(X38,X39,X40,X41,X42,X43,X44), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 1.09/1.30  fof(c_0_53, plain, ![X14, X15]:(((r1_tarski(X14,X15)|X14!=X15)&(r1_tarski(X15,X14)|X14!=X15))&(~r1_tarski(X14,X15)|~r1_tarski(X15,X14)|X14=X15)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.09/1.30  fof(c_0_54, plain, ![X16]:r1_tarski(k1_xboole_0,X16), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 1.09/1.30  cnf(c_0_55, plain, (~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 1.09/1.30  cnf(c_0_56, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_44])).
% 1.09/1.30  fof(c_0_57, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk1_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk1_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 1.09/1.30  fof(c_0_58, plain, ![X108, X109, X110, X111]:(~m1_subset_1(X111,k1_zfmisc_1(k2_zfmisc_1(X108,X110)))|(~r1_tarski(k1_relat_1(X111),X109)|m1_subset_1(X111,k1_zfmisc_1(k2_zfmisc_1(X109,X110))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relset_1])])).
% 1.09/1.30  cnf(c_0_59, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk6_0),esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 1.09/1.30  cnf(c_0_60, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 1.09/1.30  cnf(c_0_61, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 1.09/1.30  cnf(c_0_62, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 1.09/1.30  cnf(c_0_63, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 1.09/1.30  cnf(c_0_64, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 1.09/1.30  cnf(c_0_65, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 1.09/1.30  cnf(c_0_66, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 1.09/1.30  cnf(c_0_67, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 1.09/1.30  cnf(c_0_68, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 1.09/1.30  cnf(c_0_69, plain, (~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 1.09/1.30  cnf(c_0_70, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 1.09/1.30  cnf(c_0_71, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(k1_relat_1(X1),X4)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 1.09/1.30  cnf(c_0_72, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),esk7_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_60]), c_0_61]), c_0_62]), c_0_63]), c_0_64]), c_0_65]), c_0_66])).
% 1.09/1.30  cnf(c_0_73, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_53])).
% 1.09/1.30  cnf(c_0_74, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 1.09/1.30  cnf(c_0_75, plain, (r1_tarski(k1_relat_1(X1),X2)|~v1_funct_1(X1)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 1.09/1.30  fof(c_0_76, plain, ![X112, X113, X114, X115]:(~m1_subset_1(X115,k1_zfmisc_1(k2_zfmisc_1(X114,X112)))|(~r1_tarski(k2_relat_1(X115),X113)|m1_subset_1(X115,k1_zfmisc_1(k2_zfmisc_1(X114,X113))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_relset_1])])).
% 1.09/1.30  cnf(c_0_77, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk7_0)))|~r1_tarski(k1_relat_1(esk9_0),X1)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 1.09/1.30  cnf(c_0_78, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_73])).
% 1.09/1.30  cnf(c_0_79, plain, (k1_relat_1(X1)=k1_xboole_0|~v1_funct_1(X1)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 1.09/1.30  cnf(c_0_80, negated_conjecture, (v1_funct_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 1.09/1.30  fof(c_0_81, plain, ![X78, X79, X80, X81, X83, X84, X85, X86, X88]:(((((r2_hidden(esk3_4(X78,X79,X80,X81),k1_relat_1(X78))|~r2_hidden(X81,X80)|X80!=k9_relat_1(X78,X79)|(~v1_relat_1(X78)|~v1_funct_1(X78)))&(r2_hidden(esk3_4(X78,X79,X80,X81),X79)|~r2_hidden(X81,X80)|X80!=k9_relat_1(X78,X79)|(~v1_relat_1(X78)|~v1_funct_1(X78))))&(X81=k1_funct_1(X78,esk3_4(X78,X79,X80,X81))|~r2_hidden(X81,X80)|X80!=k9_relat_1(X78,X79)|(~v1_relat_1(X78)|~v1_funct_1(X78))))&(~r2_hidden(X84,k1_relat_1(X78))|~r2_hidden(X84,X79)|X83!=k1_funct_1(X78,X84)|r2_hidden(X83,X80)|X80!=k9_relat_1(X78,X79)|(~v1_relat_1(X78)|~v1_funct_1(X78))))&((~r2_hidden(esk4_3(X78,X85,X86),X86)|(~r2_hidden(X88,k1_relat_1(X78))|~r2_hidden(X88,X85)|esk4_3(X78,X85,X86)!=k1_funct_1(X78,X88))|X86=k9_relat_1(X78,X85)|(~v1_relat_1(X78)|~v1_funct_1(X78)))&(((r2_hidden(esk5_3(X78,X85,X86),k1_relat_1(X78))|r2_hidden(esk4_3(X78,X85,X86),X86)|X86=k9_relat_1(X78,X85)|(~v1_relat_1(X78)|~v1_funct_1(X78)))&(r2_hidden(esk5_3(X78,X85,X86),X85)|r2_hidden(esk4_3(X78,X85,X86),X86)|X86=k9_relat_1(X78,X85)|(~v1_relat_1(X78)|~v1_funct_1(X78))))&(esk4_3(X78,X85,X86)=k1_funct_1(X78,esk5_3(X78,X85,X86))|r2_hidden(esk4_3(X78,X85,X86),X86)|X86=k9_relat_1(X78,X85)|(~v1_relat_1(X78)|~v1_funct_1(X78)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).
% 1.09/1.30  fof(c_0_82, plain, ![X70, X71]:(~v1_relat_1(X70)|(~m1_subset_1(X71,k1_zfmisc_1(X70))|v1_relat_1(X71))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 1.09/1.30  fof(c_0_83, plain, ![X74, X75]:v1_relat_1(k2_zfmisc_1(X74,X75)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 1.09/1.30  fof(c_0_84, plain, ![X97, X98, X99, X100]:(~m1_subset_1(X99,k1_zfmisc_1(k2_zfmisc_1(X97,X98)))|m1_subset_1(k7_relset_1(X97,X98,X99,X100),k1_zfmisc_1(X98))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).
% 1.09/1.30  fof(c_0_85, plain, ![X104, X105, X106, X107]:(~m1_subset_1(X106,k1_zfmisc_1(k2_zfmisc_1(X104,X105)))|k7_relset_1(X104,X105,X106,X107)=k9_relat_1(X106,X107)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 1.09/1.30  cnf(c_0_86, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(k2_relat_1(X1),X4)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 1.09/1.30  cnf(c_0_87, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk9_0),esk7_0)))), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 1.09/1.30  cnf(c_0_88, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk7_0)))|~r1_tarski(esk9_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_79]), c_0_68]), c_0_80])])).
% 1.09/1.30  cnf(c_0_89, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),k1_relat_1(X1))|~r2_hidden(X4,X3)|X3!=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 1.09/1.30  cnf(c_0_90, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_82])).
% 1.09/1.30  cnf(c_0_91, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 1.09/1.30  fof(c_0_92, plain, ![X94, X95, X96]:((v4_relat_1(X96,X94)|~m1_subset_1(X96,k1_zfmisc_1(k2_zfmisc_1(X94,X95))))&(v5_relat_1(X96,X95)|~m1_subset_1(X96,k1_zfmisc_1(k2_zfmisc_1(X94,X95))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 1.09/1.30  cnf(c_0_93, negated_conjecture, (~r1_tarski(k7_relset_1(k1_tarski(esk6_0),esk7_0,esk9_0,esk8_0),k1_tarski(k1_funct_1(esk9_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 1.09/1.30  fof(c_0_94, plain, ![X90, X91]:(~v1_relat_1(X91)|~v1_funct_1(X91)|(k1_relat_1(X91)!=k1_tarski(X90)|k2_relat_1(X91)=k1_tarski(k1_funct_1(X91,X90)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_funct_1])])).
% 1.09/1.30  cnf(c_0_95, plain, (m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_84])).
% 1.09/1.30  cnf(c_0_96, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_85])).
% 1.09/1.30  cnf(c_0_97, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk9_0),X1)))|~r1_tarski(k2_relat_1(esk9_0),X1)), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 1.09/1.30  cnf(c_0_98, plain, (~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))|~r2_hidden(X2,k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_42, c_0_56])).
% 1.09/1.30  cnf(c_0_99, negated_conjecture, (~r2_hidden(X1,k1_relat_1(esk9_0))|~r1_tarski(esk9_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_88]), c_0_80])])).
% 1.09/1.30  cnf(c_0_100, plain, (r2_hidden(esk3_4(X1,X2,k9_relat_1(X1,X2),X3),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X3,k9_relat_1(X1,X2))), inference(er,[status(thm)],[c_0_89])).
% 1.09/1.30  cnf(c_0_101, negated_conjecture, (v1_relat_1(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_72]), c_0_91])])).
% 1.09/1.30  fof(c_0_102, plain, ![X47, X48, X49, X50, X51, X52, X53, X54, X55, X56, X57, X58, X59, X60]:(((~r2_hidden(X53,X52)|(X53=X47|X53=X48|X53=X49|X53=X50|X53=X51)|X52!=k3_enumset1(X47,X48,X49,X50,X51))&(((((X54!=X47|r2_hidden(X54,X52)|X52!=k3_enumset1(X47,X48,X49,X50,X51))&(X54!=X48|r2_hidden(X54,X52)|X52!=k3_enumset1(X47,X48,X49,X50,X51)))&(X54!=X49|r2_hidden(X54,X52)|X52!=k3_enumset1(X47,X48,X49,X50,X51)))&(X54!=X50|r2_hidden(X54,X52)|X52!=k3_enumset1(X47,X48,X49,X50,X51)))&(X54!=X51|r2_hidden(X54,X52)|X52!=k3_enumset1(X47,X48,X49,X50,X51))))&((((((esk2_6(X55,X56,X57,X58,X59,X60)!=X55|~r2_hidden(esk2_6(X55,X56,X57,X58,X59,X60),X60)|X60=k3_enumset1(X55,X56,X57,X58,X59))&(esk2_6(X55,X56,X57,X58,X59,X60)!=X56|~r2_hidden(esk2_6(X55,X56,X57,X58,X59,X60),X60)|X60=k3_enumset1(X55,X56,X57,X58,X59)))&(esk2_6(X55,X56,X57,X58,X59,X60)!=X57|~r2_hidden(esk2_6(X55,X56,X57,X58,X59,X60),X60)|X60=k3_enumset1(X55,X56,X57,X58,X59)))&(esk2_6(X55,X56,X57,X58,X59,X60)!=X58|~r2_hidden(esk2_6(X55,X56,X57,X58,X59,X60),X60)|X60=k3_enumset1(X55,X56,X57,X58,X59)))&(esk2_6(X55,X56,X57,X58,X59,X60)!=X59|~r2_hidden(esk2_6(X55,X56,X57,X58,X59,X60),X60)|X60=k3_enumset1(X55,X56,X57,X58,X59)))&(r2_hidden(esk2_6(X55,X56,X57,X58,X59,X60),X60)|(esk2_6(X55,X56,X57,X58,X59,X60)=X55|esk2_6(X55,X56,X57,X58,X59,X60)=X56|esk2_6(X55,X56,X57,X58,X59,X60)=X57|esk2_6(X55,X56,X57,X58,X59,X60)=X58|esk2_6(X55,X56,X57,X58,X59,X60)=X59)|X60=k3_enumset1(X55,X56,X57,X58,X59)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_enumset1])])])])])])).
% 1.09/1.30  fof(c_0_103, plain, ![X72, X73]:((~v4_relat_1(X73,X72)|r1_tarski(k1_relat_1(X73),X72)|~v1_relat_1(X73))&(~r1_tarski(k1_relat_1(X73),X72)|v4_relat_1(X73,X72)|~v1_relat_1(X73))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 1.09/1.30  cnf(c_0_104, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_92])).
% 1.09/1.30  fof(c_0_105, plain, ![X63, X64]:(~r2_hidden(X63,X64)|m1_subset_1(k1_tarski(X63),k1_zfmisc_1(X64))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).
% 1.09/1.30  cnf(c_0_106, negated_conjecture, (~r1_tarski(k7_relset_1(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),esk7_0,esk9_0,esk8_0),k6_enumset1(k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_60]), c_0_60]), c_0_61]), c_0_61]), c_0_62]), c_0_62]), c_0_63]), c_0_63]), c_0_64]), c_0_64]), c_0_65]), c_0_65]), c_0_66]), c_0_66])).
% 1.09/1.30  cnf(c_0_107, plain, (k2_relat_1(X1)=k1_tarski(k1_funct_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|k1_relat_1(X1)!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_94])).
% 1.09/1.30  cnf(c_0_108, plain, (m1_subset_1(k9_relat_1(X1,X2),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 1.09/1.30  cnf(c_0_109, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk9_0),k2_relat_1(esk9_0))))), inference(spm,[status(thm)],[c_0_97, c_0_78])).
% 1.09/1.30  cnf(c_0_110, plain, (r1_tarski(k1_relat_1(X1),X2)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_98, c_0_70])).
% 1.09/1.30  cnf(c_0_111, negated_conjecture, (~r2_hidden(X1,k9_relat_1(esk9_0,X2))|~r1_tarski(esk9_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_80]), c_0_101])])).
% 1.09/1.30  cnf(c_0_112, plain, (X1=X3|X1=X4|X1=X5|X1=X6|X1=X7|~r2_hidden(X1,X2)|X2!=k3_enumset1(X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_102])).
% 1.09/1.30  cnf(c_0_113, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 1.09/1.30  cnf(c_0_114, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_103])).
% 1.09/1.30  cnf(c_0_115, negated_conjecture, (v4_relat_1(esk9_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))), inference(spm,[status(thm)],[c_0_104, c_0_72])).
% 1.09/1.30  cnf(c_0_116, plain, (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_105])).
% 1.09/1.30  cnf(c_0_117, negated_conjecture, (~r1_tarski(k9_relat_1(esk9_0,esk8_0),k6_enumset1(k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_96]), c_0_72])])).
% 1.09/1.30  cnf(c_0_118, plain, (k2_relat_1(X1)=k6_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2))|k1_relat_1(X1)!=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_107, c_0_60]), c_0_60]), c_0_61]), c_0_61]), c_0_62]), c_0_62]), c_0_63]), c_0_63]), c_0_64]), c_0_64]), c_0_65]), c_0_65]), c_0_66]), c_0_66])).
% 1.09/1.30  cnf(c_0_119, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 1.09/1.30  cnf(c_0_120, negated_conjecture, (m1_subset_1(k9_relat_1(esk9_0,X1),k1_zfmisc_1(k2_relat_1(esk9_0)))), inference(spm,[status(thm)],[c_0_108, c_0_109])).
% 1.09/1.30  cnf(c_0_121, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk7_0)))|~m1_subset_1(esk9_0,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_110]), c_0_80])])).
% 1.09/1.30  cnf(c_0_122, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_40])).
% 1.09/1.30  cnf(c_0_123, negated_conjecture, (r1_tarski(k9_relat_1(esk9_0,X1),X2)|~r1_tarski(esk9_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_111, c_0_70])).
% 1.09/1.30  cnf(c_0_124, plain, (X1=X7|X1=X6|X1=X5|X1=X4|X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X4,X5,X6,X7)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_112, c_0_64]), c_0_65]), c_0_66])).
% 1.09/1.30  cnf(c_0_125, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_113, c_0_70])).
% 1.09/1.30  cnf(c_0_126, negated_conjecture, (r1_tarski(k1_relat_1(esk9_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_115]), c_0_101])])).
% 1.09/1.30  cnf(c_0_127, plain, (m1_subset_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_116, c_0_60]), c_0_61]), c_0_62]), c_0_63]), c_0_64]), c_0_65]), c_0_66])).
% 1.09/1.30  cnf(c_0_128, negated_conjecture, (k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)!=k1_relat_1(esk9_0)|~r1_tarski(k9_relat_1(esk9_0,esk8_0),k2_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_118]), c_0_80]), c_0_101])])).
% 1.09/1.30  cnf(c_0_129, negated_conjecture, (r1_tarski(k9_relat_1(esk9_0,X1),k2_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_119, c_0_120])).
% 1.09/1.30  cnf(c_0_130, negated_conjecture, (r1_tarski(esk9_0,k2_zfmisc_1(X1,esk7_0))|~m1_subset_1(esk9_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_119, c_0_121])).
% 1.09/1.30  cnf(c_0_131, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_122])).
% 1.09/1.30  cnf(c_0_132, negated_conjecture, (~r1_tarski(esk9_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_117, c_0_123])).
% 1.09/1.30  cnf(c_0_133, plain, (X1=X2|X1=X3|X1=X4|X1=X5|X1=X6|~r2_hidden(X1,k6_enumset1(X6,X6,X6,X6,X5,X4,X3,X2))), inference(er,[status(thm)],[c_0_124])).
% 1.09/1.30  cnf(c_0_134, negated_conjecture, (r2_hidden(esk1_2(k1_relat_1(esk9_0),X1),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))|r1_tarski(k1_relat_1(esk9_0),X1)), inference(spm,[status(thm)],[c_0_125, c_0_126])).
% 1.09/1.30  cnf(c_0_135, negated_conjecture, (k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)=k1_relat_1(esk9_0)|~r1_tarski(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k1_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_67, c_0_126])).
% 1.09/1.30  cnf(c_0_136, plain, (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_119, c_0_127])).
% 1.09/1.30  cnf(c_0_137, negated_conjecture, (k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)!=k1_relat_1(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_128, c_0_129])])).
% 1.09/1.30  cnf(c_0_138, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk9_0))))|~r1_tarski(k1_relat_1(esk9_0),X1)), inference(spm,[status(thm)],[c_0_71, c_0_109])).
% 1.09/1.30  cnf(c_0_139, negated_conjecture, (~m1_subset_1(esk9_0,k1_zfmisc_1(k1_xboole_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_131]), c_0_132])).
% 1.09/1.30  cnf(c_0_140, negated_conjecture, (esk1_2(k1_relat_1(esk9_0),X1)=esk6_0|r1_tarski(k1_relat_1(esk9_0),X1)), inference(spm,[status(thm)],[c_0_133, c_0_134])).
% 1.09/1.30  cnf(c_0_141, negated_conjecture, (~r2_hidden(esk6_0,k1_relat_1(esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_136]), c_0_137])).
% 1.09/1.30  cnf(c_0_142, negated_conjecture, (~r1_tarski(k1_relat_1(esk9_0),k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_131]), c_0_139])).
% 1.09/1.30  cnf(c_0_143, negated_conjecture, (r1_tarski(k1_relat_1(esk9_0),X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_140]), c_0_141])).
% 1.09/1.30  cnf(c_0_144, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_142, c_0_143])]), ['proof']).
% 1.09/1.30  # SZS output end CNFRefutation
% 1.09/1.30  # Proof object total steps             : 145
% 1.09/1.30  # Proof object clause steps            : 86
% 1.09/1.30  # Proof object formula steps           : 59
% 1.09/1.30  # Proof object conjectures             : 36
% 1.09/1.30  # Proof object clause conjectures      : 33
% 1.09/1.30  # Proof object formula conjectures     : 3
% 1.09/1.30  # Proof object initial clauses used    : 35
% 1.09/1.30  # Proof object initial formulas used   : 29
% 1.09/1.30  # Proof object generating inferences   : 39
% 1.09/1.30  # Proof object simplifying inferences  : 77
% 1.09/1.30  # Training examples: 0 positive, 0 negative
% 1.09/1.30  # Parsed axioms                        : 32
% 1.09/1.30  # Removed by relevancy pruning/SinE    : 0
% 1.09/1.30  # Initial clauses                      : 64
% 1.09/1.30  # Removed in clause preprocessing      : 7
% 1.09/1.30  # Initial clauses in saturation        : 57
% 1.09/1.30  # Processed clauses                    : 3550
% 1.09/1.30  # ...of these trivial                  : 5
% 1.09/1.30  # ...subsumed                          : 2665
% 1.09/1.30  # ...remaining for further processing  : 880
% 1.09/1.30  # Other redundant clauses eliminated   : 398
% 1.09/1.30  # Clauses deleted for lack of memory   : 0
% 1.09/1.30  # Backward-subsumed                    : 47
% 1.09/1.30  # Backward-rewritten                   : 26
% 1.09/1.30  # Generated clauses                    : 26333
% 1.09/1.30  # ...of the previous two non-trivial   : 23866
% 1.09/1.30  # Contextual simplify-reflections      : 34
% 1.09/1.30  # Paramodulations                      : 25747
% 1.09/1.30  # Factorizations                       : 194
% 1.09/1.30  # Equation resolutions                 : 398
% 1.09/1.30  # Propositional unsat checks           : 0
% 1.09/1.30  #    Propositional check models        : 0
% 1.09/1.30  #    Propositional check unsatisfiable : 0
% 1.09/1.30  #    Propositional clauses             : 0
% 1.09/1.30  #    Propositional clauses after purity: 0
% 1.09/1.30  #    Propositional unsat core size     : 0
% 1.09/1.30  #    Propositional preprocessing time  : 0.000
% 1.09/1.30  #    Propositional encoding time       : 0.000
% 1.09/1.30  #    Propositional solver time         : 0.000
% 1.09/1.30  #    Success case prop preproc time    : 0.000
% 1.09/1.30  #    Success case prop encoding time   : 0.000
% 1.09/1.30  #    Success case prop solver time     : 0.000
% 1.09/1.30  # Current number of processed clauses  : 737
% 1.09/1.30  #    Positive orientable unit clauses  : 44
% 1.09/1.30  #    Positive unorientable unit clauses: 0
% 1.09/1.30  #    Negative unit clauses             : 22
% 1.09/1.30  #    Non-unit-clauses                  : 671
% 1.09/1.30  # Current number of unprocessed clauses: 20229
% 1.09/1.30  # ...number of literals in the above   : 232192
% 1.09/1.30  # Current number of archived formulas  : 0
% 1.09/1.30  # Current number of archived clauses   : 136
% 1.09/1.30  # Clause-clause subsumption calls (NU) : 62892
% 1.09/1.30  # Rec. Clause-clause subsumption calls : 16743
% 1.09/1.30  # Non-unit clause-clause subsumptions  : 1280
% 1.09/1.30  # Unit Clause-clause subsumption calls : 1023
% 1.09/1.30  # Rewrite failures with RHS unbound    : 0
% 1.09/1.30  # BW rewrite match attempts            : 45
% 1.09/1.30  # BW rewrite match successes           : 14
% 1.09/1.30  # Condensation attempts                : 0
% 1.09/1.30  # Condensation successes               : 0
% 1.09/1.30  # Termbank termtop insertions          : 843715
% 1.09/1.30  
% 1.09/1.30  # -------------------------------------------------
% 1.09/1.30  # User time                : 0.937 s
% 1.09/1.30  # System time              : 0.026 s
% 1.09/1.30  # Total time               : 0.963 s
% 1.09/1.30  # Maximum resident set size: 1620 pages
%------------------------------------------------------------------------------
