%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:04:47 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 767 expanded)
%              Number of clauses        :   71 ( 307 expanded)
%              Number of leaves         :   29 ( 221 expanded)
%              Depth                    :   12
%              Number of atoms          :  366 (1483 expanded)
%              Number of equality atoms :  113 ( 679 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    5 (   1 average)

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

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

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

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(cc3_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_funct_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(dt_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t63_subset_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(t4_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(k2_relat_1(X2),X1)
       => ( v1_funct_1(X2)
          & v1_funct_2(X2,k1_relat_1(X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(t14_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( k1_relat_1(X2) = k1_tarski(X1)
       => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(c_0_29,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,k1_tarski(X1),X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
       => ( X2 != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1))) ) ) ),
    inference(assume_negation,[status(cth)],[t64_funct_2])).

fof(c_0_30,plain,(
    ! [X56,X57] :
      ( ( k2_zfmisc_1(X56,X57) != k1_xboole_0
        | X56 = k1_xboole_0
        | X57 = k1_xboole_0 )
      & ( X56 != k1_xboole_0
        | k2_zfmisc_1(X56,X57) = k1_xboole_0 )
      & ( X57 != k1_xboole_0
        | k2_zfmisc_1(X56,X57) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_31,negated_conjecture,
    ( v1_funct_1(esk9_0)
    & v1_funct_2(esk9_0,k1_tarski(esk6_0),esk7_0)
    & m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk6_0),esk7_0)))
    & esk7_0 != k1_xboole_0
    & ~ r1_tarski(k7_relset_1(k1_tarski(esk6_0),esk7_0,esk9_0,esk8_0),k1_tarski(k1_funct_1(esk9_0,esk6_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).

fof(c_0_32,plain,(
    ! [X28] : k2_tarski(X28,X28) = k1_tarski(X28) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_33,plain,(
    ! [X29,X30] : k1_enumset1(X29,X29,X30) = k2_tarski(X29,X30) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_34,plain,(
    ! [X31,X32,X33] : k2_enumset1(X31,X31,X32,X33) = k1_enumset1(X31,X32,X33) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_35,plain,(
    ! [X34,X35,X36,X37] : k3_enumset1(X34,X34,X35,X36,X37) = k2_enumset1(X34,X35,X36,X37) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_36,plain,(
    ! [X38,X39,X40,X41,X42] : k4_enumset1(X38,X38,X39,X40,X41,X42) = k3_enumset1(X38,X39,X40,X41,X42) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_37,plain,(
    ! [X43,X44,X45,X46,X47,X48] : k5_enumset1(X43,X43,X44,X45,X46,X47,X48) = k4_enumset1(X43,X44,X45,X46,X47,X48) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_38,plain,(
    ! [X49,X50,X51,X52,X53,X54,X55] : k6_enumset1(X49,X49,X50,X51,X52,X53,X54,X55) = k5_enumset1(X49,X50,X51,X52,X53,X54,X55) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_39,plain,(
    ! [X91,X92,X93] :
      ( ( v4_relat_1(X93,X91)
        | ~ m1_subset_1(X93,k1_zfmisc_1(k2_zfmisc_1(X91,X92))) )
      & ( v5_relat_1(X93,X92)
        | ~ m1_subset_1(X93,k1_zfmisc_1(k2_zfmisc_1(X91,X92))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_40,plain,(
    ! [X58] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X58)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_41,plain,(
    ! [X70,X71] : v1_relat_1(k2_zfmisc_1(X70,X71)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_42,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_43,plain,(
    ! [X72,X73] :
      ( ~ v1_relat_1(X72)
      | ~ v1_funct_1(X72)
      | ~ m1_subset_1(X73,k1_zfmisc_1(X72))
      | v1_funct_1(X73) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_funct_1])])])).

fof(c_0_44,plain,(
    ! [X88,X89,X90] :
      ( ~ m1_subset_1(X90,k1_zfmisc_1(k2_zfmisc_1(X88,X89)))
      | v1_relat_1(X90) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk6_0),esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_46,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_47,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_48,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_49,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_50,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_51,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_52,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

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

fof(c_0_55,plain,(
    ! [X68,X69] :
      ( ( ~ v5_relat_1(X69,X68)
        | r1_tarski(k2_relat_1(X69),X68)
        | ~ v1_relat_1(X69) )
      & ( ~ r1_tarski(k2_relat_1(X69),X68)
        | v5_relat_1(X69,X68)
        | ~ v1_relat_1(X69) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_56,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_57,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_58,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_59,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_42])).

fof(c_0_60,plain,(
    ! [X66,X67] :
      ( ( ~ v4_relat_1(X67,X66)
        | r1_tarski(k1_relat_1(X67),X66)
        | ~ v1_relat_1(X67) )
      & ( ~ r1_tarski(k1_relat_1(X67),X66)
        | v4_relat_1(X67,X66)
        | ~ v1_relat_1(X67) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_61,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_62,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(esk6_0),esk7_0,esk9_0,esk8_0),k1_tarski(k1_funct_1(esk9_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_63,plain,(
    ! [X98,X99,X100,X101] :
      ( ~ m1_subset_1(X100,k1_zfmisc_1(k2_zfmisc_1(X98,X99)))
      | k7_relset_1(X98,X99,X100,X101) = k9_relat_1(X100,X101) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

cnf(c_0_64,plain,
    ( v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_65,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),esk7_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50]),c_0_51]),c_0_52])).

cnf(c_0_67,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_68,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_69,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_70,plain,
    ( v5_relat_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_71,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_72,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_73,plain,
    ( v4_relat_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_57])).

fof(c_0_74,plain,(
    ! [X86,X87] :
      ( ~ r2_hidden(X86,X87)
      | ~ r1_tarski(X87,X86) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_75,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),esk7_0,esk9_0,esk8_0),k6_enumset1(k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_50]),c_0_50]),c_0_51]),c_0_51]),c_0_52]),c_0_52])).

cnf(c_0_76,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

fof(c_0_77,plain,(
    ! [X61,X62] :
      ( ( ~ m1_subset_1(X61,k1_zfmisc_1(X62))
        | r1_tarski(X61,X62) )
      & ( ~ r1_tarski(X61,X62)
        | m1_subset_1(X61,k1_zfmisc_1(X62)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_78,plain,(
    ! [X94,X95,X96,X97] :
      ( ~ m1_subset_1(X96,k1_zfmisc_1(k2_zfmisc_1(X94,X95)))
      | m1_subset_1(k7_relset_1(X94,X95,X96,X97),k1_zfmisc_1(X95)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).

fof(c_0_79,plain,(
    ! [X74,X75,X76,X78,X79,X80,X82] :
      ( ( r2_hidden(esk3_3(X74,X75,X76),k1_relat_1(X74))
        | ~ r2_hidden(X76,X75)
        | X75 != k2_relat_1(X74)
        | ~ v1_relat_1(X74)
        | ~ v1_funct_1(X74) )
      & ( X76 = k1_funct_1(X74,esk3_3(X74,X75,X76))
        | ~ r2_hidden(X76,X75)
        | X75 != k2_relat_1(X74)
        | ~ v1_relat_1(X74)
        | ~ v1_funct_1(X74) )
      & ( ~ r2_hidden(X79,k1_relat_1(X74))
        | X78 != k1_funct_1(X74,X79)
        | r2_hidden(X78,X75)
        | X75 != k2_relat_1(X74)
        | ~ v1_relat_1(X74)
        | ~ v1_funct_1(X74) )
      & ( ~ r2_hidden(esk4_2(X74,X80),X80)
        | ~ r2_hidden(X82,k1_relat_1(X74))
        | esk4_2(X74,X80) != k1_funct_1(X74,X82)
        | X80 = k2_relat_1(X74)
        | ~ v1_relat_1(X74)
        | ~ v1_funct_1(X74) )
      & ( r2_hidden(esk5_2(X74,X80),k1_relat_1(X74))
        | r2_hidden(esk4_2(X74,X80),X80)
        | X80 = k2_relat_1(X74)
        | ~ v1_relat_1(X74)
        | ~ v1_funct_1(X74) )
      & ( esk4_2(X74,X80) = k1_funct_1(X74,esk5_2(X74,X80))
        | r2_hidden(esk4_2(X74,X80),X80)
        | X80 = k2_relat_1(X74)
        | ~ v1_relat_1(X74)
        | ~ v1_funct_1(X74) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

cnf(c_0_80,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_57])).

cnf(c_0_81,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_82,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_83,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_84,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])])).

cnf(c_0_85,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_71])])).

cnf(c_0_86,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_87,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk9_0,esk8_0),k6_enumset1(k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_66])])).

cnf(c_0_88,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_89,plain,
    ( m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

fof(c_0_90,plain,(
    ! [X17,X18,X19,X20,X21,X22,X23,X24,X25,X26] :
      ( ( ~ r2_hidden(X21,X20)
        | X21 = X17
        | X21 = X18
        | X21 = X19
        | X20 != k1_enumset1(X17,X18,X19) )
      & ( X22 != X17
        | r2_hidden(X22,X20)
        | X20 != k1_enumset1(X17,X18,X19) )
      & ( X22 != X18
        | r2_hidden(X22,X20)
        | X20 != k1_enumset1(X17,X18,X19) )
      & ( X22 != X19
        | r2_hidden(X22,X20)
        | X20 != k1_enumset1(X17,X18,X19) )
      & ( esk2_4(X23,X24,X25,X26) != X23
        | ~ r2_hidden(esk2_4(X23,X24,X25,X26),X26)
        | X26 = k1_enumset1(X23,X24,X25) )
      & ( esk2_4(X23,X24,X25,X26) != X24
        | ~ r2_hidden(esk2_4(X23,X24,X25,X26),X26)
        | X26 = k1_enumset1(X23,X24,X25) )
      & ( esk2_4(X23,X24,X25,X26) != X25
        | ~ r2_hidden(esk2_4(X23,X24,X25,X26),X26)
        | X26 = k1_enumset1(X23,X24,X25) )
      & ( r2_hidden(esk2_4(X23,X24,X25,X26),X26)
        | esk2_4(X23,X24,X25,X26) = X23
        | esk2_4(X23,X24,X25,X26) = X24
        | esk2_4(X23,X24,X25,X26) = X25
        | X26 = k1_enumset1(X23,X24,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_91,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_92,plain,
    ( r2_hidden(esk5_2(X1,X2),k1_relat_1(X1))
    | r2_hidden(esk4_2(X1,X2),X2)
    | X2 = k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_93,negated_conjecture,
    ( v1_funct_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82])])).

cnf(c_0_94,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_95,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_83,c_0_85])).

cnf(c_0_96,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_86,c_0_68])).

fof(c_0_97,plain,(
    ! [X59,X60] :
      ( ~ r2_hidden(X59,X60)
      | m1_subset_1(k1_tarski(X59),k1_zfmisc_1(X60)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).

cnf(c_0_98,negated_conjecture,
    ( ~ m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k7_relset_1(X1,X2,esk9_0,esk8_0),k6_enumset1(k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_87,c_0_76])).

cnf(c_0_99,plain,
    ( r1_tarski(k7_relset_1(X1,X2,X3,X4),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

fof(c_0_100,plain,(
    ! [X103,X104] :
      ( ( v1_funct_1(X104)
        | ~ r1_tarski(k2_relat_1(X104),X103)
        | ~ v1_relat_1(X104)
        | ~ v1_funct_1(X104) )
      & ( v1_funct_2(X104,k1_relat_1(X104),X103)
        | ~ r1_tarski(k2_relat_1(X104),X103)
        | ~ v1_relat_1(X104)
        | ~ v1_funct_1(X104) )
      & ( m1_subset_1(X104,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X104),X103)))
        | ~ r1_tarski(k2_relat_1(X104),X103)
        | ~ v1_relat_1(X104)
        | ~ v1_funct_1(X104) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).

fof(c_0_101,plain,(
    ! [X84,X85] :
      ( ~ v1_relat_1(X85)
      | ~ v1_funct_1(X85)
      | k1_relat_1(X85) != k1_tarski(X84)
      | k2_relat_1(X85) = k1_tarski(k1_funct_1(X85,X84)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_funct_1])])).

cnf(c_0_102,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_103,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_104,negated_conjecture,
    ( X1 = k1_xboole_0
    | r2_hidden(esk4_2(k1_xboole_0,X1),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_94]),c_0_95]),c_0_71])]),c_0_96])).

cnf(c_0_105,negated_conjecture,
    ( v4_relat_1(esk9_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_66])).

cnf(c_0_106,plain,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_107,negated_conjecture,
    ( ~ m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,k6_enumset1(k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0))))) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_108,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

cnf(c_0_109,plain,
    ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_relat_1(X1) != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_110,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_111,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_48]),c_0_49]),c_0_50]),c_0_51]),c_0_52])).

cnf(c_0_112,negated_conjecture,
    ( X1 = k1_xboole_0
    | r2_hidden(esk4_2(k1_xboole_0,X1),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_113,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk9_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_105]),c_0_82])])).

cnf(c_0_114,plain,
    ( m1_subset_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106,c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50]),c_0_51]),c_0_52])).

cnf(c_0_115,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk9_0),k6_enumset1(k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_81]),c_0_82])])).

cnf(c_0_116,plain,
    ( k2_relat_1(X1) = k6_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2))
    | k1_relat_1(X1) != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109,c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_50]),c_0_50]),c_0_51]),c_0_51]),c_0_52]),c_0_52])).

cnf(c_0_117,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_110])).

cnf(c_0_118,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k6_enumset1(X4,X4,X4,X4,X4,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_111])).

cnf(c_0_119,negated_conjecture,
    ( k1_relat_1(esk9_0) = k1_xboole_0
    | r2_hidden(esk4_2(k1_xboole_0,k1_relat_1(esk9_0)),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_120,negated_conjecture,
    ( k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) = k1_relat_1(esk9_0)
    | ~ r1_tarski(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k1_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_113])).

cnf(c_0_121,plain,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_88,c_0_114])).

cnf(c_0_122,negated_conjecture,
    ( k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) != k1_relat_1(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_117]),c_0_81]),c_0_82])])).

fof(c_0_123,plain,(
    ! [X102] :
      ( ( v1_funct_1(X102)
        | ~ v1_relat_1(X102)
        | ~ v1_funct_1(X102) )
      & ( v1_funct_2(X102,k1_relat_1(X102),k2_relat_1(X102))
        | ~ v1_relat_1(X102)
        | ~ v1_funct_1(X102) )
      & ( m1_subset_1(X102,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X102),k2_relat_1(X102))))
        | ~ v1_relat_1(X102)
        | ~ v1_funct_1(X102) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

cnf(c_0_124,negated_conjecture,
    ( esk4_2(k1_xboole_0,k1_relat_1(esk9_0)) = esk6_0
    | k1_relat_1(esk9_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_118,c_0_119])).

cnf(c_0_125,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k1_relat_1(esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_121]),c_0_122])).

cnf(c_0_126,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_123])).

cnf(c_0_127,negated_conjecture,
    ( k1_relat_1(esk9_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_124]),c_0_125])).

cnf(c_0_128,negated_conjecture,
    ( ~ m1_subset_1(esk9_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_107,c_0_59])).

cnf(c_0_129,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_127]),c_0_59]),c_0_81]),c_0_82])]),c_0_128]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:12:08 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.19/0.46  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.46  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.46  #
% 0.19/0.46  # Preprocessing time       : 0.048 s
% 0.19/0.46  # Presaturation interreduction done
% 0.19/0.46  
% 0.19/0.46  # Proof found!
% 0.19/0.46  # SZS status Theorem
% 0.19/0.46  # SZS output start CNFRefutation
% 0.19/0.46  fof(t64_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,k1_tarski(X1),X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 0.19/0.46  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.46  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.46  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.46  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.46  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.46  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.19/0.46  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.19/0.46  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.19/0.46  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.46  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.19/0.46  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.19/0.46  fof(cc3_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_funct_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_funct_1)).
% 0.19/0.46  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.46  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.46  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.46  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.19/0.46  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 0.19/0.46  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.19/0.46  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.19/0.46  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.46  fof(dt_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 0.19/0.46  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 0.19/0.46  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 0.19/0.46  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.46  fof(t63_subset_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 0.19/0.46  fof(t4_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(k2_relat_1(X2),X1)=>((v1_funct_1(X2)&v1_funct_2(X2,k1_relat_1(X2),X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 0.19/0.46  fof(t14_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 0.19/0.46  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 0.19/0.46  fof(c_0_29, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,k1_tarski(X1),X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1)))))), inference(assume_negation,[status(cth)],[t64_funct_2])).
% 0.19/0.46  fof(c_0_30, plain, ![X56, X57]:((k2_zfmisc_1(X56,X57)!=k1_xboole_0|(X56=k1_xboole_0|X57=k1_xboole_0))&((X56!=k1_xboole_0|k2_zfmisc_1(X56,X57)=k1_xboole_0)&(X57!=k1_xboole_0|k2_zfmisc_1(X56,X57)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.19/0.46  fof(c_0_31, negated_conjecture, (((v1_funct_1(esk9_0)&v1_funct_2(esk9_0,k1_tarski(esk6_0),esk7_0))&m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk6_0),esk7_0))))&(esk7_0!=k1_xboole_0&~r1_tarski(k7_relset_1(k1_tarski(esk6_0),esk7_0,esk9_0,esk8_0),k1_tarski(k1_funct_1(esk9_0,esk6_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).
% 0.19/0.46  fof(c_0_32, plain, ![X28]:k2_tarski(X28,X28)=k1_tarski(X28), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.46  fof(c_0_33, plain, ![X29, X30]:k1_enumset1(X29,X29,X30)=k2_tarski(X29,X30), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.46  fof(c_0_34, plain, ![X31, X32, X33]:k2_enumset1(X31,X31,X32,X33)=k1_enumset1(X31,X32,X33), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.46  fof(c_0_35, plain, ![X34, X35, X36, X37]:k3_enumset1(X34,X34,X35,X36,X37)=k2_enumset1(X34,X35,X36,X37), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.46  fof(c_0_36, plain, ![X38, X39, X40, X41, X42]:k4_enumset1(X38,X38,X39,X40,X41,X42)=k3_enumset1(X38,X39,X40,X41,X42), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.19/0.46  fof(c_0_37, plain, ![X43, X44, X45, X46, X47, X48]:k5_enumset1(X43,X43,X44,X45,X46,X47,X48)=k4_enumset1(X43,X44,X45,X46,X47,X48), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.19/0.46  fof(c_0_38, plain, ![X49, X50, X51, X52, X53, X54, X55]:k6_enumset1(X49,X49,X50,X51,X52,X53,X54,X55)=k5_enumset1(X49,X50,X51,X52,X53,X54,X55), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.19/0.46  fof(c_0_39, plain, ![X91, X92, X93]:((v4_relat_1(X93,X91)|~m1_subset_1(X93,k1_zfmisc_1(k2_zfmisc_1(X91,X92))))&(v5_relat_1(X93,X92)|~m1_subset_1(X93,k1_zfmisc_1(k2_zfmisc_1(X91,X92))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.46  fof(c_0_40, plain, ![X58]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X58)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.19/0.46  fof(c_0_41, plain, ![X70, X71]:v1_relat_1(k2_zfmisc_1(X70,X71)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.19/0.46  cnf(c_0_42, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.46  fof(c_0_43, plain, ![X72, X73]:(~v1_relat_1(X72)|~v1_funct_1(X72)|(~m1_subset_1(X73,k1_zfmisc_1(X72))|v1_funct_1(X73))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_funct_1])])])).
% 0.19/0.46  fof(c_0_44, plain, ![X88, X89, X90]:(~m1_subset_1(X90,k1_zfmisc_1(k2_zfmisc_1(X88,X89)))|v1_relat_1(X90)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.46  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk6_0),esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.46  cnf(c_0_46, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.46  cnf(c_0_47, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.46  cnf(c_0_48, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.46  cnf(c_0_49, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.46  cnf(c_0_50, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.46  cnf(c_0_51, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.46  cnf(c_0_52, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.46  fof(c_0_53, plain, ![X14, X15]:(((r1_tarski(X14,X15)|X14!=X15)&(r1_tarski(X15,X14)|X14!=X15))&(~r1_tarski(X14,X15)|~r1_tarski(X15,X14)|X14=X15)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.46  fof(c_0_54, plain, ![X16]:r1_tarski(k1_xboole_0,X16), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.46  fof(c_0_55, plain, ![X68, X69]:((~v5_relat_1(X69,X68)|r1_tarski(k2_relat_1(X69),X68)|~v1_relat_1(X69))&(~r1_tarski(k2_relat_1(X69),X68)|v5_relat_1(X69,X68)|~v1_relat_1(X69))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.19/0.46  cnf(c_0_56, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.46  cnf(c_0_57, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.46  cnf(c_0_58, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.46  cnf(c_0_59, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_42])).
% 0.19/0.46  fof(c_0_60, plain, ![X66, X67]:((~v4_relat_1(X67,X66)|r1_tarski(k1_relat_1(X67),X66)|~v1_relat_1(X67))&(~r1_tarski(k1_relat_1(X67),X66)|v4_relat_1(X67,X66)|~v1_relat_1(X67))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.19/0.46  cnf(c_0_61, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.46  cnf(c_0_62, negated_conjecture, (~r1_tarski(k7_relset_1(k1_tarski(esk6_0),esk7_0,esk9_0,esk8_0),k1_tarski(k1_funct_1(esk9_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.46  fof(c_0_63, plain, ![X98, X99, X100, X101]:(~m1_subset_1(X100,k1_zfmisc_1(k2_zfmisc_1(X98,X99)))|k7_relset_1(X98,X99,X100,X101)=k9_relat_1(X100,X101)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.19/0.46  cnf(c_0_64, plain, (v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.46  cnf(c_0_65, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.46  cnf(c_0_66, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),esk7_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46]), c_0_47]), c_0_48]), c_0_49]), c_0_50]), c_0_51]), c_0_52])).
% 0.19/0.46  cnf(c_0_67, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.46  cnf(c_0_68, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.46  cnf(c_0_69, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.19/0.46  cnf(c_0_70, plain, (v5_relat_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.46  cnf(c_0_71, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.46  cnf(c_0_72, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.46  cnf(c_0_73, plain, (v4_relat_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_61, c_0_57])).
% 0.19/0.46  fof(c_0_74, plain, ![X86, X87]:(~r2_hidden(X86,X87)|~r1_tarski(X87,X86)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.19/0.46  cnf(c_0_75, negated_conjecture, (~r1_tarski(k7_relset_1(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),esk7_0,esk9_0,esk8_0),k6_enumset1(k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_46]), c_0_46]), c_0_47]), c_0_47]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_50]), c_0_50]), c_0_51]), c_0_51]), c_0_52]), c_0_52])).
% 0.19/0.46  cnf(c_0_76, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.19/0.46  fof(c_0_77, plain, ![X61, X62]:((~m1_subset_1(X61,k1_zfmisc_1(X62))|r1_tarski(X61,X62))&(~r1_tarski(X61,X62)|m1_subset_1(X61,k1_zfmisc_1(X62)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.46  fof(c_0_78, plain, ![X94, X95, X96, X97]:(~m1_subset_1(X96,k1_zfmisc_1(k2_zfmisc_1(X94,X95)))|m1_subset_1(k7_relset_1(X94,X95,X96,X97),k1_zfmisc_1(X95))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).
% 0.19/0.46  fof(c_0_79, plain, ![X74, X75, X76, X78, X79, X80, X82]:((((r2_hidden(esk3_3(X74,X75,X76),k1_relat_1(X74))|~r2_hidden(X76,X75)|X75!=k2_relat_1(X74)|(~v1_relat_1(X74)|~v1_funct_1(X74)))&(X76=k1_funct_1(X74,esk3_3(X74,X75,X76))|~r2_hidden(X76,X75)|X75!=k2_relat_1(X74)|(~v1_relat_1(X74)|~v1_funct_1(X74))))&(~r2_hidden(X79,k1_relat_1(X74))|X78!=k1_funct_1(X74,X79)|r2_hidden(X78,X75)|X75!=k2_relat_1(X74)|(~v1_relat_1(X74)|~v1_funct_1(X74))))&((~r2_hidden(esk4_2(X74,X80),X80)|(~r2_hidden(X82,k1_relat_1(X74))|esk4_2(X74,X80)!=k1_funct_1(X74,X82))|X80=k2_relat_1(X74)|(~v1_relat_1(X74)|~v1_funct_1(X74)))&((r2_hidden(esk5_2(X74,X80),k1_relat_1(X74))|r2_hidden(esk4_2(X74,X80),X80)|X80=k2_relat_1(X74)|(~v1_relat_1(X74)|~v1_funct_1(X74)))&(esk4_2(X74,X80)=k1_funct_1(X74,esk5_2(X74,X80))|r2_hidden(esk4_2(X74,X80),X80)|X80=k2_relat_1(X74)|(~v1_relat_1(X74)|~v1_funct_1(X74)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.19/0.46  cnf(c_0_80, plain, (v1_funct_1(k1_xboole_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_64, c_0_57])).
% 0.19/0.46  cnf(c_0_81, negated_conjecture, (v1_funct_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.46  cnf(c_0_82, negated_conjecture, (v1_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.19/0.46  cnf(c_0_83, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.19/0.46  cnf(c_0_84, plain, (r1_tarski(k2_relat_1(k1_xboole_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])])).
% 0.19/0.46  cnf(c_0_85, plain, (r1_tarski(k1_relat_1(k1_xboole_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_71])])).
% 0.19/0.46  cnf(c_0_86, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.19/0.46  cnf(c_0_87, negated_conjecture, (~r1_tarski(k9_relat_1(esk9_0,esk8_0),k6_enumset1(k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_66])])).
% 0.19/0.46  cnf(c_0_88, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.19/0.46  cnf(c_0_89, plain, (m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.19/0.46  fof(c_0_90, plain, ![X17, X18, X19, X20, X21, X22, X23, X24, X25, X26]:(((~r2_hidden(X21,X20)|(X21=X17|X21=X18|X21=X19)|X20!=k1_enumset1(X17,X18,X19))&(((X22!=X17|r2_hidden(X22,X20)|X20!=k1_enumset1(X17,X18,X19))&(X22!=X18|r2_hidden(X22,X20)|X20!=k1_enumset1(X17,X18,X19)))&(X22!=X19|r2_hidden(X22,X20)|X20!=k1_enumset1(X17,X18,X19))))&((((esk2_4(X23,X24,X25,X26)!=X23|~r2_hidden(esk2_4(X23,X24,X25,X26),X26)|X26=k1_enumset1(X23,X24,X25))&(esk2_4(X23,X24,X25,X26)!=X24|~r2_hidden(esk2_4(X23,X24,X25,X26),X26)|X26=k1_enumset1(X23,X24,X25)))&(esk2_4(X23,X24,X25,X26)!=X25|~r2_hidden(esk2_4(X23,X24,X25,X26),X26)|X26=k1_enumset1(X23,X24,X25)))&(r2_hidden(esk2_4(X23,X24,X25,X26),X26)|(esk2_4(X23,X24,X25,X26)=X23|esk2_4(X23,X24,X25,X26)=X24|esk2_4(X23,X24,X25,X26)=X25)|X26=k1_enumset1(X23,X24,X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.19/0.46  fof(c_0_91, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk1_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk1_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.46  cnf(c_0_92, plain, (r2_hidden(esk5_2(X1,X2),k1_relat_1(X1))|r2_hidden(esk4_2(X1,X2),X2)|X2=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.19/0.46  cnf(c_0_93, negated_conjecture, (v1_funct_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_82])])).
% 0.19/0.46  cnf(c_0_94, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.19/0.46  cnf(c_0_95, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_83, c_0_85])).
% 0.19/0.46  cnf(c_0_96, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_86, c_0_68])).
% 0.19/0.46  fof(c_0_97, plain, ![X59, X60]:(~r2_hidden(X59,X60)|m1_subset_1(k1_tarski(X59),k1_zfmisc_1(X60))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).
% 0.19/0.46  cnf(c_0_98, negated_conjecture, (~m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r1_tarski(k7_relset_1(X1,X2,esk9_0,esk8_0),k6_enumset1(k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0)))), inference(spm,[status(thm)],[c_0_87, c_0_76])).
% 0.19/0.46  cnf(c_0_99, plain, (r1_tarski(k7_relset_1(X1,X2,X3,X4),X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.19/0.46  fof(c_0_100, plain, ![X103, X104]:(((v1_funct_1(X104)|~r1_tarski(k2_relat_1(X104),X103)|(~v1_relat_1(X104)|~v1_funct_1(X104)))&(v1_funct_2(X104,k1_relat_1(X104),X103)|~r1_tarski(k2_relat_1(X104),X103)|(~v1_relat_1(X104)|~v1_funct_1(X104))))&(m1_subset_1(X104,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X104),X103)))|~r1_tarski(k2_relat_1(X104),X103)|(~v1_relat_1(X104)|~v1_funct_1(X104)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).
% 0.19/0.46  fof(c_0_101, plain, ![X84, X85]:(~v1_relat_1(X85)|~v1_funct_1(X85)|(k1_relat_1(X85)!=k1_tarski(X84)|k2_relat_1(X85)=k1_tarski(k1_funct_1(X85,X84)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_funct_1])])).
% 0.19/0.46  cnf(c_0_102, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.19/0.46  cnf(c_0_103, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_91])).
% 0.19/0.46  cnf(c_0_104, negated_conjecture, (X1=k1_xboole_0|r2_hidden(esk4_2(k1_xboole_0,X1),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_94]), c_0_95]), c_0_71])]), c_0_96])).
% 0.19/0.46  cnf(c_0_105, negated_conjecture, (v4_relat_1(esk9_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))), inference(spm,[status(thm)],[c_0_61, c_0_66])).
% 0.19/0.46  cnf(c_0_106, plain, (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.19/0.46  cnf(c_0_107, negated_conjecture, (~m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,k6_enumset1(k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0)))))), inference(spm,[status(thm)],[c_0_98, c_0_99])).
% 0.19/0.46  cnf(c_0_108, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_100])).
% 0.19/0.46  cnf(c_0_109, plain, (k2_relat_1(X1)=k1_tarski(k1_funct_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|k1_relat_1(X1)!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_101])).
% 0.19/0.46  cnf(c_0_110, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.46  cnf(c_0_111, plain, (X1=X5|X1=X4|X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102, c_0_48]), c_0_49]), c_0_50]), c_0_51]), c_0_52])).
% 0.19/0.46  cnf(c_0_112, negated_conjecture, (X1=k1_xboole_0|r2_hidden(esk4_2(k1_xboole_0,X1),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 0.19/0.46  cnf(c_0_113, negated_conjecture, (r1_tarski(k1_relat_1(esk9_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_105]), c_0_82])])).
% 0.19/0.46  cnf(c_0_114, plain, (m1_subset_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106, c_0_46]), c_0_47]), c_0_48]), c_0_49]), c_0_50]), c_0_51]), c_0_52])).
% 0.19/0.46  cnf(c_0_115, negated_conjecture, (~r1_tarski(k2_relat_1(esk9_0),k6_enumset1(k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0),k1_funct_1(esk9_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_81]), c_0_82])])).
% 0.19/0.46  cnf(c_0_116, plain, (k2_relat_1(X1)=k6_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2))|k1_relat_1(X1)!=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109, c_0_46]), c_0_46]), c_0_47]), c_0_47]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_50]), c_0_50]), c_0_51]), c_0_51]), c_0_52]), c_0_52])).
% 0.19/0.46  cnf(c_0_117, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_110])).
% 0.19/0.46  cnf(c_0_118, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k6_enumset1(X4,X4,X4,X4,X4,X4,X3,X2))), inference(er,[status(thm)],[c_0_111])).
% 0.19/0.46  cnf(c_0_119, negated_conjecture, (k1_relat_1(esk9_0)=k1_xboole_0|r2_hidden(esk4_2(k1_xboole_0,k1_relat_1(esk9_0)),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))), inference(spm,[status(thm)],[c_0_112, c_0_113])).
% 0.19/0.46  cnf(c_0_120, negated_conjecture, (k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)=k1_relat_1(esk9_0)|~r1_tarski(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k1_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_67, c_0_113])).
% 0.19/0.46  cnf(c_0_121, plain, (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_88, c_0_114])).
% 0.19/0.46  cnf(c_0_122, negated_conjecture, (k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)!=k1_relat_1(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116]), c_0_117]), c_0_81]), c_0_82])])).
% 0.19/0.46  fof(c_0_123, plain, ![X102]:(((v1_funct_1(X102)|(~v1_relat_1(X102)|~v1_funct_1(X102)))&(v1_funct_2(X102,k1_relat_1(X102),k2_relat_1(X102))|(~v1_relat_1(X102)|~v1_funct_1(X102))))&(m1_subset_1(X102,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X102),k2_relat_1(X102))))|(~v1_relat_1(X102)|~v1_funct_1(X102)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.19/0.46  cnf(c_0_124, negated_conjecture, (esk4_2(k1_xboole_0,k1_relat_1(esk9_0))=esk6_0|k1_relat_1(esk9_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_118, c_0_119])).
% 0.19/0.46  cnf(c_0_125, negated_conjecture, (~r2_hidden(esk6_0,k1_relat_1(esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_121]), c_0_122])).
% 0.19/0.46  cnf(c_0_126, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_123])).
% 0.19/0.46  cnf(c_0_127, negated_conjecture, (k1_relat_1(esk9_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_124]), c_0_125])).
% 0.19/0.46  cnf(c_0_128, negated_conjecture, (~m1_subset_1(esk9_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_107, c_0_59])).
% 0.19/0.46  cnf(c_0_129, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_127]), c_0_59]), c_0_81]), c_0_82])]), c_0_128]), ['proof']).
% 0.19/0.46  # SZS output end CNFRefutation
% 0.19/0.46  # Proof object total steps             : 130
% 0.19/0.46  # Proof object clause steps            : 71
% 0.19/0.46  # Proof object formula steps           : 59
% 0.19/0.46  # Proof object conjectures             : 26
% 0.19/0.46  # Proof object clause conjectures      : 23
% 0.19/0.46  # Proof object formula conjectures     : 3
% 0.19/0.46  # Proof object initial clauses used    : 33
% 0.19/0.46  # Proof object initial formulas used   : 29
% 0.19/0.46  # Proof object generating inferences   : 30
% 0.19/0.46  # Proof object simplifying inferences  : 79
% 0.19/0.46  # Training examples: 0 positive, 0 negative
% 0.19/0.46  # Parsed axioms                        : 30
% 0.19/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.46  # Initial clauses                      : 60
% 0.19/0.46  # Removed in clause preprocessing      : 9
% 0.19/0.46  # Initial clauses in saturation        : 51
% 0.19/0.46  # Processed clauses                    : 547
% 0.19/0.46  # ...of these trivial                  : 2
% 0.19/0.46  # ...subsumed                          : 210
% 0.19/0.46  # ...remaining for further processing  : 335
% 0.19/0.46  # Other redundant clauses eliminated   : 38
% 0.19/0.46  # Clauses deleted for lack of memory   : 0
% 0.19/0.46  # Backward-subsumed                    : 13
% 0.19/0.46  # Backward-rewritten                   : 27
% 0.19/0.46  # Generated clauses                    : 1650
% 0.19/0.46  # ...of the previous two non-trivial   : 1384
% 0.19/0.46  # Contextual simplify-reflections      : 6
% 0.19/0.46  # Paramodulations                      : 1604
% 0.19/0.46  # Factorizations                       : 12
% 0.19/0.46  # Equation resolutions                 : 38
% 0.19/0.46  # Propositional unsat checks           : 0
% 0.19/0.46  #    Propositional check models        : 0
% 0.19/0.46  #    Propositional check unsatisfiable : 0
% 0.19/0.46  #    Propositional clauses             : 0
% 0.19/0.46  #    Propositional clauses after purity: 0
% 0.19/0.46  #    Propositional unsat core size     : 0
% 0.19/0.46  #    Propositional preprocessing time  : 0.000
% 0.19/0.46  #    Propositional encoding time       : 0.000
% 0.19/0.46  #    Propositional solver time         : 0.000
% 0.19/0.46  #    Success case prop preproc time    : 0.000
% 0.19/0.46  #    Success case prop encoding time   : 0.000
% 0.19/0.46  #    Success case prop solver time     : 0.000
% 0.19/0.46  # Current number of processed clauses  : 234
% 0.19/0.46  #    Positive orientable unit clauses  : 35
% 0.19/0.46  #    Positive unorientable unit clauses: 0
% 0.19/0.46  #    Negative unit clauses             : 17
% 0.19/0.46  #    Non-unit-clauses                  : 182
% 0.19/0.46  # Current number of unprocessed clauses: 891
% 0.19/0.46  # ...number of literals in the above   : 3941
% 0.19/0.46  # Current number of archived formulas  : 0
% 0.19/0.46  # Current number of archived clauses   : 97
% 0.19/0.46  # Clause-clause subsumption calls (NU) : 6669
% 0.19/0.46  # Rec. Clause-clause subsumption calls : 3044
% 0.19/0.46  # Non-unit clause-clause subsumptions  : 101
% 0.19/0.46  # Unit Clause-clause subsumption calls : 729
% 0.19/0.46  # Rewrite failures with RHS unbound    : 0
% 0.19/0.46  # BW rewrite match attempts            : 21
% 0.19/0.46  # BW rewrite match successes           : 6
% 0.19/0.46  # Condensation attempts                : 0
% 0.19/0.46  # Condensation successes               : 0
% 0.19/0.46  # Termbank termtop insertions          : 30005
% 0.19/0.46  
% 0.19/0.46  # -------------------------------------------------
% 0.19/0.46  # User time                : 0.118 s
% 0.19/0.46  # System time              : 0.011 s
% 0.19/0.46  # Total time               : 0.128 s
% 0.19/0.46  # Maximum resident set size: 1612 pages
%------------------------------------------------------------------------------
