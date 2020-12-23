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
% DateTime   : Thu Dec  3 11:05:59 EST 2020

% Result     : Theorem 0.38s
% Output     : CNFRefutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 856 expanded)
%              Number of clauses        :   79 ( 335 expanded)
%              Number of leaves         :   26 ( 216 expanded)
%              Depth                    :   11
%              Number of atoms          :  414 (4654 expanded)
%              Number of equality atoms :   99 ( 382 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t87_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & v3_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ! [X3] :
          ( ( v1_funct_1(X3)
            & v1_funct_2(X3,X1,X1)
            & v3_funct_2(X3,X1,X1)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,X3),k6_partfun1(X1))
           => r2_relset_1(X1,X1,X3,k2_funct_2(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).

fof(cc2_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v3_funct_2(X3,X1,X2) )
       => ( v1_funct_1(X3)
          & v2_funct_1(X3)
          & v2_funct_2(X3,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t36_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X2,X1)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
         => ( ( k2_relset_1(X1,X2,X3) = X2
              & r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))
              & v2_funct_1(X3) )
           => ( X1 = k1_xboole_0
              | X2 = k1_xboole_0
              | X4 = k2_funct_1(X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(t29_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X2,X1)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))
           => ( v2_funct_1(X3)
              & v2_funct_2(X4,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

fof(d3_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1) )
     => ( v2_funct_2(X2,X1)
      <=> k2_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t91_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => k1_relat_1(k7_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(t81_relat_1,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(redefinition_k2_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & v3_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => k2_funct_2(X1,X2) = k2_funct_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(t78_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(cc3_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t64_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(X1)
              & k2_relat_1(X2) = k1_relat_1(X1)
              & k5_relat_1(X2,X1) = k6_relat_1(k2_relat_1(X1)) )
           => X2 = k2_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

fof(fc4_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v2_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(c_0_26,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_funct_2(X2,X1,X1)
          & v3_funct_2(X2,X1,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
       => ! [X3] :
            ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X1)
              & v3_funct_2(X3,X1,X1)
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
           => ( r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,X3),k6_partfun1(X1))
             => r2_relset_1(X1,X1,X3,k2_funct_2(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t87_funct_2])).

fof(c_0_27,plain,(
    ! [X51,X52,X53] :
      ( ( v1_funct_1(X53)
        | ~ v1_funct_1(X53)
        | ~ v3_funct_2(X53,X51,X52)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) )
      & ( v2_funct_1(X53)
        | ~ v1_funct_1(X53)
        | ~ v3_funct_2(X53,X51,X52)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) )
      & ( v2_funct_2(X53,X52)
        | ~ v1_funct_1(X53)
        | ~ v3_funct_2(X53,X51,X52)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_funct_2])])])).

fof(c_0_28,negated_conjecture,
    ( v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk2_0,esk2_0)
    & v3_funct_2(esk3_0,esk2_0,esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk2_0,esk2_0)
    & v3_funct_2(esk4_0,esk2_0,esk2_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))
    & r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,esk4_0),k6_partfun1(esk2_0))
    & ~ r2_relset_1(esk2_0,esk2_0,esk4_0,k2_funct_2(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).

fof(c_0_29,plain,(
    ! [X38,X39,X40] :
      ( ( v4_relat_1(X40,X38)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( v5_relat_1(X40,X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_30,plain,(
    ! [X35,X36,X37] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
      | v1_relat_1(X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_31,plain,(
    ! [X21,X22] :
      ( ( ~ m1_subset_1(X21,k1_zfmisc_1(X22))
        | r1_tarski(X21,X22) )
      & ( ~ r1_tarski(X21,X22)
        | m1_subset_1(X21,k1_zfmisc_1(X22)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_32,plain,(
    ! [X13] : r1_tarski(k1_xboole_0,X13) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_33,plain,(
    ! [X70,X71,X72,X73] :
      ( ~ v1_funct_1(X72)
      | ~ v1_funct_2(X72,X70,X71)
      | ~ m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X70,X71)))
      | ~ v1_funct_1(X73)
      | ~ v1_funct_2(X73,X71,X70)
      | ~ m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(X71,X70)))
      | k2_relset_1(X70,X71,X72) != X71
      | ~ r2_relset_1(X70,X70,k1_partfun1(X70,X71,X71,X70,X72,X73),k6_partfun1(X70))
      | ~ v2_funct_1(X72)
      | X70 = k1_xboole_0
      | X71 = k1_xboole_0
      | X73 = k2_funct_1(X72) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_funct_2])])])).

fof(c_0_34,plain,(
    ! [X65] : k6_partfun1(X65) = k6_relat_1(X65) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_35,plain,(
    ! [X66,X67,X68,X69] :
      ( ( v2_funct_1(X68)
        | ~ r2_relset_1(X66,X66,k1_partfun1(X66,X67,X67,X66,X68,X69),k6_partfun1(X66))
        | ~ v1_funct_1(X69)
        | ~ v1_funct_2(X69,X67,X66)
        | ~ m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(X67,X66)))
        | ~ v1_funct_1(X68)
        | ~ v1_funct_2(X68,X66,X67)
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67))) )
      & ( v2_funct_2(X69,X66)
        | ~ r2_relset_1(X66,X66,k1_partfun1(X66,X67,X67,X66,X68,X69),k6_partfun1(X66))
        | ~ v1_funct_1(X69)
        | ~ v1_funct_2(X69,X67,X66)
        | ~ m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(X67,X66)))
        | ~ v1_funct_1(X68)
        | ~ v1_funct_2(X68,X66,X67)
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_funct_2])])])])).

fof(c_0_36,plain,(
    ! [X54,X55] :
      ( ( ~ v2_funct_2(X55,X54)
        | k2_relat_1(X55) = X54
        | ~ v1_relat_1(X55)
        | ~ v5_relat_1(X55,X54) )
      & ( k2_relat_1(X55) != X54
        | v2_funct_2(X55,X54)
        | ~ v1_relat_1(X55)
        | ~ v5_relat_1(X55,X54) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).

cnf(c_0_37,plain,
    ( v2_funct_2(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ v3_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,negated_conjecture,
    ( v3_funct_2(esk3_0,esk2_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_45,plain,(
    ! [X29] :
      ( v1_relat_1(k6_relat_1(X29))
      & v1_funct_1(k6_relat_1(X29)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

cnf(c_0_46,plain,
    ( X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X3,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | k2_relset_1(X2,X3,X1) != X3
    | ~ r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,X1,X4),k6_partfun1(X2))
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_47,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_48,plain,
    ( v2_funct_1(X1)
    | ~ r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,X1,X4),k6_partfun1(X2))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X3,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_49,plain,(
    ! [X44,X45,X46] :
      ( ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))
      | k2_relset_1(X44,X45,X46) = k2_relat_1(X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_50,plain,
    ( k2_relat_1(X1) = X2
    | ~ v2_funct_2(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_51,negated_conjecture,
    ( v2_funct_2(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40])])).

cnf(c_0_52,negated_conjecture,
    ( v5_relat_1(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_38])).

cnf(c_0_53,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_38])).

fof(c_0_54,plain,(
    ! [X27,X28] :
      ( ~ v1_relat_1(X28)
      | ~ r1_tarski(X27,k1_relat_1(X28))
      | k1_relat_1(k7_relat_1(X28,X27)) = X27 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).

fof(c_0_55,plain,(
    ! [X14,X15] :
      ( ~ v1_xboole_0(X14)
      | X14 = X15
      | ~ v1_xboole_0(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

fof(c_0_56,plain,(
    ! [X25] :
      ( k1_relat_1(k6_relat_1(X25)) = X25
      & k2_relat_1(k6_relat_1(X25)) = X25 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_57,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X24)
      | ~ v4_relat_1(X24,X23)
      | X24 = k7_relat_1(X24,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_58,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_59,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_60,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_61,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t81_relat_1])).

fof(c_0_62,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_63,plain,(
    ! [X63,X64] :
      ( ~ v1_funct_1(X64)
      | ~ v1_funct_2(X64,X63,X63)
      | ~ v3_funct_2(X64,X63,X63)
      | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X63,X63)))
      | k2_funct_2(X63,X64) = k2_funct_1(X64) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_funct_2])])).

cnf(c_0_64,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X4 = k2_funct_1(X1)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_2(X4,X3,X2)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,X1,X4),k6_relat_1(X2)) ),
    inference(rw,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_65,plain,
    ( v2_funct_1(X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X4,X3,X2)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,X1,X4),k6_relat_1(X2)) ),
    inference(rw,[status(thm)],[c_0_48,c_0_47])).

cnf(c_0_66,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_67,negated_conjecture,
    ( k2_relat_1(esk3_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_53])])).

fof(c_0_68,plain,(
    ! [X47,X48,X49,X50] :
      ( ( ~ r2_relset_1(X47,X48,X49,X50)
        | X49 = X50
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X47,X48))) )
      & ( X49 != X50
        | r2_relset_1(X47,X48,X49,X50)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X47,X48))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_69,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_70,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_71,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_72,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_73,plain,
    ( v4_relat_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_74,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_75,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_76,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_77,plain,
    ( k2_funct_2(X2,X1) = k2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ v3_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_78,negated_conjecture,
    ( v1_funct_2(esk3_0,esk2_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_79,plain,
    ( X1 = k2_funct_1(X2)
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | k2_relset_1(X3,X4,X2) != X4
    | ~ v1_funct_2(X1,X4,X3)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ r2_relset_1(X3,X3,k1_partfun1(X3,X4,X4,X3,X2,X1),k6_relat_1(X3))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(csr,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_80,negated_conjecture,
    ( k2_relset_1(esk2_0,esk2_0,esk3_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_38]),c_0_67])).

cnf(c_0_81,negated_conjecture,
    ( r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,esk4_0),k6_partfun1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_82,plain,
    ( r2_relset_1(X3,X4,X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

fof(c_0_83,plain,(
    ! [X26] :
      ( ~ v1_relat_1(X26)
      | k5_relat_1(k6_relat_1(k1_relat_1(X26)),X26) = X26 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_relat_1])])).

cnf(c_0_84,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k1_relat_1(X1))
    | ~ v1_xboole_0(X3)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_85,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_71,c_0_61])).

cnf(c_0_86,plain,
    ( k7_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74])])).

cnf(c_0_87,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_88,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_89,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_90,plain,(
    ! [X41,X42,X43] :
      ( ~ v1_xboole_0(X41)
      | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
      | v1_xboole_0(X43) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).

cnf(c_0_91,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_92,negated_conjecture,
    ( ~ r2_relset_1(esk2_0,esk2_0,esk4_0,k2_funct_2(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_93,negated_conjecture,
    ( k2_funct_2(esk2_0,esk3_0) = k2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_38]),c_0_78]),c_0_39]),c_0_40])])).

cnf(c_0_94,negated_conjecture,
    ( X1 = k2_funct_1(esk3_0)
    | esk2_0 = k1_xboole_0
    | ~ v1_funct_2(X1,esk2_0,esk2_0)
    | ~ r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,X1),k6_relat_1(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_78]),c_0_40]),c_0_38])])).

cnf(c_0_95,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_96,negated_conjecture,
    ( r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,esk4_0),k6_relat_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_81,c_0_47])).

cnf(c_0_97,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_98,plain,
    ( r2_relset_1(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_82])).

fof(c_0_99,plain,(
    ! [X16,X17] :
      ( ( k2_zfmisc_1(X16,X17) != k1_xboole_0
        | X16 = k1_xboole_0
        | X17 = k1_xboole_0 )
      & ( X16 != k1_xboole_0
        | k2_zfmisc_1(X16,X17) = k1_xboole_0 )
      & ( X17 != k1_xboole_0
        | k2_zfmisc_1(X16,X17) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_100,plain,(
    ! [X31,X32] :
      ( ~ v1_relat_1(X31)
      | ~ v1_funct_1(X31)
      | ~ v1_relat_1(X32)
      | ~ v1_funct_1(X32)
      | ~ v2_funct_1(X31)
      | k2_relat_1(X32) != k1_relat_1(X31)
      | k5_relat_1(X32,X31) != k6_relat_1(k2_relat_1(X31))
      | X32 = k2_funct_1(X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_funct_1])])])).

cnf(c_0_101,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

fof(c_0_102,plain,(
    ! [X30] :
      ( v1_relat_1(k6_relat_1(X30))
      & v2_funct_1(k6_relat_1(X30)) ) ),
    inference(variable_rename,[status(thm)],[fc4_funct_1])).

cnf(c_0_103,plain,
    ( k1_xboole_0 = X1
    | ~ v1_xboole_0(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86]),c_0_85]),c_0_74]),c_0_87])])).

cnf(c_0_104,negated_conjecture,
    ( r1_tarski(esk4_0,k2_zfmisc_1(esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_105,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_106,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_91])).

cnf(c_0_107,negated_conjecture,
    ( ~ r2_relset_1(esk2_0,esk2_0,esk4_0,k2_funct_1(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_108,negated_conjecture,
    ( k2_funct_1(esk3_0) = esk4_0
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_96]),c_0_97]),c_0_89])])).

cnf(c_0_109,negated_conjecture,
    ( r2_relset_1(esk2_0,esk2_0,esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_98,c_0_89])).

cnf(c_0_110,negated_conjecture,
    ( r1_tarski(esk3_0,k2_zfmisc_1(esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_38])).

cnf(c_0_111,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_112,plain,
    ( X2 = k2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | k2_relat_1(X2) != k1_relat_1(X1)
    | k5_relat_1(X2,X1) != k6_relat_1(k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

cnf(c_0_113,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_71]),c_0_60])])).

cnf(c_0_114,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_115,plain,
    ( v2_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_116,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_117,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | ~ v1_xboole_0(k2_zfmisc_1(esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_118,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_119,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_109])])).

cnf(c_0_120,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ v1_xboole_0(k2_zfmisc_1(esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_103,c_0_110])).

cnf(c_0_121,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_111])).

cnf(c_0_122,plain,
    ( k2_funct_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_114]),c_0_114]),c_0_71]),c_0_115]),c_0_116]),c_0_60])])).

cnf(c_0_123,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_117,c_0_118])).

cnf(c_0_124,negated_conjecture,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,esk4_0,k2_funct_1(esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_107,c_0_119]),c_0_119])).

cnf(c_0_125,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_120,c_0_119]),c_0_119]),c_0_121]),c_0_87])])).

cnf(c_0_126,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_122,c_0_61])).

cnf(c_0_127,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_123,c_0_119]),c_0_87])])).

cnf(c_0_128,plain,
    ( r2_relset_1(X1,X2,k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_98,c_0_59])).

cnf(c_0_129,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_124,c_0_125]),c_0_126]),c_0_127]),c_0_128])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:18:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.38/0.59  # AutoSched0-Mode selected heuristic G_E___110_C45_F1_PI_SE_CS_SP_PS_S4S
% 0.38/0.59  # and selection function SelectNewComplexAHPNS.
% 0.38/0.59  #
% 0.38/0.59  # Preprocessing time       : 0.047 s
% 0.38/0.59  # Presaturation interreduction done
% 0.38/0.59  
% 0.38/0.59  # Proof found!
% 0.38/0.59  # SZS status Theorem
% 0.38/0.59  # SZS output start CNFRefutation
% 0.38/0.59  fof(t87_funct_2, conjecture, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:((((v1_funct_1(X3)&v1_funct_2(X3,X1,X1))&v3_funct_2(X3,X1,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,X3),k6_partfun1(X1))=>r2_relset_1(X1,X1,X3,k2_funct_2(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_funct_2)).
% 0.38/0.59  fof(cc2_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v3_funct_2(X3,X1,X2))=>((v1_funct_1(X3)&v2_funct_1(X3))&v2_funct_2(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 0.38/0.59  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.38/0.60  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.38/0.60  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.38/0.60  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.38/0.60  fof(t36_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)))&v2_funct_1(X3))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 0.38/0.60  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.38/0.60  fof(t29_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))=>(v2_funct_1(X3)&v2_funct_2(X4,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 0.38/0.60  fof(d3_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v5_relat_1(X2,X1))=>(v2_funct_2(X2,X1)<=>k2_relat_1(X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 0.38/0.60  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.38/0.60  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.38/0.60  fof(t91_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>k1_relat_1(k7_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 0.38/0.60  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 0.38/0.60  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.38/0.60  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 0.38/0.60  fof(t81_relat_1, axiom, k6_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 0.38/0.60  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.38/0.60  fof(redefinition_k2_funct_2, axiom, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>k2_funct_2(X1,X2)=k2_funct_1(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 0.38/0.60  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.38/0.60  fof(t78_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 0.38/0.60  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.38/0.60  fof(cc3_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 0.38/0.60  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.38/0.60  fof(t64_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(((v2_funct_1(X1)&k2_relat_1(X2)=k1_relat_1(X1))&k5_relat_1(X2,X1)=k6_relat_1(k2_relat_1(X1)))=>X2=k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 0.38/0.60  fof(fc4_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v2_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 0.38/0.60  fof(c_0_26, negated_conjecture, ~(![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:((((v1_funct_1(X3)&v1_funct_2(X3,X1,X1))&v3_funct_2(X3,X1,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,X3),k6_partfun1(X1))=>r2_relset_1(X1,X1,X3,k2_funct_2(X1,X2)))))), inference(assume_negation,[status(cth)],[t87_funct_2])).
% 0.38/0.60  fof(c_0_27, plain, ![X51, X52, X53]:(((v1_funct_1(X53)|(~v1_funct_1(X53)|~v3_funct_2(X53,X51,X52))|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))))&(v2_funct_1(X53)|(~v1_funct_1(X53)|~v3_funct_2(X53,X51,X52))|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))))&(v2_funct_2(X53,X52)|(~v1_funct_1(X53)|~v3_funct_2(X53,X51,X52))|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_funct_2])])])).
% 0.38/0.60  fof(c_0_28, negated_conjecture, ((((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk2_0,esk2_0))&v3_funct_2(esk3_0,esk2_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))))&((((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk2_0,esk2_0))&v3_funct_2(esk4_0,esk2_0,esk2_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))))&(r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,esk4_0),k6_partfun1(esk2_0))&~r2_relset_1(esk2_0,esk2_0,esk4_0,k2_funct_2(esk2_0,esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).
% 0.38/0.60  fof(c_0_29, plain, ![X38, X39, X40]:((v4_relat_1(X40,X38)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))))&(v5_relat_1(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.38/0.60  fof(c_0_30, plain, ![X35, X36, X37]:(~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|v1_relat_1(X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.38/0.60  fof(c_0_31, plain, ![X21, X22]:((~m1_subset_1(X21,k1_zfmisc_1(X22))|r1_tarski(X21,X22))&(~r1_tarski(X21,X22)|m1_subset_1(X21,k1_zfmisc_1(X22)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.38/0.60  fof(c_0_32, plain, ![X13]:r1_tarski(k1_xboole_0,X13), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.38/0.60  fof(c_0_33, plain, ![X70, X71, X72, X73]:(~v1_funct_1(X72)|~v1_funct_2(X72,X70,X71)|~m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X70,X71)))|(~v1_funct_1(X73)|~v1_funct_2(X73,X71,X70)|~m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(X71,X70)))|(k2_relset_1(X70,X71,X72)!=X71|~r2_relset_1(X70,X70,k1_partfun1(X70,X71,X71,X70,X72,X73),k6_partfun1(X70))|~v2_funct_1(X72)|(X70=k1_xboole_0|X71=k1_xboole_0|X73=k2_funct_1(X72))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_funct_2])])])).
% 0.38/0.60  fof(c_0_34, plain, ![X65]:k6_partfun1(X65)=k6_relat_1(X65), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.38/0.60  fof(c_0_35, plain, ![X66, X67, X68, X69]:((v2_funct_1(X68)|~r2_relset_1(X66,X66,k1_partfun1(X66,X67,X67,X66,X68,X69),k6_partfun1(X66))|(~v1_funct_1(X69)|~v1_funct_2(X69,X67,X66)|~m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(X67,X66))))|(~v1_funct_1(X68)|~v1_funct_2(X68,X66,X67)|~m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67)))))&(v2_funct_2(X69,X66)|~r2_relset_1(X66,X66,k1_partfun1(X66,X67,X67,X66,X68,X69),k6_partfun1(X66))|(~v1_funct_1(X69)|~v1_funct_2(X69,X67,X66)|~m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(X67,X66))))|(~v1_funct_1(X68)|~v1_funct_2(X68,X66,X67)|~m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_funct_2])])])])).
% 0.38/0.60  fof(c_0_36, plain, ![X54, X55]:((~v2_funct_2(X55,X54)|k2_relat_1(X55)=X54|(~v1_relat_1(X55)|~v5_relat_1(X55,X54)))&(k2_relat_1(X55)!=X54|v2_funct_2(X55,X54)|(~v1_relat_1(X55)|~v5_relat_1(X55,X54)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).
% 0.38/0.60  cnf(c_0_37, plain, (v2_funct_2(X1,X2)|~v1_funct_1(X1)|~v3_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.38/0.60  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.38/0.60  cnf(c_0_39, negated_conjecture, (v3_funct_2(esk3_0,esk2_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.38/0.60  cnf(c_0_40, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.38/0.60  cnf(c_0_41, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.38/0.60  cnf(c_0_42, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.38/0.60  cnf(c_0_43, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.38/0.60  cnf(c_0_44, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.38/0.60  fof(c_0_45, plain, ![X29]:(v1_relat_1(k6_relat_1(X29))&v1_funct_1(k6_relat_1(X29))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.38/0.60  cnf(c_0_46, plain, (X2=k1_xboole_0|X3=k1_xboole_0|X4=k2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~v1_funct_2(X4,X3,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|k2_relset_1(X2,X3,X1)!=X3|~r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,X1,X4),k6_partfun1(X2))|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.38/0.60  cnf(c_0_47, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.38/0.60  cnf(c_0_48, plain, (v2_funct_1(X1)|~r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,X1,X4),k6_partfun1(X2))|~v1_funct_1(X4)|~v1_funct_2(X4,X3,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.38/0.60  fof(c_0_49, plain, ![X44, X45, X46]:(~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))|k2_relset_1(X44,X45,X46)=k2_relat_1(X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.38/0.60  cnf(c_0_50, plain, (k2_relat_1(X1)=X2|~v2_funct_2(X1,X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.38/0.60  cnf(c_0_51, negated_conjecture, (v2_funct_2(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_40])])).
% 0.38/0.60  cnf(c_0_52, negated_conjecture, (v5_relat_1(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_41, c_0_38])).
% 0.38/0.60  cnf(c_0_53, negated_conjecture, (v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_42, c_0_38])).
% 0.38/0.60  fof(c_0_54, plain, ![X27, X28]:(~v1_relat_1(X28)|(~r1_tarski(X27,k1_relat_1(X28))|k1_relat_1(k7_relat_1(X28,X27))=X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).
% 0.38/0.60  fof(c_0_55, plain, ![X14, X15]:(~v1_xboole_0(X14)|X14=X15|~v1_xboole_0(X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 0.38/0.60  fof(c_0_56, plain, ![X25]:(k1_relat_1(k6_relat_1(X25))=X25&k2_relat_1(k6_relat_1(X25))=X25), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.38/0.60  fof(c_0_57, plain, ![X23, X24]:(~v1_relat_1(X24)|~v4_relat_1(X24,X23)|X24=k7_relat_1(X24,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.38/0.60  cnf(c_0_58, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.38/0.60  cnf(c_0_59, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.38/0.60  cnf(c_0_60, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.38/0.60  cnf(c_0_61, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t81_relat_1])).
% 0.38/0.60  fof(c_0_62, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.38/0.60  fof(c_0_63, plain, ![X63, X64]:(~v1_funct_1(X64)|~v1_funct_2(X64,X63,X63)|~v3_funct_2(X64,X63,X63)|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X63,X63)))|k2_funct_2(X63,X64)=k2_funct_1(X64)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_funct_2])])).
% 0.38/0.60  cnf(c_0_64, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X1)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_1(X4)|~v1_funct_1(X1)|~v2_funct_1(X1)|~v1_funct_2(X4,X3,X2)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,X1,X4),k6_relat_1(X2))), inference(rw,[status(thm)],[c_0_46, c_0_47])).
% 0.38/0.60  cnf(c_0_65, plain, (v2_funct_1(X1)|~v1_funct_1(X4)|~v1_funct_1(X1)|~v1_funct_2(X4,X3,X2)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,X1,X4),k6_relat_1(X2))), inference(rw,[status(thm)],[c_0_48, c_0_47])).
% 0.38/0.60  cnf(c_0_66, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.38/0.60  cnf(c_0_67, negated_conjecture, (k2_relat_1(esk3_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52]), c_0_53])])).
% 0.38/0.60  fof(c_0_68, plain, ![X47, X48, X49, X50]:((~r2_relset_1(X47,X48,X49,X50)|X49=X50|(~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))))&(X49!=X50|r2_relset_1(X47,X48,X49,X50)|(~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.38/0.60  cnf(c_0_69, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.38/0.60  cnf(c_0_70, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.38/0.60  cnf(c_0_71, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.38/0.60  cnf(c_0_72, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.38/0.60  cnf(c_0_73, plain, (v4_relat_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.38/0.60  cnf(c_0_74, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.38/0.60  cnf(c_0_75, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.38/0.60  cnf(c_0_76, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.38/0.60  cnf(c_0_77, plain, (k2_funct_2(X2,X1)=k2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X2)|~v3_funct_2(X1,X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.38/0.60  cnf(c_0_78, negated_conjecture, (v1_funct_2(esk3_0,esk2_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.38/0.60  cnf(c_0_79, plain, (X1=k2_funct_1(X2)|X3=k1_xboole_0|X4=k1_xboole_0|k2_relset_1(X3,X4,X2)!=X4|~v1_funct_2(X1,X4,X3)|~v1_funct_2(X2,X3,X4)|~r2_relset_1(X3,X3,k1_partfun1(X3,X4,X4,X3,X2,X1),k6_relat_1(X3))|~v1_funct_1(X1)|~v1_funct_1(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(csr,[status(thm)],[c_0_64, c_0_65])).
% 0.38/0.60  cnf(c_0_80, negated_conjecture, (k2_relset_1(esk2_0,esk2_0,esk3_0)=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_38]), c_0_67])).
% 0.38/0.60  cnf(c_0_81, negated_conjecture, (r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,esk4_0),k6_partfun1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.38/0.60  cnf(c_0_82, plain, (r2_relset_1(X3,X4,X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.38/0.60  fof(c_0_83, plain, ![X26]:(~v1_relat_1(X26)|k5_relat_1(k6_relat_1(k1_relat_1(X26)),X26)=X26), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_relat_1])])).
% 0.38/0.60  cnf(c_0_84, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~v1_xboole_0(k1_relat_1(X1))|~v1_xboole_0(X3)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.38/0.60  cnf(c_0_85, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_71, c_0_61])).
% 0.38/0.60  cnf(c_0_86, plain, (k7_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_74])])).
% 0.38/0.60  cnf(c_0_87, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.38/0.60  cnf(c_0_88, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.38/0.60  cnf(c_0_89, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.38/0.60  fof(c_0_90, plain, ![X41, X42, X43]:(~v1_xboole_0(X41)|(~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))|v1_xboole_0(X43))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).
% 0.38/0.60  cnf(c_0_91, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.38/0.60  cnf(c_0_92, negated_conjecture, (~r2_relset_1(esk2_0,esk2_0,esk4_0,k2_funct_2(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.38/0.60  cnf(c_0_93, negated_conjecture, (k2_funct_2(esk2_0,esk3_0)=k2_funct_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_38]), c_0_78]), c_0_39]), c_0_40])])).
% 0.38/0.60  cnf(c_0_94, negated_conjecture, (X1=k2_funct_1(esk3_0)|esk2_0=k1_xboole_0|~v1_funct_2(X1,esk2_0,esk2_0)|~r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,X1),k6_relat_1(esk2_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_78]), c_0_40]), c_0_38])])).
% 0.38/0.60  cnf(c_0_95, negated_conjecture, (v1_funct_2(esk4_0,esk2_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.38/0.60  cnf(c_0_96, negated_conjecture, (r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,esk4_0),k6_relat_1(esk2_0))), inference(rw,[status(thm)],[c_0_81, c_0_47])).
% 0.38/0.60  cnf(c_0_97, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.38/0.60  cnf(c_0_98, plain, (r2_relset_1(X1,X2,X3,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_82])).
% 0.38/0.60  fof(c_0_99, plain, ![X16, X17]:((k2_zfmisc_1(X16,X17)!=k1_xboole_0|(X16=k1_xboole_0|X17=k1_xboole_0))&((X16!=k1_xboole_0|k2_zfmisc_1(X16,X17)=k1_xboole_0)&(X17!=k1_xboole_0|k2_zfmisc_1(X16,X17)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.38/0.60  fof(c_0_100, plain, ![X31, X32]:(~v1_relat_1(X31)|~v1_funct_1(X31)|(~v1_relat_1(X32)|~v1_funct_1(X32)|(~v2_funct_1(X31)|k2_relat_1(X32)!=k1_relat_1(X31)|k5_relat_1(X32,X31)!=k6_relat_1(k2_relat_1(X31))|X32=k2_funct_1(X31)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_funct_1])])])).
% 0.38/0.60  cnf(c_0_101, plain, (k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.38/0.60  fof(c_0_102, plain, ![X30]:(v1_relat_1(k6_relat_1(X30))&v2_funct_1(k6_relat_1(X30))), inference(variable_rename,[status(thm)],[fc4_funct_1])).
% 0.38/0.60  cnf(c_0_103, plain, (k1_xboole_0=X1|~v1_xboole_0(X2)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_86]), c_0_85]), c_0_74]), c_0_87])])).
% 0.38/0.60  cnf(c_0_104, negated_conjecture, (r1_tarski(esk4_0,k2_zfmisc_1(esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.38/0.60  cnf(c_0_105, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.38/0.60  cnf(c_0_106, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_43, c_0_91])).
% 0.38/0.60  cnf(c_0_107, negated_conjecture, (~r2_relset_1(esk2_0,esk2_0,esk4_0,k2_funct_1(esk3_0))), inference(rw,[status(thm)],[c_0_92, c_0_93])).
% 0.38/0.60  cnf(c_0_108, negated_conjecture, (k2_funct_1(esk3_0)=esk4_0|esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_96]), c_0_97]), c_0_89])])).
% 0.38/0.60  cnf(c_0_109, negated_conjecture, (r2_relset_1(esk2_0,esk2_0,esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_98, c_0_89])).
% 0.38/0.60  cnf(c_0_110, negated_conjecture, (r1_tarski(esk3_0,k2_zfmisc_1(esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_88, c_0_38])).
% 0.38/0.60  cnf(c_0_111, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_99])).
% 0.38/0.60  cnf(c_0_112, plain, (X2=k2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X1)|k2_relat_1(X2)!=k1_relat_1(X1)|k5_relat_1(X2,X1)!=k6_relat_1(k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_100])).
% 0.38/0.60  cnf(c_0_113, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X1))=k6_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_71]), c_0_60])])).
% 0.38/0.60  cnf(c_0_114, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.38/0.60  cnf(c_0_115, plain, (v2_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_102])).
% 0.38/0.60  cnf(c_0_116, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.38/0.60  cnf(c_0_117, negated_conjecture, (esk4_0=k1_xboole_0|~v1_xboole_0(k2_zfmisc_1(esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 0.38/0.60  cnf(c_0_118, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_105, c_0_106])).
% 0.38/0.60  cnf(c_0_119, negated_conjecture, (esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_109])])).
% 0.38/0.60  cnf(c_0_120, negated_conjecture, (esk3_0=k1_xboole_0|~v1_xboole_0(k2_zfmisc_1(esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_103, c_0_110])).
% 0.38/0.60  cnf(c_0_121, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_111])).
% 0.38/0.60  cnf(c_0_122, plain, (k2_funct_1(k6_relat_1(X1))=k6_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_113]), c_0_114]), c_0_114]), c_0_71]), c_0_115]), c_0_116]), c_0_60])])).
% 0.38/0.60  cnf(c_0_123, negated_conjecture, (esk4_0=k1_xboole_0|~v1_xboole_0(esk2_0)), inference(spm,[status(thm)],[c_0_117, c_0_118])).
% 0.38/0.60  cnf(c_0_124, negated_conjecture, (~r2_relset_1(k1_xboole_0,k1_xboole_0,esk4_0,k2_funct_1(esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_107, c_0_119]), c_0_119])).
% 0.38/0.60  cnf(c_0_125, negated_conjecture, (esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_120, c_0_119]), c_0_119]), c_0_121]), c_0_87])])).
% 0.38/0.60  cnf(c_0_126, plain, (k2_funct_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_122, c_0_61])).
% 0.38/0.60  cnf(c_0_127, negated_conjecture, (esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_123, c_0_119]), c_0_87])])).
% 0.38/0.60  cnf(c_0_128, plain, (r2_relset_1(X1,X2,k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_98, c_0_59])).
% 0.38/0.60  cnf(c_0_129, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_124, c_0_125]), c_0_126]), c_0_127]), c_0_128])]), ['proof']).
% 0.38/0.60  # SZS output end CNFRefutation
% 0.38/0.60  # Proof object total steps             : 130
% 0.38/0.60  # Proof object clause steps            : 79
% 0.38/0.60  # Proof object formula steps           : 51
% 0.38/0.60  # Proof object conjectures             : 33
% 0.38/0.60  # Proof object clause conjectures      : 30
% 0.38/0.60  # Proof object formula conjectures     : 3
% 0.38/0.60  # Proof object initial clauses used    : 39
% 0.38/0.60  # Proof object initial formulas used   : 26
% 0.38/0.60  # Proof object generating inferences   : 29
% 0.38/0.60  # Proof object simplifying inferences  : 59
% 0.38/0.60  # Training examples: 0 positive, 0 negative
% 0.38/0.60  # Parsed axioms                        : 30
% 0.38/0.60  # Removed by relevancy pruning/SinE    : 0
% 0.38/0.60  # Initial clauses                      : 55
% 0.38/0.60  # Removed in clause preprocessing      : 2
% 0.38/0.60  # Initial clauses in saturation        : 53
% 0.38/0.60  # Processed clauses                    : 1486
% 0.38/0.60  # ...of these trivial                  : 17
% 0.38/0.60  # ...subsumed                          : 846
% 0.38/0.60  # ...remaining for further processing  : 622
% 0.38/0.60  # Other redundant clauses eliminated   : 47
% 0.38/0.60  # Clauses deleted for lack of memory   : 0
% 0.38/0.60  # Backward-subsumed                    : 25
% 0.38/0.60  # Backward-rewritten                   : 138
% 0.38/0.60  # Generated clauses                    : 17387
% 0.38/0.60  # ...of the previous two non-trivial   : 11301
% 0.38/0.60  # Contextual simplify-reflections      : 2
% 0.38/0.60  # Paramodulations                      : 17340
% 0.38/0.60  # Factorizations                       : 0
% 0.38/0.60  # Equation resolutions                 : 47
% 0.38/0.60  # Propositional unsat checks           : 0
% 0.38/0.60  #    Propositional check models        : 0
% 0.38/0.60  #    Propositional check unsatisfiable : 0
% 0.38/0.60  #    Propositional clauses             : 0
% 0.38/0.60  #    Propositional clauses after purity: 0
% 0.38/0.60  #    Propositional unsat core size     : 0
% 0.38/0.60  #    Propositional preprocessing time  : 0.000
% 0.38/0.60  #    Propositional encoding time       : 0.000
% 0.38/0.60  #    Propositional solver time         : 0.000
% 0.38/0.60  #    Success case prop preproc time    : 0.000
% 0.38/0.60  #    Success case prop encoding time   : 0.000
% 0.38/0.60  #    Success case prop solver time     : 0.000
% 0.38/0.60  # Current number of processed clauses  : 403
% 0.38/0.60  #    Positive orientable unit clauses  : 52
% 0.38/0.60  #    Positive unorientable unit clauses: 0
% 0.38/0.60  #    Negative unit clauses             : 0
% 0.38/0.60  #    Non-unit-clauses                  : 351
% 0.38/0.60  # Current number of unprocessed clauses: 9782
% 0.38/0.60  # ...number of literals in the above   : 40824
% 0.38/0.60  # Current number of archived formulas  : 0
% 0.38/0.60  # Current number of archived clauses   : 216
% 0.38/0.60  # Clause-clause subsumption calls (NU) : 49551
% 0.38/0.60  # Rec. Clause-clause subsumption calls : 30331
% 0.38/0.60  # Non-unit clause-clause subsumptions  : 873
% 0.38/0.60  # Unit Clause-clause subsumption calls : 662
% 0.38/0.60  # Rewrite failures with RHS unbound    : 0
% 0.38/0.60  # BW rewrite match attempts            : 284
% 0.38/0.60  # BW rewrite match successes           : 7
% 0.38/0.60  # Condensation attempts                : 0
% 0.38/0.60  # Condensation successes               : 0
% 0.38/0.60  # Termbank termtop insertions          : 214385
% 0.38/0.60  
% 0.38/0.60  # -------------------------------------------------
% 0.38/0.60  # User time                : 0.229 s
% 0.38/0.60  # System time              : 0.008 s
% 0.38/0.60  # Total time               : 0.237 s
% 0.38/0.60  # Maximum resident set size: 1620 pages
%------------------------------------------------------------------------------
