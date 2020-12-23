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
% DateTime   : Thu Dec  3 11:06:01 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  123 (1309 expanded)
%              Number of clauses        :   76 ( 489 expanded)
%              Number of leaves         :   23 ( 316 expanded)
%              Depth                    :   12
%              Number of atoms          :  384 (7751 expanded)
%              Number of equality atoms :   70 ( 388 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

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

fof(cc2_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v3_funct_2(X3,X1,X2) )
       => ( v1_funct_1(X3)
          & v2_funct_1(X3)
          & v2_funct_2(X3,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(d3_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1) )
     => ( v2_funct_2(X2,X1)
      <=> k2_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(t29_relset_1,axiom,(
    ! [X1] : m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(dt_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
        & m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(redefinition_k2_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & v3_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => k2_funct_2(X1,X2) = k2_funct_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(d6_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

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

fof(dt_k2_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & v3_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ( v1_funct_1(k2_funct_2(X1,X2))
        & v1_funct_2(k2_funct_2(X1,X2),X1,X1)
        & v3_funct_2(k2_funct_2(X1,X2),X1,X1)
        & m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(t19_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => r1_tarski(k3_relat_1(X3),k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relset_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t54_relset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
         => ( ! [X4] :
                ( r2_hidden(X4,X1)
               => k11_relat_1(X2,X4) = k11_relat_1(X3,X4) )
           => r2_relset_1(X1,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relset_1)).

fof(t37_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(t69_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(c_0_23,negated_conjecture,(
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

fof(c_0_24,plain,(
    ! [X26,X27,X28] :
      ( ( v4_relat_1(X28,X26)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( v5_relat_1(X28,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_25,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk3_0,esk3_0)
    & v3_funct_2(esk4_0,esk3_0,esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk3_0,esk3_0)
    & v3_funct_2(esk5_0,esk3_0,esk3_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))
    & r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0),k6_partfun1(esk3_0))
    & ~ r2_relset_1(esk3_0,esk3_0,esk5_0,k2_funct_2(esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

fof(c_0_26,plain,(
    ! [X23,X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | v1_relat_1(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_27,plain,(
    ! [X48,X49,X50] :
      ( ( v1_funct_1(X50)
        | ~ v1_funct_1(X50)
        | ~ v3_funct_2(X50,X48,X49)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) )
      & ( v2_funct_1(X50)
        | ~ v1_funct_1(X50)
        | ~ v3_funct_2(X50,X48,X49)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) )
      & ( v2_funct_2(X50,X49)
        | ~ v1_funct_1(X50)
        | ~ v3_funct_2(X50,X48,X49)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_funct_2])])])).

fof(c_0_28,plain,(
    ! [X18,X19] :
      ( ( ~ v4_relat_1(X19,X18)
        | r1_tarski(k1_relat_1(X19),X18)
        | ~ v1_relat_1(X19) )
      & ( ~ r1_tarski(k1_relat_1(X19),X18)
        | v4_relat_1(X19,X18)
        | ~ v1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_29,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_32,plain,(
    ! [X51,X52] :
      ( ( ~ v2_funct_2(X52,X51)
        | k2_relat_1(X52) = X51
        | ~ v1_relat_1(X52)
        | ~ v5_relat_1(X52,X51) )
      & ( k2_relat_1(X52) != X51
        | v2_funct_2(X52,X51)
        | ~ v1_relat_1(X52)
        | ~ v5_relat_1(X52,X51) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).

cnf(c_0_33,plain,
    ( v2_funct_2(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ v3_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( v3_funct_2(esk5_0,esk3_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_37,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | k2_xboole_0(X8,X9) = X9 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_38,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,negated_conjecture,
    ( v4_relat_1(esk5_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_30])).

fof(c_0_41,plain,(
    ! [X29,X30,X31] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | k2_relset_1(X29,X30,X31) = k2_relat_1(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_43,negated_conjecture,
    ( v3_funct_2(esk4_0,esk3_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_45,plain,(
    ! [X32,X33,X34,X35] :
      ( ( ~ r2_relset_1(X32,X33,X34,X35)
        | X34 = X35
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( X34 != X35
        | r2_relset_1(X32,X33,X34,X35)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

fof(c_0_46,plain,(
    ! [X43] : m1_subset_1(k6_relat_1(X43),k1_zfmisc_1(k2_zfmisc_1(X43,X43))) ),
    inference(variable_rename,[status(thm)],[t29_relset_1])).

fof(c_0_47,plain,(
    ! [X63] : k6_partfun1(X63) = k6_relat_1(X63) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_48,plain,(
    ! [X53,X54,X55,X56,X57,X58] :
      ( ( v1_funct_1(k1_partfun1(X53,X54,X55,X56,X57,X58))
        | ~ v1_funct_1(X57)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X53,X54)))
        | ~ v1_funct_1(X58)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X55,X56))) )
      & ( m1_subset_1(k1_partfun1(X53,X54,X55,X56,X57,X58),k1_zfmisc_1(k2_zfmisc_1(X53,X56)))
        | ~ v1_funct_1(X57)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X53,X54)))
        | ~ v1_funct_1(X58)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X55,X56))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

fof(c_0_49,plain,(
    ! [X61,X62] :
      ( ~ v1_funct_1(X62)
      | ~ v1_funct_2(X62,X61,X61)
      | ~ v3_funct_2(X62,X61,X61)
      | ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X61,X61)))
      | k2_funct_2(X61,X62) = k2_funct_1(X62) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_funct_2])])).

fof(c_0_50,plain,(
    ! [X20] :
      ( ~ v1_relat_1(X20)
      | k3_relat_1(X20) = k2_xboole_0(k1_relat_1(X20),k2_relat_1(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

cnf(c_0_51,plain,
    ( k2_relat_1(X1) = X2
    | ~ v2_funct_2(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_52,negated_conjecture,
    ( v2_funct_2(esk5_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_30]),c_0_34]),c_0_35])])).

cnf(c_0_53,negated_conjecture,
    ( v5_relat_1(esk5_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_30])).

cnf(c_0_54,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk5_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])])).

fof(c_0_56,plain,(
    ! [X69,X70,X71,X72] :
      ( ~ v1_funct_1(X71)
      | ~ v1_funct_2(X71,X69,X70)
      | ~ m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X69,X70)))
      | ~ v1_funct_1(X72)
      | ~ v1_funct_2(X72,X70,X69)
      | ~ m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X70,X69)))
      | k2_relset_1(X69,X70,X71) != X70
      | ~ r2_relset_1(X69,X69,k1_partfun1(X69,X70,X70,X69,X71,X72),k6_partfun1(X69))
      | ~ v2_funct_1(X71)
      | X69 = k1_xboole_0
      | X70 = k1_xboole_0
      | X72 = k2_funct_1(X71) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_funct_2])])])).

cnf(c_0_57,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_58,negated_conjecture,
    ( v2_funct_2(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_42]),c_0_43]),c_0_44])])).

cnf(c_0_59,negated_conjecture,
    ( v5_relat_1(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_42])).

cnf(c_0_60,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_42])).

cnf(c_0_61,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_62,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_63,negated_conjecture,
    ( r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0),k6_partfun1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_64,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_65,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_66,plain,(
    ! [X59,X60] :
      ( ( v1_funct_1(k2_funct_2(X59,X60))
        | ~ v1_funct_1(X60)
        | ~ v1_funct_2(X60,X59,X59)
        | ~ v3_funct_2(X60,X59,X59)
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X59,X59))) )
      & ( v1_funct_2(k2_funct_2(X59,X60),X59,X59)
        | ~ v1_funct_1(X60)
        | ~ v1_funct_2(X60,X59,X59)
        | ~ v3_funct_2(X60,X59,X59)
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X59,X59))) )
      & ( v3_funct_2(k2_funct_2(X59,X60),X59,X59)
        | ~ v1_funct_1(X60)
        | ~ v1_funct_2(X60,X59,X59)
        | ~ v3_funct_2(X60,X59,X59)
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X59,X59))) )
      & ( m1_subset_1(k2_funct_2(X59,X60),k1_zfmisc_1(k2_zfmisc_1(X59,X59)))
        | ~ v1_funct_1(X60)
        | ~ v1_funct_2(X60,X59,X59)
        | ~ v3_funct_2(X60,X59,X59)
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X59,X59))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_2])])])).

cnf(c_0_67,plain,
    ( k2_funct_2(X2,X1) = k2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ v3_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_68,negated_conjecture,
    ( v1_funct_2(esk4_0,esk3_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_69,plain,(
    ! [X40,X41,X42] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
      | r1_tarski(k3_relat_1(X42),k2_xboole_0(X40,X41)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_relset_1])])).

cnf(c_0_70,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_71,negated_conjecture,
    ( k2_relat_1(esk5_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_40])])).

cnf(c_0_72,negated_conjecture,
    ( k2_xboole_0(k1_relat_1(esk5_0),esk3_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

fof(c_0_73,plain,(
    ! [X7] : k2_xboole_0(X7,X7) = X7 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_74,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_75,negated_conjecture,
    ( k2_relset_1(esk3_0,esk3_0,esk4_0) = k2_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_42])).

cnf(c_0_76,negated_conjecture,
    ( k2_relat_1(esk4_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_58]),c_0_59]),c_0_60])])).

cnf(c_0_77,plain,
    ( v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v3_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_78,plain,
    ( X1 = k6_relat_1(X2)
    | ~ r2_relset_1(X2,X2,X1,k6_relat_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_79,negated_conjecture,
    ( r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0),k6_relat_1(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(k1_partfun1(X1,X2,esk3_0,esk3_0,X3,esk5_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_30]),c_0_35])])).

cnf(c_0_81,plain,
    ( r2_relset_1(X3,X4,X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_82,plain,(
    ! [X44,X45,X46] :
      ( ( r2_hidden(esk1_3(X44,X45,X46),X44)
        | r2_relset_1(X44,X44,X45,X46)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X44)))
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X44,X44))) )
      & ( k11_relat_1(X45,esk1_3(X44,X45,X46)) != k11_relat_1(X46,esk1_3(X44,X45,X46))
        | r2_relset_1(X44,X44,X45,X46)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X44)))
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X44,X44))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relset_1])])])])])).

cnf(c_0_83,plain,
    ( m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_84,negated_conjecture,
    ( k2_funct_2(esk3_0,esk4_0) = k2_funct_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_42]),c_0_68]),c_0_43]),c_0_44])])).

fof(c_0_85,plain,(
    ! [X10,X11] :
      ( ( k4_xboole_0(X10,X11) != k1_xboole_0
        | r1_tarski(X10,X11) )
      & ( ~ r1_tarski(X10,X11)
        | k4_xboole_0(X10,X11) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).

cnf(c_0_86,plain,
    ( r1_tarski(k3_relat_1(X1),k2_xboole_0(X2,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_87,negated_conjecture,
    ( k3_relat_1(esk5_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72]),c_0_40])])).

cnf(c_0_88,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_89,plain,
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
    inference(rw,[status(thm)],[c_0_74,c_0_64])).

cnf(c_0_90,negated_conjecture,
    ( k2_relset_1(esk3_0,esk3_0,esk4_0) = esk3_0 ),
    inference(rw,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_91,negated_conjecture,
    ( v2_funct_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_42]),c_0_43]),c_0_44])])).

cnf(c_0_92,negated_conjecture,
    ( k1_partfun1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0) = k6_relat_1(esk3_0)
    | ~ m1_subset_1(k1_partfun1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_93,negated_conjecture,
    ( m1_subset_1(k1_partfun1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_42]),c_0_44])])).

cnf(c_0_94,plain,
    ( r2_relset_1(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_81])).

cnf(c_0_95,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_relset_1(X1,X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_96,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_42]),c_0_84]),c_0_68]),c_0_43]),c_0_44])])).

cnf(c_0_97,negated_conjecture,
    ( ~ r2_relset_1(esk3_0,esk3_0,esk5_0,k2_funct_2(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_98,plain,(
    ! [X16,X17] :
      ( ( ~ r1_xboole_0(X16,X17)
        | k4_xboole_0(X16,X17) = X16 )
      & ( k4_xboole_0(X16,X17) != X16
        | r1_xboole_0(X16,X17) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_99,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_100,negated_conjecture,
    ( r1_tarski(esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_30]),c_0_87]),c_0_88])).

cnf(c_0_101,negated_conjecture,
    ( X1 = k2_funct_1(esk4_0)
    | esk3_0 = k1_xboole_0
    | ~ v1_funct_2(X1,esk3_0,esk3_0)
    | ~ r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,X1),k6_relat_1(esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_68]),c_0_42]),c_0_91]),c_0_44])])).

cnf(c_0_102,negated_conjecture,
    ( v1_funct_2(esk5_0,esk3_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_103,negated_conjecture,
    ( k1_partfun1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0) = k6_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_93])])).

cnf(c_0_104,plain,
    ( r2_relset_1(X1,X1,k6_relat_1(X1),k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_62])).

fof(c_0_105,plain,(
    ! [X14,X15] :
      ( ~ r2_hidden(X14,X15)
      | ~ v1_xboole_0(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_106,negated_conjecture,
    ( r2_relset_1(esk3_0,esk3_0,X1,k2_funct_1(esk4_0))
    | r2_hidden(esk1_3(esk3_0,X1,k2_funct_1(esk4_0)),esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_107,negated_conjecture,
    ( ~ r2_relset_1(esk3_0,esk3_0,esk5_0,k2_funct_1(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_97,c_0_84])).

cnf(c_0_108,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_109,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_110,negated_conjecture,
    ( k2_funct_1(esk4_0) = esk5_0
    | esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_103]),c_0_104]),c_0_30]),c_0_35])])).

cnf(c_0_111,negated_conjecture,
    ( r2_relset_1(esk3_0,esk3_0,esk5_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_30])).

cnf(c_0_112,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_105])).

cnf(c_0_113,negated_conjecture,
    ( r2_hidden(esk1_3(esk3_0,esk5_0,k2_funct_1(esk4_0)),esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_30]),c_0_107])).

fof(c_0_114,plain,(
    ! [X12,X13] :
      ( v1_xboole_0(X13)
      | ~ r1_tarski(X13,X12)
      | ~ r1_xboole_0(X13,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

cnf(c_0_115,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk3_0)
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_116,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_110]),c_0_111])])).

cnf(c_0_117,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_118,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_114])).

cnf(c_0_119,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_115,c_0_116]),c_0_116]),c_0_116])])).

cnf(c_0_120,negated_conjecture,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_116]),c_0_116])).

cnf(c_0_121,negated_conjecture,
    ( ~ v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_117,c_0_116])).

cnf(c_0_122,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_119]),c_0_120])]),c_0_121]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:49:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.21/0.35  # No SInE strategy applied
% 0.21/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.48  # AutoSched0-Mode selected heuristic G_E___215_C46_F1_AE_CS_SP_PS_S2S
% 0.21/0.48  # and selection function SelectNewComplexAHP.
% 0.21/0.48  #
% 0.21/0.48  # Preprocessing time       : 0.029 s
% 0.21/0.48  # Presaturation interreduction done
% 0.21/0.48  
% 0.21/0.48  # Proof found!
% 0.21/0.48  # SZS status Theorem
% 0.21/0.48  # SZS output start CNFRefutation
% 0.21/0.48  fof(t87_funct_2, conjecture, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:((((v1_funct_1(X3)&v1_funct_2(X3,X1,X1))&v3_funct_2(X3,X1,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,X3),k6_partfun1(X1))=>r2_relset_1(X1,X1,X3,k2_funct_2(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_funct_2)).
% 0.21/0.48  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.21/0.48  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.21/0.48  fof(cc2_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v3_funct_2(X3,X1,X2))=>((v1_funct_1(X3)&v2_funct_1(X3))&v2_funct_2(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 0.21/0.48  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 0.21/0.48  fof(d3_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v5_relat_1(X2,X1))=>(v2_funct_2(X2,X1)<=>k2_relat_1(X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 0.21/0.48  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.21/0.48  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.21/0.48  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.21/0.48  fof(t29_relset_1, axiom, ![X1]:m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 0.21/0.48  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.21/0.48  fof(dt_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))&m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 0.21/0.48  fof(redefinition_k2_funct_2, axiom, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>k2_funct_2(X1,X2)=k2_funct_1(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 0.21/0.48  fof(d6_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 0.21/0.48  fof(t36_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)))&v2_funct_1(X3))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 0.21/0.48  fof(dt_k2_funct_2, axiom, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(((v1_funct_1(k2_funct_2(X1,X2))&v1_funct_2(k2_funct_2(X1,X2),X1,X1))&v3_funct_2(k2_funct_2(X1,X2),X1,X1))&m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 0.21/0.48  fof(t19_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>r1_tarski(k3_relat_1(X3),k2_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_relset_1)).
% 0.21/0.48  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.21/0.48  fof(t54_relset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))=>(![X4]:(r2_hidden(X4,X1)=>k11_relat_1(X2,X4)=k11_relat_1(X3,X4))=>r2_relset_1(X1,X1,X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relset_1)).
% 0.21/0.48  fof(t37_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 0.21/0.48  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.21/0.48  fof(t7_boole, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_boole)).
% 0.21/0.48  fof(t69_xboole_1, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>~((r1_tarski(X2,X1)&r1_xboole_0(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 0.21/0.48  fof(c_0_23, negated_conjecture, ~(![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:((((v1_funct_1(X3)&v1_funct_2(X3,X1,X1))&v3_funct_2(X3,X1,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,X3),k6_partfun1(X1))=>r2_relset_1(X1,X1,X3,k2_funct_2(X1,X2)))))), inference(assume_negation,[status(cth)],[t87_funct_2])).
% 0.21/0.48  fof(c_0_24, plain, ![X26, X27, X28]:((v4_relat_1(X28,X26)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))&(v5_relat_1(X28,X27)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.21/0.48  fof(c_0_25, negated_conjecture, ((((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk3_0,esk3_0))&v3_funct_2(esk4_0,esk3_0,esk3_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))))&((((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk3_0,esk3_0))&v3_funct_2(esk5_0,esk3_0,esk3_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))))&(r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0),k6_partfun1(esk3_0))&~r2_relset_1(esk3_0,esk3_0,esk5_0,k2_funct_2(esk3_0,esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 0.21/0.48  fof(c_0_26, plain, ![X23, X24, X25]:(~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))|v1_relat_1(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.21/0.48  fof(c_0_27, plain, ![X48, X49, X50]:(((v1_funct_1(X50)|(~v1_funct_1(X50)|~v3_funct_2(X50,X48,X49))|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))))&(v2_funct_1(X50)|(~v1_funct_1(X50)|~v3_funct_2(X50,X48,X49))|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))))&(v2_funct_2(X50,X49)|(~v1_funct_1(X50)|~v3_funct_2(X50,X48,X49))|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_funct_2])])])).
% 0.21/0.48  fof(c_0_28, plain, ![X18, X19]:((~v4_relat_1(X19,X18)|r1_tarski(k1_relat_1(X19),X18)|~v1_relat_1(X19))&(~r1_tarski(k1_relat_1(X19),X18)|v4_relat_1(X19,X18)|~v1_relat_1(X19))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.21/0.48  cnf(c_0_29, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.48  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.48  cnf(c_0_31, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.48  fof(c_0_32, plain, ![X51, X52]:((~v2_funct_2(X52,X51)|k2_relat_1(X52)=X51|(~v1_relat_1(X52)|~v5_relat_1(X52,X51)))&(k2_relat_1(X52)!=X51|v2_funct_2(X52,X51)|(~v1_relat_1(X52)|~v5_relat_1(X52,X51)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).
% 0.21/0.48  cnf(c_0_33, plain, (v2_funct_2(X1,X2)|~v1_funct_1(X1)|~v3_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.48  cnf(c_0_34, negated_conjecture, (v3_funct_2(esk5_0,esk3_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.48  cnf(c_0_35, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.48  cnf(c_0_36, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.48  fof(c_0_37, plain, ![X8, X9]:(~r1_tarski(X8,X9)|k2_xboole_0(X8,X9)=X9), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.21/0.48  cnf(c_0_38, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.48  cnf(c_0_39, negated_conjecture, (v4_relat_1(esk5_0,esk3_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.21/0.48  cnf(c_0_40, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_31, c_0_30])).
% 0.21/0.48  fof(c_0_41, plain, ![X29, X30, X31]:(~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|k2_relset_1(X29,X30,X31)=k2_relat_1(X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.21/0.48  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.48  cnf(c_0_43, negated_conjecture, (v3_funct_2(esk4_0,esk3_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.48  cnf(c_0_44, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.48  fof(c_0_45, plain, ![X32, X33, X34, X35]:((~r2_relset_1(X32,X33,X34,X35)|X34=X35|(~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))))&(X34!=X35|r2_relset_1(X32,X33,X34,X35)|(~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.21/0.48  fof(c_0_46, plain, ![X43]:m1_subset_1(k6_relat_1(X43),k1_zfmisc_1(k2_zfmisc_1(X43,X43))), inference(variable_rename,[status(thm)],[t29_relset_1])).
% 0.21/0.48  fof(c_0_47, plain, ![X63]:k6_partfun1(X63)=k6_relat_1(X63), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.21/0.48  fof(c_0_48, plain, ![X53, X54, X55, X56, X57, X58]:((v1_funct_1(k1_partfun1(X53,X54,X55,X56,X57,X58))|(~v1_funct_1(X57)|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X53,X54)))|~v1_funct_1(X58)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X55,X56)))))&(m1_subset_1(k1_partfun1(X53,X54,X55,X56,X57,X58),k1_zfmisc_1(k2_zfmisc_1(X53,X56)))|(~v1_funct_1(X57)|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X53,X54)))|~v1_funct_1(X58)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X55,X56)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).
% 0.21/0.48  fof(c_0_49, plain, ![X61, X62]:(~v1_funct_1(X62)|~v1_funct_2(X62,X61,X61)|~v3_funct_2(X62,X61,X61)|~m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X61,X61)))|k2_funct_2(X61,X62)=k2_funct_1(X62)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_funct_2])])).
% 0.21/0.48  fof(c_0_50, plain, ![X20]:(~v1_relat_1(X20)|k3_relat_1(X20)=k2_xboole_0(k1_relat_1(X20),k2_relat_1(X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).
% 0.21/0.48  cnf(c_0_51, plain, (k2_relat_1(X1)=X2|~v2_funct_2(X1,X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.48  cnf(c_0_52, negated_conjecture, (v2_funct_2(esk5_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_30]), c_0_34]), c_0_35])])).
% 0.21/0.48  cnf(c_0_53, negated_conjecture, (v5_relat_1(esk5_0,esk3_0)), inference(spm,[status(thm)],[c_0_36, c_0_30])).
% 0.21/0.48  cnf(c_0_54, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.21/0.48  cnf(c_0_55, negated_conjecture, (r1_tarski(k1_relat_1(esk5_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])])).
% 0.21/0.48  fof(c_0_56, plain, ![X69, X70, X71, X72]:(~v1_funct_1(X71)|~v1_funct_2(X71,X69,X70)|~m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X69,X70)))|(~v1_funct_1(X72)|~v1_funct_2(X72,X70,X69)|~m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X70,X69)))|(k2_relset_1(X69,X70,X71)!=X70|~r2_relset_1(X69,X69,k1_partfun1(X69,X70,X70,X69,X71,X72),k6_partfun1(X69))|~v2_funct_1(X71)|(X69=k1_xboole_0|X70=k1_xboole_0|X72=k2_funct_1(X71))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_funct_2])])])).
% 0.21/0.48  cnf(c_0_57, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.21/0.48  cnf(c_0_58, negated_conjecture, (v2_funct_2(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_42]), c_0_43]), c_0_44])])).
% 0.21/0.48  cnf(c_0_59, negated_conjecture, (v5_relat_1(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_36, c_0_42])).
% 0.21/0.48  cnf(c_0_60, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_31, c_0_42])).
% 0.21/0.48  cnf(c_0_61, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.21/0.48  cnf(c_0_62, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.21/0.48  cnf(c_0_63, negated_conjecture, (r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0),k6_partfun1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.48  cnf(c_0_64, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.21/0.48  cnf(c_0_65, plain, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.21/0.48  fof(c_0_66, plain, ![X59, X60]:((((v1_funct_1(k2_funct_2(X59,X60))|(~v1_funct_1(X60)|~v1_funct_2(X60,X59,X59)|~v3_funct_2(X60,X59,X59)|~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X59,X59)))))&(v1_funct_2(k2_funct_2(X59,X60),X59,X59)|(~v1_funct_1(X60)|~v1_funct_2(X60,X59,X59)|~v3_funct_2(X60,X59,X59)|~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X59,X59))))))&(v3_funct_2(k2_funct_2(X59,X60),X59,X59)|(~v1_funct_1(X60)|~v1_funct_2(X60,X59,X59)|~v3_funct_2(X60,X59,X59)|~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X59,X59))))))&(m1_subset_1(k2_funct_2(X59,X60),k1_zfmisc_1(k2_zfmisc_1(X59,X59)))|(~v1_funct_1(X60)|~v1_funct_2(X60,X59,X59)|~v3_funct_2(X60,X59,X59)|~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X59,X59)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_2])])])).
% 0.21/0.48  cnf(c_0_67, plain, (k2_funct_2(X2,X1)=k2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X2)|~v3_funct_2(X1,X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.21/0.48  cnf(c_0_68, negated_conjecture, (v1_funct_2(esk4_0,esk3_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.48  fof(c_0_69, plain, ![X40, X41, X42]:(~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|r1_tarski(k3_relat_1(X42),k2_xboole_0(X40,X41))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_relset_1])])).
% 0.21/0.48  cnf(c_0_70, plain, (k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.21/0.48  cnf(c_0_71, negated_conjecture, (k2_relat_1(esk5_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53]), c_0_40])])).
% 0.21/0.48  cnf(c_0_72, negated_conjecture, (k2_xboole_0(k1_relat_1(esk5_0),esk3_0)=esk3_0), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.21/0.48  fof(c_0_73, plain, ![X7]:k2_xboole_0(X7,X7)=X7, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.21/0.48  cnf(c_0_74, plain, (X2=k1_xboole_0|X3=k1_xboole_0|X4=k2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~v1_funct_2(X4,X3,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|k2_relset_1(X2,X3,X1)!=X3|~r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,X1,X4),k6_partfun1(X2))|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.21/0.48  cnf(c_0_75, negated_conjecture, (k2_relset_1(esk3_0,esk3_0,esk4_0)=k2_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_57, c_0_42])).
% 0.21/0.48  cnf(c_0_76, negated_conjecture, (k2_relat_1(esk4_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_58]), c_0_59]), c_0_60])])).
% 0.21/0.48  cnf(c_0_77, plain, (v2_funct_1(X1)|~v1_funct_1(X1)|~v3_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.48  cnf(c_0_78, plain, (X1=k6_relat_1(X2)|~r2_relset_1(X2,X2,X1,k6_relat_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.21/0.48  cnf(c_0_79, negated_conjecture, (r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0),k6_relat_1(esk3_0))), inference(rw,[status(thm)],[c_0_63, c_0_64])).
% 0.21/0.48  cnf(c_0_80, negated_conjecture, (m1_subset_1(k1_partfun1(X1,X2,esk3_0,esk3_0,X3,esk5_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_30]), c_0_35])])).
% 0.21/0.48  cnf(c_0_81, plain, (r2_relset_1(X3,X4,X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.21/0.48  fof(c_0_82, plain, ![X44, X45, X46]:((r2_hidden(esk1_3(X44,X45,X46),X44)|r2_relset_1(X44,X44,X45,X46)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X44)))|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X44,X44))))&(k11_relat_1(X45,esk1_3(X44,X45,X46))!=k11_relat_1(X46,esk1_3(X44,X45,X46))|r2_relset_1(X44,X44,X45,X46)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X44)))|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X44,X44))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relset_1])])])])])).
% 0.21/0.48  cnf(c_0_83, plain, (m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.21/0.48  cnf(c_0_84, negated_conjecture, (k2_funct_2(esk3_0,esk4_0)=k2_funct_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_42]), c_0_68]), c_0_43]), c_0_44])])).
% 0.21/0.48  fof(c_0_85, plain, ![X10, X11]:((k4_xboole_0(X10,X11)!=k1_xboole_0|r1_tarski(X10,X11))&(~r1_tarski(X10,X11)|k4_xboole_0(X10,X11)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).
% 0.21/0.48  cnf(c_0_86, plain, (r1_tarski(k3_relat_1(X1),k2_xboole_0(X2,X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.21/0.48  cnf(c_0_87, negated_conjecture, (k3_relat_1(esk5_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72]), c_0_40])])).
% 0.21/0.48  cnf(c_0_88, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.21/0.48  cnf(c_0_89, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X1)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_1(X4)|~v1_funct_1(X1)|~v2_funct_1(X1)|~v1_funct_2(X4,X3,X2)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,X1,X4),k6_relat_1(X2))), inference(rw,[status(thm)],[c_0_74, c_0_64])).
% 0.21/0.48  cnf(c_0_90, negated_conjecture, (k2_relset_1(esk3_0,esk3_0,esk4_0)=esk3_0), inference(rw,[status(thm)],[c_0_75, c_0_76])).
% 0.21/0.48  cnf(c_0_91, negated_conjecture, (v2_funct_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_42]), c_0_43]), c_0_44])])).
% 0.21/0.48  cnf(c_0_92, negated_conjecture, (k1_partfun1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0)=k6_relat_1(esk3_0)|~m1_subset_1(k1_partfun1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.21/0.48  cnf(c_0_93, negated_conjecture, (m1_subset_1(k1_partfun1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_42]), c_0_44])])).
% 0.21/0.48  cnf(c_0_94, plain, (r2_relset_1(X1,X2,X3,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_81])).
% 0.21/0.48  cnf(c_0_95, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_relset_1(X1,X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.21/0.48  cnf(c_0_96, negated_conjecture, (m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_42]), c_0_84]), c_0_68]), c_0_43]), c_0_44])])).
% 0.21/0.48  cnf(c_0_97, negated_conjecture, (~r2_relset_1(esk3_0,esk3_0,esk5_0,k2_funct_2(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.48  fof(c_0_98, plain, ![X16, X17]:((~r1_xboole_0(X16,X17)|k4_xboole_0(X16,X17)=X16)&(k4_xboole_0(X16,X17)!=X16|r1_xboole_0(X16,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.21/0.48  cnf(c_0_99, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.21/0.48  cnf(c_0_100, negated_conjecture, (r1_tarski(esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_30]), c_0_87]), c_0_88])).
% 0.21/0.48  cnf(c_0_101, negated_conjecture, (X1=k2_funct_1(esk4_0)|esk3_0=k1_xboole_0|~v1_funct_2(X1,esk3_0,esk3_0)|~r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,X1),k6_relat_1(esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_68]), c_0_42]), c_0_91]), c_0_44])])).
% 0.21/0.48  cnf(c_0_102, negated_conjecture, (v1_funct_2(esk5_0,esk3_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.48  cnf(c_0_103, negated_conjecture, (k1_partfun1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0)=k6_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_93])])).
% 0.21/0.48  cnf(c_0_104, plain, (r2_relset_1(X1,X1,k6_relat_1(X1),k6_relat_1(X1))), inference(spm,[status(thm)],[c_0_94, c_0_62])).
% 0.21/0.48  fof(c_0_105, plain, ![X14, X15]:(~r2_hidden(X14,X15)|~v1_xboole_0(X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).
% 0.21/0.48  cnf(c_0_106, negated_conjecture, (r2_relset_1(esk3_0,esk3_0,X1,k2_funct_1(esk4_0))|r2_hidden(esk1_3(esk3_0,X1,k2_funct_1(esk4_0)),esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 0.21/0.48  cnf(c_0_107, negated_conjecture, (~r2_relset_1(esk3_0,esk3_0,esk5_0,k2_funct_1(esk4_0))), inference(rw,[status(thm)],[c_0_97, c_0_84])).
% 0.21/0.48  cnf(c_0_108, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_98])).
% 0.21/0.48  cnf(c_0_109, negated_conjecture, (k4_xboole_0(esk3_0,esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_99, c_0_100])).
% 0.21/0.48  cnf(c_0_110, negated_conjecture, (k2_funct_1(esk4_0)=esk5_0|esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_103]), c_0_104]), c_0_30]), c_0_35])])).
% 0.21/0.48  cnf(c_0_111, negated_conjecture, (r2_relset_1(esk3_0,esk3_0,esk5_0,esk5_0)), inference(spm,[status(thm)],[c_0_94, c_0_30])).
% 0.21/0.48  cnf(c_0_112, plain, (~r2_hidden(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_105])).
% 0.21/0.48  cnf(c_0_113, negated_conjecture, (r2_hidden(esk1_3(esk3_0,esk5_0,k2_funct_1(esk4_0)),esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_30]), c_0_107])).
% 0.21/0.48  fof(c_0_114, plain, ![X12, X13]:(v1_xboole_0(X13)|(~r1_tarski(X13,X12)|~r1_xboole_0(X13,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).
% 0.21/0.48  cnf(c_0_115, negated_conjecture, (r1_xboole_0(esk3_0,esk3_0)|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_108, c_0_109])).
% 0.21/0.48  cnf(c_0_116, negated_conjecture, (esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_110]), c_0_111])])).
% 0.21/0.48  cnf(c_0_117, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_112, c_0_113])).
% 0.21/0.48  cnf(c_0_118, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_114])).
% 0.21/0.48  cnf(c_0_119, negated_conjecture, (r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_115, c_0_116]), c_0_116]), c_0_116])])).
% 0.21/0.48  cnf(c_0_120, negated_conjecture, (r1_tarski(k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_100, c_0_116]), c_0_116])).
% 0.21/0.48  cnf(c_0_121, negated_conjecture, (~v1_xboole_0(k1_xboole_0)), inference(rw,[status(thm)],[c_0_117, c_0_116])).
% 0.21/0.48  cnf(c_0_122, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_119]), c_0_120])]), c_0_121]), ['proof']).
% 0.21/0.48  # SZS output end CNFRefutation
% 0.21/0.48  # Proof object total steps             : 123
% 0.21/0.48  # Proof object clause steps            : 76
% 0.21/0.48  # Proof object formula steps           : 47
% 0.21/0.48  # Proof object conjectures             : 50
% 0.21/0.48  # Proof object clause conjectures      : 47
% 0.21/0.48  # Proof object formula conjectures     : 3
% 0.21/0.48  # Proof object initial clauses used    : 35
% 0.21/0.48  # Proof object initial formulas used   : 23
% 0.21/0.48  # Proof object generating inferences   : 32
% 0.21/0.48  # Proof object simplifying inferences  : 65
% 0.21/0.48  # Training examples: 0 positive, 0 negative
% 0.21/0.48  # Parsed axioms                        : 27
% 0.21/0.48  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.48  # Initial clauses                      : 51
% 0.21/0.48  # Removed in clause preprocessing      : 2
% 0.21/0.48  # Initial clauses in saturation        : 49
% 0.21/0.48  # Processed clauses                    : 786
% 0.21/0.48  # ...of these trivial                  : 31
% 0.21/0.48  # ...subsumed                          : 3
% 0.21/0.48  # ...remaining for further processing  : 752
% 0.21/0.48  # Other redundant clauses eliminated   : 1
% 0.21/0.48  # Clauses deleted for lack of memory   : 0
% 0.21/0.48  # Backward-subsumed                    : 0
% 0.21/0.48  # Backward-rewritten                   : 583
% 0.21/0.48  # Generated clauses                    : 3723
% 0.21/0.48  # ...of the previous two non-trivial   : 4057
% 0.21/0.48  # Contextual simplify-reflections      : 0
% 0.21/0.48  # Paramodulations                      : 3717
% 0.21/0.48  # Factorizations                       : 0
% 0.21/0.48  # Equation resolutions                 : 6
% 0.21/0.48  # Propositional unsat checks           : 0
% 0.21/0.48  #    Propositional check models        : 0
% 0.21/0.48  #    Propositional check unsatisfiable : 0
% 0.21/0.48  #    Propositional clauses             : 0
% 0.21/0.48  #    Propositional clauses after purity: 0
% 0.21/0.48  #    Propositional unsat core size     : 0
% 0.21/0.48  #    Propositional preprocessing time  : 0.000
% 0.21/0.48  #    Propositional encoding time       : 0.000
% 0.21/0.48  #    Propositional solver time         : 0.000
% 0.21/0.48  #    Success case prop preproc time    : 0.000
% 0.21/0.48  #    Success case prop encoding time   : 0.000
% 0.21/0.48  #    Success case prop solver time     : 0.000
% 0.21/0.48  # Current number of processed clauses  : 119
% 0.21/0.48  #    Positive orientable unit clauses  : 61
% 0.21/0.48  #    Positive unorientable unit clauses: 0
% 0.21/0.48  #    Negative unit clauses             : 2
% 0.21/0.48  #    Non-unit-clauses                  : 56
% 0.21/0.48  # Current number of unprocessed clauses: 516
% 0.21/0.48  # ...number of literals in the above   : 784
% 0.21/0.48  # Current number of archived formulas  : 0
% 0.21/0.48  # Current number of archived clauses   : 633
% 0.21/0.48  # Clause-clause subsumption calls (NU) : 6992
% 0.21/0.48  # Rec. Clause-clause subsumption calls : 3417
% 0.21/0.48  # Non-unit clause-clause subsumptions  : 0
% 0.21/0.48  # Unit Clause-clause subsumption calls : 2018
% 0.21/0.48  # Rewrite failures with RHS unbound    : 0
% 0.21/0.48  # BW rewrite match attempts            : 7833
% 0.21/0.48  # BW rewrite match successes           : 11
% 0.21/0.48  # Condensation attempts                : 0
% 0.21/0.48  # Condensation successes               : 0
% 0.21/0.48  # Termbank termtop insertions          : 168127
% 0.21/0.48  
% 0.21/0.48  # -------------------------------------------------
% 0.21/0.48  # User time                : 0.123 s
% 0.21/0.48  # System time              : 0.006 s
% 0.21/0.48  # Total time               : 0.129 s
% 0.21/0.48  # Maximum resident set size: 1620 pages
%------------------------------------------------------------------------------
