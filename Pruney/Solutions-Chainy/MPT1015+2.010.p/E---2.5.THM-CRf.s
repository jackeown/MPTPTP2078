%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:05:46 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  145 (4709 expanded)
%              Number of clauses        :   99 (1743 expanded)
%              Number of leaves         :   23 (1167 expanded)
%              Depth                    :   15
%              Number of atoms          :  519 (26465 expanded)
%              Number of equality atoms :  108 (1796 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   70 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t67_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => k1_relset_1(X1,X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

fof(t76_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ! [X3] :
          ( ( v1_funct_1(X3)
            & v1_funct_2(X3,X1,X1)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
         => ( ( r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X3,X2),X2)
              & v2_funct_1(X2) )
           => r2_relset_1(X1,X1,X3,k6_partfun1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_funct_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(t4_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(k2_relat_1(X2),X1)
       => ( v1_funct_1(X2)
          & v1_funct_2(X2,k1_relat_1(X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(dt_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
        & m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(t31_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( v2_funct_1(X3)
          & k2_relset_1(X1,X2,X3) = X2 )
       => ( v1_funct_1(k2_funct_1(X3))
          & v1_funct_2(k2_funct_1(X3),X2,X1)
          & m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(t27_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ~ ( X1 != k1_xboole_0
          & X2 != k1_xboole_0
          & ~ ( v2_funct_1(X3)
            <=> ! [X4,X5] :
                  ( ( v1_funct_1(X5)
                    & v1_funct_2(X5,X4,X1)
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) )
                 => ! [X6] :
                      ( ( v1_funct_1(X6)
                        & v1_funct_2(X6,X4,X1)
                        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) )
                     => ( r2_relset_1(X4,X2,k1_partfun1(X4,X1,X1,X2,X5,X3),k1_partfun1(X4,X1,X1,X2,X6,X3))
                       => r2_relset_1(X4,X1,X5,X6) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_2)).

fof(t23_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r2_relset_1(X1,X2,k4_relset_1(X1,X1,X1,X2,k6_partfun1(X1),X3),X3)
        & r2_relset_1(X1,X2,k4_relset_1(X1,X2,X2,X2,X3,k6_partfun1(X2)),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(redefinition_k4_relset_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k4_relset_1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(fc4_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v2_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t61_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
          & k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t81_relat_1,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(c_0_23,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | k1_relset_1(X22,X23,X24) = k1_relat_1(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_24,plain,(
    ! [X69,X70] :
      ( ~ v1_funct_1(X70)
      | ~ v1_funct_2(X70,X69,X69)
      | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X69,X69)))
      | k1_relset_1(X69,X69,X70) = X69 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_funct_2])])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_funct_2(X2,X1,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
       => ! [X3] :
            ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X1)
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
           => ( ( r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X3,X2),X2)
                & v2_funct_1(X2) )
             => r2_relset_1(X1,X1,X3,k6_partfun1(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t76_funct_2])).

cnf(c_0_26,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,plain,
    ( k1_relset_1(X2,X2,X1) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_28,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk4_0,esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk4_0,esk4_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))
    & r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0),esk5_0)
    & v2_funct_1(esk5_0)
    & ~ r2_relset_1(esk4_0,esk4_0,esk6_0,k6_partfun1(esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

fof(c_0_29,plain,(
    ! [X19,X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | v1_relat_1(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_30,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_31,plain,(
    ! [X34,X35,X36,X37] :
      ( ( ~ r2_relset_1(X34,X35,X36,X37)
        | X36 = X37
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( X36 != X37
        | r2_relset_1(X34,X35,X36,X37)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

fof(c_0_32,plain,(
    ! [X67,X68] :
      ( ( v1_funct_1(X68)
        | ~ r1_tarski(k2_relat_1(X68),X67)
        | ~ v1_relat_1(X68)
        | ~ v1_funct_1(X68) )
      & ( v1_funct_2(X68,k1_relat_1(X68),X67)
        | ~ r1_tarski(k2_relat_1(X68),X67)
        | ~ v1_relat_1(X68)
        | ~ v1_funct_1(X68) )
      & ( m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X68),X67)))
        | ~ r1_tarski(k2_relat_1(X68),X67)
        | ~ v1_relat_1(X68)
        | ~ v1_funct_1(X68) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).

cnf(c_0_33,plain,
    ( X1 = k1_relat_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_2(esk5_0,esk4_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_41,plain,(
    ! [X38,X39,X40,X41,X42,X43] :
      ( ( v1_funct_1(k1_partfun1(X38,X39,X40,X41,X42,X43))
        | ~ v1_funct_1(X42)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
        | ~ v1_funct_1(X43)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) )
      & ( m1_subset_1(k1_partfun1(X38,X39,X40,X41,X42,X43),k1_zfmisc_1(k2_zfmisc_1(X38,X41)))
        | ~ v1_funct_1(X42)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
        | ~ v1_funct_1(X43)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

fof(c_0_42,plain,(
    ! [X45,X46,X47,X48,X49,X50] :
      ( ~ v1_funct_1(X49)
      | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))
      | ~ v1_funct_1(X50)
      | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
      | k1_partfun1(X45,X46,X47,X48,X49,X50) = k5_relat_1(X49,X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

fof(c_0_43,plain,(
    ! [X64,X65,X66] :
      ( ( v1_funct_1(k2_funct_1(X66))
        | ~ v2_funct_1(X66)
        | k2_relset_1(X64,X65,X66) != X65
        | ~ v1_funct_1(X66)
        | ~ v1_funct_2(X66,X64,X65)
        | ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65))) )
      & ( v1_funct_2(k2_funct_1(X66),X65,X64)
        | ~ v2_funct_1(X66)
        | k2_relset_1(X64,X65,X66) != X65
        | ~ v1_funct_1(X66)
        | ~ v1_funct_2(X66,X64,X65)
        | ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65))) )
      & ( m1_subset_1(k2_funct_1(X66),k1_zfmisc_1(k2_zfmisc_1(X65,X64)))
        | ~ v2_funct_1(X66)
        | k2_relset_1(X64,X65,X66) != X65
        | ~ v1_funct_1(X66)
        | ~ v1_funct_2(X66,X64,X65)
        | ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).

cnf(c_0_44,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36])])).

cnf(c_0_46,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_34])).

cnf(c_0_47,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_50,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_51,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_52,plain,(
    ! [X55,X56,X57,X58,X59,X60] :
      ( ( ~ v2_funct_1(X57)
        | ~ v1_funct_1(X59)
        | ~ v1_funct_2(X59,X58,X55)
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X58,X55)))
        | ~ v1_funct_1(X60)
        | ~ v1_funct_2(X60,X58,X55)
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X55)))
        | ~ r2_relset_1(X58,X56,k1_partfun1(X58,X55,X55,X56,X59,X57),k1_partfun1(X58,X55,X55,X56,X60,X57))
        | r2_relset_1(X58,X55,X59,X60)
        | X55 = k1_xboole_0
        | X56 = k1_xboole_0
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,X55,X56)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))) )
      & ( v1_funct_1(esk2_3(X55,X56,X57))
        | v2_funct_1(X57)
        | X55 = k1_xboole_0
        | X56 = k1_xboole_0
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,X55,X56)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))) )
      & ( v1_funct_2(esk2_3(X55,X56,X57),esk1_3(X55,X56,X57),X55)
        | v2_funct_1(X57)
        | X55 = k1_xboole_0
        | X56 = k1_xboole_0
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,X55,X56)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))) )
      & ( m1_subset_1(esk2_3(X55,X56,X57),k1_zfmisc_1(k2_zfmisc_1(esk1_3(X55,X56,X57),X55)))
        | v2_funct_1(X57)
        | X55 = k1_xboole_0
        | X56 = k1_xboole_0
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,X55,X56)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))) )
      & ( v1_funct_1(esk3_3(X55,X56,X57))
        | v2_funct_1(X57)
        | X55 = k1_xboole_0
        | X56 = k1_xboole_0
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,X55,X56)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))) )
      & ( v1_funct_2(esk3_3(X55,X56,X57),esk1_3(X55,X56,X57),X55)
        | v2_funct_1(X57)
        | X55 = k1_xboole_0
        | X56 = k1_xboole_0
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,X55,X56)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))) )
      & ( m1_subset_1(esk3_3(X55,X56,X57),k1_zfmisc_1(k2_zfmisc_1(esk1_3(X55,X56,X57),X55)))
        | v2_funct_1(X57)
        | X55 = k1_xboole_0
        | X56 = k1_xboole_0
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,X55,X56)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))) )
      & ( r2_relset_1(esk1_3(X55,X56,X57),X56,k1_partfun1(esk1_3(X55,X56,X57),X55,X55,X56,esk2_3(X55,X56,X57),X57),k1_partfun1(esk1_3(X55,X56,X57),X55,X55,X56,esk3_3(X55,X56,X57),X57))
        | v2_funct_1(X57)
        | X55 = k1_xboole_0
        | X56 = k1_xboole_0
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,X55,X56)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))) )
      & ( ~ r2_relset_1(esk1_3(X55,X56,X57),X55,esk2_3(X55,X56,X57),esk3_3(X55,X56,X57))
        | v2_funct_1(X57)
        | X55 = k1_xboole_0
        | X56 = k1_xboole_0
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,X55,X56)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_funct_2])])])])])).

cnf(c_0_53,negated_conjecture,
    ( k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0) = esk5_0
    | ~ m1_subset_1(k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_34])])).

cnf(c_0_54,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_55,plain,(
    ! [X52,X53,X54] :
      ( ( r2_relset_1(X52,X53,k4_relset_1(X52,X52,X52,X53,k6_partfun1(X52),X54),X54)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) )
      & ( r2_relset_1(X52,X53,k4_relset_1(X52,X53,X53,X53,X54,k6_partfun1(X53)),X54)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_2])])])).

fof(c_0_56,plain,(
    ! [X51] : k6_partfun1(X51) = k6_relat_1(X51) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_57,plain,(
    ! [X44] :
      ( v1_partfun1(k6_partfun1(X44),X44)
      & m1_subset_1(k6_partfun1(X44),k1_zfmisc_1(k2_zfmisc_1(X44,X44))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

cnf(c_0_58,plain,
    ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_59,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_60,plain,(
    ! [X25,X26,X27] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | k2_relset_1(X25,X26,X27) = k2_relat_1(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_61,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))
    | ~ r1_tarski(k2_relat_1(esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_36]),c_0_46])])).

cnf(c_0_63,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

fof(c_0_64,plain,(
    ! [X10,X11] :
      ( ( k2_zfmisc_1(X10,X11) != k1_xboole_0
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0 )
      & ( X10 != k1_xboole_0
        | k2_zfmisc_1(X10,X11) = k1_xboole_0 )
      & ( X11 != k1_xboole_0
        | k2_zfmisc_1(X10,X11) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_65,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_49]),c_0_50]),c_0_51])])).

cnf(c_0_66,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_49])).

cnf(c_0_67,plain,
    ( r2_relset_1(X3,X4,X2,X5)
    | X4 = k1_xboole_0
    | X6 = k1_xboole_0
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X3,X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ r2_relset_1(X3,X6,k1_partfun1(X3,X4,X4,X6,X2,X1),k1_partfun1(X3,X4,X4,X6,X5,X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X4,X6)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_68,negated_conjecture,
    ( k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_36]),c_0_51]),c_0_34]),c_0_49])])).

cnf(c_0_69,negated_conjecture,
    ( v2_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_70,plain,
    ( r2_relset_1(X1,X2,k4_relset_1(X1,X1,X1,X2,k6_partfun1(X1),X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_71,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

fof(c_0_72,plain,(
    ! [X28,X29,X30,X31,X32,X33] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
      | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      | k4_relset_1(X28,X29,X30,X31,X32,X33) = k5_relat_1(X32,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_relset_1])])).

cnf(c_0_73,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_74,plain,(
    ! [X16] :
      ( k1_relat_1(k6_relat_1(X16)) = X16
      & k2_relat_1(k6_relat_1(X16)) = X16 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_75,plain,(
    ! [X17] :
      ( v1_relat_1(k6_relat_1(X17))
      & v2_funct_1(k6_relat_1(X17)) ) ),
    inference(variable_rename,[status(thm)],[fc4_funct_1])).

cnf(c_0_76,plain,
    ( v1_funct_1(k5_relat_1(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_77,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_48])).

cnf(c_0_78,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_79,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_80,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_61])).

cnf(c_0_81,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_relat_1(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_48])).

cnf(c_0_82,negated_conjecture,
    ( v1_funct_2(esk5_0,esk4_0,k2_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_45]),c_0_36]),c_0_46])])).

fof(c_0_83,plain,(
    ! [X12,X13] :
      ( ( ~ m1_subset_1(X12,k1_zfmisc_1(X13))
        | r1_tarski(X12,X13) )
      & ( ~ r1_tarski(X12,X13)
        | m1_subset_1(X12,k1_zfmisc_1(X13)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_84,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_85,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))
    | ~ r1_tarski(k2_relat_1(esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_65]),c_0_51]),c_0_66])])).

cnf(c_0_86,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_relset_1(esk4_0,esk4_0,X1,esk6_0)
    | ~ v1_funct_2(X1,esk4_0,esk4_0)
    | ~ r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,X1,esk5_0),esk5_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_50]),c_0_35]),c_0_51]),c_0_36]),c_0_69]),c_0_49]),c_0_34])])).

cnf(c_0_87,plain,
    ( r2_relset_1(X1,X2,k4_relset_1(X1,X1,X1,X2,k6_relat_1(X1),X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_88,plain,
    ( k4_relset_1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_89,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(rw,[status(thm)],[c_0_73,c_0_71])).

cnf(c_0_90,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_91,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_92,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_93,plain,
    ( v1_funct_1(k5_relat_1(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

fof(c_0_94,plain,(
    ! [X18] :
      ( ( k5_relat_1(X18,k2_funct_1(X18)) = k6_relat_1(k1_relat_1(X18))
        | ~ v2_funct_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( k5_relat_1(k2_funct_1(X18),X18) = k6_relat_1(k2_relat_1(X18))
        | ~ v2_funct_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).

cnf(c_0_95,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_2(X1,X2,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(X1)))) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79])])).

cnf(c_0_96,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk5_0))
    | k2_relset_1(esk4_0,k2_relat_1(esk5_0),esk5_0) != k2_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82]),c_0_36]),c_0_69])])).

cnf(c_0_97,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_98,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_99,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_84])).

fof(c_0_100,plain,(
    ! [X9] : r1_tarski(k1_xboole_0,X9) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_101,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_relat_1(esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_85,c_0_48])).

cnf(c_0_102,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,k2_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_65]),c_0_51]),c_0_66])])).

cnf(c_0_103,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_relset_1(esk4_0,esk4_0,X1,esk6_0)
    | ~ v1_funct_2(X1,esk4_0,esk4_0)
    | ~ r2_relset_1(esk4_0,esk4_0,k5_relat_1(X1,esk5_0),esk5_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_59]),c_0_36]),c_0_34])])).

cnf(c_0_104,plain,
    ( r2_relset_1(X1,X2,k5_relat_1(k6_relat_1(X1),X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_89])])).

cnf(c_0_105,plain,
    ( v1_funct_2(k6_relat_1(X1),X1,X1)
    | ~ v1_funct_1(k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_90]),c_0_91]),c_0_92])])).

cnf(c_0_106,negated_conjecture,
    ( v1_funct_1(k5_relat_1(esk5_0,X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_34]),c_0_36])])).

cnf(c_0_107,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_108,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_82]),c_0_36]),c_0_69]),c_0_81])])).

cnf(c_0_109,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_79]),c_0_81])])).

cnf(c_0_110,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_111,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_99])).

cnf(c_0_112,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_113,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

cnf(c_0_114,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk6_0))
    | k2_relset_1(esk4_0,k2_relat_1(esk6_0),esk6_0) != k2_relat_1(esk6_0)
    | ~ v2_funct_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_101]),c_0_102]),c_0_51])])).

cnf(c_0_115,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_relset_1(esk4_0,esk4_0,k6_relat_1(esk4_0),esk6_0)
    | ~ v1_funct_1(k6_relat_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_89]),c_0_34])]),c_0_105])).

cnf(c_0_116,negated_conjecture,
    ( v1_funct_1(k6_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_45]),c_0_108]),c_0_109]),c_0_36]),c_0_69]),c_0_46])])).

cnf(c_0_117,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_110,c_0_98])).

cnf(c_0_118,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_1(k6_relat_1(X1))
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_90]),c_0_92])])).

cnf(c_0_119,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_120,negated_conjecture,
    ( v1_funct_1(k5_relat_1(esk6_0,X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_49]),c_0_51])])).

cnf(c_0_121,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk6_0))
    | ~ v2_funct_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_79]),c_0_101])])).

cnf(c_0_122,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk6_0))
    | ~ v2_funct_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_102]),c_0_51]),c_0_101])])).

cnf(c_0_123,negated_conjecture,
    ( ~ r2_relset_1(esk4_0,esk4_0,esk6_0,k6_partfun1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_124,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_relset_1(esk4_0,esk4_0,k6_relat_1(esk4_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_115,c_0_116])])).

cnf(c_0_125,negated_conjecture,
    ( r2_relset_1(esk4_0,esk4_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_40,c_0_68])).

cnf(c_0_126,plain,
    ( k6_relat_1(X1) = k1_xboole_0
    | ~ v1_funct_1(k6_relat_1(X1))
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_118]),c_0_119])])).

cnf(c_0_127,negated_conjecture,
    ( v1_funct_1(k6_relat_1(esk4_0))
    | ~ v2_funct_1(esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_107]),c_0_65]),c_0_51]),c_0_66])]),c_0_121]),c_0_122])).

cnf(c_0_128,negated_conjecture,
    ( ~ r2_relset_1(esk4_0,esk4_0,esk6_0,k6_relat_1(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_123,c_0_71])).

cnf(c_0_129,negated_conjecture,
    ( k6_relat_1(esk4_0) = esk6_0
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_124]),c_0_49]),c_0_89])])).

cnf(c_0_130,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_relset_1(esk4_0,esk4_0,esk6_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_68]),c_0_50]),c_0_125]),c_0_51]),c_0_49])])).

cnf(c_0_131,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_132,negated_conjecture,
    ( k6_relat_1(esk4_0) = k1_xboole_0
    | ~ v2_funct_1(esk6_0)
    | ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_126,c_0_127])).

cnf(c_0_133,negated_conjecture,
    ( k2_zfmisc_1(esk4_0,k2_relat_1(esk6_0)) = esk6_0
    | ~ m1_subset_1(k2_zfmisc_1(esk4_0,k2_relat_1(esk6_0)),k1_zfmisc_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_117,c_0_101])).

cnf(c_0_134,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_129]),c_0_130])).

cnf(c_0_135,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_131])).

cnf(c_0_136,plain,
    ( v2_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_137,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t81_relat_1])).

cnf(c_0_138,negated_conjecture,
    ( ~ r2_relset_1(esk4_0,esk4_0,esk6_0,k1_xboole_0)
    | ~ v2_funct_1(esk6_0)
    | ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_128,c_0_132])).

cnf(c_0_139,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_133,c_0_134]),c_0_135]),c_0_134]),c_0_135]),c_0_119])])).

cnf(c_0_140,plain,
    ( v2_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_136,c_0_137])).

cnf(c_0_141,plain,
    ( r2_relset_1(X3,X4,X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_142,negated_conjecture,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_138,c_0_134]),c_0_134]),c_0_134]),c_0_113])]),c_0_139]),c_0_139]),c_0_140])])).

cnf(c_0_143,plain,
    ( r2_relset_1(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_141])).

cnf(c_0_144,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_143]),c_0_135]),c_0_119])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:56:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.44  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.20/0.44  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.20/0.44  #
% 0.20/0.44  # Preprocessing time       : 0.029 s
% 0.20/0.44  # Presaturation interreduction done
% 0.20/0.44  
% 0.20/0.44  # Proof found!
% 0.20/0.44  # SZS status Theorem
% 0.20/0.44  # SZS output start CNFRefutation
% 0.20/0.44  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.44  fof(t67_funct_2, axiom, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>k1_relset_1(X1,X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 0.20/0.44  fof(t76_funct_2, conjecture, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>((r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X3,X2),X2)&v2_funct_1(X2))=>r2_relset_1(X1,X1,X3,k6_partfun1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_funct_2)).
% 0.20/0.44  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.44  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.44  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.20/0.44  fof(t4_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(k2_relat_1(X2),X1)=>((v1_funct_1(X2)&v1_funct_2(X2,k1_relat_1(X2),X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 0.20/0.44  fof(dt_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))&m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 0.20/0.44  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 0.20/0.44  fof(t31_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 0.20/0.44  fof(t27_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&~((v2_funct_1(X3)<=>![X4, X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X4,X1))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X1))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X1))))=>(r2_relset_1(X4,X2,k1_partfun1(X4,X1,X1,X2,X5,X3),k1_partfun1(X4,X1,X1,X2,X6,X3))=>r2_relset_1(X4,X1,X5,X6))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_funct_2)).
% 0.20/0.44  fof(t23_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(r2_relset_1(X1,X2,k4_relset_1(X1,X1,X1,X2,k6_partfun1(X1),X3),X3)&r2_relset_1(X1,X2,k4_relset_1(X1,X2,X2,X2,X3,k6_partfun1(X2)),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_2)).
% 0.20/0.44  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.20/0.44  fof(dt_k6_partfun1, axiom, ![X1]:(v1_partfun1(k6_partfun1(X1),X1)&m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 0.20/0.44  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.20/0.44  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.20/0.44  fof(redefinition_k4_relset_1, axiom, ![X1, X2, X3, X4, X5, X6]:((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k4_relset_1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 0.20/0.44  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.20/0.44  fof(fc4_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v2_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 0.20/0.44  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.44  fof(t61_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))&k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 0.20/0.44  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.44  fof(t81_relat_1, axiom, k6_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 0.20/0.44  fof(c_0_23, plain, ![X22, X23, X24]:(~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))|k1_relset_1(X22,X23,X24)=k1_relat_1(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.44  fof(c_0_24, plain, ![X69, X70]:(~v1_funct_1(X70)|~v1_funct_2(X70,X69,X69)|~m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X69,X69)))|k1_relset_1(X69,X69,X70)=X69), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_funct_2])])).
% 0.20/0.44  fof(c_0_25, negated_conjecture, ~(![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>((r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X3,X2),X2)&v2_funct_1(X2))=>r2_relset_1(X1,X1,X3,k6_partfun1(X1)))))), inference(assume_negation,[status(cth)],[t76_funct_2])).
% 0.20/0.44  cnf(c_0_26, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.44  cnf(c_0_27, plain, (k1_relset_1(X2,X2,X1)=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.44  fof(c_0_28, negated_conjecture, (((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk4_0,esk4_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk4_0,esk4_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))))&((r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0),esk5_0)&v2_funct_1(esk5_0))&~r2_relset_1(esk4_0,esk4_0,esk6_0,k6_partfun1(esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 0.20/0.44  fof(c_0_29, plain, ![X19, X20, X21]:(~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))|v1_relat_1(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.44  fof(c_0_30, plain, ![X7, X8]:(((r1_tarski(X7,X8)|X7!=X8)&(r1_tarski(X8,X7)|X7!=X8))&(~r1_tarski(X7,X8)|~r1_tarski(X8,X7)|X7=X8)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.44  fof(c_0_31, plain, ![X34, X35, X36, X37]:((~r2_relset_1(X34,X35,X36,X37)|X36=X37|(~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))))&(X36!=X37|r2_relset_1(X34,X35,X36,X37)|(~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.20/0.44  fof(c_0_32, plain, ![X67, X68]:(((v1_funct_1(X68)|~r1_tarski(k2_relat_1(X68),X67)|(~v1_relat_1(X68)|~v1_funct_1(X68)))&(v1_funct_2(X68,k1_relat_1(X68),X67)|~r1_tarski(k2_relat_1(X68),X67)|(~v1_relat_1(X68)|~v1_funct_1(X68))))&(m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X68),X67)))|~r1_tarski(k2_relat_1(X68),X67)|(~v1_relat_1(X68)|~v1_funct_1(X68)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).
% 0.20/0.44  cnf(c_0_33, plain, (X1=k1_relat_1(X2)|~v1_funct_2(X2,X1,X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.44  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.44  cnf(c_0_35, negated_conjecture, (v1_funct_2(esk5_0,esk4_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.44  cnf(c_0_36, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.44  cnf(c_0_37, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.44  cnf(c_0_38, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.44  cnf(c_0_39, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.44  cnf(c_0_40, negated_conjecture, (r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.44  fof(c_0_41, plain, ![X38, X39, X40, X41, X42, X43]:((v1_funct_1(k1_partfun1(X38,X39,X40,X41,X42,X43))|(~v1_funct_1(X42)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|~v1_funct_1(X43)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))))&(m1_subset_1(k1_partfun1(X38,X39,X40,X41,X42,X43),k1_zfmisc_1(k2_zfmisc_1(X38,X41)))|(~v1_funct_1(X42)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|~v1_funct_1(X43)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).
% 0.20/0.44  fof(c_0_42, plain, ![X45, X46, X47, X48, X49, X50]:(~v1_funct_1(X49)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))|~v1_funct_1(X50)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))|k1_partfun1(X45,X46,X47,X48,X49,X50)=k5_relat_1(X49,X50)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 0.20/0.44  fof(c_0_43, plain, ![X64, X65, X66]:(((v1_funct_1(k2_funct_1(X66))|(~v2_funct_1(X66)|k2_relset_1(X64,X65,X66)!=X65)|(~v1_funct_1(X66)|~v1_funct_2(X66,X64,X65)|~m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65)))))&(v1_funct_2(k2_funct_1(X66),X65,X64)|(~v2_funct_1(X66)|k2_relset_1(X64,X65,X66)!=X65)|(~v1_funct_1(X66)|~v1_funct_2(X66,X64,X65)|~m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65))))))&(m1_subset_1(k2_funct_1(X66),k1_zfmisc_1(k2_zfmisc_1(X65,X64)))|(~v2_funct_1(X66)|k2_relset_1(X64,X65,X66)!=X65)|(~v1_funct_1(X66)|~v1_funct_2(X66,X64,X65)|~m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).
% 0.20/0.44  cnf(c_0_44, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.44  cnf(c_0_45, negated_conjecture, (k1_relat_1(esk5_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36])])).
% 0.20/0.44  cnf(c_0_46, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_37, c_0_34])).
% 0.20/0.44  cnf(c_0_47, plain, (v1_funct_2(X1,k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.44  cnf(c_0_48, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_38])).
% 0.20/0.44  cnf(c_0_49, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.44  cnf(c_0_50, negated_conjecture, (v1_funct_2(esk6_0,esk4_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.44  cnf(c_0_51, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.44  fof(c_0_52, plain, ![X55, X56, X57, X58, X59, X60]:((~v2_funct_1(X57)|(~v1_funct_1(X59)|~v1_funct_2(X59,X58,X55)|~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X58,X55)))|(~v1_funct_1(X60)|~v1_funct_2(X60,X58,X55)|~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X55)))|(~r2_relset_1(X58,X56,k1_partfun1(X58,X55,X55,X56,X59,X57),k1_partfun1(X58,X55,X55,X56,X60,X57))|r2_relset_1(X58,X55,X59,X60))))|(X55=k1_xboole_0|X56=k1_xboole_0)|(~v1_funct_1(X57)|~v1_funct_2(X57,X55,X56)|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56)))))&((((v1_funct_1(esk2_3(X55,X56,X57))|v2_funct_1(X57)|(X55=k1_xboole_0|X56=k1_xboole_0)|(~v1_funct_1(X57)|~v1_funct_2(X57,X55,X56)|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56)))))&(v1_funct_2(esk2_3(X55,X56,X57),esk1_3(X55,X56,X57),X55)|v2_funct_1(X57)|(X55=k1_xboole_0|X56=k1_xboole_0)|(~v1_funct_1(X57)|~v1_funct_2(X57,X55,X56)|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))))))&(m1_subset_1(esk2_3(X55,X56,X57),k1_zfmisc_1(k2_zfmisc_1(esk1_3(X55,X56,X57),X55)))|v2_funct_1(X57)|(X55=k1_xboole_0|X56=k1_xboole_0)|(~v1_funct_1(X57)|~v1_funct_2(X57,X55,X56)|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))))))&((((v1_funct_1(esk3_3(X55,X56,X57))|v2_funct_1(X57)|(X55=k1_xboole_0|X56=k1_xboole_0)|(~v1_funct_1(X57)|~v1_funct_2(X57,X55,X56)|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56)))))&(v1_funct_2(esk3_3(X55,X56,X57),esk1_3(X55,X56,X57),X55)|v2_funct_1(X57)|(X55=k1_xboole_0|X56=k1_xboole_0)|(~v1_funct_1(X57)|~v1_funct_2(X57,X55,X56)|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))))))&(m1_subset_1(esk3_3(X55,X56,X57),k1_zfmisc_1(k2_zfmisc_1(esk1_3(X55,X56,X57),X55)))|v2_funct_1(X57)|(X55=k1_xboole_0|X56=k1_xboole_0)|(~v1_funct_1(X57)|~v1_funct_2(X57,X55,X56)|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))))))&((r2_relset_1(esk1_3(X55,X56,X57),X56,k1_partfun1(esk1_3(X55,X56,X57),X55,X55,X56,esk2_3(X55,X56,X57),X57),k1_partfun1(esk1_3(X55,X56,X57),X55,X55,X56,esk3_3(X55,X56,X57),X57))|v2_funct_1(X57)|(X55=k1_xboole_0|X56=k1_xboole_0)|(~v1_funct_1(X57)|~v1_funct_2(X57,X55,X56)|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56)))))&(~r2_relset_1(esk1_3(X55,X56,X57),X55,esk2_3(X55,X56,X57),esk3_3(X55,X56,X57))|v2_funct_1(X57)|(X55=k1_xboole_0|X56=k1_xboole_0)|(~v1_funct_1(X57)|~v1_funct_2(X57,X55,X56)|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_funct_2])])])])])).
% 0.20/0.44  cnf(c_0_53, negated_conjecture, (k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0)=esk5_0|~m1_subset_1(k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_34])])).
% 0.20/0.44  cnf(c_0_54, plain, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.44  fof(c_0_55, plain, ![X52, X53, X54]:((r2_relset_1(X52,X53,k4_relset_1(X52,X52,X52,X53,k6_partfun1(X52),X54),X54)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))))&(r2_relset_1(X52,X53,k4_relset_1(X52,X53,X53,X53,X54,k6_partfun1(X53)),X54)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_2])])])).
% 0.20/0.44  fof(c_0_56, plain, ![X51]:k6_partfun1(X51)=k6_relat_1(X51), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.20/0.44  fof(c_0_57, plain, ![X44]:(v1_partfun1(k6_partfun1(X44),X44)&m1_subset_1(k6_partfun1(X44),k1_zfmisc_1(k2_zfmisc_1(X44,X44)))), inference(variable_rename,[status(thm)],[dt_k6_partfun1])).
% 0.20/0.44  cnf(c_0_58, plain, (v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.44  cnf(c_0_59, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.44  fof(c_0_60, plain, ![X25, X26, X27]:(~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))|k2_relset_1(X25,X26,X27)=k2_relat_1(X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.20/0.44  cnf(c_0_61, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v2_funct_1(X1)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.44  cnf(c_0_62, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))|~r1_tarski(k2_relat_1(esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_36]), c_0_46])])).
% 0.20/0.44  cnf(c_0_63, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.44  fof(c_0_64, plain, ![X10, X11]:((k2_zfmisc_1(X10,X11)!=k1_xboole_0|(X10=k1_xboole_0|X11=k1_xboole_0))&((X10!=k1_xboole_0|k2_zfmisc_1(X10,X11)=k1_xboole_0)&(X11!=k1_xboole_0|k2_zfmisc_1(X10,X11)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.20/0.44  cnf(c_0_65, negated_conjecture, (k1_relat_1(esk6_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_49]), c_0_50]), c_0_51])])).
% 0.20/0.44  cnf(c_0_66, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_37, c_0_49])).
% 0.20/0.44  cnf(c_0_67, plain, (r2_relset_1(X3,X4,X2,X5)|X4=k1_xboole_0|X6=k1_xboole_0|~v2_funct_1(X1)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~r2_relset_1(X3,X6,k1_partfun1(X3,X4,X4,X6,X2,X1),k1_partfun1(X3,X4,X4,X6,X5,X1))|~v1_funct_1(X1)|~v1_funct_2(X1,X4,X6)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X6)))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.44  cnf(c_0_68, negated_conjecture, (k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_36]), c_0_51]), c_0_34]), c_0_49])])).
% 0.20/0.44  cnf(c_0_69, negated_conjecture, (v2_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.44  cnf(c_0_70, plain, (r2_relset_1(X1,X2,k4_relset_1(X1,X1,X1,X2,k6_partfun1(X1),X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.44  cnf(c_0_71, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.20/0.44  fof(c_0_72, plain, ![X28, X29, X30, X31, X32, X33]:(~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|k4_relset_1(X28,X29,X30,X31,X32,X33)=k5_relat_1(X32,X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_relset_1])])).
% 0.20/0.44  cnf(c_0_73, plain, (m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.20/0.44  fof(c_0_74, plain, ![X16]:(k1_relat_1(k6_relat_1(X16))=X16&k2_relat_1(k6_relat_1(X16))=X16), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.20/0.44  fof(c_0_75, plain, ![X17]:(v1_relat_1(k6_relat_1(X17))&v2_funct_1(k6_relat_1(X17))), inference(variable_rename,[status(thm)],[fc4_funct_1])).
% 0.20/0.44  cnf(c_0_76, plain, (v1_funct_1(k5_relat_1(X1,X2))|~v1_funct_1(X2)|~v1_funct_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.20/0.44  cnf(c_0_77, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_44, c_0_48])).
% 0.20/0.44  cnf(c_0_78, plain, (v1_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.44  cnf(c_0_79, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.44  cnf(c_0_80, plain, (v1_relat_1(k2_funct_1(X1))|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_2(X1,X2,X3)|~v1_funct_1(X1)|~v2_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_37, c_0_61])).
% 0.20/0.44  cnf(c_0_81, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_relat_1(esk5_0))))), inference(spm,[status(thm)],[c_0_62, c_0_48])).
% 0.20/0.44  cnf(c_0_82, negated_conjecture, (v1_funct_2(esk5_0,esk4_0,k2_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_45]), c_0_36]), c_0_46])])).
% 0.20/0.44  fof(c_0_83, plain, ![X12, X13]:((~m1_subset_1(X12,k1_zfmisc_1(X13))|r1_tarski(X12,X13))&(~r1_tarski(X12,X13)|m1_subset_1(X12,k1_zfmisc_1(X13)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.44  cnf(c_0_84, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.20/0.44  cnf(c_0_85, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))|~r1_tarski(k2_relat_1(esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_65]), c_0_51]), c_0_66])])).
% 0.20/0.44  cnf(c_0_86, negated_conjecture, (esk4_0=k1_xboole_0|r2_relset_1(esk4_0,esk4_0,X1,esk6_0)|~v1_funct_2(X1,esk4_0,esk4_0)|~r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,X1,esk5_0),esk5_0)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_50]), c_0_35]), c_0_51]), c_0_36]), c_0_69]), c_0_49]), c_0_34])])).
% 0.20/0.44  cnf(c_0_87, plain, (r2_relset_1(X1,X2,k4_relset_1(X1,X1,X1,X2,k6_relat_1(X1),X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(rw,[status(thm)],[c_0_70, c_0_71])).
% 0.20/0.44  cnf(c_0_88, plain, (k4_relset_1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.20/0.44  cnf(c_0_89, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(rw,[status(thm)],[c_0_73, c_0_71])).
% 0.20/0.44  cnf(c_0_90, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.20/0.44  cnf(c_0_91, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.20/0.44  cnf(c_0_92, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.20/0.44  cnf(c_0_93, plain, (v1_funct_1(k5_relat_1(X1,X2))|~v1_funct_1(X2)|~v1_funct_1(X1)|~v1_relat_1(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.20/0.44  fof(c_0_94, plain, ![X18]:((k5_relat_1(X18,k2_funct_1(X18))=k6_relat_1(k1_relat_1(X18))|~v2_funct_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18)))&(k5_relat_1(k2_funct_1(X18),X18)=k6_relat_1(k2_relat_1(X18))|~v2_funct_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).
% 0.20/0.44  cnf(c_0_95, plain, (v1_funct_1(k2_funct_1(X1))|~v1_funct_2(X1,X2,k2_relat_1(X1))|~v1_funct_1(X1)|~v2_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(X1))))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79])])).
% 0.20/0.44  cnf(c_0_96, negated_conjecture, (v1_relat_1(k2_funct_1(esk5_0))|k2_relset_1(esk4_0,k2_relat_1(esk5_0),esk5_0)!=k2_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_82]), c_0_36]), c_0_69])])).
% 0.20/0.44  cnf(c_0_97, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.44  cnf(c_0_98, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.20/0.44  cnf(c_0_99, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_84])).
% 0.20/0.44  fof(c_0_100, plain, ![X9]:r1_tarski(k1_xboole_0,X9), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.44  cnf(c_0_101, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_relat_1(esk6_0))))), inference(spm,[status(thm)],[c_0_85, c_0_48])).
% 0.20/0.44  cnf(c_0_102, negated_conjecture, (v1_funct_2(esk6_0,esk4_0,k2_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_65]), c_0_51]), c_0_66])])).
% 0.20/0.44  cnf(c_0_103, negated_conjecture, (esk4_0=k1_xboole_0|r2_relset_1(esk4_0,esk4_0,X1,esk6_0)|~v1_funct_2(X1,esk4_0,esk4_0)|~r2_relset_1(esk4_0,esk4_0,k5_relat_1(X1,esk5_0),esk5_0)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_59]), c_0_36]), c_0_34])])).
% 0.20/0.44  cnf(c_0_104, plain, (r2_relset_1(X1,X2,k5_relat_1(k6_relat_1(X1),X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_89])])).
% 0.20/0.44  cnf(c_0_105, plain, (v1_funct_2(k6_relat_1(X1),X1,X1)|~v1_funct_1(k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_90]), c_0_91]), c_0_92])])).
% 0.20/0.44  cnf(c_0_106, negated_conjecture, (v1_funct_1(k5_relat_1(esk5_0,X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_34]), c_0_36])])).
% 0.20/0.44  cnf(c_0_107, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_94])).
% 0.20/0.44  cnf(c_0_108, negated_conjecture, (v1_funct_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_82]), c_0_36]), c_0_69]), c_0_81])])).
% 0.20/0.44  cnf(c_0_109, negated_conjecture, (v1_relat_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_79]), c_0_81])])).
% 0.20/0.44  cnf(c_0_110, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 0.20/0.44  cnf(c_0_111, plain, (m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_44, c_0_99])).
% 0.20/0.44  cnf(c_0_112, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.20/0.44  cnf(c_0_113, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_100])).
% 0.20/0.44  cnf(c_0_114, negated_conjecture, (v1_relat_1(k2_funct_1(esk6_0))|k2_relset_1(esk4_0,k2_relat_1(esk6_0),esk6_0)!=k2_relat_1(esk6_0)|~v2_funct_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_101]), c_0_102]), c_0_51])])).
% 0.20/0.44  cnf(c_0_115, negated_conjecture, (esk4_0=k1_xboole_0|r2_relset_1(esk4_0,esk4_0,k6_relat_1(esk4_0),esk6_0)|~v1_funct_1(k6_relat_1(esk4_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_89]), c_0_34])]), c_0_105])).
% 0.20/0.44  cnf(c_0_116, negated_conjecture, (v1_funct_1(k6_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_45]), c_0_108]), c_0_109]), c_0_36]), c_0_69]), c_0_46])])).
% 0.20/0.44  cnf(c_0_117, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_110, c_0_98])).
% 0.20/0.44  cnf(c_0_118, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k1_xboole_0))|~v1_funct_1(k6_relat_1(X1))|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_90]), c_0_92])])).
% 0.20/0.44  cnf(c_0_119, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_112, c_0_113])).
% 0.20/0.44  cnf(c_0_120, negated_conjecture, (v1_funct_1(k5_relat_1(esk6_0,X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_49]), c_0_51])])).
% 0.20/0.44  cnf(c_0_121, negated_conjecture, (v1_relat_1(k2_funct_1(esk6_0))|~v2_funct_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_79]), c_0_101])])).
% 0.20/0.44  cnf(c_0_122, negated_conjecture, (v1_funct_1(k2_funct_1(esk6_0))|~v2_funct_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_102]), c_0_51]), c_0_101])])).
% 0.20/0.44  cnf(c_0_123, negated_conjecture, (~r2_relset_1(esk4_0,esk4_0,esk6_0,k6_partfun1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.44  cnf(c_0_124, negated_conjecture, (esk4_0=k1_xboole_0|r2_relset_1(esk4_0,esk4_0,k6_relat_1(esk4_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_115, c_0_116])])).
% 0.20/0.44  cnf(c_0_125, negated_conjecture, (r2_relset_1(esk4_0,esk4_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[c_0_40, c_0_68])).
% 0.20/0.44  cnf(c_0_126, plain, (k6_relat_1(X1)=k1_xboole_0|~v1_funct_1(k6_relat_1(X1))|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_118]), c_0_119])])).
% 0.20/0.44  cnf(c_0_127, negated_conjecture, (v1_funct_1(k6_relat_1(esk4_0))|~v2_funct_1(esk6_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_107]), c_0_65]), c_0_51]), c_0_66])]), c_0_121]), c_0_122])).
% 0.20/0.44  cnf(c_0_128, negated_conjecture, (~r2_relset_1(esk4_0,esk4_0,esk6_0,k6_relat_1(esk4_0))), inference(rw,[status(thm)],[c_0_123, c_0_71])).
% 0.20/0.44  cnf(c_0_129, negated_conjecture, (k6_relat_1(esk4_0)=esk6_0|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_124]), c_0_49]), c_0_89])])).
% 0.20/0.44  cnf(c_0_130, negated_conjecture, (esk4_0=k1_xboole_0|r2_relset_1(esk4_0,esk4_0,esk6_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_68]), c_0_50]), c_0_125]), c_0_51]), c_0_49])])).
% 0.20/0.44  cnf(c_0_131, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.20/0.44  cnf(c_0_132, negated_conjecture, (k6_relat_1(esk4_0)=k1_xboole_0|~v2_funct_1(esk6_0)|~r1_tarski(esk4_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_126, c_0_127])).
% 0.20/0.44  cnf(c_0_133, negated_conjecture, (k2_zfmisc_1(esk4_0,k2_relat_1(esk6_0))=esk6_0|~m1_subset_1(k2_zfmisc_1(esk4_0,k2_relat_1(esk6_0)),k1_zfmisc_1(esk6_0))), inference(spm,[status(thm)],[c_0_117, c_0_101])).
% 0.20/0.44  cnf(c_0_134, negated_conjecture, (esk4_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_129]), c_0_130])).
% 0.20/0.44  cnf(c_0_135, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_131])).
% 0.20/0.44  cnf(c_0_136, plain, (v2_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.20/0.44  cnf(c_0_137, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t81_relat_1])).
% 0.20/0.44  cnf(c_0_138, negated_conjecture, (~r2_relset_1(esk4_0,esk4_0,esk6_0,k1_xboole_0)|~v2_funct_1(esk6_0)|~r1_tarski(esk4_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_128, c_0_132])).
% 0.20/0.44  cnf(c_0_139, negated_conjecture, (esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_133, c_0_134]), c_0_135]), c_0_134]), c_0_135]), c_0_119])])).
% 0.20/0.44  cnf(c_0_140, plain, (v2_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_136, c_0_137])).
% 0.20/0.44  cnf(c_0_141, plain, (r2_relset_1(X3,X4,X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.44  cnf(c_0_142, negated_conjecture, (~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_138, c_0_134]), c_0_134]), c_0_134]), c_0_113])]), c_0_139]), c_0_139]), c_0_140])])).
% 0.20/0.44  cnf(c_0_143, plain, (r2_relset_1(X1,X2,X3,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_141])).
% 0.20/0.44  cnf(c_0_144, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142, c_0_143]), c_0_135]), c_0_119])]), ['proof']).
% 0.20/0.44  # SZS output end CNFRefutation
% 0.20/0.44  # Proof object total steps             : 145
% 0.20/0.44  # Proof object clause steps            : 99
% 0.20/0.44  # Proof object formula steps           : 46
% 0.20/0.44  # Proof object conjectures             : 49
% 0.20/0.44  # Proof object clause conjectures      : 46
% 0.20/0.44  # Proof object formula conjectures     : 3
% 0.20/0.44  # Proof object initial clauses used    : 40
% 0.20/0.44  # Proof object initial formulas used   : 23
% 0.20/0.44  # Proof object generating inferences   : 48
% 0.20/0.44  # Proof object simplifying inferences  : 122
% 0.20/0.44  # Training examples: 0 positive, 0 negative
% 0.20/0.44  # Parsed axioms                        : 24
% 0.20/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.44  # Initial clauses                      : 56
% 0.20/0.44  # Removed in clause preprocessing      : 2
% 0.20/0.44  # Initial clauses in saturation        : 54
% 0.20/0.44  # Processed clauses                    : 677
% 0.20/0.44  # ...of these trivial                  : 22
% 0.20/0.44  # ...subsumed                          : 227
% 0.20/0.44  # ...remaining for further processing  : 428
% 0.20/0.44  # Other redundant clauses eliminated   : 13
% 0.20/0.44  # Clauses deleted for lack of memory   : 0
% 0.20/0.44  # Backward-subsumed                    : 28
% 0.20/0.44  # Backward-rewritten                   : 188
% 0.20/0.44  # Generated clauses                    : 1562
% 0.20/0.44  # ...of the previous two non-trivial   : 1291
% 0.20/0.44  # Contextual simplify-reflections      : 37
% 0.20/0.44  # Paramodulations                      : 1533
% 0.20/0.44  # Factorizations                       : 16
% 0.20/0.44  # Equation resolutions                 : 13
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
% 0.20/0.44  # Current number of processed clauses  : 154
% 0.20/0.44  #    Positive orientable unit clauses  : 23
% 0.20/0.44  #    Positive unorientable unit clauses: 0
% 0.20/0.44  #    Negative unit clauses             : 1
% 0.20/0.44  #    Non-unit-clauses                  : 130
% 0.20/0.44  # Current number of unprocessed clauses: 715
% 0.20/0.44  # ...number of literals in the above   : 3770
% 0.20/0.44  # Current number of archived formulas  : 0
% 0.20/0.44  # Current number of archived clauses   : 270
% 0.20/0.44  # Clause-clause subsumption calls (NU) : 14882
% 0.20/0.44  # Rec. Clause-clause subsumption calls : 4136
% 0.20/0.44  # Non-unit clause-clause subsumptions  : 290
% 0.20/0.44  # Unit Clause-clause subsumption calls : 625
% 0.20/0.44  # Rewrite failures with RHS unbound    : 0
% 0.20/0.44  # BW rewrite match attempts            : 28
% 0.20/0.44  # BW rewrite match successes           : 8
% 0.20/0.44  # Condensation attempts                : 0
% 0.20/0.44  # Condensation successes               : 0
% 0.20/0.44  # Termbank termtop insertions          : 41208
% 0.20/0.44  
% 0.20/0.44  # -------------------------------------------------
% 0.20/0.44  # User time                : 0.098 s
% 0.20/0.44  # System time              : 0.007 s
% 0.20/0.44  # Total time               : 0.104 s
% 0.20/0.44  # Maximum resident set size: 1612 pages
%------------------------------------------------------------------------------
