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
% DateTime   : Thu Dec  3 11:05:47 EST 2020

% Result     : Theorem 0.54s
% Output     : CNFRefutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  219 (9009 expanded)
%              Number of clauses        :  158 (3388 expanded)
%              Number of leaves         :   30 (2301 expanded)
%              Depth                    :   19
%              Number of atoms          :  797 (45114 expanded)
%              Number of equality atoms :  170 (3338 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   70 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1) )
     => ( v2_funct_2(X2,X1)
      <=> k2_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

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

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

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

fof(t48_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(k5_relat_1(X2,X1))
              & k2_relat_1(X2) = k1_relat_1(X1) )
           => ( v2_funct_1(X2)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

fof(t61_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
          & k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(t52_funct_1,axiom,(
    ! [X1] : v2_funct_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

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

fof(t29_relset_1,axiom,(
    ! [X1] : m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

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

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(redefinition_k4_relset_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k4_relset_1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(cc3_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_funct_1)).

fof(c_0_30,plain,(
    ! [X50,X51] :
      ( ( ~ v2_funct_2(X51,X50)
        | k2_relat_1(X51) = X50
        | ~ v1_relat_1(X51)
        | ~ v5_relat_1(X51,X50) )
      & ( k2_relat_1(X51) != X50
        | v2_funct_2(X51,X50)
        | ~ v1_relat_1(X51)
        | ~ v5_relat_1(X51,X50) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).

fof(c_0_31,plain,(
    ! [X33,X34,X35] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | k1_relset_1(X33,X34,X35) = k1_relat_1(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_32,plain,(
    ! [X81,X82] :
      ( ~ v1_funct_1(X82)
      | ~ v1_funct_2(X82,X81,X81)
      | ~ m1_subset_1(X82,k1_zfmisc_1(k2_zfmisc_1(X81,X81)))
      | k1_relset_1(X81,X81,X82) = X81 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_funct_2])])).

fof(c_0_33,negated_conjecture,(
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

cnf(c_0_34,plain,
    ( v2_funct_2(X1,X2)
    | k2_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_35,plain,(
    ! [X26] :
      ( ( k2_relat_1(X26) = k1_relat_1(k2_funct_1(X26))
        | ~ v2_funct_1(X26)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( k1_relat_1(X26) = k2_relat_1(k2_funct_1(X26))
        | ~ v2_funct_1(X26)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

cnf(c_0_36,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( k1_relset_1(X2,X2,X1) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_38,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk4_0,esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk4_0,esk4_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))
    & r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0),esk5_0)
    & v2_funct_1(esk5_0)
    & ~ r2_relset_1(esk4_0,esk4_0,esk6_0,k6_partfun1(esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_33])])])).

fof(c_0_39,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X14)
      | ~ m1_subset_1(X15,k1_zfmisc_1(X14))
      | v1_relat_1(X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_40,plain,(
    ! [X18,X19] : v1_relat_1(k2_zfmisc_1(X18,X19)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_41,plain,
    ( v2_funct_2(X1,k2_relat_1(X1))
    | ~ v5_relat_1(X1,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( X1 = k1_relat_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_2(esk5_0,esk4_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_49,plain,(
    ! [X23,X24] :
      ( ( v2_funct_1(X24)
        | ~ v2_funct_1(k5_relat_1(X24,X23))
        | k2_relat_1(X24) != k1_relat_1(X23)
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( v2_funct_1(X23)
        | ~ v2_funct_1(k5_relat_1(X24,X23))
        | k2_relat_1(X24) != k1_relat_1(X23)
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_funct_1])])])])).

fof(c_0_50,plain,(
    ! [X27] :
      ( ( k5_relat_1(X27,k2_funct_1(X27)) = k6_relat_1(k1_relat_1(X27))
        | ~ v2_funct_1(X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( k5_relat_1(k2_funct_1(X27),X27) = k6_relat_1(k2_relat_1(X27))
        | ~ v2_funct_1(X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).

fof(c_0_51,plain,(
    ! [X25] : v2_funct_1(k6_relat_1(X25)) ),
    inference(variable_rename,[status(thm)],[t52_funct_1])).

cnf(c_0_52,plain,
    ( v2_funct_2(k2_funct_1(X1),k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v5_relat_1(k2_funct_1(X1),k1_relat_1(X1))
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_53,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_46])])).

cnf(c_0_54,negated_conjecture,
    ( v2_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_55,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_44]),c_0_48])])).

fof(c_0_56,plain,(
    ! [X16,X17] :
      ( ( ~ v5_relat_1(X17,X16)
        | r1_tarski(k2_relat_1(X17),X16)
        | ~ v1_relat_1(X17) )
      & ( ~ r1_tarski(k2_relat_1(X17),X16)
        | v5_relat_1(X17,X16)
        | ~ v1_relat_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

fof(c_0_57,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_58,plain,(
    ! [X77,X78,X79] :
      ( ( v1_funct_1(k2_funct_1(X79))
        | ~ v2_funct_1(X79)
        | k2_relset_1(X77,X78,X79) != X78
        | ~ v1_funct_1(X79)
        | ~ v1_funct_2(X79,X77,X78)
        | ~ m1_subset_1(X79,k1_zfmisc_1(k2_zfmisc_1(X77,X78))) )
      & ( v1_funct_2(k2_funct_1(X79),X78,X77)
        | ~ v2_funct_1(X79)
        | k2_relset_1(X77,X78,X79) != X78
        | ~ v1_funct_1(X79)
        | ~ v1_funct_2(X79,X77,X78)
        | ~ m1_subset_1(X79,k1_zfmisc_1(k2_zfmisc_1(X77,X78))) )
      & ( m1_subset_1(k2_funct_1(X79),k1_zfmisc_1(k2_zfmisc_1(X78,X77)))
        | ~ v2_funct_1(X79)
        | k2_relset_1(X77,X78,X79) != X78
        | ~ v1_funct_1(X79)
        | ~ v1_funct_2(X79,X77,X78)
        | ~ m1_subset_1(X79,k1_zfmisc_1(k2_zfmisc_1(X77,X78))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).

fof(c_0_59,plain,(
    ! [X36,X37,X38] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
      | k2_relset_1(X36,X37,X38) = k2_relat_1(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_60,plain,(
    ! [X80] :
      ( ( v1_funct_1(X80)
        | ~ v1_relat_1(X80)
        | ~ v1_funct_1(X80) )
      & ( v1_funct_2(X80,k1_relat_1(X80),k2_relat_1(X80))
        | ~ v1_relat_1(X80)
        | ~ v1_funct_1(X80) )
      & ( m1_subset_1(X80,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X80),k2_relat_1(X80))))
        | ~ v1_relat_1(X80)
        | ~ v1_funct_1(X80) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

fof(c_0_61,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X28)
      | ~ v1_funct_1(X28)
      | ~ v1_relat_1(X29)
      | ~ v1_funct_1(X29)
      | ~ v2_funct_1(X28)
      | k2_relat_1(X29) != k1_relat_1(X28)
      | k5_relat_1(X29,X28) != k6_relat_1(k2_relat_1(X28))
      | X29 = k2_funct_1(X28) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_funct_1])])])).

cnf(c_0_62,plain,
    ( v2_funct_1(X1)
    | ~ v2_funct_1(k5_relat_1(X2,X1))
    | k2_relat_1(X2) != k1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_63,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_64,plain,
    ( v2_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_65,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_66,plain,
    ( k2_relat_1(X1) = X2
    | ~ v2_funct_2(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_67,negated_conjecture,
    ( v2_funct_2(k2_funct_1(esk5_0),esk4_0)
    | ~ v5_relat_1(k2_funct_1(esk5_0),esk4_0)
    | ~ v1_relat_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_46]),c_0_55])])).

cnf(c_0_68,plain,
    ( v5_relat_1(X1,X2)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_70,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_71,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_72,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_73,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

fof(c_0_74,plain,(
    ! [X9] : r1_tarski(k1_xboole_0,X9) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_75,plain,
    ( X2 = k2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | k2_relat_1(X2) != k1_relat_1(X1)
    | k5_relat_1(X2,X1) != k6_relat_1(k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_76,plain,
    ( v2_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])]),c_0_65])).

cnf(c_0_77,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk5_0)) = esk4_0
    | ~ v5_relat_1(k2_funct_1(esk5_0),esk4_0)
    | ~ v1_relat_1(k2_funct_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_78,plain,
    ( v5_relat_1(k2_funct_1(X1),X2)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_68,c_0_42])).

cnf(c_0_79,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_69])).

cnf(c_0_80,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_2(X1,X2,k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(X1)))) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71])])).

cnf(c_0_81,negated_conjecture,
    ( v1_funct_2(esk5_0,esk4_0,k2_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_53]),c_0_46]),c_0_55])])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_relat_1(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_53]),c_0_46]),c_0_55])])).

fof(c_0_83,plain,(
    ! [X12,X13] :
      ( ( ~ m1_subset_1(X12,k1_zfmisc_1(X13))
        | r1_tarski(X12,X13) )
      & ( ~ r1_tarski(X12,X13)
        | m1_subset_1(X12,k1_zfmisc_1(X13)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_84,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_85,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

fof(c_0_86,plain,(
    ! [X10,X11] :
      ( ( k2_zfmisc_1(X10,X11) != k1_xboole_0
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0 )
      & ( X10 != k1_xboole_0
        | k2_zfmisc_1(X10,X11) = k1_xboole_0 )
      & ( X11 != k1_xboole_0
        | k2_zfmisc_1(X10,X11) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_87,plain,
    ( k2_funct_1(k2_funct_1(X1)) = X1
    | k6_relat_1(k2_relat_1(k2_funct_1(X1))) != k6_relat_1(k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_63]),c_0_76]),c_0_65])).

cnf(c_0_88,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk5_0)) = esk4_0
    | ~ v1_relat_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_54]),c_0_46]),c_0_55]),c_0_53]),c_0_79])])).

cnf(c_0_89,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_54]),c_0_46]),c_0_82])])).

cnf(c_0_90,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_91,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_92,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_93,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

fof(c_0_94,plain,(
    ! [X30,X31,X32] :
      ( ( v4_relat_1(X32,X30)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( v5_relat_1(X32,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_95,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

fof(c_0_96,plain,(
    ! [X45,X46,X47,X48] :
      ( ( ~ r2_relset_1(X45,X46,X47,X48)
        | X47 = X48
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) )
      & ( X47 != X48
        | r2_relset_1(X45,X46,X47,X48)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

fof(c_0_97,plain,(
    ! [X52,X53,X54,X55,X56,X57] :
      ( ( v1_funct_1(k1_partfun1(X52,X53,X54,X55,X56,X57))
        | ~ v1_funct_1(X56)
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))
        | ~ v1_funct_1(X57)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X54,X55))) )
      & ( m1_subset_1(k1_partfun1(X52,X53,X54,X55,X56,X57),k1_zfmisc_1(k2_zfmisc_1(X52,X55)))
        | ~ v1_funct_1(X56)
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))
        | ~ v1_funct_1(X57)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X54,X55))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

fof(c_0_98,plain,(
    ! [X58,X59,X60,X61,X62,X63] :
      ( ~ v1_funct_1(X62)
      | ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X58,X59)))
      | ~ v1_funct_1(X63)
      | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))
      | k1_partfun1(X58,X59,X60,X61,X62,X63) = k5_relat_1(X62,X63) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

cnf(c_0_99,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_100,negated_conjecture,
    ( k2_funct_1(k2_funct_1(esk5_0)) = esk5_0
    | ~ v1_relat_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_53]),c_0_54]),c_0_89]),c_0_46]),c_0_55])])).

cnf(c_0_101,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),X2)))
    | ~ v1_funct_2(X1,X2,k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(X1)))) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_71])])).

cnf(c_0_102,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_84,c_0_91])).

fof(c_0_103,plain,(
    ! [X49] : m1_subset_1(k6_relat_1(X49),k1_zfmisc_1(k2_zfmisc_1(X49,X49))) ),
    inference(variable_rename,[status(thm)],[t29_relset_1])).

cnf(c_0_104,plain,
    ( X1 = k2_relat_1(X2)
    | ~ v5_relat_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k2_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_92])).

cnf(c_0_105,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | ~ v5_relat_1(X1,k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_93,c_0_92])).

cnf(c_0_106,negated_conjecture,
    ( v5_relat_1(k2_funct_1(esk5_0),X1)
    | ~ v1_relat_1(k2_funct_1(esk5_0))
    | ~ r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_88])).

cnf(c_0_107,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_65])).

cnf(c_0_108,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_109,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_95])).

cnf(c_0_110,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_111,negated_conjecture,
    ( r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_112,plain,
    ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_113,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_114,negated_conjecture,
    ( k6_relat_1(k2_relat_1(k2_funct_1(esk5_0))) = k5_relat_1(esk5_0,k2_funct_1(esk5_0))
    | ~ v2_funct_1(k2_funct_1(esk5_0))
    | ~ v1_relat_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_89])])).

cnf(c_0_115,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_funct_2(X1,X2,k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(X1)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_101]),c_0_48])])).

cnf(c_0_116,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_102,c_0_91])).

cnf(c_0_117,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_118,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_119,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_120,plain,
    ( k2_relat_1(X1) = k2_relat_1(X2)
    | ~ v5_relat_1(X2,k2_relat_1(X1))
    | ~ v5_relat_1(X1,k2_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_92])).

cnf(c_0_121,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk5_0)) = k1_xboole_0
    | ~ v1_relat_1(k2_funct_1(esk5_0))
    | ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_122,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk5_0),esk4_0)))
    | ~ v1_relat_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_88]),c_0_54]),c_0_89]),c_0_46]),c_0_55])])).

cnf(c_0_123,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

fof(c_0_124,plain,(
    ! [X68,X69,X70,X71,X72,X73] :
      ( ( ~ v2_funct_1(X70)
        | ~ v1_funct_1(X72)
        | ~ v1_funct_2(X72,X71,X68)
        | ~ m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X71,X68)))
        | ~ v1_funct_1(X73)
        | ~ v1_funct_2(X73,X71,X68)
        | ~ m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(X71,X68)))
        | ~ r2_relset_1(X71,X69,k1_partfun1(X71,X68,X68,X69,X72,X70),k1_partfun1(X71,X68,X68,X69,X73,X70))
        | r2_relset_1(X71,X68,X72,X73)
        | X68 = k1_xboole_0
        | X69 = k1_xboole_0
        | ~ v1_funct_1(X70)
        | ~ v1_funct_2(X70,X68,X69)
        | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X68,X69))) )
      & ( v1_funct_1(esk2_3(X68,X69,X70))
        | v2_funct_1(X70)
        | X68 = k1_xboole_0
        | X69 = k1_xboole_0
        | ~ v1_funct_1(X70)
        | ~ v1_funct_2(X70,X68,X69)
        | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X68,X69))) )
      & ( v1_funct_2(esk2_3(X68,X69,X70),esk1_3(X68,X69,X70),X68)
        | v2_funct_1(X70)
        | X68 = k1_xboole_0
        | X69 = k1_xboole_0
        | ~ v1_funct_1(X70)
        | ~ v1_funct_2(X70,X68,X69)
        | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X68,X69))) )
      & ( m1_subset_1(esk2_3(X68,X69,X70),k1_zfmisc_1(k2_zfmisc_1(esk1_3(X68,X69,X70),X68)))
        | v2_funct_1(X70)
        | X68 = k1_xboole_0
        | X69 = k1_xboole_0
        | ~ v1_funct_1(X70)
        | ~ v1_funct_2(X70,X68,X69)
        | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X68,X69))) )
      & ( v1_funct_1(esk3_3(X68,X69,X70))
        | v2_funct_1(X70)
        | X68 = k1_xboole_0
        | X69 = k1_xboole_0
        | ~ v1_funct_1(X70)
        | ~ v1_funct_2(X70,X68,X69)
        | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X68,X69))) )
      & ( v1_funct_2(esk3_3(X68,X69,X70),esk1_3(X68,X69,X70),X68)
        | v2_funct_1(X70)
        | X68 = k1_xboole_0
        | X69 = k1_xboole_0
        | ~ v1_funct_1(X70)
        | ~ v1_funct_2(X70,X68,X69)
        | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X68,X69))) )
      & ( m1_subset_1(esk3_3(X68,X69,X70),k1_zfmisc_1(k2_zfmisc_1(esk1_3(X68,X69,X70),X68)))
        | v2_funct_1(X70)
        | X68 = k1_xboole_0
        | X69 = k1_xboole_0
        | ~ v1_funct_1(X70)
        | ~ v1_funct_2(X70,X68,X69)
        | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X68,X69))) )
      & ( r2_relset_1(esk1_3(X68,X69,X70),X69,k1_partfun1(esk1_3(X68,X69,X70),X68,X68,X69,esk2_3(X68,X69,X70),X70),k1_partfun1(esk1_3(X68,X69,X70),X68,X68,X69,esk3_3(X68,X69,X70),X70))
        | v2_funct_1(X70)
        | X68 = k1_xboole_0
        | X69 = k1_xboole_0
        | ~ v1_funct_1(X70)
        | ~ v1_funct_2(X70,X68,X69)
        | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X68,X69))) )
      & ( ~ r2_relset_1(esk1_3(X68,X69,X70),X68,esk2_3(X68,X69,X70),esk3_3(X68,X69,X70))
        | v2_funct_1(X70)
        | X68 = k1_xboole_0
        | X69 = k1_xboole_0
        | ~ v1_funct_1(X70)
        | ~ v1_funct_2(X70,X68,X69)
        | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X68,X69))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_funct_2])])])])])).

cnf(c_0_125,negated_conjecture,
    ( k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0) = esk5_0
    | ~ m1_subset_1(k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_44])])).

cnf(c_0_126,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_127,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_128,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_129,plain,(
    ! [X65,X66,X67] :
      ( ( r2_relset_1(X65,X66,k4_relset_1(X65,X65,X65,X66,k6_partfun1(X65),X67),X67)
        | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X66))) )
      & ( r2_relset_1(X65,X66,k4_relset_1(X65,X66,X66,X66,X67,k6_partfun1(X66)),X67)
        | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X66))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_2])])])).

fof(c_0_130,plain,(
    ! [X64] : k6_partfun1(X64) = k6_relat_1(X64) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

cnf(c_0_131,plain,
    ( v1_funct_1(k5_relat_1(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(spm,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_132,negated_conjecture,
    ( k5_relat_1(esk5_0,k2_funct_1(esk5_0)) = k6_relat_1(esk4_0)
    | ~ v2_funct_1(k2_funct_1(esk5_0))
    | ~ v1_relat_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_42]),c_0_53]),c_0_54]),c_0_46]),c_0_55])])).

cnf(c_0_133,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_82]),c_0_81]),c_0_54]),c_0_46])])).

cnf(c_0_134,plain,
    ( k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)) = X1
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_116,c_0_73])).

cnf(c_0_135,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_117])).

cnf(c_0_136,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_118,c_0_85])).

fof(c_0_137,plain,(
    ! [X20] :
      ( k1_relat_1(k6_relat_1(X20)) = X20
      & k2_relat_1(k6_relat_1(X20)) = X20 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_138,plain,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_91])).

cnf(c_0_139,plain,
    ( m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_119,c_0_109])).

cnf(c_0_140,negated_conjecture,
    ( k2_relat_1(X1) = esk4_0
    | ~ v5_relat_1(k2_funct_1(esk5_0),k2_relat_1(X1))
    | ~ v5_relat_1(X1,esk4_0)
    | ~ v1_relat_1(k2_funct_1(esk5_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_120,c_0_88])).

cnf(c_0_141,negated_conjecture,
    ( v5_relat_1(k2_funct_1(esk5_0),X1)
    | ~ v1_relat_1(k2_funct_1(esk5_0))
    | ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_121]),c_0_85])])).

cnf(c_0_142,negated_conjecture,
    ( k2_funct_1(esk5_0) = k2_zfmisc_1(k2_relat_1(esk5_0),esk4_0)
    | ~ v1_relat_1(k2_funct_1(esk5_0))
    | ~ m1_subset_1(k2_zfmisc_1(k2_relat_1(esk5_0),esk4_0),k1_zfmisc_1(k2_funct_1(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_116,c_0_122])).

cnf(c_0_143,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_105,c_0_123])).

cnf(c_0_144,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_124])).

cnf(c_0_145,negated_conjecture,
    ( k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_126]),c_0_46]),c_0_127]),c_0_44]),c_0_128])])).

cnf(c_0_146,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_147,plain,
    ( r2_relset_1(X1,X2,k4_relset_1(X1,X1,X1,X2,k6_partfun1(X1),X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_129])).

cnf(c_0_148,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_130])).

fof(c_0_149,plain,(
    ! [X39,X40,X41,X42,X43,X44] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
      | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
      | k4_relset_1(X39,X40,X41,X42,X43,X44) = k5_relat_1(X43,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_relset_1])])).

cnf(c_0_150,negated_conjecture,
    ( v1_funct_1(k6_relat_1(esk4_0))
    | ~ v2_funct_1(k2_funct_1(esk5_0))
    | ~ v1_relat_1(k2_funct_1(esk5_0))
    | ~ m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_132]),c_0_89]),c_0_46])])).

cnf(c_0_151,negated_conjecture,
    ( v2_funct_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_133]),c_0_54]),c_0_89]),c_0_46]),c_0_55])])).

fof(c_0_152,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X21)
      | ~ v1_funct_1(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(X21))
      | v1_funct_1(X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_funct_1])])])).

cnf(c_0_153,negated_conjecture,
    ( k2_funct_1(esk5_0) = k1_xboole_0
    | ~ v1_relat_1(k2_funct_1(esk5_0))
    | ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_121]),c_0_135]),c_0_89]),c_0_135]),c_0_136])])).

cnf(c_0_154,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_137])).

cnf(c_0_155,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_138,c_0_139])).

cnf(c_0_156,negated_conjecture,
    ( k2_relat_1(X1) = esk4_0
    | ~ v5_relat_1(X1,esk4_0)
    | ~ v1_relat_1(k2_funct_1(esk5_0))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_140,c_0_141])).

cnf(c_0_157,negated_conjecture,
    ( k2_funct_1(esk5_0) = k1_xboole_0
    | ~ v1_relat_1(k2_funct_1(esk5_0))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_143]),c_0_109]),c_0_109]),c_0_136]),c_0_55])])).

cnf(c_0_158,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_relset_1(esk4_0,esk4_0,X1,esk6_0)
    | ~ v1_funct_2(X1,esk4_0,esk4_0)
    | ~ r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,X1,esk5_0),esk5_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144,c_0_145]),c_0_146]),c_0_45]),c_0_54]),c_0_127]),c_0_46]),c_0_128]),c_0_44])])).

cnf(c_0_159,plain,
    ( r2_relset_1(X1,X2,k4_relset_1(X1,X1,X1,X2,k6_relat_1(X1),X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_147,c_0_148])).

cnf(c_0_160,plain,
    ( k4_relset_1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_149])).

cnf(c_0_161,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_137])).

cnf(c_0_162,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_119]),c_0_48])])).

cnf(c_0_163,negated_conjecture,
    ( v1_funct_1(k6_relat_1(esk4_0))
    | ~ m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_150,c_0_133])]),c_0_151])])).

cnf(c_0_164,plain,
    ( v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_152])).

cnf(c_0_165,negated_conjecture,
    ( k2_funct_1(esk5_0) = k1_xboole_0
    | ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_153,c_0_133])])).

cnf(c_0_166,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_154,c_0_155])).

cnf(c_0_167,plain,
    ( X1 = k2_funct_1(X2)
    | k5_relat_1(X1,X2) != k1_xboole_0
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_143]),c_0_155])).

cnf(c_0_168,negated_conjecture,
    ( k5_relat_1(esk6_0,esk5_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_145]),c_0_46]),c_0_127]),c_0_44]),c_0_128])])).

cnf(c_0_169,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_128]),c_0_48])])).

cnf(c_0_170,negated_conjecture,
    ( k2_relat_1(X1) = esk4_0
    | ~ v5_relat_1(X1,esk4_0)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_156,c_0_133])])).

cnf(c_0_171,negated_conjecture,
    ( v5_relat_1(esk6_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_108,c_0_128])).

cnf(c_0_172,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v5_relat_1(k2_funct_1(X1),X2)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_92,c_0_42])).

cnf(c_0_173,negated_conjecture,
    ( k2_funct_1(esk5_0) = k1_xboole_0
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_157,c_0_133])])).

cnf(c_0_174,plain,
    ( v5_relat_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_108,c_0_136])).

cnf(c_0_175,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_135])).

cnf(c_0_176,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_relset_1(esk4_0,esk4_0,X1,esk6_0)
    | ~ v1_funct_2(X1,esk4_0,esk4_0)
    | ~ r2_relset_1(esk4_0,esk4_0,k5_relat_1(X1,esk5_0),esk5_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_158,c_0_113]),c_0_46]),c_0_44])])).

cnf(c_0_177,plain,
    ( r2_relset_1(X1,X2,k5_relat_1(k6_relat_1(X1),X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_159,c_0_160]),c_0_119])])).

cnf(c_0_178,plain,
    ( v1_funct_2(k6_relat_1(X1),X1,X1)
    | ~ v1_funct_1(k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_161]),c_0_154]),c_0_162])])).

cnf(c_0_179,negated_conjecture,
    ( v1_funct_1(k6_relat_1(esk4_0))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_163,c_0_73]),c_0_89]),c_0_133])])).

cnf(c_0_180,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_164,c_0_136])).

cnf(c_0_181,negated_conjecture,
    ( k5_relat_1(esk5_0,k2_funct_1(esk5_0)) = k1_xboole_0
    | ~ v2_funct_1(k2_funct_1(esk5_0))
    | ~ v1_relat_1(k2_funct_1(esk5_0))
    | ~ m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_143]),c_0_155])).

cnf(c_0_182,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_72]),c_0_73])).

cnf(c_0_183,negated_conjecture,
    ( k2_relat_1(esk5_0) = k1_xboole_0
    | ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_165]),c_0_166]),c_0_54]),c_0_46]),c_0_55])])).

cnf(c_0_184,negated_conjecture,
    ( k2_funct_1(esk5_0) = esk6_0
    | k2_relat_1(esk6_0) != esk4_0
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_167,c_0_168]),c_0_53]),c_0_54]),c_0_127]),c_0_46]),c_0_169]),c_0_55])]),c_0_138])).

cnf(c_0_185,negated_conjecture,
    ( k2_relat_1(esk6_0) = esk4_0
    | ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_170,c_0_171]),c_0_169])])).

cnf(c_0_186,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_172,c_0_173]),c_0_53]),c_0_54]),c_0_46]),c_0_174]),c_0_175]),c_0_55])])).

cnf(c_0_187,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_relset_1(esk4_0,esk4_0,k6_relat_1(esk4_0),esk6_0)
    | ~ v1_funct_1(k6_relat_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_176,c_0_177]),c_0_119]),c_0_44])]),c_0_178])).

cnf(c_0_188,negated_conjecture,
    ( v1_funct_1(k6_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_179,c_0_73]),c_0_46]),c_0_55])])).

cnf(c_0_189,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_161,c_0_155])).

cnf(c_0_190,plain,
    ( v2_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_155])).

cnf(c_0_191,negated_conjecture,
    ( v1_funct_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_180,c_0_169]),c_0_127])])).

cnf(c_0_192,negated_conjecture,
    ( k6_relat_1(esk4_0) = k1_xboole_0
    | ~ v2_funct_1(k2_funct_1(esk5_0))
    | ~ v1_relat_1(k2_funct_1(esk5_0))
    | ~ m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_181]),c_0_53]),c_0_54]),c_0_46]),c_0_55])])).

cnf(c_0_193,plain,
    ( k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1))) = k2_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1))),k1_zfmisc_1(k2_funct_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_107]),c_0_182])).

cnf(c_0_194,negated_conjecture,
    ( k2_relat_1(esk5_0) = k1_xboole_0
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_183,c_0_91])).

cnf(c_0_195,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | k2_relat_1(esk6_0) != esk4_0
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_157,c_0_184]),c_0_169])])).

cnf(c_0_196,negated_conjecture,
    ( k2_relat_1(esk6_0) = esk4_0
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_185,c_0_186])).

cnf(c_0_197,negated_conjecture,
    ( ~ r2_relset_1(esk4_0,esk4_0,esk6_0,k6_partfun1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_198,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_relset_1(esk4_0,esk4_0,k6_relat_1(esk4_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_187,c_0_188])])).

cnf(c_0_199,negated_conjecture,
    ( r2_relset_1(esk4_0,esk4_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_111,c_0_145])).

cnf(c_0_200,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k1_xboole_0,X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_189]),c_0_109]),c_0_190]),c_0_191]),c_0_135]),c_0_136])])).

cnf(c_0_201,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_166]),c_0_189]),c_0_191]),c_0_175])])).

cnf(c_0_202,negated_conjecture,
    ( k6_relat_1(esk4_0) = k1_xboole_0
    | ~ m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_192,c_0_133])]),c_0_151])])).

cnf(c_0_203,negated_conjecture,
    ( k2_funct_1(esk5_0) = k1_xboole_0
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_193,c_0_194]),c_0_109]),c_0_54]),c_0_46]),c_0_133]),c_0_55]),c_0_109]),c_0_136])])).

cnf(c_0_204,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_195,c_0_196])).

cnf(c_0_205,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_194]),c_0_53]),c_0_135]),c_0_46]),c_0_55])])).

cnf(c_0_206,negated_conjecture,
    ( ~ r2_relset_1(esk4_0,esk4_0,esk6_0,k6_relat_1(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_197,c_0_148])).

cnf(c_0_207,negated_conjecture,
    ( k6_relat_1(esk4_0) = esk6_0
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_198]),c_0_128]),c_0_119])])).

cnf(c_0_208,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_relset_1(esk4_0,esk4_0,esk6_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_158,c_0_145]),c_0_146]),c_0_199]),c_0_127]),c_0_128])])).

cnf(c_0_209,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_200,c_0_201])).

cnf(c_0_210,negated_conjecture,
    ( k6_relat_1(esk4_0) = k1_xboole_0
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_202,c_0_203]),c_0_136])])).

cnf(c_0_211,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_204,c_0_205])).

cnf(c_0_212,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_206,c_0_207]),c_0_208])).

cnf(c_0_213,plain,
    ( r2_relset_1(k1_xboole_0,X1,k5_relat_1(k1_xboole_0,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_177,c_0_155]),c_0_109])).

cnf(c_0_214,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_209]),c_0_136])])).

cnf(c_0_215,negated_conjecture,
    ( ~ r2_relset_1(esk4_0,esk4_0,esk6_0,k1_xboole_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_206,c_0_210])).

cnf(c_0_216,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_211,c_0_212]),c_0_136])])).

cnf(c_0_217,plain,
    ( r2_relset_1(k1_xboole_0,X1,k1_xboole_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_213,c_0_63]),c_0_166]),c_0_155]),c_0_214]),c_0_214]),c_0_136]),c_0_190]),c_0_191]),c_0_175])])).

cnf(c_0_218,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_215,c_0_212]),c_0_212]),c_0_212]),c_0_136])]),c_0_216]),c_0_217])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:32:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.54/0.71  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.54/0.71  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.54/0.71  #
% 0.54/0.71  # Preprocessing time       : 0.030 s
% 0.54/0.71  # Presaturation interreduction done
% 0.54/0.71  
% 0.54/0.71  # Proof found!
% 0.54/0.71  # SZS status Theorem
% 0.54/0.71  # SZS output start CNFRefutation
% 0.54/0.71  fof(d3_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v5_relat_1(X2,X1))=>(v2_funct_2(X2,X1)<=>k2_relat_1(X2)=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 0.54/0.71  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.54/0.71  fof(t67_funct_2, axiom, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>k1_relset_1(X1,X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 0.54/0.71  fof(t76_funct_2, conjecture, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>((r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X3,X2),X2)&v2_funct_1(X2))=>r2_relset_1(X1,X1,X3,k6_partfun1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_funct_2)).
% 0.54/0.71  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 0.54/0.71  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.54/0.71  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.54/0.71  fof(t48_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(k5_relat_1(X2,X1))&k2_relat_1(X2)=k1_relat_1(X1))=>(v2_funct_1(X2)&v2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_1)).
% 0.54/0.71  fof(t61_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))&k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 0.54/0.71  fof(t52_funct_1, axiom, ![X1]:v2_funct_1(k6_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 0.54/0.71  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 0.54/0.71  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.54/0.71  fof(t31_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 0.54/0.71  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.54/0.71  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 0.54/0.71  fof(t64_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(((v2_funct_1(X1)&k2_relat_1(X2)=k1_relat_1(X1))&k5_relat_1(X2,X1)=k6_relat_1(k2_relat_1(X1)))=>X2=k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 0.54/0.71  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.54/0.71  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.54/0.71  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.54/0.71  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.54/0.71  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.54/0.71  fof(dt_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))&m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 0.54/0.71  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 0.54/0.71  fof(t29_relset_1, axiom, ![X1]:m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 0.54/0.71  fof(t27_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&~((v2_funct_1(X3)<=>![X4, X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X4,X1))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X1))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X1))))=>(r2_relset_1(X4,X2,k1_partfun1(X4,X1,X1,X2,X5,X3),k1_partfun1(X4,X1,X1,X2,X6,X3))=>r2_relset_1(X4,X1,X5,X6))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_funct_2)).
% 0.54/0.71  fof(t23_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(r2_relset_1(X1,X2,k4_relset_1(X1,X1,X1,X2,k6_partfun1(X1),X3),X3)&r2_relset_1(X1,X2,k4_relset_1(X1,X2,X2,X2,X3,k6_partfun1(X2)),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_2)).
% 0.54/0.71  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.54/0.71  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.54/0.71  fof(redefinition_k4_relset_1, axiom, ![X1, X2, X3, X4, X5, X6]:((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k4_relset_1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 0.54/0.71  fof(cc3_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_funct_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_funct_1)).
% 0.54/0.71  fof(c_0_30, plain, ![X50, X51]:((~v2_funct_2(X51,X50)|k2_relat_1(X51)=X50|(~v1_relat_1(X51)|~v5_relat_1(X51,X50)))&(k2_relat_1(X51)!=X50|v2_funct_2(X51,X50)|(~v1_relat_1(X51)|~v5_relat_1(X51,X50)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).
% 0.54/0.71  fof(c_0_31, plain, ![X33, X34, X35]:(~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|k1_relset_1(X33,X34,X35)=k1_relat_1(X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.54/0.71  fof(c_0_32, plain, ![X81, X82]:(~v1_funct_1(X82)|~v1_funct_2(X82,X81,X81)|~m1_subset_1(X82,k1_zfmisc_1(k2_zfmisc_1(X81,X81)))|k1_relset_1(X81,X81,X82)=X81), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_funct_2])])).
% 0.54/0.71  fof(c_0_33, negated_conjecture, ~(![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>((r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X3,X2),X2)&v2_funct_1(X2))=>r2_relset_1(X1,X1,X3,k6_partfun1(X1)))))), inference(assume_negation,[status(cth)],[t76_funct_2])).
% 0.54/0.71  cnf(c_0_34, plain, (v2_funct_2(X1,X2)|k2_relat_1(X1)!=X2|~v1_relat_1(X1)|~v5_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.54/0.71  fof(c_0_35, plain, ![X26]:((k2_relat_1(X26)=k1_relat_1(k2_funct_1(X26))|~v2_funct_1(X26)|(~v1_relat_1(X26)|~v1_funct_1(X26)))&(k1_relat_1(X26)=k2_relat_1(k2_funct_1(X26))|~v2_funct_1(X26)|(~v1_relat_1(X26)|~v1_funct_1(X26)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.54/0.71  cnf(c_0_36, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.54/0.71  cnf(c_0_37, plain, (k1_relset_1(X2,X2,X1)=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.54/0.71  fof(c_0_38, negated_conjecture, (((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk4_0,esk4_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk4_0,esk4_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))))&((r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0),esk5_0)&v2_funct_1(esk5_0))&~r2_relset_1(esk4_0,esk4_0,esk6_0,k6_partfun1(esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_33])])])).
% 0.54/0.71  fof(c_0_39, plain, ![X14, X15]:(~v1_relat_1(X14)|(~m1_subset_1(X15,k1_zfmisc_1(X14))|v1_relat_1(X15))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.54/0.71  fof(c_0_40, plain, ![X18, X19]:v1_relat_1(k2_zfmisc_1(X18,X19)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.54/0.71  cnf(c_0_41, plain, (v2_funct_2(X1,k2_relat_1(X1))|~v5_relat_1(X1,k2_relat_1(X1))|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_34])).
% 0.54/0.71  cnf(c_0_42, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.54/0.71  cnf(c_0_43, plain, (X1=k1_relat_1(X2)|~v1_funct_2(X2,X1,X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.54/0.71  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.54/0.71  cnf(c_0_45, negated_conjecture, (v1_funct_2(esk5_0,esk4_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.54/0.71  cnf(c_0_46, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.54/0.71  cnf(c_0_47, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.54/0.71  cnf(c_0_48, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.54/0.71  fof(c_0_49, plain, ![X23, X24]:((v2_funct_1(X24)|(~v2_funct_1(k5_relat_1(X24,X23))|k2_relat_1(X24)!=k1_relat_1(X23))|(~v1_relat_1(X24)|~v1_funct_1(X24))|(~v1_relat_1(X23)|~v1_funct_1(X23)))&(v2_funct_1(X23)|(~v2_funct_1(k5_relat_1(X24,X23))|k2_relat_1(X24)!=k1_relat_1(X23))|(~v1_relat_1(X24)|~v1_funct_1(X24))|(~v1_relat_1(X23)|~v1_funct_1(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_funct_1])])])])).
% 0.54/0.71  fof(c_0_50, plain, ![X27]:((k5_relat_1(X27,k2_funct_1(X27))=k6_relat_1(k1_relat_1(X27))|~v2_funct_1(X27)|(~v1_relat_1(X27)|~v1_funct_1(X27)))&(k5_relat_1(k2_funct_1(X27),X27)=k6_relat_1(k2_relat_1(X27))|~v2_funct_1(X27)|(~v1_relat_1(X27)|~v1_funct_1(X27)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).
% 0.54/0.71  fof(c_0_51, plain, ![X25]:v2_funct_1(k6_relat_1(X25)), inference(variable_rename,[status(thm)],[t52_funct_1])).
% 0.54/0.71  cnf(c_0_52, plain, (v2_funct_2(k2_funct_1(X1),k1_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v5_relat_1(k2_funct_1(X1),k1_relat_1(X1))|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.54/0.71  cnf(c_0_53, negated_conjecture, (k1_relat_1(esk5_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_46])])).
% 0.54/0.71  cnf(c_0_54, negated_conjecture, (v2_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.54/0.71  cnf(c_0_55, negated_conjecture, (v1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_44]), c_0_48])])).
% 0.54/0.71  fof(c_0_56, plain, ![X16, X17]:((~v5_relat_1(X17,X16)|r1_tarski(k2_relat_1(X17),X16)|~v1_relat_1(X17))&(~r1_tarski(k2_relat_1(X17),X16)|v5_relat_1(X17,X16)|~v1_relat_1(X17))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.54/0.71  fof(c_0_57, plain, ![X7, X8]:(((r1_tarski(X7,X8)|X7!=X8)&(r1_tarski(X8,X7)|X7!=X8))&(~r1_tarski(X7,X8)|~r1_tarski(X8,X7)|X7=X8)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.54/0.71  fof(c_0_58, plain, ![X77, X78, X79]:(((v1_funct_1(k2_funct_1(X79))|(~v2_funct_1(X79)|k2_relset_1(X77,X78,X79)!=X78)|(~v1_funct_1(X79)|~v1_funct_2(X79,X77,X78)|~m1_subset_1(X79,k1_zfmisc_1(k2_zfmisc_1(X77,X78)))))&(v1_funct_2(k2_funct_1(X79),X78,X77)|(~v2_funct_1(X79)|k2_relset_1(X77,X78,X79)!=X78)|(~v1_funct_1(X79)|~v1_funct_2(X79,X77,X78)|~m1_subset_1(X79,k1_zfmisc_1(k2_zfmisc_1(X77,X78))))))&(m1_subset_1(k2_funct_1(X79),k1_zfmisc_1(k2_zfmisc_1(X78,X77)))|(~v2_funct_1(X79)|k2_relset_1(X77,X78,X79)!=X78)|(~v1_funct_1(X79)|~v1_funct_2(X79,X77,X78)|~m1_subset_1(X79,k1_zfmisc_1(k2_zfmisc_1(X77,X78)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).
% 0.54/0.71  fof(c_0_59, plain, ![X36, X37, X38]:(~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))|k2_relset_1(X36,X37,X38)=k2_relat_1(X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.54/0.71  fof(c_0_60, plain, ![X80]:(((v1_funct_1(X80)|(~v1_relat_1(X80)|~v1_funct_1(X80)))&(v1_funct_2(X80,k1_relat_1(X80),k2_relat_1(X80))|(~v1_relat_1(X80)|~v1_funct_1(X80))))&(m1_subset_1(X80,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X80),k2_relat_1(X80))))|(~v1_relat_1(X80)|~v1_funct_1(X80)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.54/0.71  fof(c_0_61, plain, ![X28, X29]:(~v1_relat_1(X28)|~v1_funct_1(X28)|(~v1_relat_1(X29)|~v1_funct_1(X29)|(~v2_funct_1(X28)|k2_relat_1(X29)!=k1_relat_1(X28)|k5_relat_1(X29,X28)!=k6_relat_1(k2_relat_1(X28))|X29=k2_funct_1(X28)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_funct_1])])])).
% 0.54/0.71  cnf(c_0_62, plain, (v2_funct_1(X1)|~v2_funct_1(k5_relat_1(X2,X1))|k2_relat_1(X2)!=k1_relat_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.54/0.71  cnf(c_0_63, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.54/0.71  cnf(c_0_64, plain, (v2_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.54/0.71  cnf(c_0_65, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.54/0.71  cnf(c_0_66, plain, (k2_relat_1(X1)=X2|~v2_funct_2(X1,X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.54/0.71  cnf(c_0_67, negated_conjecture, (v2_funct_2(k2_funct_1(esk5_0),esk4_0)|~v5_relat_1(k2_funct_1(esk5_0),esk4_0)|~v1_relat_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_46]), c_0_55])])).
% 0.54/0.71  cnf(c_0_68, plain, (v5_relat_1(X1,X2)|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.54/0.71  cnf(c_0_69, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.54/0.71  cnf(c_0_70, plain, (v1_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.54/0.71  cnf(c_0_71, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.54/0.71  cnf(c_0_72, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.54/0.71  cnf(c_0_73, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.54/0.71  fof(c_0_74, plain, ![X9]:r1_tarski(k1_xboole_0,X9), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.54/0.71  cnf(c_0_75, plain, (X2=k2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X1)|k2_relat_1(X2)!=k1_relat_1(X1)|k5_relat_1(X2,X1)!=k6_relat_1(k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.54/0.71  cnf(c_0_76, plain, (v2_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])]), c_0_65])).
% 0.54/0.71  cnf(c_0_77, negated_conjecture, (k2_relat_1(k2_funct_1(esk5_0))=esk4_0|~v5_relat_1(k2_funct_1(esk5_0),esk4_0)|~v1_relat_1(k2_funct_1(esk5_0))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.54/0.71  cnf(c_0_78, plain, (v5_relat_1(k2_funct_1(X1),X2)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_68, c_0_42])).
% 0.54/0.71  cnf(c_0_79, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_69])).
% 0.54/0.71  cnf(c_0_80, plain, (v1_funct_1(k2_funct_1(X1))|~v1_funct_2(X1,X2,k2_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(X1))))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71])])).
% 0.54/0.71  cnf(c_0_81, negated_conjecture, (v1_funct_2(esk5_0,esk4_0,k2_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_53]), c_0_46]), c_0_55])])).
% 0.54/0.71  cnf(c_0_82, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_relat_1(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_53]), c_0_46]), c_0_55])])).
% 0.54/0.71  fof(c_0_83, plain, ![X12, X13]:((~m1_subset_1(X12,k1_zfmisc_1(X13))|r1_tarski(X12,X13))&(~r1_tarski(X12,X13)|m1_subset_1(X12,k1_zfmisc_1(X13)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.54/0.71  cnf(c_0_84, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.54/0.71  cnf(c_0_85, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.54/0.71  fof(c_0_86, plain, ![X10, X11]:((k2_zfmisc_1(X10,X11)!=k1_xboole_0|(X10=k1_xboole_0|X11=k1_xboole_0))&((X10!=k1_xboole_0|k2_zfmisc_1(X10,X11)=k1_xboole_0)&(X11!=k1_xboole_0|k2_zfmisc_1(X10,X11)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.54/0.71  cnf(c_0_87, plain, (k2_funct_1(k2_funct_1(X1))=X1|k6_relat_1(k2_relat_1(k2_funct_1(X1)))!=k6_relat_1(k1_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_63]), c_0_76]), c_0_65])).
% 0.54/0.71  cnf(c_0_88, negated_conjecture, (k2_relat_1(k2_funct_1(esk5_0))=esk4_0|~v1_relat_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_54]), c_0_46]), c_0_55]), c_0_53]), c_0_79])])).
% 0.54/0.71  cnf(c_0_89, negated_conjecture, (v1_funct_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_54]), c_0_46]), c_0_82])])).
% 0.54/0.71  cnf(c_0_90, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v2_funct_1(X1)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.54/0.71  cnf(c_0_91, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.54/0.71  cnf(c_0_92, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.54/0.71  cnf(c_0_93, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.54/0.71  fof(c_0_94, plain, ![X30, X31, X32]:((v4_relat_1(X32,X30)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))&(v5_relat_1(X32,X31)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.54/0.71  cnf(c_0_95, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.54/0.71  fof(c_0_96, plain, ![X45, X46, X47, X48]:((~r2_relset_1(X45,X46,X47,X48)|X47=X48|(~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))))&(X47!=X48|r2_relset_1(X45,X46,X47,X48)|(~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.54/0.71  fof(c_0_97, plain, ![X52, X53, X54, X55, X56, X57]:((v1_funct_1(k1_partfun1(X52,X53,X54,X55,X56,X57))|(~v1_funct_1(X56)|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))|~v1_funct_1(X57)|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))))&(m1_subset_1(k1_partfun1(X52,X53,X54,X55,X56,X57),k1_zfmisc_1(k2_zfmisc_1(X52,X55)))|(~v1_funct_1(X56)|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))|~v1_funct_1(X57)|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).
% 0.54/0.71  fof(c_0_98, plain, ![X58, X59, X60, X61, X62, X63]:(~v1_funct_1(X62)|~m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X58,X59)))|~v1_funct_1(X63)|~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))|k1_partfun1(X58,X59,X60,X61,X62,X63)=k5_relat_1(X62,X63)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 0.54/0.71  cnf(c_0_99, plain, (k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.54/0.71  cnf(c_0_100, negated_conjecture, (k2_funct_1(k2_funct_1(esk5_0))=esk5_0|~v1_relat_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_53]), c_0_54]), c_0_89]), c_0_46]), c_0_55])])).
% 0.54/0.71  cnf(c_0_101, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),X2)))|~v1_funct_2(X1,X2,k2_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(X1))))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_71])])).
% 0.54/0.71  cnf(c_0_102, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_84, c_0_91])).
% 0.54/0.71  fof(c_0_103, plain, ![X49]:m1_subset_1(k6_relat_1(X49),k1_zfmisc_1(k2_zfmisc_1(X49,X49))), inference(variable_rename,[status(thm)],[t29_relset_1])).
% 0.54/0.71  cnf(c_0_104, plain, (X1=k2_relat_1(X2)|~v5_relat_1(X2,X1)|~v1_relat_1(X2)|~r1_tarski(X1,k2_relat_1(X2))), inference(spm,[status(thm)],[c_0_84, c_0_92])).
% 0.54/0.71  cnf(c_0_105, plain, (k2_relat_1(X1)=k1_xboole_0|~v5_relat_1(X1,k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_93, c_0_92])).
% 0.54/0.71  cnf(c_0_106, negated_conjecture, (v5_relat_1(k2_funct_1(esk5_0),X1)|~v1_relat_1(k2_funct_1(esk5_0))|~r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_68, c_0_88])).
% 0.54/0.71  cnf(c_0_107, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_73, c_0_65])).
% 0.54/0.71  cnf(c_0_108, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_94])).
% 0.54/0.71  cnf(c_0_109, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_95])).
% 0.54/0.71  cnf(c_0_110, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_96])).
% 0.54/0.71  cnf(c_0_111, negated_conjecture, (r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.54/0.71  cnf(c_0_112, plain, (v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.54/0.71  cnf(c_0_113, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_98])).
% 0.54/0.71  cnf(c_0_114, negated_conjecture, (k6_relat_1(k2_relat_1(k2_funct_1(esk5_0)))=k5_relat_1(esk5_0,k2_funct_1(esk5_0))|~v2_funct_1(k2_funct_1(esk5_0))|~v1_relat_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_89])])).
% 0.54/0.71  cnf(c_0_115, plain, (v1_relat_1(k2_funct_1(X1))|~v1_funct_2(X1,X2,k2_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(X1))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_101]), c_0_48])])).
% 0.54/0.71  cnf(c_0_116, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_102, c_0_91])).
% 0.54/0.71  cnf(c_0_117, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.54/0.71  cnf(c_0_118, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.54/0.71  cnf(c_0_119, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_103])).
% 0.54/0.71  cnf(c_0_120, plain, (k2_relat_1(X1)=k2_relat_1(X2)|~v5_relat_1(X2,k2_relat_1(X1))|~v5_relat_1(X1,k2_relat_1(X2))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_104, c_0_92])).
% 0.54/0.71  cnf(c_0_121, negated_conjecture, (k2_relat_1(k2_funct_1(esk5_0))=k1_xboole_0|~v1_relat_1(k2_funct_1(esk5_0))|~r1_tarski(esk4_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_105, c_0_106])).
% 0.54/0.71  cnf(c_0_122, negated_conjecture, (m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk5_0),esk4_0)))|~v1_relat_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_88]), c_0_54]), c_0_89]), c_0_46]), c_0_55])])).
% 0.54/0.71  cnf(c_0_123, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_108, c_0_109])).
% 0.54/0.71  fof(c_0_124, plain, ![X68, X69, X70, X71, X72, X73]:((~v2_funct_1(X70)|(~v1_funct_1(X72)|~v1_funct_2(X72,X71,X68)|~m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X71,X68)))|(~v1_funct_1(X73)|~v1_funct_2(X73,X71,X68)|~m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(X71,X68)))|(~r2_relset_1(X71,X69,k1_partfun1(X71,X68,X68,X69,X72,X70),k1_partfun1(X71,X68,X68,X69,X73,X70))|r2_relset_1(X71,X68,X72,X73))))|(X68=k1_xboole_0|X69=k1_xboole_0)|(~v1_funct_1(X70)|~v1_funct_2(X70,X68,X69)|~m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X68,X69)))))&((((v1_funct_1(esk2_3(X68,X69,X70))|v2_funct_1(X70)|(X68=k1_xboole_0|X69=k1_xboole_0)|(~v1_funct_1(X70)|~v1_funct_2(X70,X68,X69)|~m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X68,X69)))))&(v1_funct_2(esk2_3(X68,X69,X70),esk1_3(X68,X69,X70),X68)|v2_funct_1(X70)|(X68=k1_xboole_0|X69=k1_xboole_0)|(~v1_funct_1(X70)|~v1_funct_2(X70,X68,X69)|~m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X68,X69))))))&(m1_subset_1(esk2_3(X68,X69,X70),k1_zfmisc_1(k2_zfmisc_1(esk1_3(X68,X69,X70),X68)))|v2_funct_1(X70)|(X68=k1_xboole_0|X69=k1_xboole_0)|(~v1_funct_1(X70)|~v1_funct_2(X70,X68,X69)|~m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X68,X69))))))&((((v1_funct_1(esk3_3(X68,X69,X70))|v2_funct_1(X70)|(X68=k1_xboole_0|X69=k1_xboole_0)|(~v1_funct_1(X70)|~v1_funct_2(X70,X68,X69)|~m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X68,X69)))))&(v1_funct_2(esk3_3(X68,X69,X70),esk1_3(X68,X69,X70),X68)|v2_funct_1(X70)|(X68=k1_xboole_0|X69=k1_xboole_0)|(~v1_funct_1(X70)|~v1_funct_2(X70,X68,X69)|~m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X68,X69))))))&(m1_subset_1(esk3_3(X68,X69,X70),k1_zfmisc_1(k2_zfmisc_1(esk1_3(X68,X69,X70),X68)))|v2_funct_1(X70)|(X68=k1_xboole_0|X69=k1_xboole_0)|(~v1_funct_1(X70)|~v1_funct_2(X70,X68,X69)|~m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X68,X69))))))&((r2_relset_1(esk1_3(X68,X69,X70),X69,k1_partfun1(esk1_3(X68,X69,X70),X68,X68,X69,esk2_3(X68,X69,X70),X70),k1_partfun1(esk1_3(X68,X69,X70),X68,X68,X69,esk3_3(X68,X69,X70),X70))|v2_funct_1(X70)|(X68=k1_xboole_0|X69=k1_xboole_0)|(~v1_funct_1(X70)|~v1_funct_2(X70,X68,X69)|~m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X68,X69)))))&(~r2_relset_1(esk1_3(X68,X69,X70),X68,esk2_3(X68,X69,X70),esk3_3(X68,X69,X70))|v2_funct_1(X70)|(X68=k1_xboole_0|X69=k1_xboole_0)|(~v1_funct_1(X70)|~v1_funct_2(X70,X68,X69)|~m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X68,X69))))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_funct_2])])])])])).
% 0.54/0.71  cnf(c_0_125, negated_conjecture, (k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0)=esk5_0|~m1_subset_1(k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_44])])).
% 0.54/0.71  cnf(c_0_126, plain, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.54/0.71  cnf(c_0_127, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.54/0.71  cnf(c_0_128, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.54/0.71  fof(c_0_129, plain, ![X65, X66, X67]:((r2_relset_1(X65,X66,k4_relset_1(X65,X65,X65,X66,k6_partfun1(X65),X67),X67)|~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X66))))&(r2_relset_1(X65,X66,k4_relset_1(X65,X66,X66,X66,X67,k6_partfun1(X66)),X67)|~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X66))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_2])])])).
% 0.54/0.71  fof(c_0_130, plain, ![X64]:k6_partfun1(X64)=k6_relat_1(X64), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.54/0.71  cnf(c_0_131, plain, (v1_funct_1(k5_relat_1(X1,X2))|~v1_funct_1(X2)|~v1_funct_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(spm,[status(thm)],[c_0_112, c_0_113])).
% 0.54/0.71  cnf(c_0_132, negated_conjecture, (k5_relat_1(esk5_0,k2_funct_1(esk5_0))=k6_relat_1(esk4_0)|~v2_funct_1(k2_funct_1(esk5_0))|~v1_relat_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_42]), c_0_53]), c_0_54]), c_0_46]), c_0_55])])).
% 0.54/0.71  cnf(c_0_133, negated_conjecture, (v1_relat_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_82]), c_0_81]), c_0_54]), c_0_46])])).
% 0.54/0.71  cnf(c_0_134, plain, (k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))=X1|~v1_funct_1(X1)|~v1_relat_1(X1)|~m1_subset_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_116, c_0_73])).
% 0.54/0.71  cnf(c_0_135, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_117])).
% 0.54/0.71  cnf(c_0_136, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_118, c_0_85])).
% 0.54/0.71  fof(c_0_137, plain, ![X20]:(k1_relat_1(k6_relat_1(X20))=X20&k2_relat_1(k6_relat_1(X20))=X20), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.54/0.71  cnf(c_0_138, plain, (X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_93, c_0_91])).
% 0.54/0.71  cnf(c_0_139, plain, (m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_119, c_0_109])).
% 0.54/0.71  cnf(c_0_140, negated_conjecture, (k2_relat_1(X1)=esk4_0|~v5_relat_1(k2_funct_1(esk5_0),k2_relat_1(X1))|~v5_relat_1(X1,esk4_0)|~v1_relat_1(k2_funct_1(esk5_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_120, c_0_88])).
% 0.54/0.71  cnf(c_0_141, negated_conjecture, (v5_relat_1(k2_funct_1(esk5_0),X1)|~v1_relat_1(k2_funct_1(esk5_0))|~r1_tarski(esk4_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_121]), c_0_85])])).
% 0.54/0.71  cnf(c_0_142, negated_conjecture, (k2_funct_1(esk5_0)=k2_zfmisc_1(k2_relat_1(esk5_0),esk4_0)|~v1_relat_1(k2_funct_1(esk5_0))|~m1_subset_1(k2_zfmisc_1(k2_relat_1(esk5_0),esk4_0),k1_zfmisc_1(k2_funct_1(esk5_0)))), inference(spm,[status(thm)],[c_0_116, c_0_122])).
% 0.54/0.71  cnf(c_0_143, plain, (k2_relat_1(X1)=k1_xboole_0|~v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_105, c_0_123])).
% 0.54/0.71  cnf(c_0_144, plain, (r2_relset_1(X3,X4,X2,X5)|X4=k1_xboole_0|X6=k1_xboole_0|~v2_funct_1(X1)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~r2_relset_1(X3,X6,k1_partfun1(X3,X4,X4,X6,X2,X1),k1_partfun1(X3,X4,X4,X6,X5,X1))|~v1_funct_1(X1)|~v1_funct_2(X1,X4,X6)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X6)))), inference(split_conjunct,[status(thm)],[c_0_124])).
% 0.54/0.71  cnf(c_0_145, negated_conjecture, (k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_126]), c_0_46]), c_0_127]), c_0_44]), c_0_128])])).
% 0.54/0.71  cnf(c_0_146, negated_conjecture, (v1_funct_2(esk6_0,esk4_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.54/0.71  cnf(c_0_147, plain, (r2_relset_1(X1,X2,k4_relset_1(X1,X1,X1,X2,k6_partfun1(X1),X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_129])).
% 0.54/0.71  cnf(c_0_148, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_130])).
% 0.54/0.71  fof(c_0_149, plain, ![X39, X40, X41, X42, X43, X44]:(~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))|k4_relset_1(X39,X40,X41,X42,X43,X44)=k5_relat_1(X43,X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_relset_1])])).
% 0.54/0.71  cnf(c_0_150, negated_conjecture, (v1_funct_1(k6_relat_1(esk4_0))|~v2_funct_1(k2_funct_1(esk5_0))|~v1_relat_1(k2_funct_1(esk5_0))|~m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_132]), c_0_89]), c_0_46])])).
% 0.54/0.71  cnf(c_0_151, negated_conjecture, (v2_funct_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_133]), c_0_54]), c_0_89]), c_0_46]), c_0_55])])).
% 0.54/0.71  fof(c_0_152, plain, ![X21, X22]:(~v1_relat_1(X21)|~v1_funct_1(X21)|(~m1_subset_1(X22,k1_zfmisc_1(X21))|v1_funct_1(X22))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_funct_1])])])).
% 0.54/0.71  cnf(c_0_153, negated_conjecture, (k2_funct_1(esk5_0)=k1_xboole_0|~v1_relat_1(k2_funct_1(esk5_0))|~r1_tarski(esk4_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_121]), c_0_135]), c_0_89]), c_0_135]), c_0_136])])).
% 0.54/0.71  cnf(c_0_154, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_137])).
% 0.54/0.71  cnf(c_0_155, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_138, c_0_139])).
% 0.54/0.71  cnf(c_0_156, negated_conjecture, (k2_relat_1(X1)=esk4_0|~v5_relat_1(X1,esk4_0)|~v1_relat_1(k2_funct_1(esk5_0))|~v1_relat_1(X1)|~r1_tarski(esk4_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_140, c_0_141])).
% 0.54/0.71  cnf(c_0_157, negated_conjecture, (k2_funct_1(esk5_0)=k1_xboole_0|~v1_relat_1(k2_funct_1(esk5_0))|~m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142, c_0_143]), c_0_109]), c_0_109]), c_0_136]), c_0_55])])).
% 0.54/0.71  cnf(c_0_158, negated_conjecture, (esk4_0=k1_xboole_0|r2_relset_1(esk4_0,esk4_0,X1,esk6_0)|~v1_funct_2(X1,esk4_0,esk4_0)|~r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,X1,esk5_0),esk5_0)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144, c_0_145]), c_0_146]), c_0_45]), c_0_54]), c_0_127]), c_0_46]), c_0_128]), c_0_44])])).
% 0.54/0.71  cnf(c_0_159, plain, (r2_relset_1(X1,X2,k4_relset_1(X1,X1,X1,X2,k6_relat_1(X1),X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(rw,[status(thm)],[c_0_147, c_0_148])).
% 0.54/0.71  cnf(c_0_160, plain, (k4_relset_1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_149])).
% 0.54/0.71  cnf(c_0_161, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_137])).
% 0.54/0.71  cnf(c_0_162, plain, (v1_relat_1(k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_119]), c_0_48])])).
% 0.54/0.71  cnf(c_0_163, negated_conjecture, (v1_funct_1(k6_relat_1(esk4_0))|~m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_150, c_0_133])]), c_0_151])])).
% 0.54/0.71  cnf(c_0_164, plain, (v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_152])).
% 0.54/0.71  cnf(c_0_165, negated_conjecture, (k2_funct_1(esk5_0)=k1_xboole_0|~r1_tarski(esk4_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_153, c_0_133])])).
% 0.54/0.71  cnf(c_0_166, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_154, c_0_155])).
% 0.54/0.71  cnf(c_0_167, plain, (X1=k2_funct_1(X2)|k5_relat_1(X1,X2)!=k1_xboole_0|k1_relat_1(X2)!=k2_relat_1(X1)|~v2_funct_1(X2)|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_143]), c_0_155])).
% 0.54/0.71  cnf(c_0_168, negated_conjecture, (k5_relat_1(esk6_0,esk5_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_145]), c_0_46]), c_0_127]), c_0_44]), c_0_128])])).
% 0.54/0.71  cnf(c_0_169, negated_conjecture, (v1_relat_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_128]), c_0_48])])).
% 0.54/0.71  cnf(c_0_170, negated_conjecture, (k2_relat_1(X1)=esk4_0|~v5_relat_1(X1,esk4_0)|~v1_relat_1(X1)|~r1_tarski(esk4_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_156, c_0_133])])).
% 0.54/0.71  cnf(c_0_171, negated_conjecture, (v5_relat_1(esk6_0,esk4_0)), inference(spm,[status(thm)],[c_0_108, c_0_128])).
% 0.54/0.71  cnf(c_0_172, plain, (r1_tarski(k1_relat_1(X1),X2)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v5_relat_1(k2_funct_1(X1),X2)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_92, c_0_42])).
% 0.54/0.71  cnf(c_0_173, negated_conjecture, (k2_funct_1(esk5_0)=k1_xboole_0|~m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_157, c_0_133])])).
% 0.54/0.71  cnf(c_0_174, plain, (v5_relat_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_108, c_0_136])).
% 0.54/0.71  cnf(c_0_175, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_48, c_0_135])).
% 0.54/0.71  cnf(c_0_176, negated_conjecture, (esk4_0=k1_xboole_0|r2_relset_1(esk4_0,esk4_0,X1,esk6_0)|~v1_funct_2(X1,esk4_0,esk4_0)|~r2_relset_1(esk4_0,esk4_0,k5_relat_1(X1,esk5_0),esk5_0)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_158, c_0_113]), c_0_46]), c_0_44])])).
% 0.54/0.71  cnf(c_0_177, plain, (r2_relset_1(X1,X2,k5_relat_1(k6_relat_1(X1),X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_159, c_0_160]), c_0_119])])).
% 0.54/0.71  cnf(c_0_178, plain, (v1_funct_2(k6_relat_1(X1),X1,X1)|~v1_funct_1(k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_161]), c_0_154]), c_0_162])])).
% 0.54/0.71  cnf(c_0_179, negated_conjecture, (v1_funct_1(k6_relat_1(esk4_0))|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_163, c_0_73]), c_0_89]), c_0_133])])).
% 0.54/0.71  cnf(c_0_180, plain, (v1_funct_1(k1_xboole_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_164, c_0_136])).
% 0.54/0.71  cnf(c_0_181, negated_conjecture, (k5_relat_1(esk5_0,k2_funct_1(esk5_0))=k1_xboole_0|~v2_funct_1(k2_funct_1(esk5_0))|~v1_relat_1(k2_funct_1(esk5_0))|~m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_143]), c_0_155])).
% 0.54/0.71  cnf(c_0_182, plain, (v1_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_72]), c_0_73])).
% 0.54/0.71  cnf(c_0_183, negated_conjecture, (k2_relat_1(esk5_0)=k1_xboole_0|~r1_tarski(esk4_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_165]), c_0_166]), c_0_54]), c_0_46]), c_0_55])])).
% 0.54/0.71  cnf(c_0_184, negated_conjecture, (k2_funct_1(esk5_0)=esk6_0|k2_relat_1(esk6_0)!=esk4_0|~m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_167, c_0_168]), c_0_53]), c_0_54]), c_0_127]), c_0_46]), c_0_169]), c_0_55])]), c_0_138])).
% 0.54/0.71  cnf(c_0_185, negated_conjecture, (k2_relat_1(esk6_0)=esk4_0|~r1_tarski(esk4_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_170, c_0_171]), c_0_169])])).
% 0.54/0.71  cnf(c_0_186, negated_conjecture, (r1_tarski(esk4_0,X1)|~m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_172, c_0_173]), c_0_53]), c_0_54]), c_0_46]), c_0_174]), c_0_175]), c_0_55])])).
% 0.54/0.71  cnf(c_0_187, negated_conjecture, (esk4_0=k1_xboole_0|r2_relset_1(esk4_0,esk4_0,k6_relat_1(esk4_0),esk6_0)|~v1_funct_1(k6_relat_1(esk4_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_176, c_0_177]), c_0_119]), c_0_44])]), c_0_178])).
% 0.54/0.71  cnf(c_0_188, negated_conjecture, (v1_funct_1(k6_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_179, c_0_73]), c_0_46]), c_0_55])])).
% 0.54/0.71  cnf(c_0_189, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_161, c_0_155])).
% 0.54/0.71  cnf(c_0_190, plain, (v2_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_64, c_0_155])).
% 0.54/0.71  cnf(c_0_191, negated_conjecture, (v1_funct_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_180, c_0_169]), c_0_127])])).
% 0.54/0.71  cnf(c_0_192, negated_conjecture, (k6_relat_1(esk4_0)=k1_xboole_0|~v2_funct_1(k2_funct_1(esk5_0))|~v1_relat_1(k2_funct_1(esk5_0))|~m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_181]), c_0_53]), c_0_54]), c_0_46]), c_0_55])])).
% 0.54/0.71  cnf(c_0_193, plain, (k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))=k2_funct_1(X1)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~m1_subset_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1))),k1_zfmisc_1(k2_funct_1(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_107]), c_0_182])).
% 0.54/0.71  cnf(c_0_194, negated_conjecture, (k2_relat_1(esk5_0)=k1_xboole_0|~m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_183, c_0_91])).
% 0.54/0.71  cnf(c_0_195, negated_conjecture, (esk6_0=k1_xboole_0|k2_relat_1(esk6_0)!=esk4_0|~m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_157, c_0_184]), c_0_169])])).
% 0.54/0.71  cnf(c_0_196, negated_conjecture, (k2_relat_1(esk6_0)=esk4_0|~m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_185, c_0_186])).
% 0.54/0.71  cnf(c_0_197, negated_conjecture, (~r2_relset_1(esk4_0,esk4_0,esk6_0,k6_partfun1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.54/0.71  cnf(c_0_198, negated_conjecture, (esk4_0=k1_xboole_0|r2_relset_1(esk4_0,esk4_0,k6_relat_1(esk4_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_187, c_0_188])])).
% 0.54/0.71  cnf(c_0_199, negated_conjecture, (r2_relset_1(esk4_0,esk4_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[c_0_111, c_0_145])).
% 0.54/0.71  cnf(c_0_200, plain, (m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))|~v1_funct_2(k1_xboole_0,X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_189]), c_0_109]), c_0_190]), c_0_191]), c_0_135]), c_0_136])])).
% 0.54/0.71  cnf(c_0_201, plain, (v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_166]), c_0_189]), c_0_191]), c_0_175])])).
% 0.54/0.71  cnf(c_0_202, negated_conjecture, (k6_relat_1(esk4_0)=k1_xboole_0|~m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_192, c_0_133])]), c_0_151])])).
% 0.54/0.71  cnf(c_0_203, negated_conjecture, (k2_funct_1(esk5_0)=k1_xboole_0|~m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_193, c_0_194]), c_0_109]), c_0_54]), c_0_46]), c_0_133]), c_0_55]), c_0_109]), c_0_136])])).
% 0.54/0.71  cnf(c_0_204, negated_conjecture, (esk6_0=k1_xboole_0|~m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_195, c_0_196])).
% 0.54/0.71  cnf(c_0_205, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))|~m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_194]), c_0_53]), c_0_135]), c_0_46]), c_0_55])])).
% 0.54/0.71  cnf(c_0_206, negated_conjecture, (~r2_relset_1(esk4_0,esk4_0,esk6_0,k6_relat_1(esk4_0))), inference(rw,[status(thm)],[c_0_197, c_0_148])).
% 0.54/0.71  cnf(c_0_207, negated_conjecture, (k6_relat_1(esk4_0)=esk6_0|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_198]), c_0_128]), c_0_119])])).
% 0.54/0.71  cnf(c_0_208, negated_conjecture, (esk4_0=k1_xboole_0|r2_relset_1(esk4_0,esk4_0,esk6_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_158, c_0_145]), c_0_146]), c_0_199]), c_0_127]), c_0_128])])).
% 0.54/0.71  cnf(c_0_209, plain, (m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_200, c_0_201])).
% 0.54/0.71  cnf(c_0_210, negated_conjecture, (k6_relat_1(esk4_0)=k1_xboole_0|~m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_202, c_0_203]), c_0_136])])).
% 0.54/0.71  cnf(c_0_211, negated_conjecture, (esk6_0=k1_xboole_0|~m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_204, c_0_205])).
% 0.54/0.71  cnf(c_0_212, negated_conjecture, (esk4_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_206, c_0_207]), c_0_208])).
% 0.54/0.71  cnf(c_0_213, plain, (r2_relset_1(k1_xboole_0,X1,k5_relat_1(k1_xboole_0,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_177, c_0_155]), c_0_109])).
% 0.54/0.71  cnf(c_0_214, plain, (k2_funct_1(k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_209]), c_0_136])])).
% 0.54/0.71  cnf(c_0_215, negated_conjecture, (~r2_relset_1(esk4_0,esk4_0,esk6_0,k1_xboole_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_206, c_0_210])).
% 0.54/0.71  cnf(c_0_216, negated_conjecture, (esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_211, c_0_212]), c_0_136])])).
% 0.54/0.71  cnf(c_0_217, plain, (r2_relset_1(k1_xboole_0,X1,k1_xboole_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_213, c_0_63]), c_0_166]), c_0_155]), c_0_214]), c_0_214]), c_0_136]), c_0_190]), c_0_191]), c_0_175])])).
% 0.54/0.71  cnf(c_0_218, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_215, c_0_212]), c_0_212]), c_0_212]), c_0_136])]), c_0_216]), c_0_217])]), ['proof']).
% 0.54/0.71  # SZS output end CNFRefutation
% 0.54/0.71  # Proof object total steps             : 219
% 0.54/0.71  # Proof object clause steps            : 158
% 0.54/0.71  # Proof object formula steps           : 61
% 0.54/0.71  # Proof object conjectures             : 74
% 0.54/0.71  # Proof object clause conjectures      : 71
% 0.54/0.71  # Proof object formula conjectures     : 3
% 0.54/0.71  # Proof object initial clauses used    : 49
% 0.54/0.71  # Proof object initial formulas used   : 30
% 0.54/0.71  # Proof object generating inferences   : 94
% 0.54/0.71  # Proof object simplifying inferences  : 233
% 0.54/0.71  # Training examples: 0 positive, 0 negative
% 0.54/0.71  # Parsed axioms                        : 30
% 0.54/0.71  # Removed by relevancy pruning/SinE    : 0
% 0.54/0.71  # Initial clauses                      : 65
% 0.54/0.71  # Removed in clause preprocessing      : 2
% 0.54/0.71  # Initial clauses in saturation        : 63
% 0.54/0.71  # Processed clauses                    : 3550
% 0.54/0.71  # ...of these trivial                  : 61
% 0.54/0.71  # ...subsumed                          : 2189
% 0.54/0.71  # ...remaining for further processing  : 1299
% 0.54/0.71  # Other redundant clauses eliminated   : 21
% 0.54/0.71  # Clauses deleted for lack of memory   : 0
% 0.54/0.71  # Backward-subsumed                    : 118
% 0.54/0.71  # Backward-rewritten                   : 785
% 0.54/0.71  # Generated clauses                    : 15538
% 0.54/0.71  # ...of the previous two non-trivial   : 12190
% 0.54/0.71  # Contextual simplify-reflections      : 231
% 0.54/0.71  # Paramodulations                      : 15497
% 0.54/0.71  # Factorizations                       : 20
% 0.54/0.71  # Equation resolutions                 : 21
% 0.54/0.71  # Propositional unsat checks           : 0
% 0.54/0.71  #    Propositional check models        : 0
% 0.54/0.71  #    Propositional check unsatisfiable : 0
% 0.54/0.71  #    Propositional clauses             : 0
% 0.54/0.71  #    Propositional clauses after purity: 0
% 0.54/0.71  #    Propositional unsat core size     : 0
% 0.54/0.71  #    Propositional preprocessing time  : 0.000
% 0.54/0.71  #    Propositional encoding time       : 0.000
% 0.54/0.71  #    Propositional solver time         : 0.000
% 0.54/0.71  #    Success case prop preproc time    : 0.000
% 0.54/0.71  #    Success case prop encoding time   : 0.000
% 0.54/0.71  #    Success case prop solver time     : 0.000
% 0.54/0.71  # Current number of processed clauses  : 328
% 0.54/0.71  #    Positive orientable unit clauses  : 37
% 0.54/0.71  #    Positive unorientable unit clauses: 0
% 0.54/0.71  #    Negative unit clauses             : 0
% 0.54/0.71  #    Non-unit-clauses                  : 291
% 0.54/0.71  # Current number of unprocessed clauses: 8688
% 0.54/0.71  # ...number of literals in the above   : 49950
% 0.54/0.71  # Current number of archived formulas  : 0
% 0.54/0.71  # Current number of archived clauses   : 966
% 0.54/0.71  # Clause-clause subsumption calls (NU) : 164339
% 0.54/0.71  # Rec. Clause-clause subsumption calls : 53274
% 0.54/0.71  # Non-unit clause-clause subsumptions  : 2526
% 0.54/0.71  # Unit Clause-clause subsumption calls : 1651
% 0.54/0.71  # Rewrite failures with RHS unbound    : 0
% 0.54/0.71  # BW rewrite match attempts            : 36
% 0.54/0.71  # BW rewrite match successes           : 17
% 0.54/0.71  # Condensation attempts                : 0
% 0.54/0.71  # Condensation successes               : 0
% 0.54/0.71  # Termbank termtop insertions          : 376540
% 0.54/0.71  
% 0.54/0.71  # -------------------------------------------------
% 0.54/0.71  # User time                : 0.346 s
% 0.54/0.71  # System time              : 0.017 s
% 0.54/0.71  # Total time               : 0.363 s
% 0.54/0.71  # Maximum resident set size: 1616 pages
%------------------------------------------------------------------------------
