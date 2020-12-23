%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:05:45 EST 2020

% Result     : Theorem 0.60s
% Output     : CNFRefutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :  217 (3320 expanded)
%              Number of clauses        :  163 (1561 expanded)
%              Number of leaves         :   27 ( 840 expanded)
%              Depth                    :   23
%              Number of atoms          :  702 (10961 expanded)
%              Number of equality atoms :  136 (1791 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   70 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(fc4_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v2_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_funct_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t67_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => k1_relset_1(X1,X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

fof(t4_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(k2_relat_1(X2),X1)
       => ( v1_funct_1(X2)
          & v1_funct_2(X2,k1_relat_1(X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(t61_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
          & k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(t23_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r2_relset_1(X1,X2,k4_relset_1(X1,X1,X1,X2,k6_partfun1(X1),X3),X3)
        & r2_relset_1(X1,X2,k4_relset_1(X1,X2,X2,X2,X3,k6_partfun1(X2)),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_2)).

fof(dt_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
        & m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(redefinition_k4_relset_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k4_relset_1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(symmetry_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
       => r2_relset_1(X1,X2,X4,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r2_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_2)).

fof(c_0_27,plain,(
    ! [X55] :
      ( v1_partfun1(k6_partfun1(X55),X55)
      & m1_subset_1(k6_partfun1(X55),k1_zfmisc_1(k2_zfmisc_1(X55,X55))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

fof(c_0_28,plain,(
    ! [X62] : k6_partfun1(X62) = k6_relat_1(X62) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_29,plain,(
    ! [X11,X12] :
      ( ( k2_zfmisc_1(X11,X12) != k1_xboole_0
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0 )
      & ( X11 != k1_xboole_0
        | k2_zfmisc_1(X11,X12) = k1_xboole_0 )
      & ( X12 != k1_xboole_0
        | k2_zfmisc_1(X11,X12) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_30,plain,(
    ! [X9,X10] :
      ( ~ v1_xboole_0(X9)
      | X9 = X10
      | ~ v1_xboole_0(X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

fof(c_0_31,plain,(
    ! [X26,X27,X28] :
      ( ~ v1_xboole_0(X26)
      | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X27,X26)))
      | v1_xboole_0(X28) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

cnf(c_0_32,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_34,plain,(
    ! [X15,X16] :
      ( ( ~ v5_relat_1(X16,X15)
        | r1_tarski(k2_relat_1(X16),X15)
        | ~ v1_relat_1(X16) )
      & ( ~ r1_tarski(k2_relat_1(X16),X15)
        | v5_relat_1(X16,X15)
        | ~ v1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

fof(c_0_35,plain,(
    ! [X17] :
      ( k1_relat_1(k6_relat_1(X17)) = X17
      & k2_relat_1(k6_relat_1(X17)) = X17 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_36,plain,(
    ! [X18] :
      ( v1_relat_1(k6_relat_1(X18))
      & v2_funct_1(k6_relat_1(X18)) ) ),
    inference(variable_rename,[status(thm)],[fc4_funct_1])).

fof(c_0_37,plain,(
    ! [X23,X24,X25] :
      ( ( v4_relat_1(X25,X23)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( v5_relat_1(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_38,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_41,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_43,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_44,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_49,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_50,plain,
    ( v1_xboole_0(k6_relat_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_51,plain,(
    ! [X13,X14] :
      ( ( ~ m1_subset_1(X13,k1_zfmisc_1(X14))
        | r1_tarski(X13,X14) )
      & ( ~ r1_tarski(X13,X14)
        | m1_subset_1(X13,k1_zfmisc_1(X14)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X2)
    | ~ v5_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])])).

cnf(c_0_54,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_55,plain,
    ( k6_relat_1(X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_52])).

fof(c_0_58,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | v1_relat_1(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_60,plain,
    ( k6_relat_1(k6_relat_1(X1)) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_50])).

cnf(c_0_61,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_63,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_64,plain,
    ( r1_tarski(k6_relat_1(X1),X2)
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])])).

fof(c_0_65,negated_conjecture,(
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

cnf(c_0_66,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_40])).

cnf(c_0_67,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_61])).

cnf(c_0_68,plain,
    ( X1 = k2_relat_1(X2)
    | ~ v5_relat_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k2_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_44])).

cnf(c_0_69,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_64])).

fof(c_0_70,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk4_0,esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk4_0,esk4_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))
    & r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0),esk5_0)
    & v2_funct_1(esk5_0)
    & ~ r2_relset_1(esk4_0,esk4_0,esk6_0,k6_partfun1(esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_65])])])).

cnf(c_0_71,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_66])).

cnf(c_0_72,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_48])).

cnf(c_0_73,plain,
    ( X1 = X2
    | ~ v5_relat_1(k6_relat_1(X2),X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_45]),c_0_46])])).

cnf(c_0_74,plain,
    ( v5_relat_1(k6_relat_1(X1),X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_69])).

cnf(c_0_75,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_61])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_77,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_78,plain,
    ( r1_tarski(k1_xboole_0,X1)
    | ~ v5_relat_1(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_71]),c_0_72])])).

cnf(c_0_79,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_80,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_81,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_75])).

fof(c_0_82,plain,(
    ! [X75,X76,X77] :
      ( ( v1_funct_1(k2_funct_1(X77))
        | ~ v2_funct_1(X77)
        | k2_relset_1(X75,X76,X77) != X76
        | ~ v1_funct_1(X77)
        | ~ v1_funct_2(X77,X75,X76)
        | ~ m1_subset_1(X77,k1_zfmisc_1(k2_zfmisc_1(X75,X76))) )
      & ( v1_funct_2(k2_funct_1(X77),X76,X75)
        | ~ v2_funct_1(X77)
        | k2_relset_1(X75,X76,X77) != X76
        | ~ v1_funct_1(X77)
        | ~ v1_funct_2(X77,X75,X76)
        | ~ m1_subset_1(X77,k1_zfmisc_1(k2_zfmisc_1(X75,X76))) )
      & ( m1_subset_1(k2_funct_1(X77),k1_zfmisc_1(k2_zfmisc_1(X76,X75)))
        | ~ v2_funct_1(X77)
        | k2_relset_1(X75,X76,X77) != X76
        | ~ v1_funct_1(X77)
        | ~ v1_funct_2(X77,X75,X76)
        | ~ m1_subset_1(X77,k1_zfmisc_1(k2_zfmisc_1(X75,X76))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).

cnf(c_0_83,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | ~ v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_76])).

cnf(c_0_84,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_77])).

cnf(c_0_85,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_54]),c_0_61])])).

cnf(c_0_86,plain,
    ( X1 = X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_87,plain,
    ( k2_zfmisc_1(X1,k6_relat_1(X2)) = k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_81,c_0_50])).

cnf(c_0_88,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_89,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_90,negated_conjecture,
    ( k6_relat_1(esk6_0) = k1_xboole_0
    | ~ v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_83])).

cnf(c_0_91,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_84]),c_0_40])])).

cnf(c_0_92,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_85])).

cnf(c_0_93,plain,
    ( k6_relat_1(X1) = k2_zfmisc_1(X1,X1)
    | ~ v1_xboole_0(k2_zfmisc_1(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_42])).

cnf(c_0_94,plain,
    ( k2_zfmisc_1(X1,k6_relat_1(k6_relat_1(X2))) = k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_87,c_0_50])).

cnf(c_0_95,plain,
    ( v1_xboole_0(k2_funct_1(X1))
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_88])).

cnf(c_0_96,negated_conjecture,
    ( v1_funct_2(esk5_0,esk4_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_97,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_98,negated_conjecture,
    ( v2_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_99,plain,
    ( m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_44])).

cnf(c_0_100,negated_conjecture,
    ( v5_relat_1(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_89])).

cnf(c_0_101,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_89])).

cnf(c_0_102,negated_conjecture,
    ( k6_relat_1(esk6_0) = k1_xboole_0
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_103,plain,
    ( v5_relat_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_92])).

cnf(c_0_104,plain,
    ( k6_relat_1(k6_relat_1(k6_relat_1(X1))) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_40])])).

cnf(c_0_105,negated_conjecture,
    ( v1_xboole_0(k2_funct_1(esk5_0))
    | k2_relset_1(esk4_0,esk4_0,esk5_0) != esk4_0
    | ~ v1_xboole_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_89]),c_0_96]),c_0_97]),c_0_98])])).

fof(c_0_106,plain,(
    ! [X32,X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
      | k2_relset_1(X32,X33,X34) = k2_relat_1(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_107,negated_conjecture,
    ( m1_subset_1(k2_relat_1(esk5_0),k1_zfmisc_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_101])])).

cnf(c_0_108,negated_conjecture,
    ( X1 = esk6_0
    | ~ v1_xboole_0(esk4_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_83])).

fof(c_0_109,plain,(
    ! [X29,X30,X31] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | k1_relset_1(X29,X30,X31) = k1_relat_1(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_110,plain,(
    ! [X80,X81] :
      ( ~ v1_funct_1(X81)
      | ~ v1_funct_2(X81,X80,X80)
      | ~ m1_subset_1(X81,k1_zfmisc_1(k2_zfmisc_1(X80,X80)))
      | k1_relset_1(X80,X80,X81) = X80 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_funct_2])])).

fof(c_0_111,plain,(
    ! [X78,X79] :
      ( ( v1_funct_1(X79)
        | ~ r1_tarski(k2_relat_1(X79),X78)
        | ~ v1_relat_1(X79)
        | ~ v1_funct_1(X79) )
      & ( v1_funct_2(X79,k1_relat_1(X79),X78)
        | ~ r1_tarski(k2_relat_1(X79),X78)
        | ~ v1_relat_1(X79)
        | ~ v1_funct_1(X79) )
      & ( m1_subset_1(X79,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X79),X78)))
        | ~ r1_tarski(k2_relat_1(X79),X78)
        | ~ v1_relat_1(X79)
        | ~ v1_funct_1(X79) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).

cnf(c_0_112,negated_conjecture,
    ( r1_tarski(esk6_0,X1)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_102]),c_0_103])])).

cnf(c_0_113,plain,
    ( r1_tarski(k6_relat_1(k6_relat_1(X1)),X2)
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_104]),c_0_103])])).

fof(c_0_114,plain,(
    ! [X19] :
      ( ( k5_relat_1(X19,k2_funct_1(X19)) = k6_relat_1(k1_relat_1(X19))
        | ~ v2_funct_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( k5_relat_1(k2_funct_1(X19),X19) = k6_relat_1(k2_relat_1(X19))
        | ~ v2_funct_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).

cnf(c_0_115,negated_conjecture,
    ( k2_funct_1(esk5_0) = k1_xboole_0
    | k2_relset_1(esk4_0,esk4_0,esk5_0) != esk4_0
    | ~ v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_105])).

cnf(c_0_116,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_106])).

cnf(c_0_117,negated_conjecture,
    ( k2_relat_1(esk5_0) = esk4_0
    | ~ v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_86,c_0_107])).

cnf(c_0_118,negated_conjecture,
    ( X1 = esk6_0
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_108,c_0_91])).

cnf(c_0_119,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_109])).

cnf(c_0_120,plain,
    ( k1_relset_1(X2,X2,X1) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_110])).

cnf(c_0_121,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_111])).

cnf(c_0_122,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_112])).

cnf(c_0_123,plain,
    ( k6_relat_1(k6_relat_1(X1)) = X2
    | ~ v1_xboole_0(X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_79,c_0_113])).

cnf(c_0_124,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_114])).

cnf(c_0_125,negated_conjecture,
    ( k2_funct_1(esk5_0) = k1_xboole_0
    | ~ v1_xboole_0(esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_89])]),c_0_117])).

cnf(c_0_126,negated_conjecture,
    ( k6_relat_1(X1) = esk6_0
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_118,c_0_50])).

cnf(c_0_127,plain,
    ( X1 = k1_relat_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_119,c_0_120])).

cnf(c_0_128,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_129,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_130,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_121,c_0_57])).

cnf(c_0_131,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | ~ v5_relat_1(X1,k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_85])).

cnf(c_0_132,negated_conjecture,
    ( v5_relat_1(esk6_0,X1)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_122])).

cnf(c_0_133,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_76])).

cnf(c_0_134,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_111])).

cnf(c_0_135,negated_conjecture,
    ( k6_relat_1(k6_relat_1(X1)) = esk6_0
    | ~ v1_xboole_0(esk4_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_123,c_0_83])).

cnf(c_0_136,negated_conjecture,
    ( k6_relat_1(k2_relat_1(esk5_0)) = k5_relat_1(k1_xboole_0,esk5_0)
    | ~ v1_xboole_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_125]),c_0_97]),c_0_98]),c_0_101])])).

cnf(c_0_137,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_138,negated_conjecture,
    ( k6_relat_1(k6_relat_1(X1)) = esk6_0
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_126,c_0_50])).

cnf(c_0_139,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_76]),c_0_128]),c_0_129])])).

cnf(c_0_140,plain,
    ( v1_xboole_0(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_130])).

cnf(c_0_141,negated_conjecture,
    ( k2_relat_1(esk6_0) = k1_xboole_0
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_132]),c_0_133])])).

cnf(c_0_142,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_143,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_134,c_0_57])).

cnf(c_0_144,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_89]),c_0_96]),c_0_97])])).

fof(c_0_145,plain,(
    ! [X41,X42,X43,X44] :
      ( ( ~ r2_relset_1(X41,X42,X43,X44)
        | X43 = X44
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) )
      & ( X43 != X44
        | r2_relset_1(X41,X42,X43,X44)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

fof(c_0_146,plain,(
    ! [X63,X64,X65] :
      ( ( r2_relset_1(X63,X64,k4_relset_1(X63,X63,X63,X64,k6_partfun1(X63),X65),X65)
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))) )
      & ( r2_relset_1(X63,X64,k4_relset_1(X63,X64,X64,X64,X65,k6_partfun1(X64)),X65)
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_2])])])).

fof(c_0_147,plain,(
    ! [X49,X50,X51,X52,X53,X54] :
      ( ( v1_funct_1(k1_partfun1(X49,X50,X51,X52,X53,X54))
        | ~ v1_funct_1(X53)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))
        | ~ v1_funct_1(X54)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) )
      & ( m1_subset_1(k1_partfun1(X49,X50,X51,X52,X53,X54),k1_zfmisc_1(k2_zfmisc_1(X49,X52)))
        | ~ v1_funct_1(X53)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))
        | ~ v1_funct_1(X54)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

fof(c_0_148,plain,(
    ! [X56,X57,X58,X59,X60,X61] :
      ( ~ v1_funct_1(X60)
      | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))
      | ~ v1_funct_1(X61)
      | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X58,X59)))
      | k1_partfun1(X56,X57,X58,X59,X60,X61) = k5_relat_1(X60,X61) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

cnf(c_0_149,negated_conjecture,
    ( k6_relat_1(k5_relat_1(k1_xboole_0,esk5_0)) = esk6_0
    | ~ v1_xboole_0(k2_relat_1(esk5_0))
    | ~ v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_135,c_0_136])).

cnf(c_0_150,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_48])).

cnf(c_0_151,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_74]),c_0_45]),c_0_46])])).

cnf(c_0_152,negated_conjecture,
    ( v1_xboole_0(esk5_0)
    | ~ v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_89])).

cnf(c_0_153,negated_conjecture,
    ( k6_relat_1(X1) = esk4_0
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_xboole_0(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_138]),c_0_139])).

cnf(c_0_154,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_141]),c_0_129]),c_0_133]),c_0_40])])).

cnf(c_0_155,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_2(X1,X2,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(X1)))) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_116])])).

cnf(c_0_156,negated_conjecture,
    ( v1_funct_2(esk5_0,esk4_0,k2_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_144]),c_0_97]),c_0_101])])).

cnf(c_0_157,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_145])).

cnf(c_0_158,negated_conjecture,
    ( r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_159,plain,
    ( r2_relset_1(X1,X2,k4_relset_1(X1,X1,X1,X2,k6_partfun1(X1),X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_146])).

fof(c_0_160,plain,(
    ! [X35,X36,X37,X38,X39,X40] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
      | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
      | k4_relset_1(X35,X36,X37,X38,X39,X40) = k5_relat_1(X39,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_relset_1])])).

fof(c_0_161,plain,(
    ! [X45,X46,X47,X48] :
      ( ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))
      | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))
      | ~ r2_relset_1(X45,X46,X47,X48)
      | r2_relset_1(X45,X46,X48,X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r2_relset_1])])).

cnf(c_0_162,plain,
    ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_147])).

cnf(c_0_163,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_148])).

cnf(c_0_164,plain,
    ( v5_relat_1(k6_relat_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_42])).

cnf(c_0_165,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk5_0) = esk4_0
    | ~ v1_xboole_0(k2_relat_1(esk5_0))
    | ~ v1_xboole_0(esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_149]),c_0_139])).

cnf(c_0_166,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_54]),c_0_150])).

cnf(c_0_167,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_151,c_0_152])).

cnf(c_0_168,negated_conjecture,
    ( ~ r2_relset_1(esk4_0,esk4_0,esk6_0,k6_partfun1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_169,negated_conjecture,
    ( k6_relat_1(esk6_0) = esk4_0
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_153,c_0_154])).

cnf(c_0_170,plain,
    ( m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_54]),c_0_150])).

cnf(c_0_171,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk5_0))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_relat_1(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_155,c_0_156]),c_0_97]),c_0_98])])).

cnf(c_0_172,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_relat_1(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_144]),c_0_97]),c_0_101])])).

fof(c_0_173,plain,(
    ! [X66,X67,X68,X69,X70,X71] :
      ( ( ~ v2_funct_1(X68)
        | ~ v1_funct_1(X70)
        | ~ v1_funct_2(X70,X69,X66)
        | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X69,X66)))
        | ~ v1_funct_1(X71)
        | ~ v1_funct_2(X71,X69,X66)
        | ~ m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X69,X66)))
        | ~ r2_relset_1(X69,X67,k1_partfun1(X69,X66,X66,X67,X70,X68),k1_partfun1(X69,X66,X66,X67,X71,X68))
        | r2_relset_1(X69,X66,X70,X71)
        | X66 = k1_xboole_0
        | X67 = k1_xboole_0
        | ~ v1_funct_1(X68)
        | ~ v1_funct_2(X68,X66,X67)
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67))) )
      & ( v1_funct_1(esk2_3(X66,X67,X68))
        | v2_funct_1(X68)
        | X66 = k1_xboole_0
        | X67 = k1_xboole_0
        | ~ v1_funct_1(X68)
        | ~ v1_funct_2(X68,X66,X67)
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67))) )
      & ( v1_funct_2(esk2_3(X66,X67,X68),esk1_3(X66,X67,X68),X66)
        | v2_funct_1(X68)
        | X66 = k1_xboole_0
        | X67 = k1_xboole_0
        | ~ v1_funct_1(X68)
        | ~ v1_funct_2(X68,X66,X67)
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67))) )
      & ( m1_subset_1(esk2_3(X66,X67,X68),k1_zfmisc_1(k2_zfmisc_1(esk1_3(X66,X67,X68),X66)))
        | v2_funct_1(X68)
        | X66 = k1_xboole_0
        | X67 = k1_xboole_0
        | ~ v1_funct_1(X68)
        | ~ v1_funct_2(X68,X66,X67)
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67))) )
      & ( v1_funct_1(esk3_3(X66,X67,X68))
        | v2_funct_1(X68)
        | X66 = k1_xboole_0
        | X67 = k1_xboole_0
        | ~ v1_funct_1(X68)
        | ~ v1_funct_2(X68,X66,X67)
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67))) )
      & ( v1_funct_2(esk3_3(X66,X67,X68),esk1_3(X66,X67,X68),X66)
        | v2_funct_1(X68)
        | X66 = k1_xboole_0
        | X67 = k1_xboole_0
        | ~ v1_funct_1(X68)
        | ~ v1_funct_2(X68,X66,X67)
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67))) )
      & ( m1_subset_1(esk3_3(X66,X67,X68),k1_zfmisc_1(k2_zfmisc_1(esk1_3(X66,X67,X68),X66)))
        | v2_funct_1(X68)
        | X66 = k1_xboole_0
        | X67 = k1_xboole_0
        | ~ v1_funct_1(X68)
        | ~ v1_funct_2(X68,X66,X67)
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67))) )
      & ( r2_relset_1(esk1_3(X66,X67,X68),X67,k1_partfun1(esk1_3(X66,X67,X68),X66,X66,X67,esk2_3(X66,X67,X68),X68),k1_partfun1(esk1_3(X66,X67,X68),X66,X66,X67,esk3_3(X66,X67,X68),X68))
        | v2_funct_1(X68)
        | X66 = k1_xboole_0
        | X67 = k1_xboole_0
        | ~ v1_funct_1(X68)
        | ~ v1_funct_2(X68,X66,X67)
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67))) )
      & ( ~ r2_relset_1(esk1_3(X66,X67,X68),X66,esk2_3(X66,X67,X68),esk3_3(X66,X67,X68))
        | v2_funct_1(X68)
        | X66 = k1_xboole_0
        | X67 = k1_xboole_0
        | ~ v1_funct_1(X68)
        | ~ v1_funct_2(X68,X66,X67)
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_funct_2])])])])])).

cnf(c_0_174,negated_conjecture,
    ( k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0) = esk5_0
    | ~ m1_subset_1(k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_157,c_0_158]),c_0_89])])).

cnf(c_0_175,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_147])).

cnf(c_0_176,plain,
    ( r2_relset_1(X1,X2,k4_relset_1(X1,X1,X1,X2,k6_relat_1(X1),X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_159,c_0_33])).

cnf(c_0_177,plain,
    ( k4_relset_1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_160])).

cnf(c_0_178,plain,
    ( r2_relset_1(X2,X3,X4,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_relset_1(X2,X3,X1,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_161])).

cnf(c_0_179,plain,
    ( v1_funct_1(k5_relat_1(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(spm,[status(thm)],[c_0_162,c_0_163])).

cnf(c_0_180,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_88])).

cnf(c_0_181,negated_conjecture,
    ( v5_relat_1(k5_relat_1(k1_xboole_0,esk5_0),k2_relat_1(esk5_0))
    | ~ v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_164,c_0_136])).

cnf(c_0_182,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk5_0) = esk4_0
    | ~ v1_xboole_0(esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_165,c_0_166]),c_0_40])]),c_0_167])).

cnf(c_0_183,negated_conjecture,
    ( ~ r2_relset_1(esk4_0,esk4_0,esk6_0,k6_relat_1(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_168,c_0_33])).

cnf(c_0_184,negated_conjecture,
    ( k6_relat_1(esk4_0) = esk6_0
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_169]),c_0_154])).

cnf(c_0_185,plain,
    ( r2_relset_1(X3,X4,X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_145])).

cnf(c_0_186,plain,
    ( v1_relat_1(k2_relat_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_170])).

cnf(c_0_187,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_171,c_0_172])])).

cnf(c_0_188,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_173])).

cnf(c_0_189,negated_conjecture,
    ( k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_174,c_0_175]),c_0_97]),c_0_129]),c_0_89]),c_0_76])])).

cnf(c_0_190,plain,
    ( r2_relset_1(X1,X2,k5_relat_1(k6_relat_1(X1),X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_176,c_0_177]),c_0_42])])).

cnf(c_0_191,negated_conjecture,
    ( r2_relset_1(esk4_0,esk4_0,esk6_0,X1)
    | ~ r2_relset_1(esk4_0,esk4_0,X1,esk6_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_178,c_0_76])).

cnf(c_0_192,plain,
    ( v1_funct_1(k5_relat_1(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(spm,[status(thm)],[c_0_179,c_0_130])).

cnf(c_0_193,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk5_0))
    | k2_relset_1(esk4_0,k2_relat_1(esk5_0),esk5_0) != k2_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_180,c_0_172]),c_0_156]),c_0_97]),c_0_98])])).

cnf(c_0_194,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ v1_funct_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_121,c_0_44])).

cnf(c_0_195,negated_conjecture,
    ( v5_relat_1(esk4_0,k2_relat_1(esk5_0))
    | ~ v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_181,c_0_182])).

cnf(c_0_196,negated_conjecture,
    ( ~ r2_relset_1(esk4_0,esk4_0,esk6_0,esk6_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_183,c_0_184])).

cnf(c_0_197,plain,
    ( r2_relset_1(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_185])).

cnf(c_0_198,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_186,c_0_45])).

cnf(c_0_199,negated_conjecture,
    ( v1_funct_1(k1_xboole_0)
    | ~ v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_187,c_0_125])).

cnf(c_0_200,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_relset_1(esk4_0,esk4_0,X1,esk6_0)
    | ~ v1_funct_2(X1,esk4_0,esk4_0)
    | ~ r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,X1,esk5_0),esk5_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_188,c_0_189]),c_0_128]),c_0_96]),c_0_129]),c_0_97]),c_0_98]),c_0_76]),c_0_89])])).

cnf(c_0_201,plain,
    ( r2_relset_1(X1,X2,k1_partfun1(X3,X4,X5,X6,k6_relat_1(X1),X7),X7)
    | ~ v1_funct_1(k6_relat_1(X1))
    | ~ v1_funct_1(X7)
    | ~ m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(spm,[status(thm)],[c_0_190,c_0_163])).

cnf(c_0_202,negated_conjecture,
    ( ~ r2_relset_1(esk4_0,esk4_0,k6_relat_1(esk4_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_191,c_0_42]),c_0_183])).

cnf(c_0_203,plain,
    ( v1_funct_2(k6_relat_1(X1),X1,X1)
    | ~ v1_funct_1(k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_45]),c_0_137]),c_0_46])])).

cnf(c_0_204,negated_conjecture,
    ( v1_funct_1(k5_relat_1(esk5_0,X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_192,c_0_89]),c_0_97])])).

cnf(c_0_205,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_114])).

cnf(c_0_206,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_193,c_0_116]),c_0_172])])).

cnf(c_0_207,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_1(X1)
    | ~ v5_relat_1(X1,k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_194,c_0_84])).

cnf(c_0_208,negated_conjecture,
    ( v5_relat_1(esk4_0,k1_xboole_0)
    | ~ v1_xboole_0(esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_195,c_0_166]),c_0_167])).

cnf(c_0_209,negated_conjecture,
    ( ~ m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_196,c_0_197]),c_0_76])])).

cnf(c_0_210,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_198,c_0_69])).

cnf(c_0_211,negated_conjecture,
    ( v1_funct_1(esk4_0)
    | ~ v1_xboole_0(esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_179,c_0_182]),c_0_97]),c_0_92])]),c_0_167]),c_0_199])).

cnf(c_0_212,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | ~ v1_funct_1(k6_relat_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_200,c_0_201]),c_0_42]),c_0_97]),c_0_89])]),c_0_202]),c_0_203])).

cnf(c_0_213,negated_conjecture,
    ( v1_funct_1(k6_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_204,c_0_205]),c_0_144]),c_0_187]),c_0_206]),c_0_97]),c_0_98]),c_0_101])])).

cnf(c_0_214,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_207,c_0_208]),c_0_209]),c_0_210]),c_0_211])).

cnf(c_0_215,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_212,c_0_213])])).

cnf(c_0_216,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_214,c_0_215]),c_0_40])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:32:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.60/0.84  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.60/0.84  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.60/0.84  #
% 0.60/0.84  # Preprocessing time       : 0.030 s
% 0.60/0.84  # Presaturation interreduction done
% 0.60/0.84  
% 0.60/0.84  # Proof found!
% 0.60/0.84  # SZS status Theorem
% 0.60/0.84  # SZS output start CNFRefutation
% 0.60/0.84  fof(dt_k6_partfun1, axiom, ![X1]:(v1_partfun1(k6_partfun1(X1),X1)&m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 0.60/0.84  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.60/0.84  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.60/0.84  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 0.60/0.84  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 0.60/0.84  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.60/0.84  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.60/0.84  fof(fc4_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v2_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 0.60/0.84  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.60/0.84  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.60/0.84  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.60/0.84  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.60/0.84  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.60/0.84  fof(t76_funct_2, conjecture, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>((r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X3,X2),X2)&v2_funct_1(X2))=>r2_relset_1(X1,X1,X3,k6_partfun1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_funct_2)).
% 0.60/0.84  fof(t31_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 0.60/0.84  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.60/0.84  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.60/0.84  fof(t67_funct_2, axiom, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>k1_relset_1(X1,X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 0.60/0.84  fof(t4_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(k2_relat_1(X2),X1)=>((v1_funct_1(X2)&v1_funct_2(X2,k1_relat_1(X2),X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 0.60/0.84  fof(t61_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))&k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 0.60/0.84  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.60/0.84  fof(t23_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(r2_relset_1(X1,X2,k4_relset_1(X1,X1,X1,X2,k6_partfun1(X1),X3),X3)&r2_relset_1(X1,X2,k4_relset_1(X1,X2,X2,X2,X3,k6_partfun1(X2)),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_2)).
% 0.60/0.84  fof(dt_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))&m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 0.60/0.84  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 0.60/0.84  fof(redefinition_k4_relset_1, axiom, ![X1, X2, X3, X4, X5, X6]:((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k4_relset_1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 0.60/0.84  fof(symmetry_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)=>r2_relset_1(X1,X2,X4,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r2_relset_1)).
% 0.60/0.84  fof(t27_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&~((v2_funct_1(X3)<=>![X4, X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X4,X1))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X1))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X1))))=>(r2_relset_1(X4,X2,k1_partfun1(X4,X1,X1,X2,X5,X3),k1_partfun1(X4,X1,X1,X2,X6,X3))=>r2_relset_1(X4,X1,X5,X6))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_funct_2)).
% 0.60/0.84  fof(c_0_27, plain, ![X55]:(v1_partfun1(k6_partfun1(X55),X55)&m1_subset_1(k6_partfun1(X55),k1_zfmisc_1(k2_zfmisc_1(X55,X55)))), inference(variable_rename,[status(thm)],[dt_k6_partfun1])).
% 0.60/0.84  fof(c_0_28, plain, ![X62]:k6_partfun1(X62)=k6_relat_1(X62), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.60/0.84  fof(c_0_29, plain, ![X11, X12]:((k2_zfmisc_1(X11,X12)!=k1_xboole_0|(X11=k1_xboole_0|X12=k1_xboole_0))&((X11!=k1_xboole_0|k2_zfmisc_1(X11,X12)=k1_xboole_0)&(X12!=k1_xboole_0|k2_zfmisc_1(X11,X12)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.60/0.84  fof(c_0_30, plain, ![X9, X10]:(~v1_xboole_0(X9)|X9=X10|~v1_xboole_0(X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 0.60/0.84  fof(c_0_31, plain, ![X26, X27, X28]:(~v1_xboole_0(X26)|(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X27,X26)))|v1_xboole_0(X28))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 0.60/0.84  cnf(c_0_32, plain, (m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.60/0.84  cnf(c_0_33, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.60/0.84  fof(c_0_34, plain, ![X15, X16]:((~v5_relat_1(X16,X15)|r1_tarski(k2_relat_1(X16),X15)|~v1_relat_1(X16))&(~r1_tarski(k2_relat_1(X16),X15)|v5_relat_1(X16,X15)|~v1_relat_1(X16))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.60/0.84  fof(c_0_35, plain, ![X17]:(k1_relat_1(k6_relat_1(X17))=X17&k2_relat_1(k6_relat_1(X17))=X17), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.60/0.84  fof(c_0_36, plain, ![X18]:(v1_relat_1(k6_relat_1(X18))&v2_funct_1(k6_relat_1(X18))), inference(variable_rename,[status(thm)],[fc4_funct_1])).
% 0.60/0.84  fof(c_0_37, plain, ![X23, X24, X25]:((v4_relat_1(X25,X23)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))&(v5_relat_1(X25,X24)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.60/0.84  cnf(c_0_38, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.60/0.84  cnf(c_0_39, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.60/0.84  cnf(c_0_40, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.60/0.84  cnf(c_0_41, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.60/0.84  cnf(c_0_42, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 0.60/0.84  fof(c_0_43, plain, ![X7, X8]:(((r1_tarski(X7,X8)|X7!=X8)&(r1_tarski(X8,X7)|X7!=X8))&(~r1_tarski(X7,X8)|~r1_tarski(X8,X7)|X7=X8)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.60/0.84  cnf(c_0_44, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.60/0.84  cnf(c_0_45, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.60/0.84  cnf(c_0_46, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.60/0.84  cnf(c_0_47, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.60/0.84  cnf(c_0_48, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_38])).
% 0.60/0.84  cnf(c_0_49, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.60/0.84  cnf(c_0_50, plain, (v1_xboole_0(k6_relat_1(X1))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.60/0.84  fof(c_0_51, plain, ![X13, X14]:((~m1_subset_1(X13,k1_zfmisc_1(X14))|r1_tarski(X13,X14))&(~r1_tarski(X13,X14)|m1_subset_1(X13,k1_zfmisc_1(X14)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.60/0.84  cnf(c_0_52, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.60/0.84  cnf(c_0_53, plain, (r1_tarski(X1,X2)|~v5_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])])).
% 0.60/0.84  cnf(c_0_54, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.60/0.84  cnf(c_0_55, plain, (k6_relat_1(X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.60/0.84  cnf(c_0_56, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.60/0.84  cnf(c_0_57, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_52])).
% 0.60/0.84  fof(c_0_58, plain, ![X20, X21, X22]:(~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|v1_relat_1(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.60/0.84  cnf(c_0_59, plain, (r1_tarski(X1,X2)|~m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.60/0.84  cnf(c_0_60, plain, (k6_relat_1(k6_relat_1(X1))=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_55, c_0_50])).
% 0.60/0.84  cnf(c_0_61, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.60/0.84  cnf(c_0_62, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.60/0.84  cnf(c_0_63, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.60/0.84  cnf(c_0_64, plain, (r1_tarski(k6_relat_1(X1),X2)|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])])).
% 0.60/0.84  fof(c_0_65, negated_conjecture, ~(![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>((r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X3,X2),X2)&v2_funct_1(X2))=>r2_relset_1(X1,X1,X3,k6_partfun1(X1)))))), inference(assume_negation,[status(cth)],[t76_funct_2])).
% 0.60/0.84  cnf(c_0_66, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_40])).
% 0.60/0.84  cnf(c_0_67, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_62, c_0_61])).
% 0.60/0.84  cnf(c_0_68, plain, (X1=k2_relat_1(X2)|~v5_relat_1(X2,X1)|~v1_relat_1(X2)|~r1_tarski(X1,k2_relat_1(X2))), inference(spm,[status(thm)],[c_0_63, c_0_44])).
% 0.60/0.84  cnf(c_0_69, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(X2))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_56, c_0_64])).
% 0.60/0.84  fof(c_0_70, negated_conjecture, (((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk4_0,esk4_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk4_0,esk4_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))))&((r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0),esk5_0)&v2_funct_1(esk5_0))&~r2_relset_1(esk4_0,esk4_0,esk6_0,k6_partfun1(esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_65])])])).
% 0.60/0.84  cnf(c_0_71, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_45, c_0_66])).
% 0.60/0.84  cnf(c_0_72, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_67, c_0_48])).
% 0.60/0.84  cnf(c_0_73, plain, (X1=X2|~v5_relat_1(k6_relat_1(X2),X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_45]), c_0_46])])).
% 0.60/0.84  cnf(c_0_74, plain, (v5_relat_1(k6_relat_1(X1),X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_47, c_0_69])).
% 0.60/0.84  cnf(c_0_75, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_41, c_0_61])).
% 0.60/0.84  cnf(c_0_76, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.60/0.84  cnf(c_0_77, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.60/0.84  cnf(c_0_78, plain, (r1_tarski(k1_xboole_0,X1)|~v5_relat_1(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_71]), c_0_72])])).
% 0.60/0.84  cnf(c_0_79, plain, (X1=X2|~r1_tarski(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.60/0.84  cnf(c_0_80, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.60/0.84  cnf(c_0_81, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_49, c_0_75])).
% 0.60/0.84  fof(c_0_82, plain, ![X75, X76, X77]:(((v1_funct_1(k2_funct_1(X77))|(~v2_funct_1(X77)|k2_relset_1(X75,X76,X77)!=X76)|(~v1_funct_1(X77)|~v1_funct_2(X77,X75,X76)|~m1_subset_1(X77,k1_zfmisc_1(k2_zfmisc_1(X75,X76)))))&(v1_funct_2(k2_funct_1(X77),X76,X75)|(~v2_funct_1(X77)|k2_relset_1(X75,X76,X77)!=X76)|(~v1_funct_1(X77)|~v1_funct_2(X77,X75,X76)|~m1_subset_1(X77,k1_zfmisc_1(k2_zfmisc_1(X75,X76))))))&(m1_subset_1(k2_funct_1(X77),k1_zfmisc_1(k2_zfmisc_1(X76,X75)))|(~v2_funct_1(X77)|k2_relset_1(X75,X76,X77)!=X76)|(~v1_funct_1(X77)|~v1_funct_2(X77,X75,X76)|~m1_subset_1(X77,k1_zfmisc_1(k2_zfmisc_1(X75,X76)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).
% 0.60/0.84  cnf(c_0_83, negated_conjecture, (v1_xboole_0(esk6_0)|~v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_41, c_0_76])).
% 0.60/0.84  cnf(c_0_84, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_77])).
% 0.60/0.84  cnf(c_0_85, plain, (r1_tarski(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_54]), c_0_61])])).
% 0.60/0.84  cnf(c_0_86, plain, (X1=X2|~m1_subset_1(X1,k1_zfmisc_1(X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.60/0.84  cnf(c_0_87, plain, (k2_zfmisc_1(X1,k6_relat_1(X2))=k1_xboole_0|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_81, c_0_50])).
% 0.60/0.84  cnf(c_0_88, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v2_funct_1(X1)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.60/0.84  cnf(c_0_89, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.60/0.84  cnf(c_0_90, negated_conjecture, (k6_relat_1(esk6_0)=k1_xboole_0|~v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_55, c_0_83])).
% 0.60/0.84  cnf(c_0_91, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_84]), c_0_40])])).
% 0.60/0.84  cnf(c_0_92, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_56, c_0_85])).
% 0.60/0.84  cnf(c_0_93, plain, (k6_relat_1(X1)=k2_zfmisc_1(X1,X1)|~v1_xboole_0(k2_zfmisc_1(X1,X1))), inference(spm,[status(thm)],[c_0_86, c_0_42])).
% 0.60/0.84  cnf(c_0_94, plain, (k2_zfmisc_1(X1,k6_relat_1(k6_relat_1(X2)))=k1_xboole_0|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_87, c_0_50])).
% 0.60/0.84  cnf(c_0_95, plain, (v1_xboole_0(k2_funct_1(X1))|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_2(X1,X2,X3)|~v1_funct_1(X1)|~v2_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_41, c_0_88])).
% 0.60/0.84  cnf(c_0_96, negated_conjecture, (v1_funct_2(esk5_0,esk4_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.60/0.84  cnf(c_0_97, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.60/0.84  cnf(c_0_98, negated_conjecture, (v2_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.60/0.84  cnf(c_0_99, plain, (m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_56, c_0_44])).
% 0.60/0.84  cnf(c_0_100, negated_conjecture, (v5_relat_1(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_47, c_0_89])).
% 0.60/0.84  cnf(c_0_101, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_62, c_0_89])).
% 0.60/0.84  cnf(c_0_102, negated_conjecture, (k6_relat_1(esk6_0)=k1_xboole_0|~m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.60/0.84  cnf(c_0_103, plain, (v5_relat_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_47, c_0_92])).
% 0.60/0.84  cnf(c_0_104, plain, (k6_relat_1(k6_relat_1(k6_relat_1(X1)))=k1_xboole_0|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_40])])).
% 0.60/0.84  cnf(c_0_105, negated_conjecture, (v1_xboole_0(k2_funct_1(esk5_0))|k2_relset_1(esk4_0,esk4_0,esk5_0)!=esk4_0|~v1_xboole_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_89]), c_0_96]), c_0_97]), c_0_98])])).
% 0.60/0.84  fof(c_0_106, plain, ![X32, X33, X34]:(~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|k2_relset_1(X32,X33,X34)=k2_relat_1(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.60/0.84  cnf(c_0_107, negated_conjecture, (m1_subset_1(k2_relat_1(esk5_0),k1_zfmisc_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_101])])).
% 0.60/0.84  cnf(c_0_108, negated_conjecture, (X1=esk6_0|~v1_xboole_0(esk4_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_39, c_0_83])).
% 0.60/0.84  fof(c_0_109, plain, ![X29, X30, X31]:(~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|k1_relset_1(X29,X30,X31)=k1_relat_1(X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.60/0.84  fof(c_0_110, plain, ![X80, X81]:(~v1_funct_1(X81)|~v1_funct_2(X81,X80,X80)|~m1_subset_1(X81,k1_zfmisc_1(k2_zfmisc_1(X80,X80)))|k1_relset_1(X80,X80,X81)=X80), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_funct_2])])).
% 0.60/0.84  fof(c_0_111, plain, ![X78, X79]:(((v1_funct_1(X79)|~r1_tarski(k2_relat_1(X79),X78)|(~v1_relat_1(X79)|~v1_funct_1(X79)))&(v1_funct_2(X79,k1_relat_1(X79),X78)|~r1_tarski(k2_relat_1(X79),X78)|(~v1_relat_1(X79)|~v1_funct_1(X79))))&(m1_subset_1(X79,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X79),X78)))|~r1_tarski(k2_relat_1(X79),X78)|(~v1_relat_1(X79)|~v1_funct_1(X79)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).
% 0.60/0.84  cnf(c_0_112, negated_conjecture, (r1_tarski(esk6_0,X1)|~m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_102]), c_0_103])])).
% 0.60/0.84  cnf(c_0_113, plain, (r1_tarski(k6_relat_1(k6_relat_1(X1)),X2)|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_104]), c_0_103])])).
% 0.60/0.84  fof(c_0_114, plain, ![X19]:((k5_relat_1(X19,k2_funct_1(X19))=k6_relat_1(k1_relat_1(X19))|~v2_funct_1(X19)|(~v1_relat_1(X19)|~v1_funct_1(X19)))&(k5_relat_1(k2_funct_1(X19),X19)=k6_relat_1(k2_relat_1(X19))|~v2_funct_1(X19)|(~v1_relat_1(X19)|~v1_funct_1(X19)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).
% 0.60/0.84  cnf(c_0_115, negated_conjecture, (k2_funct_1(esk5_0)=k1_xboole_0|k2_relset_1(esk4_0,esk4_0,esk5_0)!=esk4_0|~v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_49, c_0_105])).
% 0.60/0.84  cnf(c_0_116, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_106])).
% 0.60/0.84  cnf(c_0_117, negated_conjecture, (k2_relat_1(esk5_0)=esk4_0|~v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_86, c_0_107])).
% 0.60/0.84  cnf(c_0_118, negated_conjecture, (X1=esk6_0|~m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_108, c_0_91])).
% 0.60/0.84  cnf(c_0_119, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_109])).
% 0.60/0.84  cnf(c_0_120, plain, (k1_relset_1(X2,X2,X1)=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_110])).
% 0.60/0.84  cnf(c_0_121, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_111])).
% 0.60/0.84  cnf(c_0_122, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(X1))|~m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_56, c_0_112])).
% 0.60/0.84  cnf(c_0_123, plain, (k6_relat_1(k6_relat_1(X1))=X2|~v1_xboole_0(X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_79, c_0_113])).
% 0.60/0.84  cnf(c_0_124, plain, (k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_114])).
% 0.60/0.84  cnf(c_0_125, negated_conjecture, (k2_funct_1(esk5_0)=k1_xboole_0|~v1_xboole_0(esk4_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116]), c_0_89])]), c_0_117])).
% 0.60/0.84  cnf(c_0_126, negated_conjecture, (k6_relat_1(X1)=esk6_0|~m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_118, c_0_50])).
% 0.60/0.84  cnf(c_0_127, plain, (X1=k1_relat_1(X2)|~v1_funct_2(X2,X1,X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(spm,[status(thm)],[c_0_119, c_0_120])).
% 0.60/0.84  cnf(c_0_128, negated_conjecture, (v1_funct_2(esk6_0,esk4_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.60/0.84  cnf(c_0_129, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.60/0.84  cnf(c_0_130, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_121, c_0_57])).
% 0.60/0.84  cnf(c_0_131, plain, (k2_relat_1(X1)=k1_xboole_0|~v5_relat_1(X1,k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_68, c_0_85])).
% 0.60/0.84  cnf(c_0_132, negated_conjecture, (v5_relat_1(esk6_0,X1)|~m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_47, c_0_122])).
% 0.60/0.84  cnf(c_0_133, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_62, c_0_76])).
% 0.60/0.84  cnf(c_0_134, plain, (v1_funct_2(X1,k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_111])).
% 0.60/0.84  cnf(c_0_135, negated_conjecture, (k6_relat_1(k6_relat_1(X1))=esk6_0|~v1_xboole_0(esk4_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_123, c_0_83])).
% 0.60/0.84  cnf(c_0_136, negated_conjecture, (k6_relat_1(k2_relat_1(esk5_0))=k5_relat_1(k1_xboole_0,esk5_0)|~v1_xboole_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_125]), c_0_97]), c_0_98]), c_0_101])])).
% 0.60/0.84  cnf(c_0_137, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.60/0.84  cnf(c_0_138, negated_conjecture, (k6_relat_1(k6_relat_1(X1))=esk6_0|~m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_126, c_0_50])).
% 0.60/0.84  cnf(c_0_139, negated_conjecture, (k1_relat_1(esk6_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_76]), c_0_128]), c_0_129])])).
% 0.60/0.84  cnf(c_0_140, plain, (v1_xboole_0(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~v1_xboole_0(k2_relat_1(X1))), inference(spm,[status(thm)],[c_0_41, c_0_130])).
% 0.60/0.84  cnf(c_0_141, negated_conjecture, (k2_relat_1(esk6_0)=k1_xboole_0|~m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_132]), c_0_133])])).
% 0.60/0.84  cnf(c_0_142, plain, (v1_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.60/0.84  cnf(c_0_143, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_134, c_0_57])).
% 0.60/0.84  cnf(c_0_144, negated_conjecture, (k1_relat_1(esk5_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_89]), c_0_96]), c_0_97])])).
% 0.60/0.84  fof(c_0_145, plain, ![X41, X42, X43, X44]:((~r2_relset_1(X41,X42,X43,X44)|X43=X44|(~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))))&(X43!=X44|r2_relset_1(X41,X42,X43,X44)|(~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.60/0.84  fof(c_0_146, plain, ![X63, X64, X65]:((r2_relset_1(X63,X64,k4_relset_1(X63,X63,X63,X64,k6_partfun1(X63),X65),X65)|~m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))))&(r2_relset_1(X63,X64,k4_relset_1(X63,X64,X64,X64,X65,k6_partfun1(X64)),X65)|~m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_2])])])).
% 0.60/0.84  fof(c_0_147, plain, ![X49, X50, X51, X52, X53, X54]:((v1_funct_1(k1_partfun1(X49,X50,X51,X52,X53,X54))|(~v1_funct_1(X53)|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))|~v1_funct_1(X54)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))))&(m1_subset_1(k1_partfun1(X49,X50,X51,X52,X53,X54),k1_zfmisc_1(k2_zfmisc_1(X49,X52)))|(~v1_funct_1(X53)|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))|~v1_funct_1(X54)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).
% 0.60/0.84  fof(c_0_148, plain, ![X56, X57, X58, X59, X60, X61]:(~v1_funct_1(X60)|~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))|~v1_funct_1(X61)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X58,X59)))|k1_partfun1(X56,X57,X58,X59,X60,X61)=k5_relat_1(X60,X61)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 0.60/0.84  cnf(c_0_149, negated_conjecture, (k6_relat_1(k5_relat_1(k1_xboole_0,esk5_0))=esk6_0|~v1_xboole_0(k2_relat_1(esk5_0))|~v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_135, c_0_136])).
% 0.60/0.84  cnf(c_0_150, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_62, c_0_48])).
% 0.60/0.84  cnf(c_0_151, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_74]), c_0_45]), c_0_46])])).
% 0.60/0.84  cnf(c_0_152, negated_conjecture, (v1_xboole_0(esk5_0)|~v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_41, c_0_89])).
% 0.60/0.84  cnf(c_0_153, negated_conjecture, (k6_relat_1(X1)=esk4_0|~m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))|~v1_xboole_0(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_138]), c_0_139])).
% 0.60/0.84  cnf(c_0_154, negated_conjecture, (v1_xboole_0(esk6_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140, c_0_141]), c_0_129]), c_0_133]), c_0_40])])).
% 0.60/0.84  cnf(c_0_155, plain, (v1_funct_1(k2_funct_1(X1))|~v1_funct_2(X1,X2,k2_relat_1(X1))|~v1_funct_1(X1)|~v2_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(X1))))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_142, c_0_116])])).
% 0.60/0.84  cnf(c_0_156, negated_conjecture, (v1_funct_2(esk5_0,esk4_0,k2_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_144]), c_0_97]), c_0_101])])).
% 0.60/0.84  cnf(c_0_157, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_145])).
% 0.60/0.84  cnf(c_0_158, negated_conjecture, (r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.60/0.84  cnf(c_0_159, plain, (r2_relset_1(X1,X2,k4_relset_1(X1,X1,X1,X2,k6_partfun1(X1),X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_146])).
% 0.60/0.84  fof(c_0_160, plain, ![X35, X36, X37, X38, X39, X40]:(~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))|k4_relset_1(X35,X36,X37,X38,X39,X40)=k5_relat_1(X39,X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_relset_1])])).
% 0.60/0.84  fof(c_0_161, plain, ![X45, X46, X47, X48]:(~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))|(~r2_relset_1(X45,X46,X47,X48)|r2_relset_1(X45,X46,X48,X47))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r2_relset_1])])).
% 0.60/0.84  cnf(c_0_162, plain, (v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_147])).
% 0.60/0.84  cnf(c_0_163, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_148])).
% 0.60/0.85  cnf(c_0_164, plain, (v5_relat_1(k6_relat_1(X1),X1)), inference(spm,[status(thm)],[c_0_47, c_0_42])).
% 0.60/0.85  cnf(c_0_165, negated_conjecture, (k5_relat_1(k1_xboole_0,esk5_0)=esk4_0|~v1_xboole_0(k2_relat_1(esk5_0))|~v1_xboole_0(esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_149]), c_0_139])).
% 0.60/0.85  cnf(c_0_166, plain, (k2_relat_1(X1)=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_54]), c_0_150])).
% 0.60/0.85  cnf(c_0_167, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(X1))|~v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_151, c_0_152])).
% 0.60/0.85  cnf(c_0_168, negated_conjecture, (~r2_relset_1(esk4_0,esk4_0,esk6_0,k6_partfun1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.60/0.85  cnf(c_0_169, negated_conjecture, (k6_relat_1(esk6_0)=esk4_0|~m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_153, c_0_154])).
% 0.60/0.85  cnf(c_0_170, plain, (m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_54]), c_0_150])).
% 0.60/0.85  cnf(c_0_171, negated_conjecture, (v1_funct_1(k2_funct_1(esk5_0))|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_relat_1(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_155, c_0_156]), c_0_97]), c_0_98])])).
% 0.60/0.85  cnf(c_0_172, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_relat_1(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_144]), c_0_97]), c_0_101])])).
% 0.60/0.85  fof(c_0_173, plain, ![X66, X67, X68, X69, X70, X71]:((~v2_funct_1(X68)|(~v1_funct_1(X70)|~v1_funct_2(X70,X69,X66)|~m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X69,X66)))|(~v1_funct_1(X71)|~v1_funct_2(X71,X69,X66)|~m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X69,X66)))|(~r2_relset_1(X69,X67,k1_partfun1(X69,X66,X66,X67,X70,X68),k1_partfun1(X69,X66,X66,X67,X71,X68))|r2_relset_1(X69,X66,X70,X71))))|(X66=k1_xboole_0|X67=k1_xboole_0)|(~v1_funct_1(X68)|~v1_funct_2(X68,X66,X67)|~m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67)))))&((((v1_funct_1(esk2_3(X66,X67,X68))|v2_funct_1(X68)|(X66=k1_xboole_0|X67=k1_xboole_0)|(~v1_funct_1(X68)|~v1_funct_2(X68,X66,X67)|~m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67)))))&(v1_funct_2(esk2_3(X66,X67,X68),esk1_3(X66,X67,X68),X66)|v2_funct_1(X68)|(X66=k1_xboole_0|X67=k1_xboole_0)|(~v1_funct_1(X68)|~v1_funct_2(X68,X66,X67)|~m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67))))))&(m1_subset_1(esk2_3(X66,X67,X68),k1_zfmisc_1(k2_zfmisc_1(esk1_3(X66,X67,X68),X66)))|v2_funct_1(X68)|(X66=k1_xboole_0|X67=k1_xboole_0)|(~v1_funct_1(X68)|~v1_funct_2(X68,X66,X67)|~m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67))))))&((((v1_funct_1(esk3_3(X66,X67,X68))|v2_funct_1(X68)|(X66=k1_xboole_0|X67=k1_xboole_0)|(~v1_funct_1(X68)|~v1_funct_2(X68,X66,X67)|~m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67)))))&(v1_funct_2(esk3_3(X66,X67,X68),esk1_3(X66,X67,X68),X66)|v2_funct_1(X68)|(X66=k1_xboole_0|X67=k1_xboole_0)|(~v1_funct_1(X68)|~v1_funct_2(X68,X66,X67)|~m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67))))))&(m1_subset_1(esk3_3(X66,X67,X68),k1_zfmisc_1(k2_zfmisc_1(esk1_3(X66,X67,X68),X66)))|v2_funct_1(X68)|(X66=k1_xboole_0|X67=k1_xboole_0)|(~v1_funct_1(X68)|~v1_funct_2(X68,X66,X67)|~m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67))))))&((r2_relset_1(esk1_3(X66,X67,X68),X67,k1_partfun1(esk1_3(X66,X67,X68),X66,X66,X67,esk2_3(X66,X67,X68),X68),k1_partfun1(esk1_3(X66,X67,X68),X66,X66,X67,esk3_3(X66,X67,X68),X68))|v2_funct_1(X68)|(X66=k1_xboole_0|X67=k1_xboole_0)|(~v1_funct_1(X68)|~v1_funct_2(X68,X66,X67)|~m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67)))))&(~r2_relset_1(esk1_3(X66,X67,X68),X66,esk2_3(X66,X67,X68),esk3_3(X66,X67,X68))|v2_funct_1(X68)|(X66=k1_xboole_0|X67=k1_xboole_0)|(~v1_funct_1(X68)|~v1_funct_2(X68,X66,X67)|~m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67))))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_funct_2])])])])])).
% 0.60/0.85  cnf(c_0_174, negated_conjecture, (k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0)=esk5_0|~m1_subset_1(k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_157, c_0_158]), c_0_89])])).
% 0.60/0.85  cnf(c_0_175, plain, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_147])).
% 0.60/0.85  cnf(c_0_176, plain, (r2_relset_1(X1,X2,k4_relset_1(X1,X1,X1,X2,k6_relat_1(X1),X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(rw,[status(thm)],[c_0_159, c_0_33])).
% 0.60/0.85  cnf(c_0_177, plain, (k4_relset_1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_160])).
% 0.60/0.85  cnf(c_0_178, plain, (r2_relset_1(X2,X3,X4,X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_relset_1(X2,X3,X1,X4)), inference(split_conjunct,[status(thm)],[c_0_161])).
% 0.60/0.85  cnf(c_0_179, plain, (v1_funct_1(k5_relat_1(X1,X2))|~v1_funct_1(X2)|~v1_funct_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(spm,[status(thm)],[c_0_162, c_0_163])).
% 0.60/0.85  cnf(c_0_180, plain, (v1_relat_1(k2_funct_1(X1))|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_2(X1,X2,X3)|~v1_funct_1(X1)|~v2_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_62, c_0_88])).
% 0.60/0.85  cnf(c_0_181, negated_conjecture, (v5_relat_1(k5_relat_1(k1_xboole_0,esk5_0),k2_relat_1(esk5_0))|~v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_164, c_0_136])).
% 0.60/0.85  cnf(c_0_182, negated_conjecture, (k5_relat_1(k1_xboole_0,esk5_0)=esk4_0|~v1_xboole_0(esk4_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_165, c_0_166]), c_0_40])]), c_0_167])).
% 0.60/0.85  cnf(c_0_183, negated_conjecture, (~r2_relset_1(esk4_0,esk4_0,esk6_0,k6_relat_1(esk4_0))), inference(rw,[status(thm)],[c_0_168, c_0_33])).
% 0.60/0.85  cnf(c_0_184, negated_conjecture, (k6_relat_1(esk4_0)=esk6_0|~m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_169]), c_0_154])).
% 0.60/0.85  cnf(c_0_185, plain, (r2_relset_1(X3,X4,X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_145])).
% 0.60/0.85  cnf(c_0_186, plain, (v1_relat_1(k2_relat_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_62, c_0_170])).
% 0.60/0.85  cnf(c_0_187, negated_conjecture, (v1_funct_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_171, c_0_172])])).
% 0.60/0.85  cnf(c_0_188, plain, (r2_relset_1(X3,X4,X2,X5)|X4=k1_xboole_0|X6=k1_xboole_0|~v2_funct_1(X1)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~r2_relset_1(X3,X6,k1_partfun1(X3,X4,X4,X6,X2,X1),k1_partfun1(X3,X4,X4,X6,X5,X1))|~v1_funct_1(X1)|~v1_funct_2(X1,X4,X6)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X6)))), inference(split_conjunct,[status(thm)],[c_0_173])).
% 0.60/0.85  cnf(c_0_189, negated_conjecture, (k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_174, c_0_175]), c_0_97]), c_0_129]), c_0_89]), c_0_76])])).
% 0.60/0.85  cnf(c_0_190, plain, (r2_relset_1(X1,X2,k5_relat_1(k6_relat_1(X1),X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_176, c_0_177]), c_0_42])])).
% 0.60/0.85  cnf(c_0_191, negated_conjecture, (r2_relset_1(esk4_0,esk4_0,esk6_0,X1)|~r2_relset_1(esk4_0,esk4_0,X1,esk6_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))), inference(spm,[status(thm)],[c_0_178, c_0_76])).
% 0.60/0.85  cnf(c_0_192, plain, (v1_funct_1(k5_relat_1(X1,X2))|~v1_funct_1(X2)|~v1_funct_1(X1)|~v1_relat_1(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(spm,[status(thm)],[c_0_179, c_0_130])).
% 0.60/0.85  cnf(c_0_193, negated_conjecture, (v1_relat_1(k2_funct_1(esk5_0))|k2_relset_1(esk4_0,k2_relat_1(esk5_0),esk5_0)!=k2_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_180, c_0_172]), c_0_156]), c_0_97]), c_0_98])])).
% 0.60/0.85  cnf(c_0_194, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|~v1_funct_1(X1)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_121, c_0_44])).
% 0.60/0.85  cnf(c_0_195, negated_conjecture, (v5_relat_1(esk4_0,k2_relat_1(esk5_0))|~v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_181, c_0_182])).
% 0.60/0.85  cnf(c_0_196, negated_conjecture, (~r2_relset_1(esk4_0,esk4_0,esk6_0,esk6_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_183, c_0_184])).
% 0.60/0.85  cnf(c_0_197, plain, (r2_relset_1(X1,X2,X3,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_185])).
% 0.60/0.85  cnf(c_0_198, plain, (v1_relat_1(X1)|~m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_186, c_0_45])).
% 0.60/0.85  cnf(c_0_199, negated_conjecture, (v1_funct_1(k1_xboole_0)|~v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_187, c_0_125])).
% 0.60/0.85  cnf(c_0_200, negated_conjecture, (esk4_0=k1_xboole_0|r2_relset_1(esk4_0,esk4_0,X1,esk6_0)|~v1_funct_2(X1,esk4_0,esk4_0)|~r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,X1,esk5_0),esk5_0)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_188, c_0_189]), c_0_128]), c_0_96]), c_0_129]), c_0_97]), c_0_98]), c_0_76]), c_0_89])])).
% 0.60/0.85  cnf(c_0_201, plain, (r2_relset_1(X1,X2,k1_partfun1(X3,X4,X5,X6,k6_relat_1(X1),X7),X7)|~v1_funct_1(k6_relat_1(X1))|~v1_funct_1(X7)|~m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(spm,[status(thm)],[c_0_190, c_0_163])).
% 0.60/0.85  cnf(c_0_202, negated_conjecture, (~r2_relset_1(esk4_0,esk4_0,k6_relat_1(esk4_0),esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_191, c_0_42]), c_0_183])).
% 0.60/0.85  cnf(c_0_203, plain, (v1_funct_2(k6_relat_1(X1),X1,X1)|~v1_funct_1(k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_45]), c_0_137]), c_0_46])])).
% 0.60/0.85  cnf(c_0_204, negated_conjecture, (v1_funct_1(k5_relat_1(esk5_0,X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_192, c_0_89]), c_0_97])])).
% 0.60/0.85  cnf(c_0_205, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_114])).
% 0.60/0.85  cnf(c_0_206, negated_conjecture, (v1_relat_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_193, c_0_116]), c_0_172])])).
% 0.60/0.85  cnf(c_0_207, plain, (m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))|~v1_funct_1(X1)|~v5_relat_1(X1,k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_194, c_0_84])).
% 0.60/0.85  cnf(c_0_208, negated_conjecture, (v5_relat_1(esk4_0,k1_xboole_0)|~v1_xboole_0(esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_195, c_0_166]), c_0_167])).
% 0.60/0.85  cnf(c_0_209, negated_conjecture, (~m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_196, c_0_197]), c_0_76])])).
% 0.60/0.85  cnf(c_0_210, plain, (v1_relat_1(X1)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_198, c_0_69])).
% 0.60/0.85  cnf(c_0_211, negated_conjecture, (v1_funct_1(esk4_0)|~v1_xboole_0(esk4_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_179, c_0_182]), c_0_97]), c_0_92])]), c_0_167]), c_0_199])).
% 0.60/0.85  cnf(c_0_212, negated_conjecture, (esk4_0=k1_xboole_0|~v1_funct_1(k6_relat_1(esk4_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_200, c_0_201]), c_0_42]), c_0_97]), c_0_89])]), c_0_202]), c_0_203])).
% 0.60/0.85  cnf(c_0_213, negated_conjecture, (v1_funct_1(k6_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_204, c_0_205]), c_0_144]), c_0_187]), c_0_206]), c_0_97]), c_0_98]), c_0_101])])).
% 0.60/0.85  cnf(c_0_214, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_207, c_0_208]), c_0_209]), c_0_210]), c_0_211])).
% 0.60/0.85  cnf(c_0_215, negated_conjecture, (esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_212, c_0_213])])).
% 0.60/0.85  cnf(c_0_216, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_214, c_0_215]), c_0_40])]), ['proof']).
% 0.60/0.85  # SZS output end CNFRefutation
% 0.60/0.85  # Proof object total steps             : 217
% 0.60/0.85  # Proof object clause steps            : 163
% 0.60/0.85  # Proof object formula steps           : 54
% 0.60/0.85  # Proof object conjectures             : 69
% 0.60/0.85  # Proof object clause conjectures      : 66
% 0.60/0.85  # Proof object formula conjectures     : 3
% 0.60/0.85  # Proof object initial clauses used    : 44
% 0.60/0.85  # Proof object initial formulas used   : 27
% 0.60/0.85  # Proof object generating inferences   : 109
% 0.60/0.85  # Proof object simplifying inferences  : 131
% 0.60/0.85  # Training examples: 0 positive, 0 negative
% 0.60/0.85  # Parsed axioms                        : 27
% 0.60/0.85  # Removed by relevancy pruning/SinE    : 0
% 0.60/0.85  # Initial clauses                      : 61
% 0.60/0.85  # Removed in clause preprocessing      : 2
% 0.60/0.85  # Initial clauses in saturation        : 59
% 0.60/0.85  # Processed clauses                    : 6503
% 0.60/0.85  # ...of these trivial                  : 31
% 0.60/0.85  # ...subsumed                          : 5060
% 0.60/0.85  # ...remaining for further processing  : 1412
% 0.60/0.85  # Other redundant clauses eliminated   : 40
% 0.60/0.85  # Clauses deleted for lack of memory   : 0
% 0.60/0.85  # Backward-subsumed                    : 103
% 0.60/0.85  # Backward-rewritten                   : 516
% 0.60/0.85  # Generated clauses                    : 29030
% 0.60/0.85  # ...of the previous two non-trivial   : 24114
% 0.60/0.85  # Contextual simplify-reflections      : 200
% 0.60/0.85  # Paramodulations                      : 28958
% 0.60/0.85  # Factorizations                       : 32
% 0.60/0.85  # Equation resolutions                 : 40
% 0.60/0.85  # Propositional unsat checks           : 0
% 0.60/0.85  #    Propositional check models        : 0
% 0.60/0.85  #    Propositional check unsatisfiable : 0
% 0.60/0.85  #    Propositional clauses             : 0
% 0.60/0.85  #    Propositional clauses after purity: 0
% 0.60/0.85  #    Propositional unsat core size     : 0
% 0.60/0.85  #    Propositional preprocessing time  : 0.000
% 0.60/0.85  #    Propositional encoding time       : 0.000
% 0.60/0.85  #    Propositional solver time         : 0.000
% 0.60/0.85  #    Success case prop preproc time    : 0.000
% 0.60/0.85  #    Success case prop encoding time   : 0.000
% 0.60/0.85  #    Success case prop solver time     : 0.000
% 0.60/0.85  # Current number of processed clauses  : 730
% 0.60/0.85  #    Positive orientable unit clauses  : 46
% 0.60/0.85  #    Positive unorientable unit clauses: 0
% 0.60/0.85  #    Negative unit clauses             : 0
% 0.60/0.85  #    Non-unit-clauses                  : 684
% 0.60/0.85  # Current number of unprocessed clauses: 17371
% 0.60/0.85  # ...number of literals in the above   : 99189
% 0.60/0.85  # Current number of archived formulas  : 0
% 0.60/0.85  # Current number of archived clauses   : 678
% 0.60/0.85  # Clause-clause subsumption calls (NU) : 360274
% 0.60/0.85  # Rec. Clause-clause subsumption calls : 93007
% 0.60/0.85  # Non-unit clause-clause subsumptions  : 3268
% 0.60/0.85  # Unit Clause-clause subsumption calls : 1159
% 0.60/0.85  # Rewrite failures with RHS unbound    : 0
% 0.60/0.85  # BW rewrite match attempts            : 175
% 0.60/0.85  # BW rewrite match successes           : 13
% 0.60/0.85  # Condensation attempts                : 0
% 0.60/0.85  # Condensation successes               : 0
% 0.60/0.85  # Termbank termtop insertions          : 591909
% 0.68/0.85  
% 0.68/0.85  # -------------------------------------------------
% 0.68/0.85  # User time                : 0.487 s
% 0.68/0.85  # System time              : 0.020 s
% 0.68/0.85  # Total time               : 0.507 s
% 0.68/0.85  # Maximum resident set size: 1620 pages
%------------------------------------------------------------------------------
