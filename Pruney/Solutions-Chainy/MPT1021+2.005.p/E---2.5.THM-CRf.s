%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:07 EST 2020

% Result     : Theorem 1.29s
% Output     : CNFRefutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :  236 (17766 expanded)
%              Number of clauses        :  166 (6949 expanded)
%              Number of leaves         :   35 (4499 expanded)
%              Depth                    :   23
%              Number of atoms          :  688 (69461 expanded)
%              Number of equality atoms :  154 (5473 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t88_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & v3_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ( r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,k2_funct_2(X1,X2)),k6_partfun1(X1))
        & r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,k2_funct_2(X1,X2),X2),k6_partfun1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(t29_relset_1,axiom,(
    ! [X1] : m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t69_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

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

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(rc1_funct_2,axiom,(
    ! [X1,X2] :
    ? [X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_relat_1(X3)
      & v4_relat_1(X3,X1)
      & v5_relat_1(X3,X2)
      & v1_funct_1(X3)
      & v1_funct_2(X3,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(redefinition_k2_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & v3_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => k2_funct_2(X1,X2) = k2_funct_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(d3_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1) )
     => ( v2_funct_2(X2,X1)
      <=> k2_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

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

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(t38_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( k7_relset_1(X1,X2,X3,X1) = k2_relset_1(X1,X2,X3)
        & k8_relset_1(X1,X2,X3,X2) = k1_relset_1(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

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

fof(dt_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(t35_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( k2_relset_1(X1,X2,X3) = X2
          & v2_funct_1(X3) )
       => ( X2 = k1_xboole_0
          | ( k5_relat_1(X3,k2_funct_1(X3)) = k6_partfun1(X1)
            & k5_relat_1(k2_funct_1(X3),X3) = k6_partfun1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(dt_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
        & m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(reflexivity_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => r2_relset_1(X1,X2,X3,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(c_0_35,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_funct_2(X2,X1,X1)
          & v3_funct_2(X2,X1,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
       => ( r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,k2_funct_2(X1,X2)),k6_partfun1(X1))
          & r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,k2_funct_2(X1,X2),X2),k6_partfun1(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t88_funct_2])).

fof(c_0_36,plain,(
    ! [X42,X43,X44] :
      ( ~ v1_xboole_0(X42)
      | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X43,X42)))
      | v1_xboole_0(X44) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

fof(c_0_37,plain,(
    ! [X56] : m1_subset_1(k6_relat_1(X56),k1_zfmisc_1(k2_zfmisc_1(X56,X56))) ),
    inference(variable_rename,[status(thm)],[t29_relset_1])).

fof(c_0_38,plain,(
    ! [X18,X19] :
      ( ( k2_zfmisc_1(X18,X19) != k1_xboole_0
        | X18 = k1_xboole_0
        | X19 = k1_xboole_0 )
      & ( X18 != k1_xboole_0
        | k2_zfmisc_1(X18,X19) = k1_xboole_0 )
      & ( X19 != k1_xboole_0
        | k2_zfmisc_1(X18,X19) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_39,plain,(
    ! [X14,X15] :
      ( v1_xboole_0(X15)
      | ~ r1_tarski(X15,X14)
      | ~ r1_xboole_0(X15,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

fof(c_0_40,plain,(
    ! [X13] : r1_xboole_0(X13,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_41,plain,(
    ! [X64,X65,X66] :
      ( ( v1_funct_1(X66)
        | ~ v1_funct_1(X66)
        | ~ v3_funct_2(X66,X64,X65)
        | ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65))) )
      & ( v2_funct_1(X66)
        | ~ v1_funct_1(X66)
        | ~ v3_funct_2(X66,X64,X65)
        | ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65))) )
      & ( v2_funct_2(X66,X65)
        | ~ v1_funct_1(X66)
        | ~ v3_funct_2(X66,X64,X65)
        | ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_funct_2])])])).

fof(c_0_42,negated_conjecture,
    ( v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk5_0,esk5_0)
    & v3_funct_2(esk6_0,esk5_0,esk5_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk5_0)))
    & ( ~ r2_relset_1(esk5_0,esk5_0,k1_partfun1(esk5_0,esk5_0,esk5_0,esk5_0,esk6_0,k2_funct_2(esk5_0,esk6_0)),k6_partfun1(esk5_0))
      | ~ r2_relset_1(esk5_0,esk5_0,k1_partfun1(esk5_0,esk5_0,esk5_0,esk5_0,k2_funct_2(esk5_0,esk6_0),esk6_0),k6_partfun1(esk5_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_35])])])).

fof(c_0_43,plain,(
    ! [X39,X40,X41] :
      ( ( v4_relat_1(X41,X39)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( v5_relat_1(X41,X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_44,plain,(
    ! [X36,X37,X38] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
      | v1_relat_1(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_45,plain,(
    ! [X16,X17] :
      ( ~ v1_xboole_0(X16)
      | X16 = X17
      | ~ v1_xboole_0(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_46,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_48,plain,(
    ! [X77,X78] :
      ( m1_subset_1(esk4_2(X77,X78),k1_zfmisc_1(k2_zfmisc_1(X77,X78)))
      & v1_relat_1(esk4_2(X77,X78))
      & v4_relat_1(esk4_2(X77,X78),X77)
      & v5_relat_1(esk4_2(X77,X78),X78)
      & v1_funct_1(esk4_2(X77,X78))
      & v1_funct_2(esk4_2(X77,X78),X77,X78) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_funct_2])])).

cnf(c_0_49,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_50,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_51,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_52,plain,(
    ! [X11] :
      ( X11 = k1_xboole_0
      | r2_hidden(esk2_1(X11),X11) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_53,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_54,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_55,plain,(
    ! [X29,X30] :
      ( ( ~ v4_relat_1(X30,X29)
        | r1_tarski(k1_relat_1(X30),X29)
        | ~ v1_relat_1(X30) )
      & ( ~ r1_tarski(k1_relat_1(X30),X29)
        | v4_relat_1(X30,X29)
        | ~ v1_relat_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

fof(c_0_56,plain,(
    ! [X86,X87] :
      ( ~ v1_funct_1(X87)
      | ~ v1_funct_2(X87,X86,X86)
      | ~ v3_funct_2(X87,X86,X86)
      | ~ m1_subset_1(X87,k1_zfmisc_1(k2_zfmisc_1(X86,X86)))
      | k2_funct_2(X86,X87) = k2_funct_1(X87) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_funct_2])])).

fof(c_0_57,plain,(
    ! [X67,X68] :
      ( ( ~ v2_funct_2(X68,X67)
        | k2_relat_1(X68) = X67
        | ~ v1_relat_1(X68)
        | ~ v5_relat_1(X68,X67) )
      & ( k2_relat_1(X68) != X67
        | v2_funct_2(X68,X67)
        | ~ v1_relat_1(X68)
        | ~ v5_relat_1(X68,X67) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).

cnf(c_0_58,plain,
    ( v2_funct_2(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ v3_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_59,negated_conjecture,
    ( v3_funct_2(esk6_0,esk5_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_60,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_62,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_63,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_64,plain,(
    ! [X27,X28] :
      ( ~ v1_relat_1(X27)
      | ~ m1_subset_1(X28,k1_zfmisc_1(X27))
      | v1_relat_1(X28) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_65,plain,(
    ! [X75,X76] :
      ( ( v1_funct_1(k2_funct_2(X75,X76))
        | ~ v1_funct_1(X76)
        | ~ v1_funct_2(X76,X75,X75)
        | ~ v3_funct_2(X76,X75,X75)
        | ~ m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X75,X75))) )
      & ( v1_funct_2(k2_funct_2(X75,X76),X75,X75)
        | ~ v1_funct_1(X76)
        | ~ v1_funct_2(X76,X75,X75)
        | ~ v3_funct_2(X76,X75,X75)
        | ~ m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X75,X75))) )
      & ( v3_funct_2(k2_funct_2(X75,X76),X75,X75)
        | ~ v1_funct_1(X76)
        | ~ v1_funct_2(X76,X75,X75)
        | ~ v3_funct_2(X76,X75,X75)
        | ~ m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X75,X75))) )
      & ( m1_subset_1(k2_funct_2(X75,X76),k1_zfmisc_1(k2_zfmisc_1(X75,X75)))
        | ~ v1_funct_1(X76)
        | ~ v1_funct_2(X76,X75,X75)
        | ~ v3_funct_2(X76,X75,X75)
        | ~ m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X75,X75))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_2])])])).

fof(c_0_66,plain,(
    ! [X31,X32] : v1_relat_1(k2_zfmisc_1(X31,X32)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_67,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_68,plain,
    ( v1_xboole_0(k6_relat_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

fof(c_0_69,plain,(
    ! [X24,X25,X26] :
      ( ~ r2_hidden(X24,X25)
      | ~ m1_subset_1(X25,k1_zfmisc_1(X26))
      | ~ v1_xboole_0(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_70,plain,
    ( m1_subset_1(esk4_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_71,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_72,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_73,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_74,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_75,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_76,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_77,plain,(
    ! [X35] :
      ( ( k2_relat_1(X35) = k1_relat_1(k2_funct_1(X35))
        | ~ v2_funct_1(X35)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( k1_relat_1(X35) = k2_relat_1(k2_funct_1(X35))
        | ~ v2_funct_1(X35)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

cnf(c_0_78,plain,
    ( k2_funct_2(X2,X1) = k2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ v3_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_79,negated_conjecture,
    ( v1_funct_2(esk6_0,esk5_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_80,plain,
    ( v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v3_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_81,plain,
    ( k2_relat_1(X1) = X2
    | ~ v2_funct_2(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_82,negated_conjecture,
    ( v2_funct_2(esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60]),c_0_61])])).

cnf(c_0_83,negated_conjecture,
    ( v5_relat_1(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_61])).

cnf(c_0_84,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_61])).

cnf(c_0_85,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_86,plain,
    ( m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_87,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_88,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_89,plain,
    ( X1 = k6_relat_1(X2)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_90,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_61])).

fof(c_0_91,plain,(
    ! [X34] :
      ( ( k1_relat_1(X34) != k1_xboole_0
        | X34 = k1_xboole_0
        | ~ v1_relat_1(X34) )
      & ( k2_relat_1(X34) != k1_xboole_0
        | X34 = k1_xboole_0
        | ~ v1_relat_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

cnf(c_0_92,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_93,plain,
    ( m1_subset_1(esk4_2(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_94,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_95,plain,(
    ! [X20] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X20)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_96,plain,
    ( m1_subset_1(esk4_2(X1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_72])).

cnf(c_0_97,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_98,plain,
    ( v1_xboole_0(k1_relat_1(X1))
    | ~ v4_relat_1(X1,k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

fof(c_0_99,plain,(
    ! [X92] :
      ( ( v1_funct_1(X92)
        | ~ v1_relat_1(X92)
        | ~ v1_funct_1(X92) )
      & ( v1_funct_2(X92,k1_relat_1(X92),k2_relat_1(X92))
        | ~ v1_relat_1(X92)
        | ~ v1_funct_1(X92) )
      & ( m1_subset_1(X92,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X92),k2_relat_1(X92))))
        | ~ v1_relat_1(X92)
        | ~ v1_funct_1(X92) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

cnf(c_0_100,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_101,negated_conjecture,
    ( k2_funct_1(esk6_0) = k2_funct_2(esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_59]),c_0_79]),c_0_60]),c_0_61])])).

cnf(c_0_102,negated_conjecture,
    ( v2_funct_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_59]),c_0_60]),c_0_61])])).

cnf(c_0_103,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_104,negated_conjecture,
    ( k2_relat_1(esk6_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_83]),c_0_84])])).

cnf(c_0_105,plain,
    ( v1_funct_1(k2_funct_2(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_106,plain,
    ( v1_relat_1(k2_funct_2(X1,X2))
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_87])])).

cnf(c_0_107,plain,
    ( v4_relat_1(k6_relat_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_88,c_0_47])).

cnf(c_0_108,negated_conjecture,
    ( k6_relat_1(X1) = esk6_0
    | ~ v1_xboole_0(esk5_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_109,plain,
    ( X1 = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_110,plain,
    ( ~ r2_hidden(X1,esk4_2(k1_xboole_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_94])])).

cnf(c_0_111,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_112,plain,
    ( ~ r2_hidden(X1,esk4_2(X2,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_96]),c_0_94])])).

cnf(c_0_113,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | ~ v4_relat_1(X1,k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_114,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_72])).

cnf(c_0_115,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_72])).

cnf(c_0_116,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_117,negated_conjecture,
    ( k2_relat_1(k2_funct_2(esk5_0,esk6_0)) = k1_relat_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_102]),c_0_60]),c_0_84])])).

cnf(c_0_118,negated_conjecture,
    ( k1_relat_1(k2_funct_2(esk5_0,esk6_0)) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_101]),c_0_104]),c_0_102]),c_0_60]),c_0_84])])).

cnf(c_0_119,negated_conjecture,
    ( v1_funct_1(k2_funct_2(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_59]),c_0_79]),c_0_60]),c_0_61])])).

cnf(c_0_120,negated_conjecture,
    ( v1_relat_1(k2_funct_2(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_59]),c_0_79]),c_0_60]),c_0_61])])).

cnf(c_0_121,negated_conjecture,
    ( v4_relat_1(esk6_0,X1)
    | ~ v1_xboole_0(esk5_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_107,c_0_108])).

cnf(c_0_122,plain,
    ( k2_funct_1(X1) = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_109,c_0_103])).

cnf(c_0_123,plain,
    ( v4_relat_1(esk4_2(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_124,plain,
    ( esk4_2(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_110,c_0_74])).

cnf(c_0_125,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_111])).

cnf(c_0_126,plain,
    ( esk4_2(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_112,c_0_74])).

cnf(c_0_127,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_115])).

cnf(c_0_128,negated_conjecture,
    ( m1_subset_1(k2_funct_2(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_relat_1(esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_117]),c_0_118]),c_0_119]),c_0_120])])).

cnf(c_0_129,negated_conjecture,
    ( k1_relat_1(esk6_0) = k1_xboole_0
    | ~ v1_xboole_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_121]),c_0_84]),c_0_94])])).

cnf(c_0_130,plain,
    ( v2_funct_2(X1,X2)
    | k2_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_131,negated_conjecture,
    ( k2_funct_2(esk5_0,esk6_0) = k1_xboole_0
    | esk5_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_101]),c_0_104]),c_0_102]),c_0_60]),c_0_120]),c_0_84])])).

cnf(c_0_132,plain,
    ( v5_relat_1(esk4_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_133,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_123]),c_0_124]),c_0_124]),c_0_125])])).

cnf(c_0_134,plain,
    ( v4_relat_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_123,c_0_126])).

cnf(c_0_135,plain,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_127]),c_0_115])).

cnf(c_0_136,negated_conjecture,
    ( m1_subset_1(k2_funct_2(esk5_0,esk6_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_xboole_0(esk5_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_129]),c_0_72])).

cnf(c_0_137,plain,
    ( v2_funct_2(X1,k2_relat_1(X1))
    | ~ v5_relat_1(X1,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_130])).

cnf(c_0_138,negated_conjecture,
    ( k2_relat_1(k1_xboole_0) = k1_relat_1(esk6_0)
    | esk5_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_117,c_0_131])).

cnf(c_0_139,plain,
    ( v5_relat_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_132,c_0_124])).

cnf(c_0_140,plain,
    ( X1 = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_141,plain,
    ( v4_relat_1(X1,X2)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_142,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_133]),c_0_134]),c_0_125])])).

cnf(c_0_143,plain,
    ( v3_funct_2(k2_funct_2(X1,X2),X1,X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_144,negated_conjecture,
    ( k2_funct_2(esk5_0,esk6_0) = k1_xboole_0
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_135,c_0_136])).

cnf(c_0_145,plain,
    ( v1_funct_1(esk4_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_146,negated_conjecture,
    ( v2_funct_2(k1_xboole_0,k1_relat_1(esk6_0))
    | esk5_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_138]),c_0_139]),c_0_125])])).

cnf(c_0_147,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_104]),c_0_84])])).

cnf(c_0_148,plain,
    ( X1 = k1_relat_1(X2)
    | ~ v4_relat_1(X2,k1_xboole_0)
    | ~ v1_relat_1(X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_98])).

cnf(c_0_149,negated_conjecture,
    ( v4_relat_1(esk6_0,X1)
    | ~ v1_xboole_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_129]),c_0_84]),c_0_142])])).

cnf(c_0_150,negated_conjecture,
    ( ~ r2_hidden(X1,k2_funct_2(esk5_0,esk6_0))
    | ~ v1_xboole_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_136]),c_0_94])])).

cnf(c_0_151,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_152,negated_conjecture,
    ( v3_funct_2(k1_xboole_0,esk5_0,esk5_0)
    | ~ v1_xboole_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_144]),c_0_79]),c_0_59]),c_0_60]),c_0_61])])).

cnf(c_0_153,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_145,c_0_126])).

cnf(c_0_154,negated_conjecture,
    ( v2_funct_2(k1_xboole_0,k1_xboole_0)
    | esk5_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_146,c_0_147]),c_0_133])).

cnf(c_0_155,negated_conjecture,
    ( X1 = k1_relat_1(esk6_0)
    | ~ v1_xboole_0(esk5_0)
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_149]),c_0_84])])).

cnf(c_0_156,negated_conjecture,
    ( v1_xboole_0(k2_funct_2(esk5_0,esk6_0))
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_150,c_0_151])).

cnf(c_0_157,negated_conjecture,
    ( v2_funct_2(k1_xboole_0,esk5_0)
    | ~ v1_xboole_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_152]),c_0_153]),c_0_111])])).

cnf(c_0_158,plain,
    ( ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X1)
    | ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) ),
    inference(spm,[status(thm)],[c_0_92,c_0_116])).

cnf(c_0_159,negated_conjecture,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | esk5_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_154]),c_0_139]),c_0_125])])).

cnf(c_0_160,negated_conjecture,
    ( k2_funct_2(esk5_0,esk6_0) = k1_relat_1(esk6_0)
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_155,c_0_156])).

cnf(c_0_161,negated_conjecture,
    ( k2_relat_1(k1_xboole_0) = esk5_0
    | ~ v1_xboole_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_157]),c_0_139]),c_0_125])])).

cnf(c_0_162,negated_conjecture,
    ( k2_relat_1(k1_xboole_0) = k1_relat_1(esk6_0)
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_117,c_0_144])).

fof(c_0_163,plain,(
    ! [X33] :
      ( ~ v1_relat_1(X33)
      | k9_relat_1(X33,k1_relat_1(X33)) = k2_relat_1(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

cnf(c_0_164,plain,
    ( ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_funct_1(X1))
    | ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))) ),
    inference(spm,[status(thm)],[c_0_158,c_0_100])).

cnf(c_0_165,negated_conjecture,
    ( k1_relat_1(esk6_0) = k1_xboole_0
    | esk5_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_138,c_0_159])).

cnf(c_0_166,negated_conjecture,
    ( m1_subset_1(k1_relat_1(esk6_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_136,c_0_160])).

cnf(c_0_167,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk5_0
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_161,c_0_162])).

cnf(c_0_168,negated_conjecture,
    ( v1_xboole_0(esk5_0)
    | ~ v4_relat_1(k2_funct_2(esk5_0,esk6_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_118]),c_0_120])])).

cnf(c_0_169,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_163])).

fof(c_0_170,plain,(
    ! [X48,X49,X50,X51] :
      ( ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))
      | k7_relset_1(X48,X49,X50,X51) = k9_relat_1(X50,X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_171,plain,(
    ! [X57,X58,X59] :
      ( ( k7_relset_1(X57,X58,X59,X57) = k2_relset_1(X57,X58,X59)
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58))) )
      & ( k8_relset_1(X57,X58,X59,X58) = k1_relset_1(X57,X58,X59)
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).

fof(c_0_172,plain,(
    ! [X88] : k6_partfun1(X88) = k6_relat_1(X88) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

cnf(c_0_173,negated_conjecture,
    ( X1 = esk6_0
    | ~ v1_xboole_0(esk5_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_90])).

cnf(c_0_174,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_72]),c_0_94])])).

cnf(c_0_175,negated_conjecture,
    ( esk5_0 != k1_xboole_0
    | ~ r2_hidden(X1,k2_funct_2(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_164,c_0_165]),c_0_102]),c_0_101]),c_0_119]),c_0_60]),c_0_101]),c_0_120]),c_0_84]),c_0_101]),c_0_72]),c_0_94])])).

cnf(c_0_176,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_166,c_0_167])).

cnf(c_0_177,negated_conjecture,
    ( v1_xboole_0(esk5_0)
    | esk5_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_168,c_0_131]),c_0_134])])).

cnf(c_0_178,negated_conjecture,
    ( k9_relat_1(k2_funct_2(esk5_0,esk6_0),esk5_0) = k1_relat_1(esk6_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_169,c_0_118]),c_0_120])]),c_0_117])).

cnf(c_0_179,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_170])).

cnf(c_0_180,plain,
    ( k7_relset_1(X1,X2,X3,X1) = k2_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_171])).

cnf(c_0_181,negated_conjecture,
    ( ~ r2_relset_1(esk5_0,esk5_0,k1_partfun1(esk5_0,esk5_0,esk5_0,esk5_0,esk6_0,k2_funct_2(esk5_0,esk6_0)),k6_partfun1(esk5_0))
    | ~ r2_relset_1(esk5_0,esk5_0,k1_partfun1(esk5_0,esk5_0,esk5_0,esk5_0,k2_funct_2(esk5_0,esk6_0),esk6_0),k6_partfun1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_182,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_172])).

cnf(c_0_183,negated_conjecture,
    ( X1 = esk6_0
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_173,c_0_174])).

cnf(c_0_184,negated_conjecture,
    ( v1_xboole_0(k2_funct_2(esk5_0,esk6_0))
    | esk5_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_175,c_0_151])).

cnf(c_0_185,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))
    | esk5_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_176,c_0_177])).

cnf(c_0_186,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk6_0
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_155,c_0_90])).

fof(c_0_187,plain,(
    ! [X60,X61,X62] :
      ( ( r2_hidden(esk3_3(X60,X61,X62),X60)
        | r2_relset_1(X60,X60,X61,X62)
        | ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X60)))
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X60,X60))) )
      & ( k11_relat_1(X61,esk3_3(X60,X61,X62)) != k11_relat_1(X62,esk3_3(X60,X61,X62))
        | r2_relset_1(X60,X60,X61,X62)
        | ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X60)))
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X60,X60))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relset_1])])])])])).

fof(c_0_188,plain,(
    ! [X45,X46,X47] :
      ( ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))
      | m1_subset_1(k2_relset_1(X45,X46,X47),k1_zfmisc_1(X46)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).

cnf(c_0_189,negated_conjecture,
    ( k9_relat_1(k1_xboole_0,esk5_0) = k1_relat_1(esk6_0)
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_178,c_0_144])).

cnf(c_0_190,plain,
    ( k2_relset_1(X1,X2,X3) = k9_relat_1(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_179,c_0_180])).

cnf(c_0_191,plain,
    ( v2_funct_2(k2_funct_2(X1,X2),X1)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_143]),c_0_86]),c_0_105])).

cnf(c_0_192,plain,
    ( v5_relat_1(k2_funct_2(X1,X2),X1)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_86])).

cnf(c_0_193,negated_conjecture,
    ( ~ r2_relset_1(esk5_0,esk5_0,k1_partfun1(esk5_0,esk5_0,esk5_0,esk5_0,esk6_0,k2_funct_2(esk5_0,esk6_0)),k6_relat_1(esk5_0))
    | ~ r2_relset_1(esk5_0,esk5_0,k1_partfun1(esk5_0,esk5_0,esk5_0,esk5_0,k2_funct_2(esk5_0,esk6_0),esk6_0),k6_relat_1(esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_181,c_0_182]),c_0_182])).

cnf(c_0_194,negated_conjecture,
    ( k2_funct_2(esk5_0,esk6_0) = esk6_0
    | esk5_0 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_183,c_0_184]),c_0_185])).

cnf(c_0_195,negated_conjecture,
    ( esk6_0 = esk5_0
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_167,c_0_186])).

cnf(c_0_196,negated_conjecture,
    ( esk5_0 != k1_xboole_0
    | ~ r2_hidden(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_158,c_0_165]),c_0_60]),c_0_84]),c_0_104]),c_0_71]),c_0_94])])).

cnf(c_0_197,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X1)
    | r2_relset_1(X1,X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_187])).

cnf(c_0_198,plain,
    ( m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_188])).

cnf(c_0_199,negated_conjecture,
    ( k2_relset_1(esk5_0,X1,k1_xboole_0) = k1_relat_1(esk6_0)
    | ~ v1_xboole_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_189,c_0_190]),c_0_111])])).

cnf(c_0_200,plain,
    ( k2_relat_1(k2_funct_2(X1,X2)) = X1
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_191]),c_0_106]),c_0_192])).

cnf(c_0_201,negated_conjecture,
    ( esk5_0 != k1_xboole_0
    | ~ r2_relset_1(esk5_0,esk5_0,k1_partfun1(esk5_0,esk5_0,esk5_0,esk5_0,esk6_0,esk6_0),k6_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_193,c_0_194])).

cnf(c_0_202,negated_conjecture,
    ( esk6_0 = esk5_0
    | esk5_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_195,c_0_177])).

cnf(c_0_203,negated_conjecture,
    ( r2_relset_1(esk6_0,esk6_0,X1,X2)
    | esk5_0 != k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk6_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_196,c_0_197])).

cnf(c_0_204,negated_conjecture,
    ( m1_subset_1(k1_relat_1(esk6_0),k1_zfmisc_1(X1))
    | ~ v1_xboole_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198,c_0_199]),c_0_111])])).

cnf(c_0_205,negated_conjecture,
    ( v1_funct_1(k1_relat_1(esk6_0))
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_119,c_0_160])).

fof(c_0_206,plain,(
    ! [X80,X81,X82,X83,X84,X85] :
      ( ~ v1_funct_1(X84)
      | ~ m1_subset_1(X84,k1_zfmisc_1(k2_zfmisc_1(X80,X81)))
      | ~ v1_funct_1(X85)
      | ~ m1_subset_1(X85,k1_zfmisc_1(k2_zfmisc_1(X82,X83)))
      | k1_partfun1(X80,X81,X82,X83,X84,X85) = k5_relat_1(X84,X85) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

fof(c_0_207,plain,(
    ! [X89,X90,X91] :
      ( ( k5_relat_1(X91,k2_funct_1(X91)) = k6_partfun1(X89)
        | X90 = k1_xboole_0
        | k2_relset_1(X89,X90,X91) != X90
        | ~ v2_funct_1(X91)
        | ~ v1_funct_1(X91)
        | ~ v1_funct_2(X91,X89,X90)
        | ~ m1_subset_1(X91,k1_zfmisc_1(k2_zfmisc_1(X89,X90))) )
      & ( k5_relat_1(k2_funct_1(X91),X91) = k6_partfun1(X90)
        | X90 = k1_xboole_0
        | k2_relset_1(X89,X90,X91) != X90
        | ~ v2_funct_1(X91)
        | ~ v1_funct_1(X91)
        | ~ v1_funct_2(X91,X89,X90)
        | ~ m1_subset_1(X91,k1_zfmisc_1(k2_zfmisc_1(X89,X90))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).

cnf(c_0_208,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_200,c_0_59]),c_0_117]),c_0_79]),c_0_60]),c_0_61])])).

cnf(c_0_209,negated_conjecture,
    ( esk5_0 != k1_xboole_0
    | ~ r2_relset_1(esk5_0,esk5_0,k1_partfun1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k6_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_201,c_0_202])).

cnf(c_0_210,negated_conjecture,
    ( r2_relset_1(esk5_0,esk5_0,X1,X2)
    | esk5_0 != k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk5_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_203,c_0_202])).

fof(c_0_211,plain,(
    ! [X69,X70,X71,X72,X73,X74] :
      ( ( v1_funct_1(k1_partfun1(X69,X70,X71,X72,X73,X74))
        | ~ v1_funct_1(X73)
        | ~ m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(X69,X70)))
        | ~ v1_funct_1(X74)
        | ~ m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(X71,X72))) )
      & ( m1_subset_1(k1_partfun1(X69,X70,X71,X72,X73,X74),k1_zfmisc_1(k2_zfmisc_1(X69,X72)))
        | ~ v1_funct_1(X73)
        | ~ m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(X69,X70)))
        | ~ v1_funct_1(X74)
        | ~ m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(X71,X72))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

cnf(c_0_212,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_204,c_0_167])).

cnf(c_0_213,negated_conjecture,
    ( v1_funct_1(esk5_0)
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_205,c_0_167])).

cnf(c_0_214,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_206])).

cnf(c_0_215,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_partfun1(X2)
    | X3 = k1_xboole_0
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_207])).

cnf(c_0_216,negated_conjecture,
    ( k9_relat_1(esk6_0,esk5_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_169,c_0_208]),c_0_104]),c_0_84])])).

cnf(c_0_217,negated_conjecture,
    ( esk5_0 != k1_xboole_0
    | ~ m1_subset_1(k1_partfun1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_209,c_0_210]),c_0_47])])).

cnf(c_0_218,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_211])).

cnf(c_0_219,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(X1))
    | esk5_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_212,c_0_177])).

cnf(c_0_220,negated_conjecture,
    ( v1_funct_1(esk5_0)
    | esk5_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_213,c_0_177])).

cnf(c_0_221,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_partfun1(X2)
    | X2 = k1_xboole_0
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_207])).

cnf(c_0_222,negated_conjecture,
    ( ~ r2_relset_1(esk5_0,esk5_0,k1_partfun1(esk5_0,esk5_0,esk5_0,esk5_0,esk6_0,k2_funct_2(esk5_0,esk6_0)),k6_relat_1(esk5_0))
    | ~ r2_relset_1(esk5_0,esk5_0,k5_relat_1(k2_funct_2(esk5_0,esk6_0),esk6_0),k6_relat_1(esk5_0))
    | ~ m1_subset_1(k2_funct_2(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_193,c_0_214]),c_0_60]),c_0_119]),c_0_61])])).

cnf(c_0_223,plain,
    ( X3 = k1_xboole_0
    | k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(X2)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_215,c_0_182])).

cnf(c_0_224,negated_conjecture,
    ( k2_relset_1(esk5_0,X1,esk6_0) = esk5_0
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1))) ),
    inference(spm,[status(thm)],[c_0_190,c_0_216])).

cnf(c_0_225,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_217,c_0_218]),c_0_219]),c_0_220])).

cnf(c_0_226,plain,
    ( X2 = k1_xboole_0
    | k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(X2)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(rw,[status(thm)],[c_0_221,c_0_182])).

fof(c_0_227,plain,(
    ! [X52,X53,X54,X55] :
      ( ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))
      | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))
      | r2_relset_1(X52,X53,X54,X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[reflexivity_r2_relset_1])])).

cnf(c_0_228,negated_conjecture,
    ( ~ r2_relset_1(esk5_0,esk5_0,k5_relat_1(esk6_0,k2_funct_2(esk5_0,esk6_0)),k6_relat_1(esk5_0))
    | ~ r2_relset_1(esk5_0,esk5_0,k5_relat_1(k2_funct_2(esk5_0,esk6_0),esk6_0),k6_relat_1(esk5_0))
    | ~ m1_subset_1(k2_funct_2(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_222,c_0_214]),c_0_119]),c_0_60]),c_0_61])])).

cnf(c_0_229,negated_conjecture,
    ( m1_subset_1(k2_funct_2(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk5_0))) ),
    inference(rw,[status(thm)],[c_0_128,c_0_208])).

cnf(c_0_230,negated_conjecture,
    ( k5_relat_1(esk6_0,k2_funct_2(esk5_0,esk6_0)) = k6_relat_1(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_223,c_0_224]),c_0_101]),c_0_102]),c_0_60])])]),c_0_79]),c_0_61])]),c_0_225])).

cnf(c_0_231,negated_conjecture,
    ( k5_relat_1(k2_funct_2(esk5_0,esk6_0),esk6_0) = k6_relat_1(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_226,c_0_224]),c_0_101]),c_0_102]),c_0_60])])]),c_0_79]),c_0_61])]),c_0_225])).

cnf(c_0_232,plain,
    ( r2_relset_1(X2,X3,X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_227])).

cnf(c_0_233,negated_conjecture,
    ( ~ r2_relset_1(esk5_0,esk5_0,k6_relat_1(esk5_0),k6_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_228,c_0_229])]),c_0_230]),c_0_231])])).

cnf(c_0_234,plain,
    ( r2_relset_1(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_232,c_0_70])).

cnf(c_0_235,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_233,c_0_234]),c_0_47])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:54:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 1.29/1.46  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 1.29/1.46  # and selection function SelectMaxLComplexAvoidPosPred.
% 1.29/1.46  #
% 1.29/1.46  # Preprocessing time       : 0.031 s
% 1.29/1.46  
% 1.29/1.46  # Proof found!
% 1.29/1.46  # SZS status Theorem
% 1.29/1.46  # SZS output start CNFRefutation
% 1.29/1.46  fof(t88_funct_2, conjecture, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,k2_funct_2(X1,X2)),k6_partfun1(X1))&r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,k2_funct_2(X1,X2),X2),k6_partfun1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_funct_2)).
% 1.29/1.46  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 1.29/1.46  fof(t29_relset_1, axiom, ![X1]:m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 1.29/1.46  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.29/1.46  fof(t69_xboole_1, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>~((r1_tarski(X2,X1)&r1_xboole_0(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 1.29/1.46  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.29/1.46  fof(cc2_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v3_funct_2(X3,X1,X2))=>((v1_funct_1(X3)&v2_funct_1(X3))&v2_funct_2(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 1.29/1.46  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.29/1.46  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.29/1.46  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 1.29/1.46  fof(rc1_funct_2, axiom, ![X1, X2]:?[X3]:(((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&v1_relat_1(X3))&v4_relat_1(X3,X1))&v5_relat_1(X3,X2))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_funct_2)).
% 1.29/1.46  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.29/1.46  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.29/1.46  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 1.29/1.46  fof(redefinition_k2_funct_2, axiom, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>k2_funct_2(X1,X2)=k2_funct_1(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 1.29/1.46  fof(d3_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v5_relat_1(X2,X1))=>(v2_funct_2(X2,X1)<=>k2_relat_1(X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 1.29/1.46  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.29/1.46  fof(dt_k2_funct_2, axiom, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(((v1_funct_1(k2_funct_2(X1,X2))&v1_funct_2(k2_funct_2(X1,X2),X1,X1))&v3_funct_2(k2_funct_2(X1,X2),X1,X1))&m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 1.29/1.46  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.29/1.46  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 1.29/1.46  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 1.29/1.46  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 1.29/1.46  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.29/1.46  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 1.29/1.46  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 1.29/1.46  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 1.29/1.46  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 1.29/1.46  fof(t38_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(k7_relset_1(X1,X2,X3,X1)=k2_relset_1(X1,X2,X3)&k8_relset_1(X1,X2,X3,X2)=k1_relset_1(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 1.29/1.46  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 1.29/1.46  fof(t54_relset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))=>(![X4]:(r2_hidden(X4,X1)=>k11_relat_1(X2,X4)=k11_relat_1(X3,X4))=>r2_relset_1(X1,X1,X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relset_1)).
% 1.29/1.46  fof(dt_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 1.29/1.46  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 1.29/1.46  fof(t35_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((k2_relset_1(X1,X2,X3)=X2&v2_funct_1(X3))=>(X2=k1_xboole_0|(k5_relat_1(X3,k2_funct_1(X3))=k6_partfun1(X1)&k5_relat_1(k2_funct_1(X3),X3)=k6_partfun1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 1.29/1.46  fof(dt_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))&m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 1.29/1.46  fof(reflexivity_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r2_relset_1(X1,X2,X3,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 1.29/1.46  fof(c_0_35, negated_conjecture, ~(![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,k2_funct_2(X1,X2)),k6_partfun1(X1))&r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,k2_funct_2(X1,X2),X2),k6_partfun1(X1))))), inference(assume_negation,[status(cth)],[t88_funct_2])).
% 1.29/1.46  fof(c_0_36, plain, ![X42, X43, X44]:(~v1_xboole_0(X42)|(~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X43,X42)))|v1_xboole_0(X44))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 1.29/1.46  fof(c_0_37, plain, ![X56]:m1_subset_1(k6_relat_1(X56),k1_zfmisc_1(k2_zfmisc_1(X56,X56))), inference(variable_rename,[status(thm)],[t29_relset_1])).
% 1.29/1.46  fof(c_0_38, plain, ![X18, X19]:((k2_zfmisc_1(X18,X19)!=k1_xboole_0|(X18=k1_xboole_0|X19=k1_xboole_0))&((X18!=k1_xboole_0|k2_zfmisc_1(X18,X19)=k1_xboole_0)&(X19!=k1_xboole_0|k2_zfmisc_1(X18,X19)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 1.29/1.46  fof(c_0_39, plain, ![X14, X15]:(v1_xboole_0(X15)|(~r1_tarski(X15,X14)|~r1_xboole_0(X15,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).
% 1.29/1.46  fof(c_0_40, plain, ![X13]:r1_xboole_0(X13,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 1.29/1.46  fof(c_0_41, plain, ![X64, X65, X66]:(((v1_funct_1(X66)|(~v1_funct_1(X66)|~v3_funct_2(X66,X64,X65))|~m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65))))&(v2_funct_1(X66)|(~v1_funct_1(X66)|~v3_funct_2(X66,X64,X65))|~m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65)))))&(v2_funct_2(X66,X65)|(~v1_funct_1(X66)|~v3_funct_2(X66,X64,X65))|~m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_funct_2])])])).
% 1.29/1.46  fof(c_0_42, negated_conjecture, ((((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk5_0,esk5_0))&v3_funct_2(esk6_0,esk5_0,esk5_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk5_0))))&(~r2_relset_1(esk5_0,esk5_0,k1_partfun1(esk5_0,esk5_0,esk5_0,esk5_0,esk6_0,k2_funct_2(esk5_0,esk6_0)),k6_partfun1(esk5_0))|~r2_relset_1(esk5_0,esk5_0,k1_partfun1(esk5_0,esk5_0,esk5_0,esk5_0,k2_funct_2(esk5_0,esk6_0),esk6_0),k6_partfun1(esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_35])])])).
% 1.29/1.46  fof(c_0_43, plain, ![X39, X40, X41]:((v4_relat_1(X41,X39)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))&(v5_relat_1(X41,X40)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 1.29/1.46  fof(c_0_44, plain, ![X36, X37, X38]:(~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))|v1_relat_1(X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 1.29/1.46  fof(c_0_45, plain, ![X16, X17]:(~v1_xboole_0(X16)|X16=X17|~v1_xboole_0(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 1.29/1.46  cnf(c_0_46, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 1.29/1.46  cnf(c_0_47, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 1.29/1.46  fof(c_0_48, plain, ![X77, X78]:(((((m1_subset_1(esk4_2(X77,X78),k1_zfmisc_1(k2_zfmisc_1(X77,X78)))&v1_relat_1(esk4_2(X77,X78)))&v4_relat_1(esk4_2(X77,X78),X77))&v5_relat_1(esk4_2(X77,X78),X78))&v1_funct_1(esk4_2(X77,X78)))&v1_funct_2(esk4_2(X77,X78),X77,X78)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_funct_2])])).
% 1.29/1.46  cnf(c_0_49, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_38])).
% 1.29/1.46  cnf(c_0_50, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_38])).
% 1.29/1.46  fof(c_0_51, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 1.29/1.46  fof(c_0_52, plain, ![X11]:(X11=k1_xboole_0|r2_hidden(esk2_1(X11),X11)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 1.29/1.46  cnf(c_0_53, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 1.29/1.46  cnf(c_0_54, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 1.29/1.46  fof(c_0_55, plain, ![X29, X30]:((~v4_relat_1(X30,X29)|r1_tarski(k1_relat_1(X30),X29)|~v1_relat_1(X30))&(~r1_tarski(k1_relat_1(X30),X29)|v4_relat_1(X30,X29)|~v1_relat_1(X30))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 1.29/1.46  fof(c_0_56, plain, ![X86, X87]:(~v1_funct_1(X87)|~v1_funct_2(X87,X86,X86)|~v3_funct_2(X87,X86,X86)|~m1_subset_1(X87,k1_zfmisc_1(k2_zfmisc_1(X86,X86)))|k2_funct_2(X86,X87)=k2_funct_1(X87)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_funct_2])])).
% 1.29/1.46  fof(c_0_57, plain, ![X67, X68]:((~v2_funct_2(X68,X67)|k2_relat_1(X68)=X67|(~v1_relat_1(X68)|~v5_relat_1(X68,X67)))&(k2_relat_1(X68)!=X67|v2_funct_2(X68,X67)|(~v1_relat_1(X68)|~v5_relat_1(X68,X67)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).
% 1.29/1.46  cnf(c_0_58, plain, (v2_funct_2(X1,X2)|~v1_funct_1(X1)|~v3_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.29/1.46  cnf(c_0_59, negated_conjecture, (v3_funct_2(esk6_0,esk5_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 1.29/1.46  cnf(c_0_60, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 1.29/1.46  cnf(c_0_61, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 1.29/1.46  cnf(c_0_62, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 1.29/1.46  cnf(c_0_63, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 1.29/1.46  fof(c_0_64, plain, ![X27, X28]:(~v1_relat_1(X27)|(~m1_subset_1(X28,k1_zfmisc_1(X27))|v1_relat_1(X28))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 1.29/1.46  fof(c_0_65, plain, ![X75, X76]:((((v1_funct_1(k2_funct_2(X75,X76))|(~v1_funct_1(X76)|~v1_funct_2(X76,X75,X75)|~v3_funct_2(X76,X75,X75)|~m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X75,X75)))))&(v1_funct_2(k2_funct_2(X75,X76),X75,X75)|(~v1_funct_1(X76)|~v1_funct_2(X76,X75,X75)|~v3_funct_2(X76,X75,X75)|~m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X75,X75))))))&(v3_funct_2(k2_funct_2(X75,X76),X75,X75)|(~v1_funct_1(X76)|~v1_funct_2(X76,X75,X75)|~v3_funct_2(X76,X75,X75)|~m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X75,X75))))))&(m1_subset_1(k2_funct_2(X75,X76),k1_zfmisc_1(k2_zfmisc_1(X75,X75)))|(~v1_funct_1(X76)|~v1_funct_2(X76,X75,X75)|~v3_funct_2(X76,X75,X75)|~m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X75,X75)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_2])])])).
% 1.29/1.46  fof(c_0_66, plain, ![X31, X32]:v1_relat_1(k2_zfmisc_1(X31,X32)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 1.29/1.46  cnf(c_0_67, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 1.29/1.46  cnf(c_0_68, plain, (v1_xboole_0(k6_relat_1(X1))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 1.29/1.46  fof(c_0_69, plain, ![X24, X25, X26]:(~r2_hidden(X24,X25)|~m1_subset_1(X25,k1_zfmisc_1(X26))|~v1_xboole_0(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 1.29/1.46  cnf(c_0_70, plain, (m1_subset_1(esk4_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 1.29/1.46  cnf(c_0_71, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_49])).
% 1.29/1.46  cnf(c_0_72, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_50])).
% 1.29/1.46  cnf(c_0_73, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 1.29/1.46  cnf(c_0_74, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 1.29/1.46  cnf(c_0_75, plain, (v1_xboole_0(X1)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 1.29/1.46  cnf(c_0_76, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 1.29/1.46  fof(c_0_77, plain, ![X35]:((k2_relat_1(X35)=k1_relat_1(k2_funct_1(X35))|~v2_funct_1(X35)|(~v1_relat_1(X35)|~v1_funct_1(X35)))&(k1_relat_1(X35)=k2_relat_1(k2_funct_1(X35))|~v2_funct_1(X35)|(~v1_relat_1(X35)|~v1_funct_1(X35)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 1.29/1.46  cnf(c_0_78, plain, (k2_funct_2(X2,X1)=k2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X2)|~v3_funct_2(X1,X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 1.29/1.46  cnf(c_0_79, negated_conjecture, (v1_funct_2(esk6_0,esk5_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 1.29/1.46  cnf(c_0_80, plain, (v2_funct_1(X1)|~v1_funct_1(X1)|~v3_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.29/1.46  cnf(c_0_81, plain, (k2_relat_1(X1)=X2|~v2_funct_2(X1,X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 1.29/1.46  cnf(c_0_82, negated_conjecture, (v2_funct_2(esk6_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60]), c_0_61])])).
% 1.29/1.46  cnf(c_0_83, negated_conjecture, (v5_relat_1(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_62, c_0_61])).
% 1.29/1.46  cnf(c_0_84, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_63, c_0_61])).
% 1.29/1.46  cnf(c_0_85, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 1.29/1.46  cnf(c_0_86, plain, (m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 1.29/1.46  cnf(c_0_87, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 1.29/1.46  cnf(c_0_88, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 1.29/1.46  cnf(c_0_89, plain, (X1=k6_relat_1(X2)|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 1.29/1.46  cnf(c_0_90, negated_conjecture, (v1_xboole_0(esk6_0)|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_46, c_0_61])).
% 1.29/1.46  fof(c_0_91, plain, ![X34]:((k1_relat_1(X34)!=k1_xboole_0|X34=k1_xboole_0|~v1_relat_1(X34))&(k2_relat_1(X34)!=k1_xboole_0|X34=k1_xboole_0|~v1_relat_1(X34))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 1.29/1.46  cnf(c_0_92, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 1.29/1.46  cnf(c_0_93, plain, (m1_subset_1(esk4_2(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 1.29/1.46  cnf(c_0_94, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 1.29/1.46  fof(c_0_95, plain, ![X20]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X20)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 1.29/1.46  cnf(c_0_96, plain, (m1_subset_1(esk4_2(X1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_70, c_0_72])).
% 1.29/1.46  cnf(c_0_97, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 1.29/1.46  cnf(c_0_98, plain, (v1_xboole_0(k1_relat_1(X1))|~v4_relat_1(X1,k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 1.29/1.46  fof(c_0_99, plain, ![X92]:(((v1_funct_1(X92)|(~v1_relat_1(X92)|~v1_funct_1(X92)))&(v1_funct_2(X92,k1_relat_1(X92),k2_relat_1(X92))|(~v1_relat_1(X92)|~v1_funct_1(X92))))&(m1_subset_1(X92,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X92),k2_relat_1(X92))))|(~v1_relat_1(X92)|~v1_funct_1(X92)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 1.29/1.46  cnf(c_0_100, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 1.29/1.46  cnf(c_0_101, negated_conjecture, (k2_funct_1(esk6_0)=k2_funct_2(esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_59]), c_0_79]), c_0_60]), c_0_61])])).
% 1.29/1.46  cnf(c_0_102, negated_conjecture, (v2_funct_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_59]), c_0_60]), c_0_61])])).
% 1.29/1.46  cnf(c_0_103, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 1.29/1.46  cnf(c_0_104, negated_conjecture, (k2_relat_1(esk6_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_83]), c_0_84])])).
% 1.29/1.46  cnf(c_0_105, plain, (v1_funct_1(k2_funct_2(X1,X2))|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 1.29/1.46  cnf(c_0_106, plain, (v1_relat_1(k2_funct_2(X1,X2))|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_87])])).
% 1.29/1.46  cnf(c_0_107, plain, (v4_relat_1(k6_relat_1(X1),X1)), inference(spm,[status(thm)],[c_0_88, c_0_47])).
% 1.29/1.46  cnf(c_0_108, negated_conjecture, (k6_relat_1(X1)=esk6_0|~v1_xboole_0(esk5_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 1.29/1.46  cnf(c_0_109, plain, (X1=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_91])).
% 1.29/1.46  cnf(c_0_110, plain, (~r2_hidden(X1,esk4_2(k1_xboole_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_94])])).
% 1.29/1.46  cnf(c_0_111, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_95])).
% 1.29/1.46  cnf(c_0_112, plain, (~r2_hidden(X1,esk4_2(X2,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_96]), c_0_94])])).
% 1.29/1.46  cnf(c_0_113, plain, (k1_relat_1(X1)=k1_xboole_0|~v4_relat_1(X1,k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 1.29/1.46  cnf(c_0_114, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_88, c_0_72])).
% 1.29/1.46  cnf(c_0_115, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_63, c_0_72])).
% 1.29/1.46  cnf(c_0_116, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_99])).
% 1.29/1.46  cnf(c_0_117, negated_conjecture, (k2_relat_1(k2_funct_2(esk5_0,esk6_0))=k1_relat_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_102]), c_0_60]), c_0_84])])).
% 1.29/1.46  cnf(c_0_118, negated_conjecture, (k1_relat_1(k2_funct_2(esk5_0,esk6_0))=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_101]), c_0_104]), c_0_102]), c_0_60]), c_0_84])])).
% 1.29/1.46  cnf(c_0_119, negated_conjecture, (v1_funct_1(k2_funct_2(esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_59]), c_0_79]), c_0_60]), c_0_61])])).
% 1.29/1.46  cnf(c_0_120, negated_conjecture, (v1_relat_1(k2_funct_2(esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_59]), c_0_79]), c_0_60]), c_0_61])])).
% 1.29/1.46  cnf(c_0_121, negated_conjecture, (v4_relat_1(esk6_0,X1)|~v1_xboole_0(esk5_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_107, c_0_108])).
% 1.29/1.46  cnf(c_0_122, plain, (k2_funct_1(X1)=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_109, c_0_103])).
% 1.29/1.46  cnf(c_0_123, plain, (v4_relat_1(esk4_2(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 1.29/1.46  cnf(c_0_124, plain, (esk4_2(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_110, c_0_74])).
% 1.29/1.46  cnf(c_0_125, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_63, c_0_111])).
% 1.29/1.46  cnf(c_0_126, plain, (esk4_2(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_112, c_0_74])).
% 1.29/1.46  cnf(c_0_127, plain, (k1_relat_1(X1)=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_114]), c_0_115])).
% 1.29/1.46  cnf(c_0_128, negated_conjecture, (m1_subset_1(k2_funct_2(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_relat_1(esk6_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_117]), c_0_118]), c_0_119]), c_0_120])])).
% 1.29/1.46  cnf(c_0_129, negated_conjecture, (k1_relat_1(esk6_0)=k1_xboole_0|~v1_xboole_0(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_121]), c_0_84]), c_0_94])])).
% 1.29/1.46  cnf(c_0_130, plain, (v2_funct_2(X1,X2)|k2_relat_1(X1)!=X2|~v1_relat_1(X1)|~v5_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 1.29/1.46  cnf(c_0_131, negated_conjecture, (k2_funct_2(esk5_0,esk6_0)=k1_xboole_0|esk5_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_101]), c_0_104]), c_0_102]), c_0_60]), c_0_120]), c_0_84])])).
% 1.29/1.46  cnf(c_0_132, plain, (v5_relat_1(esk4_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 1.29/1.46  cnf(c_0_133, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_123]), c_0_124]), c_0_124]), c_0_125])])).
% 1.29/1.46  cnf(c_0_134, plain, (v4_relat_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_123, c_0_126])).
% 1.29/1.46  cnf(c_0_135, plain, (X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_127]), c_0_115])).
% 1.29/1.46  cnf(c_0_136, negated_conjecture, (m1_subset_1(k2_funct_2(esk5_0,esk6_0),k1_zfmisc_1(k1_xboole_0))|~v1_xboole_0(esk5_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_129]), c_0_72])).
% 1.29/1.46  cnf(c_0_137, plain, (v2_funct_2(X1,k2_relat_1(X1))|~v5_relat_1(X1,k2_relat_1(X1))|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_130])).
% 1.29/1.46  cnf(c_0_138, negated_conjecture, (k2_relat_1(k1_xboole_0)=k1_relat_1(esk6_0)|esk5_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_117, c_0_131])).
% 1.29/1.46  cnf(c_0_139, plain, (v5_relat_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_132, c_0_124])).
% 1.29/1.46  cnf(c_0_140, plain, (X1=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_91])).
% 1.29/1.46  cnf(c_0_141, plain, (v4_relat_1(X1,X2)|~r1_tarski(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 1.29/1.46  cnf(c_0_142, plain, (r1_tarski(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_133]), c_0_134]), c_0_125])])).
% 1.29/1.46  cnf(c_0_143, plain, (v3_funct_2(k2_funct_2(X1,X2),X1,X1)|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 1.29/1.46  cnf(c_0_144, negated_conjecture, (k2_funct_2(esk5_0,esk6_0)=k1_xboole_0|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_135, c_0_136])).
% 1.29/1.46  cnf(c_0_145, plain, (v1_funct_1(esk4_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 1.29/1.46  cnf(c_0_146, negated_conjecture, (v2_funct_2(k1_xboole_0,k1_relat_1(esk6_0))|esk5_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_138]), c_0_139]), c_0_125])])).
% 1.29/1.46  cnf(c_0_147, negated_conjecture, (esk6_0=k1_xboole_0|esk5_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140, c_0_104]), c_0_84])])).
% 1.29/1.46  cnf(c_0_148, plain, (X1=k1_relat_1(X2)|~v4_relat_1(X2,k1_xboole_0)|~v1_relat_1(X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_67, c_0_98])).
% 1.29/1.46  cnf(c_0_149, negated_conjecture, (v4_relat_1(esk6_0,X1)|~v1_xboole_0(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141, c_0_129]), c_0_84]), c_0_142])])).
% 1.29/1.46  cnf(c_0_150, negated_conjecture, (~r2_hidden(X1,k2_funct_2(esk5_0,esk6_0))|~v1_xboole_0(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_136]), c_0_94])])).
% 1.29/1.46  cnf(c_0_151, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 1.29/1.46  cnf(c_0_152, negated_conjecture, (v3_funct_2(k1_xboole_0,esk5_0,esk5_0)|~v1_xboole_0(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_144]), c_0_79]), c_0_59]), c_0_60]), c_0_61])])).
% 1.29/1.46  cnf(c_0_153, plain, (v1_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_145, c_0_126])).
% 1.29/1.46  cnf(c_0_154, negated_conjecture, (v2_funct_2(k1_xboole_0,k1_xboole_0)|esk5_0!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_146, c_0_147]), c_0_133])).
% 1.29/1.46  cnf(c_0_155, negated_conjecture, (X1=k1_relat_1(esk6_0)|~v1_xboole_0(esk5_0)|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148, c_0_149]), c_0_84])])).
% 1.29/1.46  cnf(c_0_156, negated_conjecture, (v1_xboole_0(k2_funct_2(esk5_0,esk6_0))|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_150, c_0_151])).
% 1.29/1.46  cnf(c_0_157, negated_conjecture, (v2_funct_2(k1_xboole_0,esk5_0)|~v1_xboole_0(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_152]), c_0_153]), c_0_111])])).
% 1.29/1.46  cnf(c_0_158, plain, (~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,X1)|~v1_xboole_0(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))), inference(spm,[status(thm)],[c_0_92, c_0_116])).
% 1.29/1.46  cnf(c_0_159, negated_conjecture, (k2_relat_1(k1_xboole_0)=k1_xboole_0|esk5_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_154]), c_0_139]), c_0_125])])).
% 1.29/1.46  cnf(c_0_160, negated_conjecture, (k2_funct_2(esk5_0,esk6_0)=k1_relat_1(esk6_0)|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_155, c_0_156])).
% 1.29/1.46  cnf(c_0_161, negated_conjecture, (k2_relat_1(k1_xboole_0)=esk5_0|~v1_xboole_0(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_157]), c_0_139]), c_0_125])])).
% 1.29/1.46  cnf(c_0_162, negated_conjecture, (k2_relat_1(k1_xboole_0)=k1_relat_1(esk6_0)|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_117, c_0_144])).
% 1.29/1.46  fof(c_0_163, plain, ![X33]:(~v1_relat_1(X33)|k9_relat_1(X33,k1_relat_1(X33))=k2_relat_1(X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 1.29/1.46  cnf(c_0_164, plain, (~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~r2_hidden(X2,k2_funct_1(X1))|~v1_xboole_0(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1)))), inference(spm,[status(thm)],[c_0_158, c_0_100])).
% 1.29/1.46  cnf(c_0_165, negated_conjecture, (k1_relat_1(esk6_0)=k1_xboole_0|esk5_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_138, c_0_159])).
% 1.29/1.46  cnf(c_0_166, negated_conjecture, (m1_subset_1(k1_relat_1(esk6_0),k1_zfmisc_1(k1_xboole_0))|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_136, c_0_160])).
% 1.29/1.46  cnf(c_0_167, negated_conjecture, (k1_relat_1(esk6_0)=esk5_0|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_161, c_0_162])).
% 1.29/1.46  cnf(c_0_168, negated_conjecture, (v1_xboole_0(esk5_0)|~v4_relat_1(k2_funct_2(esk5_0,esk6_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_118]), c_0_120])])).
% 1.29/1.46  cnf(c_0_169, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_163])).
% 1.29/1.46  fof(c_0_170, plain, ![X48, X49, X50, X51]:(~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))|k7_relset_1(X48,X49,X50,X51)=k9_relat_1(X50,X51)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 1.29/1.46  fof(c_0_171, plain, ![X57, X58, X59]:((k7_relset_1(X57,X58,X59,X57)=k2_relset_1(X57,X58,X59)|~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58))))&(k8_relset_1(X57,X58,X59,X58)=k1_relset_1(X57,X58,X59)|~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).
% 1.29/1.46  fof(c_0_172, plain, ![X88]:k6_partfun1(X88)=k6_relat_1(X88), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 1.29/1.46  cnf(c_0_173, negated_conjecture, (X1=esk6_0|~v1_xboole_0(esk5_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_67, c_0_90])).
% 1.29/1.46  cnf(c_0_174, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_72]), c_0_94])])).
% 1.29/1.46  cnf(c_0_175, negated_conjecture, (esk5_0!=k1_xboole_0|~r2_hidden(X1,k2_funct_2(esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_164, c_0_165]), c_0_102]), c_0_101]), c_0_119]), c_0_60]), c_0_101]), c_0_120]), c_0_84]), c_0_101]), c_0_72]), c_0_94])])).
% 1.29/1.46  cnf(c_0_176, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_166, c_0_167])).
% 1.29/1.46  cnf(c_0_177, negated_conjecture, (v1_xboole_0(esk5_0)|esk5_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_168, c_0_131]), c_0_134])])).
% 1.29/1.46  cnf(c_0_178, negated_conjecture, (k9_relat_1(k2_funct_2(esk5_0,esk6_0),esk5_0)=k1_relat_1(esk6_0)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_169, c_0_118]), c_0_120])]), c_0_117])).
% 1.29/1.46  cnf(c_0_179, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_170])).
% 1.29/1.46  cnf(c_0_180, plain, (k7_relset_1(X1,X2,X3,X1)=k2_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_171])).
% 1.29/1.46  cnf(c_0_181, negated_conjecture, (~r2_relset_1(esk5_0,esk5_0,k1_partfun1(esk5_0,esk5_0,esk5_0,esk5_0,esk6_0,k2_funct_2(esk5_0,esk6_0)),k6_partfun1(esk5_0))|~r2_relset_1(esk5_0,esk5_0,k1_partfun1(esk5_0,esk5_0,esk5_0,esk5_0,k2_funct_2(esk5_0,esk6_0),esk6_0),k6_partfun1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 1.29/1.46  cnf(c_0_182, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_172])).
% 1.29/1.46  cnf(c_0_183, negated_conjecture, (X1=esk6_0|~m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_173, c_0_174])).
% 1.29/1.46  cnf(c_0_184, negated_conjecture, (v1_xboole_0(k2_funct_2(esk5_0,esk6_0))|esk5_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_175, c_0_151])).
% 1.29/1.46  cnf(c_0_185, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))|esk5_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_176, c_0_177])).
% 1.29/1.46  cnf(c_0_186, negated_conjecture, (k1_relat_1(esk6_0)=esk6_0|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_155, c_0_90])).
% 1.29/1.46  fof(c_0_187, plain, ![X60, X61, X62]:((r2_hidden(esk3_3(X60,X61,X62),X60)|r2_relset_1(X60,X60,X61,X62)|~m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X60)))|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X60,X60))))&(k11_relat_1(X61,esk3_3(X60,X61,X62))!=k11_relat_1(X62,esk3_3(X60,X61,X62))|r2_relset_1(X60,X60,X61,X62)|~m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X60)))|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X60,X60))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relset_1])])])])])).
% 1.29/1.46  fof(c_0_188, plain, ![X45, X46, X47]:(~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))|m1_subset_1(k2_relset_1(X45,X46,X47),k1_zfmisc_1(X46))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).
% 1.29/1.46  cnf(c_0_189, negated_conjecture, (k9_relat_1(k1_xboole_0,esk5_0)=k1_relat_1(esk6_0)|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_178, c_0_144])).
% 1.29/1.46  cnf(c_0_190, plain, (k2_relset_1(X1,X2,X3)=k9_relat_1(X3,X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_179, c_0_180])).
% 1.29/1.46  cnf(c_0_191, plain, (v2_funct_2(k2_funct_2(X1,X2),X1)|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_143]), c_0_86]), c_0_105])).
% 1.29/1.46  cnf(c_0_192, plain, (v5_relat_1(k2_funct_2(X1,X2),X1)|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(spm,[status(thm)],[c_0_62, c_0_86])).
% 1.29/1.46  cnf(c_0_193, negated_conjecture, (~r2_relset_1(esk5_0,esk5_0,k1_partfun1(esk5_0,esk5_0,esk5_0,esk5_0,esk6_0,k2_funct_2(esk5_0,esk6_0)),k6_relat_1(esk5_0))|~r2_relset_1(esk5_0,esk5_0,k1_partfun1(esk5_0,esk5_0,esk5_0,esk5_0,k2_funct_2(esk5_0,esk6_0),esk6_0),k6_relat_1(esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_181, c_0_182]), c_0_182])).
% 1.29/1.46  cnf(c_0_194, negated_conjecture, (k2_funct_2(esk5_0,esk6_0)=esk6_0|esk5_0!=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_183, c_0_184]), c_0_185])).
% 1.29/1.46  cnf(c_0_195, negated_conjecture, (esk6_0=esk5_0|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_167, c_0_186])).
% 1.29/1.46  cnf(c_0_196, negated_conjecture, (esk5_0!=k1_xboole_0|~r2_hidden(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_158, c_0_165]), c_0_60]), c_0_84]), c_0_104]), c_0_71]), c_0_94])])).
% 1.29/1.46  cnf(c_0_197, plain, (r2_hidden(esk3_3(X1,X2,X3),X1)|r2_relset_1(X1,X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_187])).
% 1.29/1.46  cnf(c_0_198, plain, (m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_188])).
% 1.29/1.46  cnf(c_0_199, negated_conjecture, (k2_relset_1(esk5_0,X1,k1_xboole_0)=k1_relat_1(esk6_0)|~v1_xboole_0(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_189, c_0_190]), c_0_111])])).
% 1.29/1.46  cnf(c_0_200, plain, (k2_relat_1(k2_funct_2(X1,X2))=X1|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_191]), c_0_106]), c_0_192])).
% 1.29/1.46  cnf(c_0_201, negated_conjecture, (esk5_0!=k1_xboole_0|~r2_relset_1(esk5_0,esk5_0,k1_partfun1(esk5_0,esk5_0,esk5_0,esk5_0,esk6_0,esk6_0),k6_relat_1(esk5_0))), inference(spm,[status(thm)],[c_0_193, c_0_194])).
% 1.29/1.46  cnf(c_0_202, negated_conjecture, (esk6_0=esk5_0|esk5_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_195, c_0_177])).
% 1.29/1.46  cnf(c_0_203, negated_conjecture, (r2_relset_1(esk6_0,esk6_0,X1,X2)|esk5_0!=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk6_0)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk6_0)))), inference(spm,[status(thm)],[c_0_196, c_0_197])).
% 1.29/1.46  cnf(c_0_204, negated_conjecture, (m1_subset_1(k1_relat_1(esk6_0),k1_zfmisc_1(X1))|~v1_xboole_0(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198, c_0_199]), c_0_111])])).
% 1.29/1.46  cnf(c_0_205, negated_conjecture, (v1_funct_1(k1_relat_1(esk6_0))|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_119, c_0_160])).
% 1.29/1.46  fof(c_0_206, plain, ![X80, X81, X82, X83, X84, X85]:(~v1_funct_1(X84)|~m1_subset_1(X84,k1_zfmisc_1(k2_zfmisc_1(X80,X81)))|~v1_funct_1(X85)|~m1_subset_1(X85,k1_zfmisc_1(k2_zfmisc_1(X82,X83)))|k1_partfun1(X80,X81,X82,X83,X84,X85)=k5_relat_1(X84,X85)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 1.29/1.46  fof(c_0_207, plain, ![X89, X90, X91]:((k5_relat_1(X91,k2_funct_1(X91))=k6_partfun1(X89)|X90=k1_xboole_0|(k2_relset_1(X89,X90,X91)!=X90|~v2_funct_1(X91))|(~v1_funct_1(X91)|~v1_funct_2(X91,X89,X90)|~m1_subset_1(X91,k1_zfmisc_1(k2_zfmisc_1(X89,X90)))))&(k5_relat_1(k2_funct_1(X91),X91)=k6_partfun1(X90)|X90=k1_xboole_0|(k2_relset_1(X89,X90,X91)!=X90|~v2_funct_1(X91))|(~v1_funct_1(X91)|~v1_funct_2(X91,X89,X90)|~m1_subset_1(X91,k1_zfmisc_1(k2_zfmisc_1(X89,X90)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).
% 1.29/1.46  cnf(c_0_208, negated_conjecture, (k1_relat_1(esk6_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_200, c_0_59]), c_0_117]), c_0_79]), c_0_60]), c_0_61])])).
% 1.29/1.46  cnf(c_0_209, negated_conjecture, (esk5_0!=k1_xboole_0|~r2_relset_1(esk5_0,esk5_0,k1_partfun1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k6_relat_1(esk5_0))), inference(spm,[status(thm)],[c_0_201, c_0_202])).
% 1.29/1.46  cnf(c_0_210, negated_conjecture, (r2_relset_1(esk5_0,esk5_0,X1,X2)|esk5_0!=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk5_0)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk5_0)))), inference(spm,[status(thm)],[c_0_203, c_0_202])).
% 1.29/1.46  fof(c_0_211, plain, ![X69, X70, X71, X72, X73, X74]:((v1_funct_1(k1_partfun1(X69,X70,X71,X72,X73,X74))|(~v1_funct_1(X73)|~m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(X69,X70)))|~v1_funct_1(X74)|~m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(X71,X72)))))&(m1_subset_1(k1_partfun1(X69,X70,X71,X72,X73,X74),k1_zfmisc_1(k2_zfmisc_1(X69,X72)))|(~v1_funct_1(X73)|~m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(X69,X70)))|~v1_funct_1(X74)|~m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(X71,X72)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).
% 1.29/1.46  cnf(c_0_212, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(X1))|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_204, c_0_167])).
% 1.29/1.46  cnf(c_0_213, negated_conjecture, (v1_funct_1(esk5_0)|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_205, c_0_167])).
% 1.29/1.46  cnf(c_0_214, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_206])).
% 1.29/1.46  cnf(c_0_215, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_partfun1(X2)|X3=k1_xboole_0|k2_relset_1(X2,X3,X1)!=X3|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_207])).
% 1.29/1.46  cnf(c_0_216, negated_conjecture, (k9_relat_1(esk6_0,esk5_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_169, c_0_208]), c_0_104]), c_0_84])])).
% 1.29/1.46  cnf(c_0_217, negated_conjecture, (esk5_0!=k1_xboole_0|~m1_subset_1(k1_partfun1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_209, c_0_210]), c_0_47])])).
% 1.29/1.46  cnf(c_0_218, plain, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_211])).
% 1.29/1.46  cnf(c_0_219, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(X1))|esk5_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_212, c_0_177])).
% 1.29/1.46  cnf(c_0_220, negated_conjecture, (v1_funct_1(esk5_0)|esk5_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_213, c_0_177])).
% 1.29/1.46  cnf(c_0_221, plain, (k5_relat_1(k2_funct_1(X1),X1)=k6_partfun1(X2)|X2=k1_xboole_0|k2_relset_1(X3,X2,X1)!=X2|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_207])).
% 1.29/1.46  cnf(c_0_222, negated_conjecture, (~r2_relset_1(esk5_0,esk5_0,k1_partfun1(esk5_0,esk5_0,esk5_0,esk5_0,esk6_0,k2_funct_2(esk5_0,esk6_0)),k6_relat_1(esk5_0))|~r2_relset_1(esk5_0,esk5_0,k5_relat_1(k2_funct_2(esk5_0,esk6_0),esk6_0),k6_relat_1(esk5_0))|~m1_subset_1(k2_funct_2(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_193, c_0_214]), c_0_60]), c_0_119]), c_0_61])])).
% 1.29/1.46  cnf(c_0_223, plain, (X3=k1_xboole_0|k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(X2)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_1(X1)|~v2_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[c_0_215, c_0_182])).
% 1.29/1.46  cnf(c_0_224, negated_conjecture, (k2_relset_1(esk5_0,X1,esk6_0)=esk5_0|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1)))), inference(spm,[status(thm)],[c_0_190, c_0_216])).
% 1.29/1.46  cnf(c_0_225, negated_conjecture, (esk5_0!=k1_xboole_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_217, c_0_218]), c_0_219]), c_0_220])).
% 1.29/1.46  cnf(c_0_226, plain, (X2=k1_xboole_0|k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(X2)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v2_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(rw,[status(thm)],[c_0_221, c_0_182])).
% 1.29/1.46  fof(c_0_227, plain, ![X52, X53, X54, X55]:(~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))|r2_relset_1(X52,X53,X54,X54)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[reflexivity_r2_relset_1])])).
% 1.29/1.46  cnf(c_0_228, negated_conjecture, (~r2_relset_1(esk5_0,esk5_0,k5_relat_1(esk6_0,k2_funct_2(esk5_0,esk6_0)),k6_relat_1(esk5_0))|~r2_relset_1(esk5_0,esk5_0,k5_relat_1(k2_funct_2(esk5_0,esk6_0),esk6_0),k6_relat_1(esk5_0))|~m1_subset_1(k2_funct_2(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_222, c_0_214]), c_0_119]), c_0_60]), c_0_61])])).
% 1.29/1.46  cnf(c_0_229, negated_conjecture, (m1_subset_1(k2_funct_2(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk5_0)))), inference(rw,[status(thm)],[c_0_128, c_0_208])).
% 1.29/1.46  cnf(c_0_230, negated_conjecture, (k5_relat_1(esk6_0,k2_funct_2(esk5_0,esk6_0))=k6_relat_1(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_223, c_0_224]), c_0_101]), c_0_102]), c_0_60])])]), c_0_79]), c_0_61])]), c_0_225])).
% 1.29/1.46  cnf(c_0_231, negated_conjecture, (k5_relat_1(k2_funct_2(esk5_0,esk6_0),esk6_0)=k6_relat_1(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_226, c_0_224]), c_0_101]), c_0_102]), c_0_60])])]), c_0_79]), c_0_61])]), c_0_225])).
% 1.29/1.46  cnf(c_0_232, plain, (r2_relset_1(X2,X3,X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_227])).
% 1.29/1.46  cnf(c_0_233, negated_conjecture, (~r2_relset_1(esk5_0,esk5_0,k6_relat_1(esk5_0),k6_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_228, c_0_229])]), c_0_230]), c_0_231])])).
% 1.29/1.46  cnf(c_0_234, plain, (r2_relset_1(X1,X2,X3,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_232, c_0_70])).
% 1.29/1.46  cnf(c_0_235, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_233, c_0_234]), c_0_47])]), ['proof']).
% 1.29/1.46  # SZS output end CNFRefutation
% 1.29/1.46  # Proof object total steps             : 236
% 1.29/1.46  # Proof object clause steps            : 166
% 1.29/1.46  # Proof object formula steps           : 70
% 1.29/1.46  # Proof object conjectures             : 82
% 1.29/1.46  # Proof object clause conjectures      : 79
% 1.29/1.46  # Proof object formula conjectures     : 3
% 1.29/1.46  # Proof object initial clauses used    : 53
% 1.29/1.46  # Proof object initial formulas used   : 35
% 1.29/1.46  # Proof object generating inferences   : 105
% 1.29/1.46  # Proof object simplifying inferences  : 174
% 1.29/1.46  # Training examples: 0 positive, 0 negative
% 1.29/1.46  # Parsed axioms                        : 36
% 1.29/1.46  # Removed by relevancy pruning/SinE    : 0
% 1.29/1.46  # Initial clauses                      : 64
% 1.29/1.46  # Removed in clause preprocessing      : 3
% 1.29/1.46  # Initial clauses in saturation        : 61
% 1.29/1.46  # Processed clauses                    : 21377
% 1.29/1.46  # ...of these trivial                  : 874
% 1.29/1.46  # ...subsumed                          : 16628
% 1.29/1.46  # ...remaining for further processing  : 3875
% 1.29/1.46  # Other redundant clauses eliminated   : 32
% 1.29/1.46  # Clauses deleted for lack of memory   : 0
% 1.29/1.46  # Backward-subsumed                    : 348
% 1.29/1.46  # Backward-rewritten                   : 1146
% 1.29/1.46  # Generated clauses                    : 137627
% 1.29/1.46  # ...of the previous two non-trivial   : 103793
% 1.29/1.46  # Contextual simplify-reflections      : 109
% 1.29/1.46  # Paramodulations                      : 137594
% 1.29/1.46  # Factorizations                       : 0
% 1.29/1.46  # Equation resolutions                 : 33
% 1.29/1.46  # Propositional unsat checks           : 0
% 1.29/1.46  #    Propositional check models        : 0
% 1.29/1.46  #    Propositional check unsatisfiable : 0
% 1.29/1.46  #    Propositional clauses             : 0
% 1.29/1.46  #    Propositional clauses after purity: 0
% 1.29/1.46  #    Propositional unsat core size     : 0
% 1.29/1.46  #    Propositional preprocessing time  : 0.000
% 1.29/1.46  #    Propositional encoding time       : 0.000
% 1.29/1.46  #    Propositional solver time         : 0.000
% 1.29/1.46  #    Success case prop preproc time    : 0.000
% 1.29/1.46  #    Success case prop encoding time   : 0.000
% 1.29/1.46  #    Success case prop solver time     : 0.000
% 1.29/1.46  # Current number of processed clauses  : 2378
% 1.29/1.46  #    Positive orientable unit clauses  : 1094
% 1.29/1.46  #    Positive unorientable unit clauses: 0
% 1.29/1.46  #    Negative unit clauses             : 12
% 1.29/1.46  #    Non-unit-clauses                  : 1272
% 1.29/1.46  # Current number of unprocessed clauses: 76706
% 1.29/1.46  # ...number of literals in the above   : 246558
% 1.29/1.46  # Current number of archived formulas  : 0
% 1.29/1.46  # Current number of archived clauses   : 1495
% 1.29/1.46  # Clause-clause subsumption calls (NU) : 393353
% 1.29/1.46  # Rec. Clause-clause subsumption calls : 289615
% 1.29/1.46  # Non-unit clause-clause subsumptions  : 5341
% 1.29/1.46  # Unit Clause-clause subsumption calls : 118919
% 1.29/1.46  # Rewrite failures with RHS unbound    : 0
% 1.29/1.46  # BW rewrite match attempts            : 97014
% 1.29/1.46  # BW rewrite match successes           : 83
% 1.29/1.46  # Condensation attempts                : 0
% 1.29/1.46  # Condensation successes               : 0
% 1.29/1.46  # Termbank termtop insertions          : 1935995
% 1.29/1.46  
% 1.29/1.46  # -------------------------------------------------
% 1.29/1.46  # User time                : 1.083 s
% 1.29/1.46  # System time              : 0.040 s
% 1.29/1.46  # Total time               : 1.123 s
% 1.29/1.46  # Maximum resident set size: 1628 pages
%------------------------------------------------------------------------------
