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
% DateTime   : Thu Dec  3 11:08:15 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 555 expanded)
%              Number of clauses        :   69 ( 198 expanded)
%              Number of leaves         :   20 ( 136 expanded)
%              Depth                    :   10
%              Number of atoms          :  342 (3413 expanded)
%              Number of equality atoms :   59 ( 362 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t192_funct_2,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3,X4] :
              ( ( v1_funct_1(X4)
                & v1_funct_2(X4,X2,X1)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
             => ! [X5] :
                  ( ( v1_funct_1(X5)
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) )
                 => ! [X6] :
                      ( m1_subset_1(X6,X2)
                     => ( v1_partfun1(X5,X1)
                       => k3_funct_2(X2,X3,k8_funct_2(X2,X1,X3,X4,X5),X6) = k1_funct_1(X5,k3_funct_2(X2,X1,X4,X6)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_funct_2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(cc6_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1) )
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X2))
         => v5_relat_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

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

fof(dt_k8_funct_2,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
     => ( v1_funct_1(k8_funct_2(X1,X2,X3,X4,X5))
        & v1_funct_2(k8_funct_2(X1,X2,X3,X4,X5),X1,X3)
        & m1_subset_1(k8_funct_2(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_funct_2)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(redefinition_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => k3_funct_2(X1,X2,X3,X4) = k1_funct_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(t189_funct_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( m1_subset_1(X3,X1)
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,X1,X2)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
                 => r2_hidden(k3_funct_2(X1,X2,X4,X3),k2_relset_1(X1,X2,X4)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_funct_2)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t185_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ~ v1_xboole_0(X3)
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X2,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
         => ! [X5] :
              ( ( v1_funct_1(X5)
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) )
             => ! [X6] :
                  ( m1_subset_1(X6,X2)
                 => ( r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))
                   => ( X2 = k1_xboole_0
                      | k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6) = k1_funct_1(X5,k1_funct_1(X4,X6)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3,X4] :
                ( ( v1_funct_1(X4)
                  & v1_funct_2(X4,X2,X1)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
               => ! [X5] :
                    ( ( v1_funct_1(X5)
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) )
                   => ! [X6] :
                        ( m1_subset_1(X6,X2)
                       => ( v1_partfun1(X5,X1)
                         => k3_funct_2(X2,X3,k8_funct_2(X2,X1,X3,X4,X5),X6) = k1_funct_1(X5,k3_funct_2(X2,X1,X4,X6)) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t192_funct_2])).

fof(c_0_21,plain,(
    ! [X13,X14] :
      ( ( r1_tarski(X13,X14)
        | X13 != X14 )
      & ( r1_tarski(X14,X13)
        | X13 != X14 )
      & ( ~ r1_tarski(X13,X14)
        | ~ r1_tarski(X14,X13)
        | X13 = X14 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_22,plain,(
    ! [X22,X23,X24] :
      ( ~ v1_relat_1(X23)
      | ~ v5_relat_1(X23,X22)
      | ~ m1_subset_1(X24,k1_zfmisc_1(X23))
      | v5_relat_1(X24,X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc6_relat_1])])])).

fof(c_0_23,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0)
    & ~ v1_xboole_0(esk4_0)
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk4_0,esk3_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))
    & v1_funct_1(esk7_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk5_0)))
    & m1_subset_1(esk8_0,esk4_0)
    & v1_partfun1(esk7_0,esk3_0)
    & k3_funct_2(esk4_0,esk5_0,k8_funct_2(esk4_0,esk3_0,esk5_0,esk6_0,esk7_0),esk8_0) != k1_funct_1(esk7_0,k3_funct_2(esk4_0,esk3_0,esk6_0,esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).

fof(c_0_24,plain,(
    ! [X27,X28] : v1_relat_1(k2_zfmisc_1(X27,X28)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_25,plain,(
    ! [X25,X26] :
      ( ( ~ v5_relat_1(X26,X25)
        | r1_tarski(k2_relat_1(X26),X25)
        | ~ v1_relat_1(X26) )
      & ( ~ r1_tarski(k2_relat_1(X26),X25)
        | v5_relat_1(X26,X25)
        | ~ v1_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_27,plain,(
    ! [X31,X32,X33] :
      ( ( v4_relat_1(X33,X31)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( v5_relat_1(X33,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_28,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X20)
      | ~ m1_subset_1(X21,k1_zfmisc_1(X20))
      | v1_relat_1(X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_29,plain,(
    ! [X42,X43,X44,X45,X46] :
      ( ( v1_funct_1(k8_funct_2(X42,X43,X44,X45,X46))
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,X42,X43)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
        | ~ v1_funct_1(X46)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) )
      & ( v1_funct_2(k8_funct_2(X42,X43,X44,X45,X46),X42,X44)
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,X42,X43)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
        | ~ v1_funct_1(X46)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) )
      & ( m1_subset_1(k8_funct_2(X42,X43,X44,X45,X46),k1_zfmisc_1(k2_zfmisc_1(X42,X44)))
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,X42,X43)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
        | ~ v1_funct_1(X46)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_funct_2])])])).

cnf(c_0_30,plain,
    ( v5_relat_1(X3,X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( v5_relat_1(X1,X2)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_26])).

fof(c_0_35,plain,(
    ! [X37,X38,X39] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
      | k2_relset_1(X37,X38,X39) = k2_relat_1(X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_36,plain,(
    ! [X47,X48,X49,X50] :
      ( v1_xboole_0(X47)
      | ~ v1_funct_1(X49)
      | ~ v1_funct_2(X49,X47,X48)
      | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
      | ~ m1_subset_1(X50,X47)
      | k3_funct_2(X47,X48,X49,X50) = k1_funct_1(X49,X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).

fof(c_0_37,plain,(
    ! [X40,X41] :
      ( ( ~ v1_partfun1(X41,X40)
        | k1_relat_1(X41) = X40
        | ~ v1_relat_1(X41)
        | ~ v4_relat_1(X41,X40) )
      & ( k1_relat_1(X41) != X40
        | v1_partfun1(X41,X40)
        | ~ v1_relat_1(X41)
        | ~ v4_relat_1(X41,X40) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).

cnf(c_0_38,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_40,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,plain,
    ( m1_subset_1(k8_funct_2(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_43,plain,
    ( v1_funct_2(k8_funct_2(X1,X2,X3,X4,X5),X1,X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_44,plain,
    ( v1_funct_1(k8_funct_2(X1,X2,X3,X4,X5))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_45,negated_conjecture,
    ( v5_relat_1(esk6_0,X1)
    | ~ v5_relat_1(k2_zfmisc_1(esk4_0,esk3_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])])).

cnf(c_0_46,plain,
    ( v5_relat_1(X1,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_47,plain,(
    ! [X57,X58,X59,X60] :
      ( v1_xboole_0(X57)
      | v1_xboole_0(X58)
      | ~ m1_subset_1(X59,X57)
      | ~ v1_funct_1(X60)
      | ~ v1_funct_2(X60,X57,X58)
      | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X57,X58)))
      | r2_hidden(k3_funct_2(X57,X58,X60,X59),k2_relset_1(X57,X58,X60)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t189_funct_2])])])])).

cnf(c_0_48,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_49,plain,
    ( v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X4) = k1_funct_1(X2,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_50,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_51,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_52,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_53,plain,(
    ! [X18] : m1_subset_1(esk2_1(X18),X18) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_54,plain,(
    ! [X34,X35,X36] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
      | k1_relset_1(X34,X35,X36) = k1_relat_1(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_55,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_56,negated_conjecture,
    ( v1_partfun1(esk7_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_57,negated_conjecture,
    ( v4_relat_1(esk7_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_58,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_39]),c_0_32])])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(k8_funct_2(X1,esk3_0,esk5_0,X2,esk7_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk5_0)))
    | ~ v1_funct_2(X2,X1,esk3_0)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_39]),c_0_42])])).

cnf(c_0_60,negated_conjecture,
    ( v1_funct_2(k8_funct_2(X1,esk3_0,esk5_0,X2,esk7_0),X1,esk5_0)
    | ~ v1_funct_2(X2,X1,esk3_0)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_39]),c_0_42])])).

cnf(c_0_61,negated_conjecture,
    ( v1_funct_1(k8_funct_2(X1,esk3_0,esk5_0,X2,esk7_0))
    | ~ v1_funct_2(X2,X1,esk3_0)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_39]),c_0_42])])).

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

cnf(c_0_63,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_64,negated_conjecture,
    ( v5_relat_1(esk6_0,k2_relat_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_32])])).

cnf(c_0_65,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_31]),c_0_32])])).

cnf(c_0_66,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | r2_hidden(k3_funct_2(X1,X2,X4,X3),k2_relset_1(X1,X2,X4))
    | ~ m1_subset_1(X3,X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_67,negated_conjecture,
    ( k2_relset_1(esk4_0,esk3_0,esk6_0) = k2_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_31])).

cnf(c_0_68,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_69,negated_conjecture,
    ( k3_funct_2(esk4_0,esk3_0,esk6_0,X1) = k1_funct_1(esk6_0,X1)
    | ~ m1_subset_1(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_31]),c_0_50]),c_0_51])]),c_0_52])).

cnf(c_0_70,plain,
    ( m1_subset_1(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_71,plain,(
    ! [X51,X52,X53,X54,X55,X56] :
      ( v1_xboole_0(X53)
      | ~ v1_funct_1(X54)
      | ~ v1_funct_2(X54,X52,X53)
      | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))
      | ~ v1_funct_1(X55)
      | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X51)))
      | ~ m1_subset_1(X56,X52)
      | ~ r1_tarski(k2_relset_1(X52,X53,X54),k1_relset_1(X53,X51,X55))
      | X52 = k1_xboole_0
      | k1_funct_1(k8_funct_2(X52,X53,X51,X54,X55),X56) = k1_funct_1(X55,k1_funct_1(X54,X56)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t185_funct_2])])])])).

cnf(c_0_72,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_73,negated_conjecture,
    ( k1_relat_1(esk7_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57]),c_0_58])])).

cnf(c_0_74,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(esk8_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(k8_funct_2(esk4_0,esk3_0,esk5_0,esk6_0,esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_50]),c_0_51]),c_0_31])])).

cnf(c_0_77,negated_conjecture,
    ( v1_funct_2(k8_funct_2(esk4_0,esk3_0,esk5_0,esk6_0,esk7_0),esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_50]),c_0_51]),c_0_31])])).

cnf(c_0_78,negated_conjecture,
    ( v1_funct_1(k8_funct_2(esk4_0,esk3_0,esk5_0,esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_50]),c_0_51]),c_0_31])])).

cnf(c_0_79,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk6_0),k2_relat_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(k3_funct_2(esk4_0,esk3_0,esk6_0,X1),k2_relat_1(esk6_0))
    | ~ m1_subset_1(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_31]),c_0_67]),c_0_50]),c_0_51])]),c_0_68]),c_0_52])).

cnf(c_0_82,negated_conjecture,
    ( k3_funct_2(esk4_0,esk3_0,esk6_0,esk2_1(esk4_0)) = k1_funct_1(esk6_0,esk2_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_83,plain,
    ( v1_xboole_0(X1)
    | X3 = k1_xboole_0
    | k1_funct_1(k8_funct_2(X3,X1,X5,X2,X4),X6) = k1_funct_1(X4,k1_funct_1(X2,X6))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X5)))
    | ~ m1_subset_1(X6,X3)
    | ~ r1_tarski(k2_relset_1(X3,X1,X2),k1_relset_1(X1,X5,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_84,negated_conjecture,
    ( k1_relset_1(esk3_0,esk5_0,esk7_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_39]),c_0_73])).

cnf(c_0_85,negated_conjecture,
    ( v5_relat_1(esk6_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_31])).

cnf(c_0_86,negated_conjecture,
    ( k3_funct_2(esk4_0,esk5_0,k8_funct_2(esk4_0,esk3_0,esk5_0,esk6_0,esk7_0),esk8_0) != k1_funct_1(esk7_0,k3_funct_2(esk4_0,esk3_0,esk6_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_87,negated_conjecture,
    ( k3_funct_2(esk4_0,esk3_0,esk6_0,esk8_0) = k1_funct_1(esk6_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_75])).

cnf(c_0_88,negated_conjecture,
    ( k3_funct_2(esk4_0,esk5_0,k8_funct_2(esk4_0,esk3_0,esk5_0,esk6_0,esk7_0),X1) = k1_funct_1(k8_funct_2(esk4_0,esk3_0,esk5_0,esk6_0,esk7_0),X1)
    | ~ m1_subset_1(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_76]),c_0_77]),c_0_78])]),c_0_52])).

fof(c_0_89,plain,(
    ! [X29,X30] :
      ( ~ r2_hidden(X29,X30)
      | ~ r1_tarski(X30,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(X1,k2_relat_1(k2_zfmisc_1(esk4_0,esk3_0)))
    | ~ r2_hidden(X1,k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk6_0,esk2_1(esk4_0)),k2_relat_1(esk6_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_70]),c_0_82])).

cnf(c_0_92,negated_conjecture,
    ( k1_funct_1(k8_funct_2(X1,esk3_0,esk5_0,X2,esk7_0),X3) = k1_funct_1(esk7_0,k1_funct_1(X2,X3))
    | X1 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,esk3_0)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))
    | ~ m1_subset_1(X3,X1)
    | ~ r1_tarski(k2_relset_1(X1,esk3_0,X2),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_39]),c_0_42]),c_0_84])]),c_0_68])).

cnf(c_0_93,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk6_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_85]),c_0_65])])).

cnf(c_0_94,negated_conjecture,
    ( k3_funct_2(esk4_0,esk5_0,k8_funct_2(esk4_0,esk3_0,esk5_0,esk6_0,esk7_0),esk8_0) != k1_funct_1(esk7_0,k1_funct_1(esk6_0,esk8_0)) ),
    inference(rw,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_95,negated_conjecture,
    ( k3_funct_2(esk4_0,esk5_0,k8_funct_2(esk4_0,esk3_0,esk5_0,esk6_0,esk7_0),esk8_0) = k1_funct_1(k8_funct_2(esk4_0,esk3_0,esk5_0,esk6_0,esk7_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_88,c_0_75])).

fof(c_0_96,plain,(
    ! [X16,X17] :
      ( ( k2_zfmisc_1(X16,X17) != k1_xboole_0
        | X16 = k1_xboole_0
        | X17 = k1_xboole_0 )
      & ( X16 != k1_xboole_0
        | k2_zfmisc_1(X16,X17) = k1_xboole_0 )
      & ( X17 != k1_xboole_0
        | k2_zfmisc_1(X16,X17) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_97,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk6_0,esk2_1(esk4_0)),k2_relat_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_99,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk4_0,esk3_0,esk5_0,esk6_0,esk7_0),X1) = k1_funct_1(esk7_0,k1_funct_1(esk6_0,X1))
    | esk4_0 = k1_xboole_0
    | ~ m1_subset_1(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_50]),c_0_51]),c_0_31]),c_0_67]),c_0_93])])).

cnf(c_0_100,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk4_0,esk3_0,esk5_0,esk6_0,esk7_0),esk8_0) != k1_funct_1(esk7_0,k1_funct_1(esk6_0,esk8_0)) ),
    inference(rw,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_101,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

fof(c_0_102,plain,(
    ! [X15] : r1_tarski(k1_xboole_0,X15) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_103,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k2_zfmisc_1(esk4_0,esk3_0)),k1_funct_1(esk6_0,esk2_1(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_104,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_75]),c_0_100])).

cnf(c_0_105,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_101])).

cnf(c_0_106,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_107,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_108,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_103,c_0_104]),c_0_105]),c_0_106]),c_0_104]),c_0_107])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:11:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.42  # AutoSched0-Mode selected heuristic G_E___215_C46_F1_AE_CS_SP_PS_S2S
% 0.18/0.42  # and selection function SelectNewComplexAHP.
% 0.18/0.42  #
% 0.18/0.42  # Preprocessing time       : 0.029 s
% 0.18/0.42  # Presaturation interreduction done
% 0.18/0.42  
% 0.18/0.42  # Proof found!
% 0.18/0.42  # SZS status Theorem
% 0.18/0.42  # SZS output start CNFRefutation
% 0.18/0.42  fof(t192_funct_2, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))=>![X6]:(m1_subset_1(X6,X2)=>(v1_partfun1(X5,X1)=>k3_funct_2(X2,X3,k8_funct_2(X2,X1,X3,X4,X5),X6)=k1_funct_1(X5,k3_funct_2(X2,X1,X4,X6)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_funct_2)).
% 0.18/0.42  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.18/0.42  fof(cc6_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v5_relat_1(X2,X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X2))=>v5_relat_1(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc6_relat_1)).
% 0.18/0.42  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.18/0.42  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.18/0.42  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.18/0.42  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.18/0.42  fof(dt_k8_funct_2, axiom, ![X1, X2, X3, X4, X5]:(((((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X5))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>((v1_funct_1(k8_funct_2(X1,X2,X3,X4,X5))&v1_funct_2(k8_funct_2(X1,X2,X3,X4,X5),X1,X3))&m1_subset_1(k8_funct_2(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X1,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_funct_2)).
% 0.18/0.42  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.18/0.42  fof(redefinition_k3_funct_2, axiom, ![X1, X2, X3, X4]:(((((~(v1_xboole_0(X1))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,X1))=>k3_funct_2(X1,X2,X3,X4)=k1_funct_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 0.18/0.42  fof(d4_partfun1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>(v1_partfun1(X2,X1)<=>k1_relat_1(X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 0.18/0.42  fof(t189_funct_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,X1)=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r2_hidden(k3_funct_2(X1,X2,X4,X3),k2_relset_1(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t189_funct_2)).
% 0.18/0.42  fof(existence_m1_subset_1, axiom, ![X1]:?[X2]:m1_subset_1(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 0.18/0.42  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.18/0.42  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.18/0.42  fof(t185_funct_2, axiom, ![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k1_funct_1(X5,k1_funct_1(X4,X6)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 0.18/0.42  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.18/0.42  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.18/0.42  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.18/0.42  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.18/0.42  fof(c_0_20, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))=>![X6]:(m1_subset_1(X6,X2)=>(v1_partfun1(X5,X1)=>k3_funct_2(X2,X3,k8_funct_2(X2,X1,X3,X4,X5),X6)=k1_funct_1(X5,k3_funct_2(X2,X1,X4,X6))))))))), inference(assume_negation,[status(cth)],[t192_funct_2])).
% 0.18/0.42  fof(c_0_21, plain, ![X13, X14]:(((r1_tarski(X13,X14)|X13!=X14)&(r1_tarski(X14,X13)|X13!=X14))&(~r1_tarski(X13,X14)|~r1_tarski(X14,X13)|X13=X14)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.18/0.42  fof(c_0_22, plain, ![X22, X23, X24]:(~v1_relat_1(X23)|~v5_relat_1(X23,X22)|(~m1_subset_1(X24,k1_zfmisc_1(X23))|v5_relat_1(X24,X22))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc6_relat_1])])])).
% 0.18/0.42  fof(c_0_23, negated_conjecture, (~v1_xboole_0(esk3_0)&(~v1_xboole_0(esk4_0)&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk4_0,esk3_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))))&((v1_funct_1(esk7_0)&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk5_0))))&(m1_subset_1(esk8_0,esk4_0)&(v1_partfun1(esk7_0,esk3_0)&k3_funct_2(esk4_0,esk5_0,k8_funct_2(esk4_0,esk3_0,esk5_0,esk6_0,esk7_0),esk8_0)!=k1_funct_1(esk7_0,k3_funct_2(esk4_0,esk3_0,esk6_0,esk8_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).
% 0.18/0.42  fof(c_0_24, plain, ![X27, X28]:v1_relat_1(k2_zfmisc_1(X27,X28)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.18/0.42  fof(c_0_25, plain, ![X25, X26]:((~v5_relat_1(X26,X25)|r1_tarski(k2_relat_1(X26),X25)|~v1_relat_1(X26))&(~r1_tarski(k2_relat_1(X26),X25)|v5_relat_1(X26,X25)|~v1_relat_1(X26))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.18/0.42  cnf(c_0_26, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.42  fof(c_0_27, plain, ![X31, X32, X33]:((v4_relat_1(X33,X31)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))&(v5_relat_1(X33,X32)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.18/0.42  fof(c_0_28, plain, ![X20, X21]:(~v1_relat_1(X20)|(~m1_subset_1(X21,k1_zfmisc_1(X20))|v1_relat_1(X21))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.18/0.42  fof(c_0_29, plain, ![X42, X43, X44, X45, X46]:(((v1_funct_1(k8_funct_2(X42,X43,X44,X45,X46))|(~v1_funct_1(X45)|~v1_funct_2(X45,X42,X43)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))|~v1_funct_1(X46)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))))&(v1_funct_2(k8_funct_2(X42,X43,X44,X45,X46),X42,X44)|(~v1_funct_1(X45)|~v1_funct_2(X45,X42,X43)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))|~v1_funct_1(X46)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X43,X44))))))&(m1_subset_1(k8_funct_2(X42,X43,X44,X45,X46),k1_zfmisc_1(k2_zfmisc_1(X42,X44)))|(~v1_funct_1(X45)|~v1_funct_2(X45,X42,X43)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))|~v1_funct_1(X46)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_funct_2])])])).
% 0.18/0.42  cnf(c_0_30, plain, (v5_relat_1(X3,X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.42  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.42  cnf(c_0_32, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.42  cnf(c_0_33, plain, (v5_relat_1(X1,X2)|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.18/0.42  cnf(c_0_34, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_26])).
% 0.18/0.42  fof(c_0_35, plain, ![X37, X38, X39]:(~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))|k2_relset_1(X37,X38,X39)=k2_relat_1(X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.18/0.42  fof(c_0_36, plain, ![X47, X48, X49, X50]:(v1_xboole_0(X47)|~v1_funct_1(X49)|~v1_funct_2(X49,X47,X48)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))|~m1_subset_1(X50,X47)|k3_funct_2(X47,X48,X49,X50)=k1_funct_1(X49,X50)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).
% 0.18/0.42  fof(c_0_37, plain, ![X40, X41]:((~v1_partfun1(X41,X40)|k1_relat_1(X41)=X40|(~v1_relat_1(X41)|~v4_relat_1(X41,X40)))&(k1_relat_1(X41)!=X40|v1_partfun1(X41,X40)|(~v1_relat_1(X41)|~v4_relat_1(X41,X40)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).
% 0.18/0.42  cnf(c_0_38, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.18/0.42  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.42  cnf(c_0_40, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.42  cnf(c_0_41, plain, (m1_subset_1(k8_funct_2(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.42  cnf(c_0_42, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.42  cnf(c_0_43, plain, (v1_funct_2(k8_funct_2(X1,X2,X3,X4,X5),X1,X3)|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.42  cnf(c_0_44, plain, (v1_funct_1(k8_funct_2(X1,X2,X3,X4,X5))|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.42  cnf(c_0_45, negated_conjecture, (v5_relat_1(esk6_0,X1)|~v5_relat_1(k2_zfmisc_1(esk4_0,esk3_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])])).
% 0.18/0.42  cnf(c_0_46, plain, (v5_relat_1(X1,k2_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.18/0.42  fof(c_0_47, plain, ![X57, X58, X59, X60]:(v1_xboole_0(X57)|(v1_xboole_0(X58)|(~m1_subset_1(X59,X57)|(~v1_funct_1(X60)|~v1_funct_2(X60,X57,X58)|~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X57,X58)))|r2_hidden(k3_funct_2(X57,X58,X60,X59),k2_relset_1(X57,X58,X60)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t189_funct_2])])])])).
% 0.18/0.42  cnf(c_0_48, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.18/0.42  cnf(c_0_49, plain, (v1_xboole_0(X1)|k3_funct_2(X1,X3,X2,X4)=k1_funct_1(X2,X4)|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~m1_subset_1(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.18/0.42  cnf(c_0_50, negated_conjecture, (v1_funct_2(esk6_0,esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.42  cnf(c_0_51, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.42  cnf(c_0_52, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.42  fof(c_0_53, plain, ![X18]:m1_subset_1(esk2_1(X18),X18), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).
% 0.18/0.42  fof(c_0_54, plain, ![X34, X35, X36]:(~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|k1_relset_1(X34,X35,X36)=k1_relat_1(X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.18/0.42  cnf(c_0_55, plain, (k1_relat_1(X1)=X2|~v1_partfun1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.18/0.42  cnf(c_0_56, negated_conjecture, (v1_partfun1(esk7_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.42  cnf(c_0_57, negated_conjecture, (v4_relat_1(esk7_0,esk3_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.18/0.42  cnf(c_0_58, negated_conjecture, (v1_relat_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_39]), c_0_32])])).
% 0.18/0.42  cnf(c_0_59, negated_conjecture, (m1_subset_1(k8_funct_2(X1,esk3_0,esk5_0,X2,esk7_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk5_0)))|~v1_funct_2(X2,X1,esk3_0)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_39]), c_0_42])])).
% 0.18/0.42  cnf(c_0_60, negated_conjecture, (v1_funct_2(k8_funct_2(X1,esk3_0,esk5_0,X2,esk7_0),X1,esk5_0)|~v1_funct_2(X2,X1,esk3_0)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_39]), c_0_42])])).
% 0.18/0.42  cnf(c_0_61, negated_conjecture, (v1_funct_1(k8_funct_2(X1,esk3_0,esk5_0,X2,esk7_0))|~v1_funct_2(X2,X1,esk3_0)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_39]), c_0_42])])).
% 0.18/0.42  fof(c_0_62, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.18/0.42  cnf(c_0_63, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.18/0.42  cnf(c_0_64, negated_conjecture, (v5_relat_1(esk6_0,k2_relat_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_32])])).
% 0.18/0.42  cnf(c_0_65, negated_conjecture, (v1_relat_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_31]), c_0_32])])).
% 0.18/0.42  cnf(c_0_66, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|r2_hidden(k3_funct_2(X1,X2,X4,X3),k2_relset_1(X1,X2,X4))|~m1_subset_1(X3,X1)|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.18/0.42  cnf(c_0_67, negated_conjecture, (k2_relset_1(esk4_0,esk3_0,esk6_0)=k2_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_48, c_0_31])).
% 0.18/0.42  cnf(c_0_68, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.42  cnf(c_0_69, negated_conjecture, (k3_funct_2(esk4_0,esk3_0,esk6_0,X1)=k1_funct_1(esk6_0,X1)|~m1_subset_1(X1,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_31]), c_0_50]), c_0_51])]), c_0_52])).
% 0.18/0.42  cnf(c_0_70, plain, (m1_subset_1(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.18/0.42  fof(c_0_71, plain, ![X51, X52, X53, X54, X55, X56]:(v1_xboole_0(X53)|(~v1_funct_1(X54)|~v1_funct_2(X54,X52,X53)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))|(~v1_funct_1(X55)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X51)))|(~m1_subset_1(X56,X52)|(~r1_tarski(k2_relset_1(X52,X53,X54),k1_relset_1(X53,X51,X55))|(X52=k1_xboole_0|k1_funct_1(k8_funct_2(X52,X53,X51,X54,X55),X56)=k1_funct_1(X55,k1_funct_1(X54,X56)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t185_funct_2])])])])).
% 0.18/0.42  cnf(c_0_72, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.18/0.42  cnf(c_0_73, negated_conjecture, (k1_relat_1(esk7_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57]), c_0_58])])).
% 0.18/0.42  cnf(c_0_74, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.18/0.42  cnf(c_0_75, negated_conjecture, (m1_subset_1(esk8_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.42  cnf(c_0_76, negated_conjecture, (m1_subset_1(k8_funct_2(esk4_0,esk3_0,esk5_0,esk6_0,esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_50]), c_0_51]), c_0_31])])).
% 0.18/0.42  cnf(c_0_77, negated_conjecture, (v1_funct_2(k8_funct_2(esk4_0,esk3_0,esk5_0,esk6_0,esk7_0),esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_50]), c_0_51]), c_0_31])])).
% 0.18/0.42  cnf(c_0_78, negated_conjecture, (v1_funct_1(k8_funct_2(esk4_0,esk3_0,esk5_0,esk6_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_50]), c_0_51]), c_0_31])])).
% 0.18/0.42  cnf(c_0_79, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.18/0.42  cnf(c_0_80, negated_conjecture, (r1_tarski(k2_relat_1(esk6_0),k2_relat_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65])])).
% 0.18/0.42  cnf(c_0_81, negated_conjecture, (r2_hidden(k3_funct_2(esk4_0,esk3_0,esk6_0,X1),k2_relat_1(esk6_0))|~m1_subset_1(X1,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_31]), c_0_67]), c_0_50]), c_0_51])]), c_0_68]), c_0_52])).
% 0.18/0.42  cnf(c_0_82, negated_conjecture, (k3_funct_2(esk4_0,esk3_0,esk6_0,esk2_1(esk4_0))=k1_funct_1(esk6_0,esk2_1(esk4_0))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.18/0.42  cnf(c_0_83, plain, (v1_xboole_0(X1)|X3=k1_xboole_0|k1_funct_1(k8_funct_2(X3,X1,X5,X2,X4),X6)=k1_funct_1(X4,k1_funct_1(X2,X6))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X5)))|~m1_subset_1(X6,X3)|~r1_tarski(k2_relset_1(X3,X1,X2),k1_relset_1(X1,X5,X4))), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.18/0.42  cnf(c_0_84, negated_conjecture, (k1_relset_1(esk3_0,esk5_0,esk7_0)=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_39]), c_0_73])).
% 0.18/0.42  cnf(c_0_85, negated_conjecture, (v5_relat_1(esk6_0,esk3_0)), inference(spm,[status(thm)],[c_0_74, c_0_31])).
% 0.18/0.42  cnf(c_0_86, negated_conjecture, (k3_funct_2(esk4_0,esk5_0,k8_funct_2(esk4_0,esk3_0,esk5_0,esk6_0,esk7_0),esk8_0)!=k1_funct_1(esk7_0,k3_funct_2(esk4_0,esk3_0,esk6_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.42  cnf(c_0_87, negated_conjecture, (k3_funct_2(esk4_0,esk3_0,esk6_0,esk8_0)=k1_funct_1(esk6_0,esk8_0)), inference(spm,[status(thm)],[c_0_69, c_0_75])).
% 0.18/0.42  cnf(c_0_88, negated_conjecture, (k3_funct_2(esk4_0,esk5_0,k8_funct_2(esk4_0,esk3_0,esk5_0,esk6_0,esk7_0),X1)=k1_funct_1(k8_funct_2(esk4_0,esk3_0,esk5_0,esk6_0,esk7_0),X1)|~m1_subset_1(X1,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_76]), c_0_77]), c_0_78])]), c_0_52])).
% 0.18/0.42  fof(c_0_89, plain, ![X29, X30]:(~r2_hidden(X29,X30)|~r1_tarski(X30,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.18/0.42  cnf(c_0_90, negated_conjecture, (r2_hidden(X1,k2_relat_1(k2_zfmisc_1(esk4_0,esk3_0)))|~r2_hidden(X1,k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.18/0.42  cnf(c_0_91, negated_conjecture, (r2_hidden(k1_funct_1(esk6_0,esk2_1(esk4_0)),k2_relat_1(esk6_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_70]), c_0_82])).
% 0.18/0.42  cnf(c_0_92, negated_conjecture, (k1_funct_1(k8_funct_2(X1,esk3_0,esk5_0,X2,esk7_0),X3)=k1_funct_1(esk7_0,k1_funct_1(X2,X3))|X1=k1_xboole_0|~v1_funct_2(X2,X1,esk3_0)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))|~m1_subset_1(X3,X1)|~r1_tarski(k2_relset_1(X1,esk3_0,X2),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_39]), c_0_42]), c_0_84])]), c_0_68])).
% 0.18/0.42  cnf(c_0_93, negated_conjecture, (r1_tarski(k2_relat_1(esk6_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_85]), c_0_65])])).
% 0.18/0.42  cnf(c_0_94, negated_conjecture, (k3_funct_2(esk4_0,esk5_0,k8_funct_2(esk4_0,esk3_0,esk5_0,esk6_0,esk7_0),esk8_0)!=k1_funct_1(esk7_0,k1_funct_1(esk6_0,esk8_0))), inference(rw,[status(thm)],[c_0_86, c_0_87])).
% 0.18/0.42  cnf(c_0_95, negated_conjecture, (k3_funct_2(esk4_0,esk5_0,k8_funct_2(esk4_0,esk3_0,esk5_0,esk6_0,esk7_0),esk8_0)=k1_funct_1(k8_funct_2(esk4_0,esk3_0,esk5_0,esk6_0,esk7_0),esk8_0)), inference(spm,[status(thm)],[c_0_88, c_0_75])).
% 0.18/0.42  fof(c_0_96, plain, ![X16, X17]:((k2_zfmisc_1(X16,X17)!=k1_xboole_0|(X16=k1_xboole_0|X17=k1_xboole_0))&((X16!=k1_xboole_0|k2_zfmisc_1(X16,X17)=k1_xboole_0)&(X17!=k1_xboole_0|k2_zfmisc_1(X16,X17)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.18/0.42  cnf(c_0_97, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_89])).
% 0.18/0.42  cnf(c_0_98, negated_conjecture, (r2_hidden(k1_funct_1(esk6_0,esk2_1(esk4_0)),k2_relat_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.18/0.42  cnf(c_0_99, negated_conjecture, (k1_funct_1(k8_funct_2(esk4_0,esk3_0,esk5_0,esk6_0,esk7_0),X1)=k1_funct_1(esk7_0,k1_funct_1(esk6_0,X1))|esk4_0=k1_xboole_0|~m1_subset_1(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_50]), c_0_51]), c_0_31]), c_0_67]), c_0_93])])).
% 0.18/0.42  cnf(c_0_100, negated_conjecture, (k1_funct_1(k8_funct_2(esk4_0,esk3_0,esk5_0,esk6_0,esk7_0),esk8_0)!=k1_funct_1(esk7_0,k1_funct_1(esk6_0,esk8_0))), inference(rw,[status(thm)],[c_0_94, c_0_95])).
% 0.18/0.42  cnf(c_0_101, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_96])).
% 0.18/0.42  fof(c_0_102, plain, ![X15]:r1_tarski(k1_xboole_0,X15), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.18/0.42  cnf(c_0_103, negated_conjecture, (~r1_tarski(k2_relat_1(k2_zfmisc_1(esk4_0,esk3_0)),k1_funct_1(esk6_0,esk2_1(esk4_0)))), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 0.18/0.42  cnf(c_0_104, negated_conjecture, (esk4_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_75]), c_0_100])).
% 0.18/0.42  cnf(c_0_105, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_101])).
% 0.18/0.42  cnf(c_0_106, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.18/0.42  cnf(c_0_107, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_102])).
% 0.18/0.42  cnf(c_0_108, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_103, c_0_104]), c_0_105]), c_0_106]), c_0_104]), c_0_107])]), ['proof']).
% 0.18/0.42  # SZS output end CNFRefutation
% 0.18/0.42  # Proof object total steps             : 109
% 0.18/0.42  # Proof object clause steps            : 69
% 0.18/0.42  # Proof object formula steps           : 40
% 0.18/0.42  # Proof object conjectures             : 46
% 0.18/0.42  # Proof object clause conjectures      : 43
% 0.18/0.42  # Proof object formula conjectures     : 3
% 0.18/0.42  # Proof object initial clauses used    : 33
% 0.18/0.42  # Proof object initial formulas used   : 20
% 0.18/0.42  # Proof object generating inferences   : 32
% 0.18/0.42  # Proof object simplifying inferences  : 65
% 0.18/0.42  # Training examples: 0 positive, 0 negative
% 0.18/0.42  # Parsed axioms                        : 20
% 0.18/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.42  # Initial clauses                      : 41
% 0.18/0.42  # Removed in clause preprocessing      : 0
% 0.18/0.42  # Initial clauses in saturation        : 41
% 0.18/0.42  # Processed clauses                    : 541
% 0.18/0.42  # ...of these trivial                  : 8
% 0.18/0.42  # ...subsumed                          : 8
% 0.18/0.42  # ...remaining for further processing  : 525
% 0.18/0.42  # Other redundant clauses eliminated   : 2
% 0.18/0.42  # Clauses deleted for lack of memory   : 0
% 0.18/0.42  # Backward-subsumed                    : 3
% 0.18/0.42  # Backward-rewritten                   : 271
% 0.18/0.42  # Generated clauses                    : 689
% 0.18/0.42  # ...of the previous two non-trivial   : 629
% 0.18/0.42  # Contextual simplify-reflections      : 4
% 0.18/0.42  # Paramodulations                      : 682
% 0.18/0.42  # Factorizations                       : 0
% 0.18/0.42  # Equation resolutions                 : 7
% 0.18/0.42  # Propositional unsat checks           : 0
% 0.18/0.42  #    Propositional check models        : 0
% 0.18/0.42  #    Propositional check unsatisfiable : 0
% 0.18/0.42  #    Propositional clauses             : 0
% 0.18/0.42  #    Propositional clauses after purity: 0
% 0.18/0.42  #    Propositional unsat core size     : 0
% 0.18/0.42  #    Propositional preprocessing time  : 0.000
% 0.18/0.42  #    Propositional encoding time       : 0.000
% 0.18/0.42  #    Propositional solver time         : 0.000
% 0.18/0.42  #    Success case prop preproc time    : 0.000
% 0.18/0.42  #    Success case prop encoding time   : 0.000
% 0.18/0.42  #    Success case prop solver time     : 0.000
% 0.18/0.42  # Current number of processed clauses  : 209
% 0.18/0.42  #    Positive orientable unit clauses  : 80
% 0.18/0.42  #    Positive unorientable unit clauses: 0
% 0.18/0.42  #    Negative unit clauses             : 3
% 0.18/0.42  #    Non-unit-clauses                  : 126
% 0.18/0.42  # Current number of unprocessed clauses: 80
% 0.18/0.42  # ...number of literals in the above   : 231
% 0.18/0.42  # Current number of archived formulas  : 0
% 0.18/0.42  # Current number of archived clauses   : 314
% 0.18/0.42  # Clause-clause subsumption calls (NU) : 5496
% 0.18/0.42  # Rec. Clause-clause subsumption calls : 2685
% 0.18/0.42  # Non-unit clause-clause subsumptions  : 15
% 0.18/0.42  # Unit Clause-clause subsumption calls : 183
% 0.18/0.42  # Rewrite failures with RHS unbound    : 0
% 0.18/0.42  # BW rewrite match attempts            : 575
% 0.18/0.42  # BW rewrite match successes           : 68
% 0.18/0.42  # Condensation attempts                : 0
% 0.18/0.42  # Condensation successes               : 0
% 0.18/0.42  # Termbank termtop insertions          : 19639
% 0.18/0.42  
% 0.18/0.42  # -------------------------------------------------
% 0.18/0.42  # User time                : 0.074 s
% 0.18/0.42  # System time              : 0.008 s
% 0.18/0.42  # Total time               : 0.081 s
% 0.18/0.42  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
