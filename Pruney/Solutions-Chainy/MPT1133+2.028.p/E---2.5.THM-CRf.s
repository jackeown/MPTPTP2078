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
% DateTime   : Thu Dec  3 11:09:25 EST 2020

% Result     : Theorem 0.53s
% Output     : CNFRefutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  207 (333014 expanded)
%              Number of clauses        :  165 (136026 expanded)
%              Number of leaves         :   21 (78766 expanded)
%              Depth                    :   48
%              Number of atoms          :  743 (2382662 expanded)
%              Number of equality atoms :  106 (234549 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t64_pre_topc,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) )
                 => ( X3 = X4
                   => ( v5_pre_topc(X3,X1,X2)
                    <=> v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_pre_topc)).

fof(t132_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | v1_partfun1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t62_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) )
                 => ( X3 = X4
                   => ( v5_pre_topc(X3,X1,X2)
                    <=> v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_pre_topc)).

fof(t63_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) )
                 => ( X3 = X4
                   => ( v5_pre_topc(X3,X1,X2)
                    <=> v5_pre_topc(X4,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_pre_topc)).

fof(fc6_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(dt_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( v1_pre_topc(g1_pre_topc(X1,X2))
        & l1_pre_topc(g1_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(rc1_funct_2,axiom,(
    ! [X1,X2] :
    ? [X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_relat_1(X3)
      & v4_relat_1(X3,X1)
      & v5_relat_1(X3,X2)
      & v1_funct_1(X3)
      & v1_funct_2(X3,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( v2_pre_topc(X2)
              & l1_pre_topc(X2) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
               => ! [X4] :
                    ( ( v1_funct_1(X4)
                      & v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) )
                   => ( X3 = X4
                     => ( v5_pre_topc(X3,X1,X2)
                      <=> v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t64_pre_topc])).

fof(c_0_22,plain,(
    ! [X39,X40,X41] :
      ( ( X40 = k1_xboole_0
        | v1_partfun1(X41,X39)
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,X39,X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
        | ~ v1_funct_1(X41)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( X39 != k1_xboole_0
        | v1_partfun1(X41,X39)
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,X39,X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
        | ~ v1_funct_1(X41)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_funct_2])])])).

fof(c_0_23,negated_conjecture,
    ( v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & v2_pre_topc(esk5_0)
    & l1_pre_topc(esk5_0)
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0))))
    & v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))))
    & esk6_0 = esk7_0
    & ( ~ v5_pre_topc(esk6_0,esk4_0,esk5_0)
      | ~ v5_pre_topc(esk7_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) )
    & ( v5_pre_topc(esk6_0,esk4_0,esk5_0)
      | v5_pre_topc(esk7_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

cnf(c_0_24,plain,
    ( X1 = k1_xboole_0
    | v1_partfun1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_25,plain,(
    ! [X28,X29,X30] :
      ( ( v4_relat_1(X30,X28)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))) )
      & ( v5_relat_1(X30,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_26,plain,(
    ! [X25,X26,X27] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | v1_relat_1(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( esk6_0 = esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_2(esk7_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_30,plain,(
    ! [X16,X17] :
      ( ( k2_zfmisc_1(X16,X17) != k1_xboole_0
        | X16 = k1_xboole_0
        | X17 = k1_xboole_0 )
      & ( X16 != k1_xboole_0
        | k2_zfmisc_1(X16,X17) = k1_xboole_0 )
      & ( X17 != k1_xboole_0
        | k2_zfmisc_1(X16,X17) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_31,plain,(
    ! [X34,X35] :
      ( ( ~ v1_partfun1(X35,X34)
        | k1_relat_1(X35) = X34
        | ~ v1_relat_1(X35)
        | ~ v4_relat_1(X35,X34) )
      & ( k1_relat_1(X35) != X34
        | v1_partfun1(X35,X34)
        | ~ v1_relat_1(X35)
        | ~ v4_relat_1(X35,X34) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).

cnf(c_0_32,plain,
    ( X1 = k1_xboole_0
    | v1_partfun1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(cn,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))))) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))) ),
    inference(rw,[status(thm)],[c_0_29,c_0_28])).

fof(c_0_40,plain,(
    ! [X22,X23,X24] :
      ( ~ r2_hidden(X22,X23)
      | ~ m1_subset_1(X23,k1_zfmisc_1(X24))
      | ~ v1_xboole_0(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_41,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_42,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_43,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_44,plain,(
    ! [X31,X32,X33] :
      ( ~ v1_xboole_0(X31)
      | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X32,X31)))
      | v1_xboole_0(X33) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

cnf(c_0_45,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_46,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | v1_partfun1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35])])).

cnf(c_0_47,negated_conjecture,
    ( v4_relat_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_33])).

cnf(c_0_48,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) = k1_xboole_0
    | v1_partfun1(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_38]),c_0_39]),c_0_35])])).

cnf(c_0_50,negated_conjecture,
    ( v4_relat_1(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_38])).

cnf(c_0_51,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k1_xboole_0))
    | u1_struct_0(esk5_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_41])).

cnf(c_0_53,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_54,plain,(
    ! [X20,X21] :
      ( ( ~ m1_subset_1(X20,k1_zfmisc_1(X21))
        | r1_tarski(X20,X21) )
      & ( ~ r1_tarski(X20,X21)
        | m1_subset_1(X20,k1_zfmisc_1(X21)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_55,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_56,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_57,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_58,negated_conjecture,
    ( k1_relat_1(esk6_0) = u1_struct_0(esk4_0)
    | u1_struct_0(esk5_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_48])])).

cnf(c_0_59,negated_conjecture,
    ( k1_relat_1(esk6_0) = u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_49]),c_0_50]),c_0_48])])).

cnf(c_0_60,negated_conjecture,
    ( u1_struct_0(esk5_0) != k1_xboole_0
    | ~ r2_hidden(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])])).

cnf(c_0_61,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_62,plain,(
    ! [X46,X47,X48,X49] :
      ( ( ~ v5_pre_topc(X48,X46,X47)
        | v5_pre_topc(X49,g1_pre_topc(u1_struct_0(X46),u1_pre_topc(X46)),X47)
        | X48 != X49
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,u1_struct_0(g1_pre_topc(u1_struct_0(X46),u1_pre_topc(X46))),u1_struct_0(X47))
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X46),u1_pre_topc(X46))),u1_struct_0(X47))))
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,u1_struct_0(X46),u1_struct_0(X47))
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X47))))
        | ~ v2_pre_topc(X47)
        | ~ l1_pre_topc(X47)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46) )
      & ( ~ v5_pre_topc(X49,g1_pre_topc(u1_struct_0(X46),u1_pre_topc(X46)),X47)
        | v5_pre_topc(X48,X46,X47)
        | X48 != X49
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,u1_struct_0(g1_pre_topc(u1_struct_0(X46),u1_pre_topc(X46))),u1_struct_0(X47))
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X46),u1_pre_topc(X46))),u1_struct_0(X47))))
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,u1_struct_0(X46),u1_struct_0(X47))
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X47))))
        | ~ v2_pre_topc(X47)
        | ~ l1_pre_topc(X47)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_pre_topc])])])])).

cnf(c_0_63,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_65,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_38])).

cnf(c_0_66,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) = u1_struct_0(esk4_0)
    | u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) = k1_xboole_0
    | u1_struct_0(esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | u1_struct_0(esk5_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_68,plain,
    ( v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)
    | ~ v5_pre_topc(X1,X2,X3)
    | X1 != X4
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_69,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) = u1_struct_0(esk4_0)
    | v1_xboole_0(esk6_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_53])]),c_0_67])).

cnf(c_0_71,negated_conjecture,
    ( ~ v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | ~ v5_pre_topc(esk7_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_72,plain,
    ( v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) ),
    inference(er,[status(thm)],[c_0_68])).

cnf(c_0_73,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_74,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_75,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) = u1_struct_0(esk4_0)
    | m1_subset_1(esk6_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

fof(c_0_76,plain,(
    ! [X50,X51,X52,X53] :
      ( ( ~ v5_pre_topc(X52,X50,X51)
        | v5_pre_topc(X53,X50,g1_pre_topc(u1_struct_0(X51),u1_pre_topc(X51)))
        | X52 != X53
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,u1_struct_0(X50),u1_struct_0(g1_pre_topc(u1_struct_0(X51),u1_pre_topc(X51))))
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(g1_pre_topc(u1_struct_0(X51),u1_pre_topc(X51))))))
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,u1_struct_0(X50),u1_struct_0(X51))
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X51))))
        | ~ v2_pre_topc(X51)
        | ~ l1_pre_topc(X51)
        | ~ v2_pre_topc(X50)
        | ~ l1_pre_topc(X50) )
      & ( ~ v5_pre_topc(X53,X50,g1_pre_topc(u1_struct_0(X51),u1_pre_topc(X51)))
        | v5_pre_topc(X52,X50,X51)
        | X52 != X53
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,u1_struct_0(X50),u1_struct_0(g1_pre_topc(u1_struct_0(X51),u1_pre_topc(X51))))
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(g1_pre_topc(u1_struct_0(X51),u1_pre_topc(X51))))))
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,u1_struct_0(X50),u1_struct_0(X51))
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X51))))
        | ~ v2_pre_topc(X51)
        | ~ l1_pre_topc(X51)
        | ~ v2_pre_topc(X50)
        | ~ l1_pre_topc(X50) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_pre_topc])])])])).

cnf(c_0_77,negated_conjecture,
    ( ~ v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(esk6_0,esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_71,c_0_28])).

cnf(c_0_78,negated_conjecture,
    ( v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_38]),c_0_73]),c_0_74]),c_0_39]),c_0_35])])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))))
    | m1_subset_1(esk6_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))
    | m1_subset_1(esk6_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_75])).

cnf(c_0_81,plain,
    ( v5_pre_topc(X4,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
    | ~ v5_pre_topc(X1,X2,X3)
    | X1 != X4
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_82,negated_conjecture,
    ( ~ v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))))) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))))) ),
    inference(ef,[status(thm)],[c_0_79])).

cnf(c_0_84,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))
    | v1_xboole_0(esk6_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_80])).

cnf(c_0_85,plain,
    ( v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) ),
    inference(er,[status(thm)],[c_0_81])).

cnf(c_0_86,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_87,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_88,plain,
    ( v5_pre_topc(X4,X2,X3)
    | ~ v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)
    | X4 != X1
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_89,negated_conjecture,
    ( ~ v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_83])])).

cnf(c_0_90,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))
    | v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_53])).

cnf(c_0_91,negated_conjecture,
    ( v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | ~ v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_83]),c_0_86]),c_0_73]),c_0_87]),c_0_74]),c_0_34]),c_0_35]),c_0_33])])).

cnf(c_0_92,plain,
    ( v5_pre_topc(X1,X2,X3)
    | ~ v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) ),
    inference(er,[status(thm)],[c_0_88])).

cnf(c_0_93,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | ~ v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_94,negated_conjecture,
    ( v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | v1_xboole_0(esk6_0)
    | ~ v5_pre_topc(esk6_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_91,c_0_90])).

fof(c_0_95,plain,(
    ! [X45] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X45),u1_pre_topc(X45)))
        | ~ v2_pre_topc(X45)
        | ~ l1_pre_topc(X45) )
      & ( v2_pre_topc(g1_pre_topc(u1_struct_0(X45),u1_pre_topc(X45)))
        | ~ v2_pre_topc(X45)
        | ~ l1_pre_topc(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_pre_topc])])])).

cnf(c_0_96,plain,
    ( v5_pre_topc(X4,X2,X3)
    | ~ v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
    | X4 != X1
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_97,negated_conjecture,
    ( v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_38]),c_0_73]),c_0_74]),c_0_39]),c_0_35])])).

cnf(c_0_98,negated_conjecture,
    ( v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | v5_pre_topc(esk7_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_99,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | ~ v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_100,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

fof(c_0_101,plain,(
    ! [X42,X43] :
      ( ( v1_pre_topc(g1_pre_topc(X42,X43))
        | ~ m1_subset_1(X43,k1_zfmisc_1(k1_zfmisc_1(X42))) )
      & ( l1_pre_topc(g1_pre_topc(X42,X43))
        | ~ m1_subset_1(X43,k1_zfmisc_1(k1_zfmisc_1(X42))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).

cnf(c_0_102,plain,
    ( v5_pre_topc(X1,X2,X3)
    | ~ v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) ),
    inference(er,[status(thm)],[c_0_96])).

cnf(c_0_103,negated_conjecture,
    ( v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_97,c_0_83])])).

cnf(c_0_104,negated_conjecture,
    ( v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | v5_pre_topc(esk6_0,esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_98,c_0_28])).

cnf(c_0_105,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | ~ v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_86]),c_0_87])])).

cnf(c_0_106,plain,
    ( l1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

fof(c_0_107,plain,(
    ! [X44] :
      ( ~ l1_pre_topc(X44)
      | m1_subset_1(u1_pre_topc(X44),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X44)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_108,negated_conjecture,
    ( v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | ~ v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_83]),c_0_86]),c_0_73]),c_0_87]),c_0_74]),c_0_34]),c_0_35]),c_0_33])])).

cnf(c_0_109,negated_conjecture,
    ( v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_91])).

cnf(c_0_110,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | ~ v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | ~ m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_111,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_107])).

cnf(c_0_112,negated_conjecture,
    ( v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | v1_xboole_0(esk6_0)
    | ~ v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_108,c_0_90])).

cnf(c_0_113,negated_conjecture,
    ( v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | v1_xboole_0(esk6_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_109,c_0_90])).

cnf(c_0_114,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | ~ v5_pre_topc(esk6_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_87])])).

fof(c_0_115,plain,(
    ! [X15] :
      ( ~ v1_xboole_0(X15)
      | X15 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_116,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_114])).

cnf(c_0_117,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_115])).

cnf(c_0_118,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_100]),c_0_86]),c_0_87])])).

cnf(c_0_119,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_xboole_0(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_41]),c_0_117])).

fof(c_0_120,plain,(
    ! [X36,X37] :
      ( m1_subset_1(esk3_2(X36,X37),k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
      & v1_relat_1(esk3_2(X36,X37))
      & v4_relat_1(esk3_2(X36,X37),X36)
      & v5_relat_1(esk3_2(X36,X37),X37)
      & v1_funct_1(esk3_2(X36,X37))
      & v1_funct_2(esk3_2(X36,X37),X36,X37) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_funct_2])])).

cnf(c_0_121,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | ~ m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_118,c_0_106])).

cnf(c_0_122,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_119,c_0_53])).

cnf(c_0_123,plain,
    ( m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_120])).

cnf(c_0_124,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_125,negated_conjecture,
    ( v1_xboole_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_111]),c_0_87])])).

cnf(c_0_126,plain,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_117,c_0_122])).

cnf(c_0_127,plain,
    ( m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(k1_xboole_0))
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_123,c_0_124])).

cnf(c_0_128,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_117,c_0_125])).

cnf(c_0_129,plain,
    ( v1_funct_2(esk3_2(X1,X2),X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_120])).

cnf(c_0_130,plain,
    ( esk3_2(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_126,c_0_127])).

cnf(c_0_131,negated_conjecture,
    ( ~ v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_128]),c_0_128]),c_0_128])).

cnf(c_0_132,plain,
    ( v1_funct_2(k1_xboole_0,X1,X2)
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_129,c_0_130])).

cnf(c_0_133,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_128]),c_0_128]),c_0_128])).

cnf(c_0_134,negated_conjecture,
    ( u1_struct_0(esk4_0) != k1_xboole_0
    | ~ v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_131,c_0_132])).

cnf(c_0_135,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | u1_struct_0(esk4_0) != k1_xboole_0
    | ~ v5_pre_topc(k1_xboole_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_133,c_0_132])).

cnf(c_0_136,negated_conjecture,
    ( u1_struct_0(esk4_0) != k1_xboole_0
    | ~ v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_134,c_0_135])).

fof(c_0_137,plain,(
    ! [X19] : m1_subset_1(k2_subset_1(X19),k1_zfmisc_1(X19)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_138,plain,(
    ! [X18] : k2_subset_1(X18) = X18 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_139,plain,
    ( v1_partfun1(X2,X1)
    | X1 != k1_xboole_0
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_140,plain,
    ( v1_funct_1(esk3_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_120])).

cnf(c_0_141,negated_conjecture,
    ( u1_struct_0(esk4_0) != k1_xboole_0
    | ~ v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_100]),c_0_86]),c_0_87])])).

cnf(c_0_142,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_137])).

cnf(c_0_143,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_138])).

cnf(c_0_144,plain,
    ( v1_partfun1(X2,X1)
    | X1 != k1_xboole_0
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(cn,[status(thm)],[c_0_139])).

cnf(c_0_145,plain,
    ( v5_pre_topc(esk3_2(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))),X1,X2)
    | ~ v5_pre_topc(esk3_2(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))),X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(esk3_2(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))),u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(esk3_2(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_123]),c_0_129]),c_0_140])])).

cnf(c_0_146,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_53])).

cnf(c_0_147,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109,c_0_128]),c_0_128])).

cnf(c_0_148,negated_conjecture,
    ( u1_struct_0(esk4_0) != k1_xboole_0
    | ~ v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)
    | ~ m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_141,c_0_106])).

cnf(c_0_149,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_142,c_0_143])).

cnf(c_0_150,plain,
    ( v1_partfun1(esk3_2(X1,X2),X1)
    | X1 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144,c_0_123]),c_0_129]),c_0_140])])).

cnf(c_0_151,plain,
    ( v5_pre_topc(k1_xboole_0,X1,X2)
    | u1_struct_0(X1) != k1_xboole_0
    | ~ v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_130]),c_0_146])]),c_0_132])).

cnf(c_0_152,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | u1_struct_0(esk4_0) != k1_xboole_0
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_147,c_0_132])).

cnf(c_0_153,negated_conjecture,
    ( u1_struct_0(esk4_0) != k1_xboole_0
    | ~ v5_pre_topc(k1_xboole_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_111]),c_0_87])])).

cnf(c_0_154,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_149])).

cnf(c_0_155,plain,
    ( v1_partfun1(k1_xboole_0,X1)
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_150,c_0_130])).

cnf(c_0_156,plain,
    ( v4_relat_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_146])).

cnf(c_0_157,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_146])).

cnf(c_0_158,negated_conjecture,
    ( u1_struct_0(esk4_0) != k1_xboole_0
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151,c_0_152]),c_0_86]),c_0_73]),c_0_87]),c_0_74])]),c_0_153])).

cnf(c_0_159,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_117,c_0_154])).

cnf(c_0_160,plain,
    ( k1_relat_1(k1_xboole_0) = X1
    | X1 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_155]),c_0_156]),c_0_157])])).

cnf(c_0_161,negated_conjecture,
    ( u1_struct_0(esk4_0) != k1_xboole_0
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_158,c_0_100]),c_0_86]),c_0_87])])).

cnf(c_0_162,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_159,c_0_53])).

cnf(c_0_163,negated_conjecture,
    ( v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_38]),c_0_86]),c_0_87]),c_0_39]),c_0_35])])).

cnf(c_0_164,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_160])).

cnf(c_0_165,negated_conjecture,
    ( u1_struct_0(esk4_0) != k1_xboole_0
    | ~ m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_161,c_0_106])).

cnf(c_0_166,plain,
    ( m1_subset_1(esk3_2(X1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_123,c_0_162])).

cnf(c_0_167,plain,
    ( m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(k1_xboole_0))
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_123,c_0_41])).

cnf(c_0_168,negated_conjecture,
    ( ~ v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)
    | ~ v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_77,c_0_163])).

cnf(c_0_169,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | u1_struct_0(esk4_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_128]),c_0_164])).

cnf(c_0_170,negated_conjecture,
    ( u1_struct_0(esk4_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_165,c_0_111]),c_0_87])])).

cnf(c_0_171,plain,
    ( esk3_2(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_126,c_0_166])).

cnf(c_0_172,plain,
    ( esk3_2(X1,X2) = k1_xboole_0
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_126,c_0_167])).

cnf(c_0_173,negated_conjecture,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)
    | ~ v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_168,c_0_128]),c_0_128]),c_0_128]),c_0_128]),c_0_146])])).

cnf(c_0_174,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_169,c_0_170])).

cnf(c_0_175,plain,
    ( v1_funct_2(k1_xboole_0,X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_129,c_0_171])).

cnf(c_0_176,plain,
    ( v1_funct_1(k1_xboole_0)
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_140,c_0_172])).

cnf(c_0_177,negated_conjecture,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)
    | ~ v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_173,c_0_174]),c_0_175])])).

cnf(c_0_178,negated_conjecture,
    ( v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),esk5_0)
    | ~ v5_pre_topc(X1,X2,esk5_0)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),k1_xboole_0)
    | ~ v1_funct_2(X1,u1_struct_0(X2),k1_xboole_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_174]),c_0_86]),c_0_87]),c_0_162]),c_0_162])])).

cnf(c_0_179,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_176])).

cnf(c_0_180,negated_conjecture,
    ( ~ v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_177,c_0_178]),c_0_73]),c_0_74]),c_0_175]),c_0_175]),c_0_179]),c_0_146])])).

cnf(c_0_181,negated_conjecture,
    ( ~ v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_180,c_0_100]),c_0_73]),c_0_74])])).

cnf(c_0_182,negated_conjecture,
    ( ~ v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)
    | ~ m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_181,c_0_106])).

cnf(c_0_183,negated_conjecture,
    ( u1_struct_0(esk4_0) = k1_xboole_0
    | v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_169]),c_0_86]),c_0_87])])).

cnf(c_0_184,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)
    | ~ v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_108,c_0_128]),c_0_128]),c_0_128])).

cnf(c_0_185,negated_conjecture,
    ( ~ v5_pre_topc(k1_xboole_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_182,c_0_111]),c_0_74])])).

cnf(c_0_186,negated_conjecture,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0))) ),
    inference(sr,[status(thm)],[c_0_183,c_0_170])).

cnf(c_0_187,negated_conjecture,
    ( ~ v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0)))) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_184,c_0_174]),c_0_174]),c_0_185])).

cnf(c_0_188,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_128]),c_0_164])).

cnf(c_0_189,negated_conjecture,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_147,c_0_174]),c_0_174]),c_0_174]),c_0_174]),c_0_186])]),c_0_187])).

cnf(c_0_190,plain,
    ( v1_funct_2(k1_xboole_0,X1,X2)
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_129,c_0_172])).

cnf(c_0_191,negated_conjecture,
    ( u1_struct_0(esk4_0) = k1_xboole_0
    | m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_169]),c_0_87])])).

cnf(c_0_192,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0))) = k1_xboole_0
    | u1_struct_0(esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_188,c_0_169])).

cnf(c_0_193,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0))) != k1_xboole_0
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_189,c_0_190])).

cnf(c_0_194,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    inference(sr,[status(thm)],[c_0_191,c_0_170])).

cnf(c_0_195,negated_conjecture,
    ( v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)
    | ~ v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_38]),c_0_86]),c_0_87]),c_0_39]),c_0_35])])).

cnf(c_0_196,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0))) = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_192,c_0_170])).

cnf(c_0_197,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0))) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_193,c_0_106]),c_0_194])])).

cnf(c_0_198,negated_conjecture,
    ( v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)
    | v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_195,c_0_104])).

cnf(c_0_199,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_196,c_0_197])).

cnf(c_0_200,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)
    | v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_198,c_0_128]),c_0_128]),c_0_128]),c_0_128]),c_0_146])])).

cnf(c_0_201,negated_conjecture,
    ( v5_pre_topc(X1,esk4_0,X2)
    | ~ v5_pre_topc(X1,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(esk4_0),u1_struct_0(X2))
    | ~ v1_funct_2(X1,k1_xboole_0,u1_struct_0(X2))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X2))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X2)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_199]),c_0_73]),c_0_74])])).

cnf(c_0_202,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_200,c_0_174]),c_0_175])]),c_0_185])).

cnf(c_0_203,negated_conjecture,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_201,c_0_202]),c_0_86]),c_0_87]),c_0_174]),c_0_175]),c_0_174]),c_0_175]),c_0_179]),c_0_146]),c_0_146])]),c_0_185])).

cnf(c_0_204,negated_conjecture,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_203,c_0_100]),c_0_73]),c_0_74])])).

cnf(c_0_205,negated_conjecture,
    ( ~ m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_204,c_0_106])).

cnf(c_0_206,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_205,c_0_111]),c_0_74])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:34:45 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.53/0.69  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_S0Y
% 0.53/0.69  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.53/0.69  #
% 0.53/0.69  # Preprocessing time       : 0.044 s
% 0.53/0.69  
% 0.53/0.69  # Proof found!
% 0.53/0.69  # SZS status Theorem
% 0.53/0.69  # SZS output start CNFRefutation
% 0.53/0.69  fof(t64_pre_topc, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_pre_topc)).
% 0.53/0.69  fof(t132_funct_2, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0&X1!=k1_xboole_0)|v1_partfun1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_funct_2)).
% 0.53/0.69  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.53/0.69  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.53/0.69  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.53/0.69  fof(d4_partfun1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>(v1_partfun1(X2,X1)<=>k1_relat_1(X2)=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 0.53/0.69  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.53/0.69  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.53/0.69  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.53/0.69  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 0.53/0.69  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.53/0.69  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.53/0.69  fof(t62_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_pre_topc)).
% 0.53/0.69  fof(t63_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_pre_topc)).
% 0.53/0.69  fof(fc6_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))&v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_pre_topc)).
% 0.53/0.69  fof(dt_g1_pre_topc, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(v1_pre_topc(g1_pre_topc(X1,X2))&l1_pre_topc(g1_pre_topc(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 0.53/0.69  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.53/0.69  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.53/0.69  fof(rc1_funct_2, axiom, ![X1, X2]:?[X3]:(((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&v1_relat_1(X3))&v4_relat_1(X3,X1))&v5_relat_1(X3,X2))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_funct_2)).
% 0.53/0.69  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.53/0.69  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.53/0.69  fof(c_0_21, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))))), inference(assume_negation,[status(cth)],[t64_pre_topc])).
% 0.53/0.69  fof(c_0_22, plain, ![X39, X40, X41]:((X40=k1_xboole_0|v1_partfun1(X41,X39)|(~v1_funct_1(X41)|~v1_funct_2(X41,X39,X40)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))|(~v1_funct_1(X41)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))))&(X39!=k1_xboole_0|v1_partfun1(X41,X39)|(~v1_funct_1(X41)|~v1_funct_2(X41,X39,X40)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))|(~v1_funct_1(X41)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_funct_2])])])).
% 0.53/0.69  fof(c_0_23, negated_conjecture, ((v2_pre_topc(esk4_0)&l1_pre_topc(esk4_0))&((v2_pre_topc(esk5_0)&l1_pre_topc(esk5_0))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))))&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))))))&(esk6_0=esk7_0&((~v5_pre_topc(esk6_0,esk4_0,esk5_0)|~v5_pre_topc(esk7_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))&(v5_pre_topc(esk6_0,esk4_0,esk5_0)|v5_pre_topc(esk7_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.53/0.69  cnf(c_0_24, plain, (X1=k1_xboole_0|v1_partfun1(X2,X3)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.53/0.69  fof(c_0_25, plain, ![X28, X29, X30]:((v4_relat_1(X30,X28)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))))&(v5_relat_1(X30,X29)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.53/0.69  fof(c_0_26, plain, ![X25, X26, X27]:(~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))|v1_relat_1(X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.53/0.69  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.53/0.69  cnf(c_0_28, negated_conjecture, (esk6_0=esk7_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.53/0.69  cnf(c_0_29, negated_conjecture, (v1_funct_2(esk7_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.53/0.69  fof(c_0_30, plain, ![X16, X17]:((k2_zfmisc_1(X16,X17)!=k1_xboole_0|(X16=k1_xboole_0|X17=k1_xboole_0))&((X16!=k1_xboole_0|k2_zfmisc_1(X16,X17)=k1_xboole_0)&(X17!=k1_xboole_0|k2_zfmisc_1(X16,X17)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.53/0.69  fof(c_0_31, plain, ![X34, X35]:((~v1_partfun1(X35,X34)|k1_relat_1(X35)=X34|(~v1_relat_1(X35)|~v4_relat_1(X35,X34)))&(k1_relat_1(X35)!=X34|v1_partfun1(X35,X34)|(~v1_relat_1(X35)|~v4_relat_1(X35,X34)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).
% 0.53/0.69  cnf(c_0_32, plain, (X1=k1_xboole_0|v1_partfun1(X2,X3)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(cn,[status(thm)],[c_0_24])).
% 0.53/0.69  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0))))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.53/0.69  cnf(c_0_34, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.53/0.69  cnf(c_0_35, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.53/0.69  cnf(c_0_36, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.53/0.69  cnf(c_0_37, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.53/0.69  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))))), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.53/0.69  cnf(c_0_39, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))), inference(rw,[status(thm)],[c_0_29, c_0_28])).
% 0.53/0.69  fof(c_0_40, plain, ![X22, X23, X24]:(~r2_hidden(X22,X23)|~m1_subset_1(X23,k1_zfmisc_1(X24))|~v1_xboole_0(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.53/0.69  cnf(c_0_41, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.53/0.69  fof(c_0_42, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.53/0.69  fof(c_0_43, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.53/0.69  fof(c_0_44, plain, ![X31, X32, X33]:(~v1_xboole_0(X31)|(~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X32,X31)))|v1_xboole_0(X33))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 0.53/0.69  cnf(c_0_45, plain, (k1_relat_1(X1)=X2|~v1_partfun1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.53/0.69  cnf(c_0_46, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|v1_partfun1(esk6_0,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35])])).
% 0.53/0.69  cnf(c_0_47, negated_conjecture, (v4_relat_1(esk6_0,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_36, c_0_33])).
% 0.53/0.69  cnf(c_0_48, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.53/0.69  cnf(c_0_49, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))=k1_xboole_0|v1_partfun1(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_38]), c_0_39]), c_0_35])])).
% 0.53/0.69  cnf(c_0_50, negated_conjecture, (v4_relat_1(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))))), inference(spm,[status(thm)],[c_0_36, c_0_38])).
% 0.53/0.69  cnf(c_0_51, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.53/0.69  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k1_xboole_0))|u1_struct_0(esk5_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_41])).
% 0.53/0.69  cnf(c_0_53, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.53/0.69  fof(c_0_54, plain, ![X20, X21]:((~m1_subset_1(X20,k1_zfmisc_1(X21))|r1_tarski(X20,X21))&(~r1_tarski(X20,X21)|m1_subset_1(X20,k1_zfmisc_1(X21)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.53/0.69  cnf(c_0_55, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.53/0.69  cnf(c_0_56, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.53/0.69  cnf(c_0_57, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.53/0.69  cnf(c_0_58, negated_conjecture, (k1_relat_1(esk6_0)=u1_struct_0(esk4_0)|u1_struct_0(esk5_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47]), c_0_48])])).
% 0.53/0.69  cnf(c_0_59, negated_conjecture, (k1_relat_1(esk6_0)=u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_49]), c_0_50]), c_0_48])])).
% 0.53/0.69  cnf(c_0_60, negated_conjecture, (u1_struct_0(esk5_0)!=k1_xboole_0|~r2_hidden(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])])).
% 0.53/0.69  cnf(c_0_61, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.53/0.69  fof(c_0_62, plain, ![X46, X47, X48, X49]:((~v5_pre_topc(X48,X46,X47)|v5_pre_topc(X49,g1_pre_topc(u1_struct_0(X46),u1_pre_topc(X46)),X47)|X48!=X49|(~v1_funct_1(X49)|~v1_funct_2(X49,u1_struct_0(g1_pre_topc(u1_struct_0(X46),u1_pre_topc(X46))),u1_struct_0(X47))|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X46),u1_pre_topc(X46))),u1_struct_0(X47)))))|(~v1_funct_1(X48)|~v1_funct_2(X48,u1_struct_0(X46),u1_struct_0(X47))|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X47)))))|(~v2_pre_topc(X47)|~l1_pre_topc(X47))|(~v2_pre_topc(X46)|~l1_pre_topc(X46)))&(~v5_pre_topc(X49,g1_pre_topc(u1_struct_0(X46),u1_pre_topc(X46)),X47)|v5_pre_topc(X48,X46,X47)|X48!=X49|(~v1_funct_1(X49)|~v1_funct_2(X49,u1_struct_0(g1_pre_topc(u1_struct_0(X46),u1_pre_topc(X46))),u1_struct_0(X47))|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X46),u1_pre_topc(X46))),u1_struct_0(X47)))))|(~v1_funct_1(X48)|~v1_funct_2(X48,u1_struct_0(X46),u1_struct_0(X47))|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X47)))))|(~v2_pre_topc(X47)|~l1_pre_topc(X47))|(~v2_pre_topc(X46)|~l1_pre_topc(X46)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_pre_topc])])])])).
% 0.53/0.69  cnf(c_0_63, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.53/0.69  cnf(c_0_64, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.53/0.69  cnf(c_0_65, negated_conjecture, (v1_xboole_0(esk6_0)|~v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))), inference(spm,[status(thm)],[c_0_57, c_0_38])).
% 0.53/0.69  cnf(c_0_66, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))=u1_struct_0(esk4_0)|u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))=k1_xboole_0|u1_struct_0(esk5_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.53/0.69  cnf(c_0_67, negated_conjecture, (v1_xboole_0(esk6_0)|u1_struct_0(esk5_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.53/0.69  cnf(c_0_68, plain, (v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|~v5_pre_topc(X1,X2,X3)|X1!=X4|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.53/0.69  cnf(c_0_69, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.53/0.69  cnf(c_0_70, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))=u1_struct_0(esk4_0)|v1_xboole_0(esk6_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_53])]), c_0_67])).
% 0.53/0.69  cnf(c_0_71, negated_conjecture, (~v5_pre_topc(esk6_0,esk4_0,esk5_0)|~v5_pre_topc(esk7_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.53/0.69  cnf(c_0_72, plain, (v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|~v5_pre_topc(X1,X2,X3)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_68])).
% 0.53/0.69  cnf(c_0_73, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.53/0.69  cnf(c_0_74, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.53/0.69  cnf(c_0_75, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))=u1_struct_0(esk4_0)|m1_subset_1(esk6_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.53/0.69  fof(c_0_76, plain, ![X50, X51, X52, X53]:((~v5_pre_topc(X52,X50,X51)|v5_pre_topc(X53,X50,g1_pre_topc(u1_struct_0(X51),u1_pre_topc(X51)))|X52!=X53|(~v1_funct_1(X53)|~v1_funct_2(X53,u1_struct_0(X50),u1_struct_0(g1_pre_topc(u1_struct_0(X51),u1_pre_topc(X51))))|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(g1_pre_topc(u1_struct_0(X51),u1_pre_topc(X51)))))))|(~v1_funct_1(X52)|~v1_funct_2(X52,u1_struct_0(X50),u1_struct_0(X51))|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X51)))))|(~v2_pre_topc(X51)|~l1_pre_topc(X51))|(~v2_pre_topc(X50)|~l1_pre_topc(X50)))&(~v5_pre_topc(X53,X50,g1_pre_topc(u1_struct_0(X51),u1_pre_topc(X51)))|v5_pre_topc(X52,X50,X51)|X52!=X53|(~v1_funct_1(X53)|~v1_funct_2(X53,u1_struct_0(X50),u1_struct_0(g1_pre_topc(u1_struct_0(X51),u1_pre_topc(X51))))|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(g1_pre_topc(u1_struct_0(X51),u1_pre_topc(X51)))))))|(~v1_funct_1(X52)|~v1_funct_2(X52,u1_struct_0(X50),u1_struct_0(X51))|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X51)))))|(~v2_pre_topc(X51)|~l1_pre_topc(X51))|(~v2_pre_topc(X50)|~l1_pre_topc(X50)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_pre_topc])])])])).
% 0.53/0.69  cnf(c_0_77, negated_conjecture, (~v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(esk6_0,esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_71, c_0_28])).
% 0.53/0.69  cnf(c_0_78, negated_conjecture, (v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_38]), c_0_73]), c_0_74]), c_0_39]), c_0_35])])).
% 0.53/0.69  cnf(c_0_79, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))))|m1_subset_1(esk6_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_38, c_0_75])).
% 0.53/0.69  cnf(c_0_80, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))|m1_subset_1(esk6_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_39, c_0_75])).
% 0.53/0.69  cnf(c_0_81, plain, (v5_pre_topc(X4,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|~v5_pre_topc(X1,X2,X3)|X1!=X4|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.53/0.69  cnf(c_0_82, negated_conjecture, (~v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(esk6_0,esk4_0,esk5_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))))), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.53/0.69  cnf(c_0_83, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))))), inference(ef,[status(thm)],[c_0_79])).
% 0.53/0.69  cnf(c_0_84, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))|v1_xboole_0(esk6_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_57, c_0_80])).
% 0.53/0.69  cnf(c_0_85, plain, (v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|~v5_pre_topc(X1,X2,X3)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_81])).
% 0.53/0.69  cnf(c_0_86, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.53/0.69  cnf(c_0_87, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.53/0.69  cnf(c_0_88, plain, (v5_pre_topc(X4,X2,X3)|~v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|X4!=X1|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.53/0.69  cnf(c_0_89, negated_conjecture, (~v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(esk6_0,esk4_0,esk5_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_83])])).
% 0.53/0.69  cnf(c_0_90, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))|v1_xboole_0(esk6_0)), inference(spm,[status(thm)],[c_0_84, c_0_53])).
% 0.53/0.69  cnf(c_0_91, negated_conjecture, (v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(esk6_0,esk4_0,esk5_0)|~v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_83]), c_0_86]), c_0_73]), c_0_87]), c_0_74]), c_0_34]), c_0_35]), c_0_33])])).
% 0.53/0.69  cnf(c_0_92, plain, (v5_pre_topc(X1,X2,X3)|~v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_88])).
% 0.53/0.69  cnf(c_0_93, negated_conjecture, (v1_xboole_0(esk6_0)|~v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(esk6_0,esk4_0,esk5_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.53/0.69  cnf(c_0_94, negated_conjecture, (v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|v1_xboole_0(esk6_0)|~v5_pre_topc(esk6_0,esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_91, c_0_90])).
% 0.53/0.69  fof(c_0_95, plain, ![X45]:((v1_pre_topc(g1_pre_topc(u1_struct_0(X45),u1_pre_topc(X45)))|(~v2_pre_topc(X45)|~l1_pre_topc(X45)))&(v2_pre_topc(g1_pre_topc(u1_struct_0(X45),u1_pre_topc(X45)))|(~v2_pre_topc(X45)|~l1_pre_topc(X45)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_pre_topc])])])).
% 0.53/0.69  cnf(c_0_96, plain, (v5_pre_topc(X4,X2,X3)|~v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|X4!=X1|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.53/0.69  cnf(c_0_97, negated_conjecture, (v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_38]), c_0_73]), c_0_74]), c_0_39]), c_0_35])])).
% 0.53/0.69  cnf(c_0_98, negated_conjecture, (v5_pre_topc(esk6_0,esk4_0,esk5_0)|v5_pre_topc(esk7_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.53/0.69  cnf(c_0_99, negated_conjecture, (v1_xboole_0(esk6_0)|~v5_pre_topc(esk6_0,esk4_0,esk5_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(spm,[status(thm)],[c_0_93, c_0_94])).
% 0.53/0.69  cnf(c_0_100, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_95])).
% 0.53/0.69  fof(c_0_101, plain, ![X42, X43]:((v1_pre_topc(g1_pre_topc(X42,X43))|~m1_subset_1(X43,k1_zfmisc_1(k1_zfmisc_1(X42))))&(l1_pre_topc(g1_pre_topc(X42,X43))|~m1_subset_1(X43,k1_zfmisc_1(k1_zfmisc_1(X42))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).
% 0.53/0.69  cnf(c_0_102, plain, (v5_pre_topc(X1,X2,X3)|~v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_96])).
% 0.53/0.69  cnf(c_0_103, negated_conjecture, (v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_97, c_0_83])])).
% 0.53/0.69  cnf(c_0_104, negated_conjecture, (v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|v5_pre_topc(esk6_0,esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_98, c_0_28])).
% 0.53/0.69  cnf(c_0_105, negated_conjecture, (v1_xboole_0(esk6_0)|~v5_pre_topc(esk6_0,esk4_0,esk5_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_86]), c_0_87])])).
% 0.53/0.69  cnf(c_0_106, plain, (l1_pre_topc(g1_pre_topc(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_101])).
% 0.53/0.69  fof(c_0_107, plain, ![X44]:(~l1_pre_topc(X44)|m1_subset_1(u1_pre_topc(X44),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X44))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.53/0.69  cnf(c_0_108, negated_conjecture, (v5_pre_topc(esk6_0,esk4_0,esk5_0)|~v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_83]), c_0_86]), c_0_73]), c_0_87]), c_0_74]), c_0_34]), c_0_35]), c_0_33])])).
% 0.53/0.69  cnf(c_0_109, negated_conjecture, (v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_91])).
% 0.53/0.69  cnf(c_0_110, negated_conjecture, (v1_xboole_0(esk6_0)|~v5_pre_topc(esk6_0,esk4_0,esk5_0)|~m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))), inference(spm,[status(thm)],[c_0_105, c_0_106])).
% 0.53/0.69  cnf(c_0_111, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_107])).
% 0.53/0.69  cnf(c_0_112, negated_conjecture, (v5_pre_topc(esk6_0,esk4_0,esk5_0)|v1_xboole_0(esk6_0)|~v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(spm,[status(thm)],[c_0_108, c_0_90])).
% 0.53/0.69  cnf(c_0_113, negated_conjecture, (v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|v1_xboole_0(esk6_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(spm,[status(thm)],[c_0_109, c_0_90])).
% 0.53/0.69  cnf(c_0_114, negated_conjecture, (v1_xboole_0(esk6_0)|~v5_pre_topc(esk6_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_87])])).
% 0.53/0.69  fof(c_0_115, plain, ![X15]:(~v1_xboole_0(X15)|X15=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.53/0.69  cnf(c_0_116, negated_conjecture, (v1_xboole_0(esk6_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_113]), c_0_114])).
% 0.53/0.69  cnf(c_0_117, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_115])).
% 0.53/0.69  cnf(c_0_118, negated_conjecture, (v1_xboole_0(esk6_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_100]), c_0_86]), c_0_87])])).
% 0.53/0.69  cnf(c_0_119, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))|~v1_xboole_0(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_41]), c_0_117])).
% 0.53/0.69  fof(c_0_120, plain, ![X36, X37]:(((((m1_subset_1(esk3_2(X36,X37),k1_zfmisc_1(k2_zfmisc_1(X36,X37)))&v1_relat_1(esk3_2(X36,X37)))&v4_relat_1(esk3_2(X36,X37),X36))&v5_relat_1(esk3_2(X36,X37),X37))&v1_funct_1(esk3_2(X36,X37)))&v1_funct_2(esk3_2(X36,X37),X36,X37)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_funct_2])])).
% 0.53/0.69  cnf(c_0_121, negated_conjecture, (v1_xboole_0(esk6_0)|~m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))), inference(spm,[status(thm)],[c_0_118, c_0_106])).
% 0.53/0.69  cnf(c_0_122, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_119, c_0_53])).
% 0.53/0.69  cnf(c_0_123, plain, (m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_120])).
% 0.53/0.69  cnf(c_0_124, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.53/0.69  cnf(c_0_125, negated_conjecture, (v1_xboole_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_111]), c_0_87])])).
% 0.53/0.69  cnf(c_0_126, plain, (X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_117, c_0_122])).
% 0.53/0.69  cnf(c_0_127, plain, (m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(k1_xboole_0))|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_123, c_0_124])).
% 0.53/0.69  cnf(c_0_128, negated_conjecture, (esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_117, c_0_125])).
% 0.53/0.69  cnf(c_0_129, plain, (v1_funct_2(esk3_2(X1,X2),X1,X2)), inference(split_conjunct,[status(thm)],[c_0_120])).
% 0.53/0.69  cnf(c_0_130, plain, (esk3_2(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_126, c_0_127])).
% 0.53/0.69  cnf(c_0_131, negated_conjecture, (~v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v1_funct_2(k1_xboole_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_128]), c_0_128]), c_0_128])).
% 0.53/0.69  cnf(c_0_132, plain, (v1_funct_2(k1_xboole_0,X1,X2)|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_129, c_0_130])).
% 0.53/0.69  cnf(c_0_133, negated_conjecture, (v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)|~v1_funct_2(k1_xboole_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_128]), c_0_128]), c_0_128])).
% 0.53/0.69  cnf(c_0_134, negated_conjecture, (u1_struct_0(esk4_0)!=k1_xboole_0|~v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(spm,[status(thm)],[c_0_131, c_0_132])).
% 0.53/0.69  cnf(c_0_135, negated_conjecture, (v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|u1_struct_0(esk4_0)!=k1_xboole_0|~v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_133, c_0_132])).
% 0.53/0.69  cnf(c_0_136, negated_conjecture, (u1_struct_0(esk4_0)!=k1_xboole_0|~v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(spm,[status(thm)],[c_0_134, c_0_135])).
% 0.53/0.69  fof(c_0_137, plain, ![X19]:m1_subset_1(k2_subset_1(X19),k1_zfmisc_1(X19)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.53/0.69  fof(c_0_138, plain, ![X18]:k2_subset_1(X18)=X18, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.53/0.69  cnf(c_0_139, plain, (v1_partfun1(X2,X1)|X1!=k1_xboole_0|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.53/0.69  cnf(c_0_140, plain, (v1_funct_1(esk3_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_120])).
% 0.53/0.69  cnf(c_0_141, negated_conjecture, (u1_struct_0(esk4_0)!=k1_xboole_0|~v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136, c_0_100]), c_0_86]), c_0_87])])).
% 0.53/0.69  cnf(c_0_142, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_137])).
% 0.53/0.69  cnf(c_0_143, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_138])).
% 0.53/0.69  cnf(c_0_144, plain, (v1_partfun1(X2,X1)|X1!=k1_xboole_0|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(cn,[status(thm)],[c_0_139])).
% 0.53/0.69  cnf(c_0_145, plain, (v5_pre_topc(esk3_2(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))),X1,X2)|~v5_pre_topc(esk3_2(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))),X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v1_funct_2(esk3_2(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))),u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(esk3_2(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_123]), c_0_129]), c_0_140])])).
% 0.53/0.69  cnf(c_0_146, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_69, c_0_53])).
% 0.53/0.69  cnf(c_0_147, negated_conjecture, (v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v1_funct_2(k1_xboole_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109, c_0_128]), c_0_128])).
% 0.53/0.69  cnf(c_0_148, negated_conjecture, (u1_struct_0(esk4_0)!=k1_xboole_0|~v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)|~m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))), inference(spm,[status(thm)],[c_0_141, c_0_106])).
% 0.53/0.69  cnf(c_0_149, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_142, c_0_143])).
% 0.53/0.69  cnf(c_0_150, plain, (v1_partfun1(esk3_2(X1,X2),X1)|X1!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144, c_0_123]), c_0_129]), c_0_140])])).
% 0.53/0.69  cnf(c_0_151, plain, (v5_pre_topc(k1_xboole_0,X1,X2)|u1_struct_0(X1)!=k1_xboole_0|~v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145, c_0_130]), c_0_146])]), c_0_132])).
% 0.53/0.69  cnf(c_0_152, negated_conjecture, (v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|u1_struct_0(esk4_0)!=k1_xboole_0|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(spm,[status(thm)],[c_0_147, c_0_132])).
% 0.53/0.69  cnf(c_0_153, negated_conjecture, (u1_struct_0(esk4_0)!=k1_xboole_0|~v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148, c_0_111]), c_0_87])])).
% 0.53/0.69  cnf(c_0_154, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_57, c_0_149])).
% 0.53/0.69  cnf(c_0_155, plain, (v1_partfun1(k1_xboole_0,X1)|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_150, c_0_130])).
% 0.53/0.69  cnf(c_0_156, plain, (v4_relat_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_36, c_0_146])).
% 0.53/0.69  cnf(c_0_157, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_37, c_0_146])).
% 0.53/0.69  cnf(c_0_158, negated_conjecture, (u1_struct_0(esk4_0)!=k1_xboole_0|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151, c_0_152]), c_0_86]), c_0_73]), c_0_87]), c_0_74])]), c_0_153])).
% 0.53/0.69  cnf(c_0_159, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_117, c_0_154])).
% 0.53/0.69  cnf(c_0_160, plain, (k1_relat_1(k1_xboole_0)=X1|X1!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_155]), c_0_156]), c_0_157])])).
% 0.53/0.69  cnf(c_0_161, negated_conjecture, (u1_struct_0(esk4_0)!=k1_xboole_0|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_158, c_0_100]), c_0_86]), c_0_87])])).
% 0.53/0.69  cnf(c_0_162, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_159, c_0_53])).
% 0.53/0.69  cnf(c_0_163, negated_conjecture, (v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_38]), c_0_86]), c_0_87]), c_0_39]), c_0_35])])).
% 0.53/0.69  cnf(c_0_164, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_160])).
% 0.53/0.69  cnf(c_0_165, negated_conjecture, (u1_struct_0(esk4_0)!=k1_xboole_0|~m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))), inference(spm,[status(thm)],[c_0_161, c_0_106])).
% 0.53/0.69  cnf(c_0_166, plain, (m1_subset_1(esk3_2(X1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_123, c_0_162])).
% 0.53/0.69  cnf(c_0_167, plain, (m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(k1_xboole_0))|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_123, c_0_41])).
% 0.53/0.69  cnf(c_0_168, negated_conjecture, (~v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)|~v5_pre_topc(esk6_0,esk4_0,esk5_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))))), inference(spm,[status(thm)],[c_0_77, c_0_163])).
% 0.53/0.69  cnf(c_0_169, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|u1_struct_0(esk4_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_128]), c_0_164])).
% 0.53/0.69  cnf(c_0_170, negated_conjecture, (u1_struct_0(esk4_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_165, c_0_111]), c_0_87])])).
% 0.53/0.69  cnf(c_0_171, plain, (esk3_2(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_126, c_0_166])).
% 0.53/0.69  cnf(c_0_172, plain, (esk3_2(X1,X2)=k1_xboole_0|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_126, c_0_167])).
% 0.53/0.69  cnf(c_0_173, negated_conjecture, (~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)|~v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_168, c_0_128]), c_0_128]), c_0_128]), c_0_128]), c_0_146])])).
% 0.53/0.69  cnf(c_0_174, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0), inference(sr,[status(thm)],[c_0_169, c_0_170])).
% 0.53/0.69  cnf(c_0_175, plain, (v1_funct_2(k1_xboole_0,X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_129, c_0_171])).
% 0.53/0.69  cnf(c_0_176, plain, (v1_funct_1(k1_xboole_0)|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_140, c_0_172])).
% 0.53/0.69  cnf(c_0_177, negated_conjecture, (~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)|~v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_173, c_0_174]), c_0_175])])).
% 0.53/0.69  cnf(c_0_178, negated_conjecture, (v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),esk5_0)|~v5_pre_topc(X1,X2,esk5_0)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),k1_xboole_0)|~v1_funct_2(X1,u1_struct_0(X2),k1_xboole_0)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_174]), c_0_86]), c_0_87]), c_0_162]), c_0_162])])).
% 0.53/0.69  cnf(c_0_179, plain, (v1_funct_1(k1_xboole_0)), inference(er,[status(thm)],[c_0_176])).
% 0.53/0.69  cnf(c_0_180, negated_conjecture, (~v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_177, c_0_178]), c_0_73]), c_0_74]), c_0_175]), c_0_175]), c_0_179]), c_0_146])])).
% 0.53/0.69  cnf(c_0_181, negated_conjecture, (~v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_180, c_0_100]), c_0_73]), c_0_74])])).
% 0.53/0.69  cnf(c_0_182, negated_conjecture, (~v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)|~m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(spm,[status(thm)],[c_0_181, c_0_106])).
% 0.53/0.69  cnf(c_0_183, negated_conjecture, (u1_struct_0(esk4_0)=k1_xboole_0|v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_169]), c_0_86]), c_0_87])])).
% 0.53/0.69  cnf(c_0_184, negated_conjecture, (v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)|~v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v1_funct_2(k1_xboole_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_108, c_0_128]), c_0_128]), c_0_128])).
% 0.53/0.69  cnf(c_0_185, negated_conjecture, (~v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_182, c_0_111]), c_0_74])])).
% 0.53/0.69  cnf(c_0_186, negated_conjecture, (v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0)))), inference(sr,[status(thm)],[c_0_183, c_0_170])).
% 0.53/0.69  cnf(c_0_187, negated_conjecture, (~v5_pre_topc(k1_xboole_0,esk4_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0)))|~v1_funct_2(k1_xboole_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0))))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_184, c_0_174]), c_0_174]), c_0_185])).
% 0.53/0.69  cnf(c_0_188, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))=k1_xboole_0|u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_128]), c_0_164])).
% 0.53/0.69  cnf(c_0_189, negated_conjecture, (~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0)))|~v1_funct_2(k1_xboole_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0))))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_147, c_0_174]), c_0_174]), c_0_174]), c_0_174]), c_0_186])]), c_0_187])).
% 0.53/0.69  cnf(c_0_190, plain, (v1_funct_2(k1_xboole_0,X1,X2)|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_129, c_0_172])).
% 0.53/0.69  cnf(c_0_191, negated_conjecture, (u1_struct_0(esk4_0)=k1_xboole_0|m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_169]), c_0_87])])).
% 0.53/0.69  cnf(c_0_192, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))=k1_xboole_0|u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0)))=k1_xboole_0|u1_struct_0(esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_188, c_0_169])).
% 0.53/0.69  cnf(c_0_193, negated_conjecture, (u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0)))!=k1_xboole_0|~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0)))), inference(spm,[status(thm)],[c_0_189, c_0_190])).
% 0.53/0.69  cnf(c_0_194, negated_conjecture, (m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))), inference(sr,[status(thm)],[c_0_191, c_0_170])).
% 0.53/0.69  cnf(c_0_195, negated_conjecture, (v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)|~v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_38]), c_0_86]), c_0_87]), c_0_39]), c_0_35])])).
% 0.53/0.69  cnf(c_0_196, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))=k1_xboole_0|u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0)))=k1_xboole_0), inference(sr,[status(thm)],[c_0_192, c_0_170])).
% 0.53/0.69  cnf(c_0_197, negated_conjecture, (u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk5_0)))!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_193, c_0_106]), c_0_194])])).
% 0.53/0.69  cnf(c_0_198, negated_conjecture, (v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)|v5_pre_topc(esk6_0,esk4_0,esk5_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))))), inference(spm,[status(thm)],[c_0_195, c_0_104])).
% 0.53/0.69  cnf(c_0_199, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))=k1_xboole_0), inference(sr,[status(thm)],[c_0_196, c_0_197])).
% 0.53/0.69  cnf(c_0_200, negated_conjecture, (v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)|v5_pre_topc(k1_xboole_0,esk4_0,esk5_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_198, c_0_128]), c_0_128]), c_0_128]), c_0_128]), c_0_146])])).
% 0.53/0.69  cnf(c_0_201, negated_conjecture, (v5_pre_topc(X1,esk4_0,X2)|~v5_pre_topc(X1,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(esk4_0),u1_struct_0(X2))|~v1_funct_2(X1,k1_xboole_0,u1_struct_0(X2))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X2))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X2))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_199]), c_0_73]), c_0_74])])).
% 0.53/0.69  cnf(c_0_202, negated_conjecture, (v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_200, c_0_174]), c_0_175])]), c_0_185])).
% 0.53/0.69  cnf(c_0_203, negated_conjecture, (~v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_201, c_0_202]), c_0_86]), c_0_87]), c_0_174]), c_0_175]), c_0_174]), c_0_175]), c_0_179]), c_0_146]), c_0_146])]), c_0_185])).
% 0.53/0.69  cnf(c_0_204, negated_conjecture, (~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_203, c_0_100]), c_0_73]), c_0_74])])).
% 0.53/0.69  cnf(c_0_205, negated_conjecture, (~m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(spm,[status(thm)],[c_0_204, c_0_106])).
% 0.53/0.69  cnf(c_0_206, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_205, c_0_111]), c_0_74])]), ['proof']).
% 0.53/0.69  # SZS output end CNFRefutation
% 0.53/0.69  # Proof object total steps             : 207
% 0.53/0.69  # Proof object clause steps            : 165
% 0.53/0.69  # Proof object formula steps           : 42
% 0.53/0.69  # Proof object conjectures             : 106
% 0.53/0.69  # Proof object clause conjectures      : 103
% 0.53/0.69  # Proof object formula conjectures     : 3
% 0.53/0.69  # Proof object initial clauses used    : 39
% 0.53/0.69  # Proof object initial formulas used   : 21
% 0.53/0.69  # Proof object generating inferences   : 96
% 0.53/0.69  # Proof object simplifying inferences  : 201
% 0.53/0.69  # Training examples: 0 positive, 0 negative
% 0.53/0.69  # Parsed axioms                        : 21
% 0.53/0.69  # Removed by relevancy pruning/SinE    : 0
% 0.53/0.69  # Initial clauses                      : 51
% 0.53/0.69  # Removed in clause preprocessing      : 1
% 0.53/0.69  # Initial clauses in saturation        : 50
% 0.53/0.69  # Processed clauses                    : 1269
% 0.53/0.69  # ...of these trivial                  : 29
% 0.53/0.69  # ...subsumed                          : 549
% 0.53/0.69  # ...remaining for further processing  : 691
% 0.53/0.69  # Other redundant clauses eliminated   : 6
% 0.53/0.69  # Clauses deleted for lack of memory   : 0
% 0.53/0.69  # Backward-subsumed                    : 132
% 0.53/0.69  # Backward-rewritten                   : 261
% 0.53/0.69  # Generated clauses                    : 5456
% 0.53/0.69  # ...of the previous two non-trivial   : 4559
% 0.53/0.69  # Contextual simplify-reflections      : 102
% 0.53/0.69  # Paramodulations                      : 5430
% 0.53/0.69  # Factorizations                       : 2
% 0.53/0.69  # Equation resolutions                 : 15
% 0.53/0.69  # Propositional unsat checks           : 0
% 0.53/0.69  #    Propositional check models        : 0
% 0.53/0.69  #    Propositional check unsatisfiable : 0
% 0.53/0.69  #    Propositional clauses             : 0
% 0.53/0.69  #    Propositional clauses after purity: 0
% 0.53/0.69  #    Propositional unsat core size     : 0
% 0.53/0.69  #    Propositional preprocessing time  : 0.000
% 0.53/0.69  #    Propositional encoding time       : 0.000
% 0.53/0.69  #    Propositional solver time         : 0.000
% 0.53/0.69  #    Success case prop preproc time    : 0.000
% 0.53/0.69  #    Success case prop encoding time   : 0.000
% 0.53/0.69  #    Success case prop solver time     : 0.000
% 0.53/0.69  # Current number of processed clauses  : 285
% 0.53/0.69  #    Positive orientable unit clauses  : 36
% 0.53/0.69  #    Positive unorientable unit clauses: 0
% 0.53/0.69  #    Negative unit clauses             : 6
% 0.53/0.69  #    Non-unit-clauses                  : 243
% 0.53/0.69  # Current number of unprocessed clauses: 2470
% 0.53/0.69  # ...number of literals in the above   : 23805
% 0.53/0.69  # Current number of archived formulas  : 0
% 0.53/0.69  # Current number of archived clauses   : 403
% 0.53/0.69  # Clause-clause subsumption calls (NU) : 149709
% 0.53/0.69  # Rec. Clause-clause subsumption calls : 12848
% 0.53/0.69  # Non-unit clause-clause subsumptions  : 673
% 0.53/0.69  # Unit Clause-clause subsumption calls : 1693
% 0.53/0.69  # Rewrite failures with RHS unbound    : 0
% 0.53/0.69  # BW rewrite match attempts            : 30
% 0.53/0.69  # BW rewrite match successes           : 12
% 0.53/0.69  # Condensation attempts                : 0
% 0.53/0.69  # Condensation successes               : 0
% 0.53/0.69  # Termbank termtop insertions          : 296511
% 0.53/0.69  
% 0.53/0.69  # -------------------------------------------------
% 0.53/0.69  # User time                : 0.342 s
% 0.53/0.69  # System time              : 0.013 s
% 0.53/0.69  # Total time               : 0.355 s
% 0.53/0.69  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
