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
% DateTime   : Thu Dec  3 11:09:23 EST 2020

% Result     : Theorem 0.84s
% Output     : CNFRefutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :  176 (412067 expanded)
%              Number of clauses        :  134 (164681 expanded)
%              Number of leaves         :   21 (97176 expanded)
%              Depth                    :   38
%              Number of atoms          :  663 (3024363 expanded)
%              Number of equality atoms :  105 (338316 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_pre_topc)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

fof(cc5_funct_2,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X2) )
           => ( v1_funct_1(X3)
              & v1_partfun1(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

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

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(fc3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X2)
     => v1_xboole_0(k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(t29_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k3_mcart_1(X3,X4,X5) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_pre_topc)).

fof(fc6_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(dt_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( v1_pre_topc(g1_pre_topc(X1,X2))
        & l1_pre_topc(g1_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_pre_topc)).

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

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(fc10_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

fof(cc1_funct_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

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
    ( v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))))
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))))))
    & esk5_0 = esk6_0
    & ( ~ v5_pre_topc(esk5_0,esk3_0,esk4_0)
      | ~ v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) )
    & ( v5_pre_topc(esk5_0,esk3_0,esk4_0)
      | v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

fof(c_0_24,plain,(
    ! [X31,X32,X33] :
      ( ( v1_funct_1(X33)
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,X31,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
        | v1_xboole_0(X32) )
      & ( v1_partfun1(X33,X31)
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,X31,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
        | v1_xboole_0(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

fof(c_0_25,plain,(
    ! [X23,X24,X25] :
      ( ( v4_relat_1(X25,X23)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( v5_relat_1(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_26,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | v1_relat_1(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_27,plain,
    ( X1 = k1_xboole_0
    | v1_partfun1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( esk5_0 = esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_31,plain,(
    ! [X15,X16,X17] :
      ( ~ r2_hidden(X15,X16)
      | ~ m1_subset_1(X16,k1_zfmisc_1(X17))
      | ~ v1_xboole_0(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_32,plain,(
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

cnf(c_0_33,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_37,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,plain,
    ( X1 = k1_xboole_0
    | v1_partfun1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(cn,[status(thm)],[c_0_27])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))))) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_41,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))) ),
    inference(rw,[status(thm)],[c_0_30,c_0_29])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_43,plain,(
    ! [X7,X8] :
      ( ~ v1_xboole_0(X8)
      | v1_xboole_0(k2_zfmisc_1(X7,X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_zfmisc_1])])).

cnf(c_0_44,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,negated_conjecture,
    ( v1_partfun1(esk5_0,u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36])])).

cnf(c_0_46,negated_conjecture,
    ( v4_relat_1(esk5_0,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_34])).

cnf(c_0_47,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_34])).

cnf(c_0_48,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) = k1_xboole_0
    | v1_partfun1(esk5_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_36])])).

cnf(c_0_49,negated_conjecture,
    ( v4_relat_1(esk5_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( ~ r2_hidden(X1,esk5_0)
    | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_34])).

cnf(c_0_51,plain,
    ( v1_xboole_0(k2_zfmisc_1(X2,X1))
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( k1_relat_1(esk5_0) = u1_struct_0(esk3_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47])])).

cnf(c_0_53,negated_conjecture,
    ( k1_relat_1(esk5_0) = u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_48]),c_0_49]),c_0_47])])).

cnf(c_0_54,negated_conjecture,
    ( ~ r2_hidden(X1,esk5_0)
    | ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) = u1_struct_0(esk3_0)
    | u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

fof(c_0_56,plain,(
    ! [X26,X28,X29,X30] :
      ( ( r2_hidden(esk1_1(X26),X26)
        | X26 = k1_xboole_0 )
      & ( ~ r2_hidden(X28,X26)
        | esk1_1(X26) != k3_mcart_1(X28,X29,X30)
        | X26 = k1_xboole_0 )
      & ( ~ r2_hidden(X29,X26)
        | esk1_1(X26) != k3_mcart_1(X28,X29,X30)
        | X26 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).

fof(c_0_57,plain,(
    ! [X9,X10] :
      ( ( k2_zfmisc_1(X9,X10) != k1_xboole_0
        | X9 = k1_xboole_0
        | X10 = k1_xboole_0 )
      & ( X9 != k1_xboole_0
        | k2_zfmisc_1(X9,X10) = k1_xboole_0 )
      & ( X10 != k1_xboole_0
        | k2_zfmisc_1(X9,X10) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_58,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) = u1_struct_0(esk3_0)
    | u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) = k1_xboole_0
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_59,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_60,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( ~ r2_hidden(X1,esk5_0)
    | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_40])).

cnf(c_0_62,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) = u1_struct_0(esk3_0)
    | u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_63,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_60])).

cnf(c_0_64,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_65,plain,(
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

cnf(c_0_66,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) = u1_struct_0(esk3_0)
    | esk5_0 = k1_xboole_0
    | ~ r2_hidden(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63]),c_0_64])])).

cnf(c_0_67,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) = u1_struct_0(esk3_0)
    | esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_66,c_0_59])).

cnf(c_0_69,plain,
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
    inference(er,[status(thm)],[c_0_67])).

cnf(c_0_70,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_68])).

cnf(c_0_71,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_72,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_73,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_68])).

fof(c_0_74,plain,(
    ! [X45] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X45),u1_pre_topc(X45)))
        | ~ v2_pre_topc(X45)
        | ~ l1_pre_topc(X45) )
      & ( v2_pre_topc(g1_pre_topc(u1_struct_0(X45),u1_pre_topc(X45)))
        | ~ v2_pre_topc(X45)
        | ~ l1_pre_topc(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_pre_topc])])])).

fof(c_0_75,plain,(
    ! [X42,X43] :
      ( ( v1_pre_topc(g1_pre_topc(X42,X43))
        | ~ m1_subset_1(X43,k1_zfmisc_1(k1_zfmisc_1(X42))) )
      & ( l1_pre_topc(g1_pre_topc(X42,X43))
        | ~ m1_subset_1(X43,k1_zfmisc_1(k1_zfmisc_1(X42))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).

fof(c_0_76,plain,(
    ! [X44] :
      ( ~ l1_pre_topc(X44)
      | m1_subset_1(u1_pre_topc(X44),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X44)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_77,plain,(
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

cnf(c_0_78,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | v5_pre_topc(esk5_0,esk3_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ v5_pre_topc(esk5_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71]),c_0_72]),c_0_41]),c_0_36]),c_0_40])]),c_0_73])).

cnf(c_0_79,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_81,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_82,plain,
    ( l1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_83,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

fof(c_0_84,plain,(
    ! [X36,X37] :
      ( m1_subset_1(esk2_2(X36,X37),k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
      & v1_relat_1(esk2_2(X36,X37))
      & v4_relat_1(esk2_2(X36,X37),X36)
      & v5_relat_1(esk2_2(X36,X37),X37)
      & v1_funct_1(esk2_2(X36,X37))
      & v1_funct_2(esk2_2(X36,X37),X36,X37) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_funct_2])])).

cnf(c_0_85,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_86,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_87,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | v5_pre_topc(esk5_0,esk3_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ v5_pre_topc(esk5_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80]),c_0_81])])).

cnf(c_0_88,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_89,negated_conjecture,
    ( v5_pre_topc(esk5_0,esk3_0,esk4_0)
    | v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_90,plain,
    ( m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_91,plain,
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
    inference(er,[status(thm)],[c_0_85])).

cnf(c_0_92,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_93,plain,
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
    inference(er,[status(thm)],[c_0_86])).

cnf(c_0_94,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | v5_pre_topc(esk5_0,esk3_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ v5_pre_topc(esk5_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_81])])).

cnf(c_0_95,negated_conjecture,
    ( v5_pre_topc(esk5_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | v5_pre_topc(esk5_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_89,c_0_29])).

cnf(c_0_96,plain,
    ( ~ r2_hidden(X1,esk2_2(X2,X3))
    | ~ v1_xboole_0(k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_90])).

fof(c_0_97,plain,(
    ! [X6] :
      ( ~ v1_xboole_0(X6)
      | X6 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

fof(c_0_98,plain,(
    ! [X18] :
      ( ~ v1_xboole_0(X18)
      | v1_xboole_0(k1_relat_1(X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_relat_1])])).

cnf(c_0_99,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | v5_pre_topc(esk5_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ v5_pre_topc(esk5_0,esk3_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_70]),c_0_71]),c_0_72]),c_0_41]),c_0_36]),c_0_40])]),c_0_73])).

cnf(c_0_100,plain,
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
    inference(er,[status(thm)],[c_0_92])).

cnf(c_0_101,negated_conjecture,
    ( v5_pre_topc(esk5_0,esk3_0,esk4_0)
    | ~ v5_pre_topc(esk5_0,esk3_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_35]),c_0_80]),c_0_71]),c_0_81]),c_0_72]),c_0_36]),c_0_34])])).

cnf(c_0_102,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | v5_pre_topc(esk5_0,esk3_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | v5_pre_topc(esk5_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_103,negated_conjecture,
    ( ~ v5_pre_topc(esk5_0,esk3_0,esk4_0)
    | ~ v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_104,plain,
    ( ~ r2_hidden(X1,esk2_2(X2,X3))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_96,c_0_51])).

fof(c_0_105,plain,(
    ! [X19] :
      ( ~ v1_xboole_0(X19)
      | v1_funct_1(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_1])])).

cnf(c_0_106,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_107,plain,
    ( v1_xboole_0(k1_relat_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_108,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | v5_pre_topc(esk5_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ v5_pre_topc(esk5_0,esk3_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_79]),c_0_80]),c_0_81])])).

cnf(c_0_109,negated_conjecture,
    ( v5_pre_topc(esk5_0,esk3_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ v5_pre_topc(esk5_0,esk3_0,esk4_0)
    | ~ v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_35]),c_0_80]),c_0_71]),c_0_81]),c_0_72]),c_0_36]),c_0_34])])).

cnf(c_0_110,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | v5_pre_topc(esk5_0,esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_73]),c_0_70])).

cnf(c_0_111,negated_conjecture,
    ( ~ v5_pre_topc(esk5_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ v5_pre_topc(esk5_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_103,c_0_29])).

cnf(c_0_112,plain,
    ( v1_funct_2(esk2_2(X1,X2),X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_113,plain,
    ( esk2_2(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_104,c_0_59])).

cnf(c_0_114,plain,
    ( v1_funct_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_105])).

fof(c_0_115,plain,(
    ! [X11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X11)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_116,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_117,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | v5_pre_topc(esk5_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ v5_pre_topc(esk5_0,esk3_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_88]),c_0_81])])).

cnf(c_0_118,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | v5_pre_topc(esk5_0,esk3_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_73]),c_0_70])).

cnf(c_0_119,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | ~ v5_pre_topc(esk5_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_111,c_0_110])).

cnf(c_0_120,plain,
    ( v1_funct_2(k1_xboole_0,X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_121,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_114,c_0_64])).

cnf(c_0_122,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_115])).

cnf(c_0_123,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_116,c_0_52])).

cnf(c_0_124,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_118]),c_0_119])).

cnf(c_0_125,negated_conjecture,
    ( u1_struct_0(esk4_0) = k1_xboole_0
    | v1_partfun1(esk5_0,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_34]),c_0_35]),c_0_36])])).

cnf(c_0_126,plain,
    ( v5_pre_topc(k1_xboole_0,X1,X2)
    | ~ v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
    | ~ v1_xboole_0(u1_struct_0(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_120]),c_0_121]),c_0_122]),c_0_122])])).

cnf(c_0_127,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_123,c_0_124]),c_0_64])])).

cnf(c_0_128,negated_conjecture,
    ( k1_relat_1(esk5_0) = u1_struct_0(esk3_0)
    | u1_struct_0(esk4_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_125]),c_0_46]),c_0_47])])).

cnf(c_0_129,plain,
    ( ~ r2_hidden(X1,esk2_2(X2,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_63]),c_0_64])])).

cnf(c_0_130,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | v5_pre_topc(k1_xboole_0,X1,esk4_0)
    | ~ v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_127]),c_0_80]),c_0_81])])).

cnf(c_0_131,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | v5_pre_topc(k1_xboole_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_124]),c_0_124])).

cnf(c_0_132,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))) ),
    inference(rw,[status(thm)],[c_0_41,c_0_124])).

cnf(c_0_133,plain,
    ( v1_funct_1(esk2_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_134,negated_conjecture,
    ( u1_struct_0(esk4_0) = k1_xboole_0
    | u1_struct_0(esk3_0) = k1_xboole_0
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_128,c_0_116])).

cnf(c_0_135,plain,
    ( esk2_2(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_129,c_0_59])).

cnf(c_0_136,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0)
    | v5_pre_topc(k1_xboole_0,esk3_0,esk4_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_131]),c_0_132])])).

cnf(c_0_137,plain,
    ( v5_pre_topc(esk2_2(u1_struct_0(X1),u1_struct_0(X2)),X1,X2)
    | ~ v5_pre_topc(esk2_2(u1_struct_0(X1),u1_struct_0(X2)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(esk2_2(u1_struct_0(X1),u1_struct_0(X2)),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
    | ~ m1_subset_1(esk2_2(u1_struct_0(X1),u1_struct_0(X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_112]),c_0_133]),c_0_90])])).

cnf(c_0_138,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | u1_struct_0(esk4_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_134,c_0_124]),c_0_64])])).

cnf(c_0_139,plain,
    ( v1_funct_2(k1_xboole_0,X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_112,c_0_135])).

cnf(c_0_140,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0)
    | v5_pre_topc(k1_xboole_0,esk3_0,esk4_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_79]),c_0_71]),c_0_72])])).

cnf(c_0_141,plain,
    ( v5_pre_topc(esk2_2(u1_struct_0(X1),u1_struct_0(X2)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ v5_pre_topc(esk2_2(u1_struct_0(X1),u1_struct_0(X2)),X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(esk2_2(u1_struct_0(X1),u1_struct_0(X2)),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
    | ~ m1_subset_1(esk2_2(u1_struct_0(X1),u1_struct_0(X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_112]),c_0_133]),c_0_90])])).

cnf(c_0_142,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | v5_pre_topc(k1_xboole_0,X1,esk4_0)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),esk4_0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_138]),c_0_135]),c_0_135]),c_0_80]),c_0_81]),c_0_135]),c_0_139]),c_0_135]),c_0_63]),c_0_122])])).

cnf(c_0_143,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0)
    | v5_pre_topc(k1_xboole_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_88]),c_0_72])])).

cnf(c_0_144,plain,
    ( v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ v5_pre_topc(k1_xboole_0,X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
    | ~ v1_xboole_0(u1_struct_0(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_120]),c_0_121]),c_0_122]),c_0_122])])).

cnf(c_0_145,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),esk4_0)
    | ~ v5_pre_topc(k1_xboole_0,X1,esk4_0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_138]),c_0_135]),c_0_135]),c_0_80]),c_0_81]),c_0_135]),c_0_139]),c_0_135]),c_0_63]),c_0_122])])).

cnf(c_0_146,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | v5_pre_topc(k1_xboole_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_143]),c_0_71]),c_0_72])])).

cnf(c_0_147,negated_conjecture,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ v5_pre_topc(k1_xboole_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111,c_0_124]),c_0_124])).

cnf(c_0_148,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_149,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ v5_pre_topc(k1_xboole_0,X1,esk4_0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144,c_0_127]),c_0_80]),c_0_81])])).

cnf(c_0_150,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_146]),c_0_71]),c_0_72])])).

cnf(c_0_151,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_147,c_0_146])).

cnf(c_0_152,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_148])).

cnf(c_0_153,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149,c_0_150]),c_0_132])]),c_0_151])).

cnf(c_0_154,plain,
    ( ~ r2_hidden(X1,esk2_2(k1_xboole_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_152]),c_0_64])])).

cnf(c_0_155,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153,c_0_79]),c_0_71]),c_0_72])])).

cnf(c_0_156,plain,
    ( esk2_2(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_154,c_0_59])).

cnf(c_0_157,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_155,c_0_88]),c_0_72])])).

cnf(c_0_158,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,esk3_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ v5_pre_topc(k1_xboole_0,esk3_0,esk4_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(esk3_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109,c_0_124]),c_0_124]),c_0_124]),c_0_124]),c_0_122])])).

cnf(c_0_159,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_112,c_0_156])).

cnf(c_0_160,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,esk3_0,X1)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk3_0)),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk3_0))),u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_157]),c_0_156]),c_0_156]),c_0_71]),c_0_72]),c_0_156]),c_0_156]),c_0_122])])).

cnf(c_0_161,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk3_0)),g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | v5_pre_topc(k1_xboole_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_131,c_0_157])).

cnf(c_0_162,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk3_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))) ),
    inference(rw,[status(thm)],[c_0_132,c_0_157])).

cnf(c_0_163,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,esk3_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ v5_pre_topc(k1_xboole_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_158,c_0_157]),c_0_159])])).

cnf(c_0_164,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,esk3_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160,c_0_161]),c_0_162])]),c_0_163])).

cnf(c_0_165,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,esk3_0,esk4_0)
    | ~ v5_pre_topc(k1_xboole_0,esk3_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(esk3_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101,c_0_124]),c_0_124]),c_0_124]),c_0_124]),c_0_122])])).

cnf(c_0_166,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,esk3_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_164,c_0_79]),c_0_80]),c_0_81])])).

cnf(c_0_167,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,esk3_0,esk4_0)
    | ~ v5_pre_topc(k1_xboole_0,esk3_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_165,c_0_157]),c_0_159])])).

cnf(c_0_168,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,esk3_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_166,c_0_88]),c_0_81])])).

cnf(c_0_169,negated_conjecture,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk3_0)),g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ v5_pre_topc(k1_xboole_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_147,c_0_157])).

cnf(c_0_170,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_167,c_0_168])])).

cnf(c_0_171,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk3_0)),X1)
    | ~ v5_pre_topc(k1_xboole_0,esk3_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk3_0))),u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_157]),c_0_156]),c_0_156]),c_0_71]),c_0_72]),c_0_156]),c_0_156]),c_0_122])])).

cnf(c_0_172,negated_conjecture,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk3_0)),g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_169,c_0_170])])).

cnf(c_0_173,negated_conjecture,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171,c_0_168]),c_0_162])]),c_0_172])).

cnf(c_0_174,negated_conjecture,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_173,c_0_79]),c_0_80]),c_0_81])])).

cnf(c_0_175,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_174,c_0_88]),c_0_81])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % WCLimit    : 600
% 0.19/0.34  % DateTime   : Tue Dec  1 11:05:38 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  # Version: 2.5pre002
% 0.19/0.34  # No SInE strategy applied
% 0.19/0.34  # Trying AutoSched0 for 299 seconds
% 0.84/1.04  # AutoSched0-Mode selected heuristic G_E___110_C45_F1_PI_SE_CS_SP_PS_S4S
% 0.84/1.04  # and selection function SelectNewComplexAHPNS.
% 0.84/1.04  #
% 0.84/1.04  # Preprocessing time       : 0.031 s
% 0.84/1.04  # Presaturation interreduction done
% 0.84/1.04  
% 0.84/1.04  # Proof found!
% 0.84/1.04  # SZS status Theorem
% 0.84/1.04  # SZS output start CNFRefutation
% 0.84/1.04  fof(t64_pre_topc, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_pre_topc)).
% 0.84/1.04  fof(t132_funct_2, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0&X1!=k1_xboole_0)|v1_partfun1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_funct_2)).
% 0.84/1.04  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.84/1.04  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.84/1.04  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.84/1.04  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.84/1.04  fof(d4_partfun1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>(v1_partfun1(X2,X1)<=>k1_relat_1(X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 0.84/1.04  fof(fc3_zfmisc_1, axiom, ![X1, X2]:(v1_xboole_0(X2)=>v1_xboole_0(k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 0.84/1.04  fof(t29_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k3_mcart_1(X3,X4,X5))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 0.84/1.04  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.84/1.04  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.84/1.04  fof(t62_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_pre_topc)).
% 0.84/1.04  fof(fc6_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))&v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_pre_topc)).
% 0.84/1.04  fof(dt_g1_pre_topc, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(v1_pre_topc(g1_pre_topc(X1,X2))&l1_pre_topc(g1_pre_topc(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 0.84/1.04  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.84/1.04  fof(t63_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_pre_topc)).
% 0.84/1.04  fof(rc1_funct_2, axiom, ![X1, X2]:?[X3]:(((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&v1_relat_1(X3))&v4_relat_1(X3,X1))&v5_relat_1(X3,X2))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_funct_2)).
% 0.84/1.04  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.84/1.04  fof(fc10_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_xboole_0(k1_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 0.84/1.04  fof(cc1_funct_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_funct_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 0.84/1.04  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.84/1.04  fof(c_0_21, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))))), inference(assume_negation,[status(cth)],[t64_pre_topc])).
% 0.84/1.04  fof(c_0_22, plain, ![X39, X40, X41]:((X40=k1_xboole_0|v1_partfun1(X41,X39)|(~v1_funct_1(X41)|~v1_funct_2(X41,X39,X40)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))|(~v1_funct_1(X41)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))))&(X39!=k1_xboole_0|v1_partfun1(X41,X39)|(~v1_funct_1(X41)|~v1_funct_2(X41,X39,X40)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))|(~v1_funct_1(X41)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_funct_2])])])).
% 0.84/1.04  fof(c_0_23, negated_conjecture, ((v2_pre_topc(esk3_0)&l1_pre_topc(esk3_0))&((v2_pre_topc(esk4_0)&l1_pre_topc(esk4_0))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0)))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))))))&(esk5_0=esk6_0&((~v5_pre_topc(esk5_0,esk3_0,esk4_0)|~v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))))&(v5_pre_topc(esk5_0,esk3_0,esk4_0)|v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.84/1.04  fof(c_0_24, plain, ![X31, X32, X33]:((v1_funct_1(X33)|(~v1_funct_1(X33)|~v1_funct_2(X33,X31,X32))|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|v1_xboole_0(X32))&(v1_partfun1(X33,X31)|(~v1_funct_1(X33)|~v1_funct_2(X33,X31,X32))|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|v1_xboole_0(X32))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.84/1.04  fof(c_0_25, plain, ![X23, X24, X25]:((v4_relat_1(X25,X23)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))&(v5_relat_1(X25,X24)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.84/1.04  fof(c_0_26, plain, ![X20, X21, X22]:(~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|v1_relat_1(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.84/1.04  cnf(c_0_27, plain, (X1=k1_xboole_0|v1_partfun1(X2,X3)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.84/1.04  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))))))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.84/1.04  cnf(c_0_29, negated_conjecture, (esk5_0=esk6_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.84/1.04  cnf(c_0_30, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.84/1.04  fof(c_0_31, plain, ![X15, X16, X17]:(~r2_hidden(X15,X16)|~m1_subset_1(X16,k1_zfmisc_1(X17))|~v1_xboole_0(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.84/1.04  fof(c_0_32, plain, ![X34, X35]:((~v1_partfun1(X35,X34)|k1_relat_1(X35)=X34|(~v1_relat_1(X35)|~v4_relat_1(X35,X34)))&(k1_relat_1(X35)!=X34|v1_partfun1(X35,X34)|(~v1_relat_1(X35)|~v4_relat_1(X35,X34)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).
% 0.84/1.04  cnf(c_0_33, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.84/1.04  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.84/1.04  cnf(c_0_35, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.84/1.04  cnf(c_0_36, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.84/1.04  cnf(c_0_37, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.84/1.04  cnf(c_0_38, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.84/1.04  cnf(c_0_39, plain, (X1=k1_xboole_0|v1_partfun1(X2,X3)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(cn,[status(thm)],[c_0_27])).
% 0.84/1.04  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))))))), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 0.84/1.04  cnf(c_0_41, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))))), inference(rw,[status(thm)],[c_0_30, c_0_29])).
% 0.84/1.04  cnf(c_0_42, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.84/1.04  fof(c_0_43, plain, ![X7, X8]:(~v1_xboole_0(X8)|v1_xboole_0(k2_zfmisc_1(X7,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_zfmisc_1])])).
% 0.84/1.04  cnf(c_0_44, plain, (k1_relat_1(X1)=X2|~v1_partfun1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.84/1.04  cnf(c_0_45, negated_conjecture, (v1_partfun1(esk5_0,u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36])])).
% 0.84/1.04  cnf(c_0_46, negated_conjecture, (v4_relat_1(esk5_0,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_37, c_0_34])).
% 0.84/1.04  cnf(c_0_47, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_38, c_0_34])).
% 0.84/1.04  cnf(c_0_48, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))=k1_xboole_0|v1_partfun1(esk5_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_36])])).
% 0.84/1.04  cnf(c_0_49, negated_conjecture, (v4_relat_1(esk5_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))), inference(spm,[status(thm)],[c_0_37, c_0_40])).
% 0.84/1.04  cnf(c_0_50, negated_conjecture, (~r2_hidden(X1,esk5_0)|~v1_xboole_0(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_42, c_0_34])).
% 0.84/1.04  cnf(c_0_51, plain, (v1_xboole_0(k2_zfmisc_1(X2,X1))|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.84/1.04  cnf(c_0_52, negated_conjecture, (k1_relat_1(esk5_0)=u1_struct_0(esk3_0)|v1_xboole_0(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_47])])).
% 0.84/1.04  cnf(c_0_53, negated_conjecture, (k1_relat_1(esk5_0)=u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_48]), c_0_49]), c_0_47])])).
% 0.84/1.04  cnf(c_0_54, negated_conjecture, (~r2_hidden(X1,esk5_0)|~v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.84/1.04  cnf(c_0_55, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))=u1_struct_0(esk3_0)|u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))=k1_xboole_0|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.84/1.04  fof(c_0_56, plain, ![X26, X28, X29, X30]:((r2_hidden(esk1_1(X26),X26)|X26=k1_xboole_0)&((~r2_hidden(X28,X26)|esk1_1(X26)!=k3_mcart_1(X28,X29,X30)|X26=k1_xboole_0)&(~r2_hidden(X29,X26)|esk1_1(X26)!=k3_mcart_1(X28,X29,X30)|X26=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).
% 0.84/1.04  fof(c_0_57, plain, ![X9, X10]:((k2_zfmisc_1(X9,X10)!=k1_xboole_0|(X9=k1_xboole_0|X10=k1_xboole_0))&((X9!=k1_xboole_0|k2_zfmisc_1(X9,X10)=k1_xboole_0)&(X10!=k1_xboole_0|k2_zfmisc_1(X9,X10)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.84/1.04  cnf(c_0_58, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))=u1_struct_0(esk3_0)|u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))=k1_xboole_0|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.84/1.04  cnf(c_0_59, plain, (r2_hidden(esk1_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.84/1.04  cnf(c_0_60, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.84/1.04  cnf(c_0_61, negated_conjecture, (~r2_hidden(X1,esk5_0)|~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))))), inference(spm,[status(thm)],[c_0_42, c_0_40])).
% 0.84/1.04  cnf(c_0_62, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))=u1_struct_0(esk3_0)|u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))=k1_xboole_0|esk5_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.84/1.04  cnf(c_0_63, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_60])).
% 0.84/1.04  cnf(c_0_64, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.84/1.04  fof(c_0_65, plain, ![X46, X47, X48, X49]:((~v5_pre_topc(X48,X46,X47)|v5_pre_topc(X49,g1_pre_topc(u1_struct_0(X46),u1_pre_topc(X46)),X47)|X48!=X49|(~v1_funct_1(X49)|~v1_funct_2(X49,u1_struct_0(g1_pre_topc(u1_struct_0(X46),u1_pre_topc(X46))),u1_struct_0(X47))|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X46),u1_pre_topc(X46))),u1_struct_0(X47)))))|(~v1_funct_1(X48)|~v1_funct_2(X48,u1_struct_0(X46),u1_struct_0(X47))|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X47)))))|(~v2_pre_topc(X47)|~l1_pre_topc(X47))|(~v2_pre_topc(X46)|~l1_pre_topc(X46)))&(~v5_pre_topc(X49,g1_pre_topc(u1_struct_0(X46),u1_pre_topc(X46)),X47)|v5_pre_topc(X48,X46,X47)|X48!=X49|(~v1_funct_1(X49)|~v1_funct_2(X49,u1_struct_0(g1_pre_topc(u1_struct_0(X46),u1_pre_topc(X46))),u1_struct_0(X47))|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X46),u1_pre_topc(X46))),u1_struct_0(X47)))))|(~v1_funct_1(X48)|~v1_funct_2(X48,u1_struct_0(X46),u1_struct_0(X47))|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X47)))))|(~v2_pre_topc(X47)|~l1_pre_topc(X47))|(~v2_pre_topc(X46)|~l1_pre_topc(X46)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_pre_topc])])])])).
% 0.84/1.04  cnf(c_0_66, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))=u1_struct_0(esk3_0)|esk5_0=k1_xboole_0|~r2_hidden(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63]), c_0_64])])).
% 0.84/1.04  cnf(c_0_67, plain, (v5_pre_topc(X4,X2,X3)|~v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|X4!=X1|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.84/1.04  cnf(c_0_68, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))=u1_struct_0(esk3_0)|esk5_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_66, c_0_59])).
% 0.84/1.04  cnf(c_0_69, plain, (v5_pre_topc(X1,X2,X3)|~v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_67])).
% 0.84/1.04  cnf(c_0_70, negated_conjecture, (esk5_0=k1_xboole_0|v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))))), inference(spm,[status(thm)],[c_0_41, c_0_68])).
% 0.84/1.04  cnf(c_0_71, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.84/1.04  cnf(c_0_72, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.84/1.04  cnf(c_0_73, negated_conjecture, (esk5_0=k1_xboole_0|m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))))))), inference(spm,[status(thm)],[c_0_40, c_0_68])).
% 0.84/1.04  fof(c_0_74, plain, ![X45]:((v1_pre_topc(g1_pre_topc(u1_struct_0(X45),u1_pre_topc(X45)))|(~v2_pre_topc(X45)|~l1_pre_topc(X45)))&(v2_pre_topc(g1_pre_topc(u1_struct_0(X45),u1_pre_topc(X45)))|(~v2_pre_topc(X45)|~l1_pre_topc(X45)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_pre_topc])])])).
% 0.84/1.04  fof(c_0_75, plain, ![X42, X43]:((v1_pre_topc(g1_pre_topc(X42,X43))|~m1_subset_1(X43,k1_zfmisc_1(k1_zfmisc_1(X42))))&(l1_pre_topc(g1_pre_topc(X42,X43))|~m1_subset_1(X43,k1_zfmisc_1(k1_zfmisc_1(X42))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).
% 0.84/1.04  fof(c_0_76, plain, ![X44]:(~l1_pre_topc(X44)|m1_subset_1(u1_pre_topc(X44),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X44))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.84/1.04  fof(c_0_77, plain, ![X50, X51, X52, X53]:((~v5_pre_topc(X52,X50,X51)|v5_pre_topc(X53,X50,g1_pre_topc(u1_struct_0(X51),u1_pre_topc(X51)))|X52!=X53|(~v1_funct_1(X53)|~v1_funct_2(X53,u1_struct_0(X50),u1_struct_0(g1_pre_topc(u1_struct_0(X51),u1_pre_topc(X51))))|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(g1_pre_topc(u1_struct_0(X51),u1_pre_topc(X51)))))))|(~v1_funct_1(X52)|~v1_funct_2(X52,u1_struct_0(X50),u1_struct_0(X51))|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X51)))))|(~v2_pre_topc(X51)|~l1_pre_topc(X51))|(~v2_pre_topc(X50)|~l1_pre_topc(X50)))&(~v5_pre_topc(X53,X50,g1_pre_topc(u1_struct_0(X51),u1_pre_topc(X51)))|v5_pre_topc(X52,X50,X51)|X52!=X53|(~v1_funct_1(X53)|~v1_funct_2(X53,u1_struct_0(X50),u1_struct_0(g1_pre_topc(u1_struct_0(X51),u1_pre_topc(X51))))|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(g1_pre_topc(u1_struct_0(X51),u1_pre_topc(X51)))))))|(~v1_funct_1(X52)|~v1_funct_2(X52,u1_struct_0(X50),u1_struct_0(X51))|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X51)))))|(~v2_pre_topc(X51)|~l1_pre_topc(X51))|(~v2_pre_topc(X50)|~l1_pre_topc(X50)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_pre_topc])])])])).
% 0.84/1.04  cnf(c_0_78, negated_conjecture, (esk5_0=k1_xboole_0|v5_pre_topc(esk5_0,esk3_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~v5_pre_topc(esk5_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71]), c_0_72]), c_0_41]), c_0_36]), c_0_40])]), c_0_73])).
% 0.84/1.04  cnf(c_0_79, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.84/1.04  cnf(c_0_80, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.84/1.04  cnf(c_0_81, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.84/1.04  cnf(c_0_82, plain, (l1_pre_topc(g1_pre_topc(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.84/1.04  cnf(c_0_83, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.84/1.04  fof(c_0_84, plain, ![X36, X37]:(((((m1_subset_1(esk2_2(X36,X37),k1_zfmisc_1(k2_zfmisc_1(X36,X37)))&v1_relat_1(esk2_2(X36,X37)))&v4_relat_1(esk2_2(X36,X37),X36))&v5_relat_1(esk2_2(X36,X37),X37))&v1_funct_1(esk2_2(X36,X37)))&v1_funct_2(esk2_2(X36,X37),X36,X37)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_funct_2])])).
% 0.84/1.04  cnf(c_0_85, plain, (v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|~v5_pre_topc(X1,X2,X3)|X1!=X4|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.84/1.04  cnf(c_0_86, plain, (v5_pre_topc(X4,X2,X3)|~v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|X4!=X1|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.84/1.04  cnf(c_0_87, negated_conjecture, (esk5_0=k1_xboole_0|v5_pre_topc(esk5_0,esk3_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~v5_pre_topc(esk5_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80]), c_0_81])])).
% 0.84/1.04  cnf(c_0_88, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.84/1.04  cnf(c_0_89, negated_conjecture, (v5_pre_topc(esk5_0,esk3_0,esk4_0)|v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.84/1.04  cnf(c_0_90, plain, (m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.84/1.04  cnf(c_0_91, plain, (v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|~v5_pre_topc(X1,X2,X3)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_85])).
% 0.84/1.04  cnf(c_0_92, plain, (v5_pre_topc(X4,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|~v5_pre_topc(X1,X2,X3)|X1!=X4|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.84/1.04  cnf(c_0_93, plain, (v5_pre_topc(X1,X2,X3)|~v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_86])).
% 0.84/1.04  cnf(c_0_94, negated_conjecture, (esk5_0=k1_xboole_0|v5_pre_topc(esk5_0,esk3_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~v5_pre_topc(esk5_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_81])])).
% 0.84/1.04  cnf(c_0_95, negated_conjecture, (v5_pre_topc(esk5_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|v5_pre_topc(esk5_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_89, c_0_29])).
% 0.84/1.04  cnf(c_0_96, plain, (~r2_hidden(X1,esk2_2(X2,X3))|~v1_xboole_0(k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_42, c_0_90])).
% 0.84/1.04  fof(c_0_97, plain, ![X6]:(~v1_xboole_0(X6)|X6=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.84/1.04  fof(c_0_98, plain, ![X18]:(~v1_xboole_0(X18)|v1_xboole_0(k1_relat_1(X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_relat_1])])).
% 0.84/1.04  cnf(c_0_99, negated_conjecture, (esk5_0=k1_xboole_0|v5_pre_topc(esk5_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~v5_pre_topc(esk5_0,esk3_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_70]), c_0_71]), c_0_72]), c_0_41]), c_0_36]), c_0_40])]), c_0_73])).
% 0.84/1.04  cnf(c_0_100, plain, (v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|~v5_pre_topc(X1,X2,X3)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_92])).
% 0.84/1.04  cnf(c_0_101, negated_conjecture, (v5_pre_topc(esk5_0,esk3_0,esk4_0)|~v5_pre_topc(esk5_0,esk3_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))))|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_35]), c_0_80]), c_0_71]), c_0_81]), c_0_72]), c_0_36]), c_0_34])])).
% 0.84/1.04  cnf(c_0_102, negated_conjecture, (esk5_0=k1_xboole_0|v5_pre_topc(esk5_0,esk3_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|v5_pre_topc(esk5_0,esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.84/1.04  cnf(c_0_103, negated_conjecture, (~v5_pre_topc(esk5_0,esk3_0,esk4_0)|~v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.84/1.04  cnf(c_0_104, plain, (~r2_hidden(X1,esk2_2(X2,X3))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_96, c_0_51])).
% 0.84/1.04  fof(c_0_105, plain, ![X19]:(~v1_xboole_0(X19)|v1_funct_1(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_1])])).
% 0.84/1.04  cnf(c_0_106, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.84/1.04  cnf(c_0_107, plain, (v1_xboole_0(k1_relat_1(X1))|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_98])).
% 0.84/1.04  cnf(c_0_108, negated_conjecture, (esk5_0=k1_xboole_0|v5_pre_topc(esk5_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~v5_pre_topc(esk5_0,esk3_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_79]), c_0_80]), c_0_81])])).
% 0.84/1.04  cnf(c_0_109, negated_conjecture, (v5_pre_topc(esk5_0,esk3_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~v5_pre_topc(esk5_0,esk3_0,esk4_0)|~v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))))|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_35]), c_0_80]), c_0_71]), c_0_81]), c_0_72]), c_0_36]), c_0_34])])).
% 0.84/1.04  cnf(c_0_110, negated_conjecture, (esk5_0=k1_xboole_0|v5_pre_topc(esk5_0,esk3_0,esk4_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_73]), c_0_70])).
% 0.84/1.04  cnf(c_0_111, negated_conjecture, (~v5_pre_topc(esk5_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~v5_pre_topc(esk5_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_103, c_0_29])).
% 0.84/1.04  cnf(c_0_112, plain, (v1_funct_2(esk2_2(X1,X2),X1,X2)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.84/1.04  cnf(c_0_113, plain, (esk2_2(X1,X2)=k1_xboole_0|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_104, c_0_59])).
% 0.84/1.04  cnf(c_0_114, plain, (v1_funct_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_105])).
% 0.84/1.04  fof(c_0_115, plain, ![X11]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X11)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.84/1.04  cnf(c_0_116, plain, (k1_relat_1(X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_106, c_0_107])).
% 0.84/1.04  cnf(c_0_117, negated_conjecture, (esk5_0=k1_xboole_0|v5_pre_topc(esk5_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~v5_pre_topc(esk5_0,esk3_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_88]), c_0_81])])).
% 0.84/1.04  cnf(c_0_118, negated_conjecture, (esk5_0=k1_xboole_0|v5_pre_topc(esk5_0,esk3_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_110]), c_0_73]), c_0_70])).
% 0.84/1.04  cnf(c_0_119, negated_conjecture, (esk5_0=k1_xboole_0|~v5_pre_topc(esk5_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(spm,[status(thm)],[c_0_111, c_0_110])).
% 0.84/1.04  cnf(c_0_120, plain, (v1_funct_2(k1_xboole_0,X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_112, c_0_113])).
% 0.84/1.04  cnf(c_0_121, plain, (v1_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_114, c_0_64])).
% 0.84/1.04  cnf(c_0_122, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_115])).
% 0.84/1.04  cnf(c_0_123, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|v1_xboole_0(u1_struct_0(esk4_0))|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_116, c_0_52])).
% 0.84/1.04  cnf(c_0_124, negated_conjecture, (esk5_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_118]), c_0_119])).
% 0.84/1.04  cnf(c_0_125, negated_conjecture, (u1_struct_0(esk4_0)=k1_xboole_0|v1_partfun1(esk5_0,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_34]), c_0_35]), c_0_36])])).
% 0.84/1.04  cnf(c_0_126, plain, (v5_pre_topc(k1_xboole_0,X1,X2)|~v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))|~v1_xboole_0(u1_struct_0(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_120]), c_0_121]), c_0_122]), c_0_122])])).
% 0.84/1.04  cnf(c_0_127, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|v1_xboole_0(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_123, c_0_124]), c_0_64])])).
% 0.84/1.04  cnf(c_0_128, negated_conjecture, (k1_relat_1(esk5_0)=u1_struct_0(esk3_0)|u1_struct_0(esk4_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_125]), c_0_46]), c_0_47])])).
% 0.84/1.04  cnf(c_0_129, plain, (~r2_hidden(X1,esk2_2(X2,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_63]), c_0_64])])).
% 0.84/1.04  cnf(c_0_130, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|v5_pre_topc(k1_xboole_0,X1,esk4_0)|~v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_127]), c_0_80]), c_0_81])])).
% 0.84/1.04  cnf(c_0_131, negated_conjecture, (v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|v5_pre_topc(k1_xboole_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95, c_0_124]), c_0_124])).
% 0.84/1.04  cnf(c_0_132, negated_conjecture, (v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))))), inference(rw,[status(thm)],[c_0_41, c_0_124])).
% 0.84/1.04  cnf(c_0_133, plain, (v1_funct_1(esk2_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.84/1.04  cnf(c_0_134, negated_conjecture, (u1_struct_0(esk4_0)=k1_xboole_0|u1_struct_0(esk3_0)=k1_xboole_0|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_128, c_0_116])).
% 0.84/1.04  cnf(c_0_135, plain, (esk2_2(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_129, c_0_59])).
% 0.84/1.04  cnf(c_0_136, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0)|v5_pre_topc(k1_xboole_0,esk3_0,esk4_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_131]), c_0_132])])).
% 0.84/1.04  cnf(c_0_137, plain, (v5_pre_topc(esk2_2(u1_struct_0(X1),u1_struct_0(X2)),X1,X2)|~v5_pre_topc(esk2_2(u1_struct_0(X1),u1_struct_0(X2)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v1_funct_2(esk2_2(u1_struct_0(X1),u1_struct_0(X2)),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))|~m1_subset_1(esk2_2(u1_struct_0(X1),u1_struct_0(X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_112]), c_0_133]), c_0_90])])).
% 0.84/1.04  cnf(c_0_138, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|u1_struct_0(esk4_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_134, c_0_124]), c_0_64])])).
% 0.84/1.04  cnf(c_0_139, plain, (v1_funct_2(k1_xboole_0,X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_112, c_0_135])).
% 0.84/1.04  cnf(c_0_140, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0)|v5_pre_topc(k1_xboole_0,esk3_0,esk4_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136, c_0_79]), c_0_71]), c_0_72])])).
% 0.84/1.04  cnf(c_0_141, plain, (v5_pre_topc(esk2_2(u1_struct_0(X1),u1_struct_0(X2)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)|~v5_pre_topc(esk2_2(u1_struct_0(X1),u1_struct_0(X2)),X1,X2)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v1_funct_2(esk2_2(u1_struct_0(X1),u1_struct_0(X2)),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))|~m1_subset_1(esk2_2(u1_struct_0(X1),u1_struct_0(X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_112]), c_0_133]), c_0_90])])).
% 0.84/1.04  cnf(c_0_142, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|v5_pre_topc(k1_xboole_0,X1,esk4_0)|~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),esk4_0)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_138]), c_0_135]), c_0_135]), c_0_80]), c_0_81]), c_0_135]), c_0_139]), c_0_135]), c_0_63]), c_0_122])])).
% 0.84/1.04  cnf(c_0_143, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0)|v5_pre_topc(k1_xboole_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140, c_0_88]), c_0_72])])).
% 0.84/1.04  cnf(c_0_144, plain, (v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~v5_pre_topc(k1_xboole_0,X1,X2)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))|~v1_xboole_0(u1_struct_0(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_120]), c_0_121]), c_0_122]), c_0_122])])).
% 0.84/1.04  cnf(c_0_145, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),esk4_0)|~v5_pre_topc(k1_xboole_0,X1,esk4_0)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141, c_0_138]), c_0_135]), c_0_135]), c_0_80]), c_0_81]), c_0_135]), c_0_139]), c_0_135]), c_0_63]), c_0_122])])).
% 0.84/1.04  cnf(c_0_146, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|v5_pre_topc(k1_xboole_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142, c_0_143]), c_0_71]), c_0_72])])).
% 0.84/1.04  cnf(c_0_147, negated_conjecture, (~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~v5_pre_topc(k1_xboole_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111, c_0_124]), c_0_124])).
% 0.84/1.04  cnf(c_0_148, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.84/1.04  cnf(c_0_149, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~v5_pre_topc(k1_xboole_0,X1,esk4_0)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144, c_0_127]), c_0_80]), c_0_81])])).
% 0.84/1.04  cnf(c_0_150, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145, c_0_146]), c_0_71]), c_0_72])])).
% 0.84/1.04  cnf(c_0_151, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(spm,[status(thm)],[c_0_147, c_0_146])).
% 0.84/1.04  cnf(c_0_152, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_148])).
% 0.84/1.04  cnf(c_0_153, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149, c_0_150]), c_0_132])]), c_0_151])).
% 0.84/1.04  cnf(c_0_154, plain, (~r2_hidden(X1,esk2_2(k1_xboole_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_152]), c_0_64])])).
% 0.84/1.04  cnf(c_0_155, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153, c_0_79]), c_0_71]), c_0_72])])).
% 0.84/1.04  cnf(c_0_156, plain, (esk2_2(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_154, c_0_59])).
% 0.84/1.04  cnf(c_0_157, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_155, c_0_88]), c_0_72])])).
% 0.84/1.04  cnf(c_0_158, negated_conjecture, (v5_pre_topc(k1_xboole_0,esk3_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~v5_pre_topc(k1_xboole_0,esk3_0,esk4_0)|~v1_funct_2(k1_xboole_0,u1_struct_0(esk3_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109, c_0_124]), c_0_124]), c_0_124]), c_0_124]), c_0_122])])).
% 0.84/1.04  cnf(c_0_159, plain, (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_112, c_0_156])).
% 0.84/1.04  cnf(c_0_160, negated_conjecture, (v5_pre_topc(k1_xboole_0,esk3_0,X1)|~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk3_0)),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk3_0))),u1_struct_0(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_157]), c_0_156]), c_0_156]), c_0_71]), c_0_72]), c_0_156]), c_0_156]), c_0_122])])).
% 0.84/1.04  cnf(c_0_161, negated_conjecture, (v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk3_0)),g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|v5_pre_topc(k1_xboole_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_131, c_0_157])).
% 0.84/1.04  cnf(c_0_162, negated_conjecture, (v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk3_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))))), inference(rw,[status(thm)],[c_0_132, c_0_157])).
% 0.84/1.04  cnf(c_0_163, negated_conjecture, (v5_pre_topc(k1_xboole_0,esk3_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~v5_pre_topc(k1_xboole_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_158, c_0_157]), c_0_159])])).
% 0.84/1.04  cnf(c_0_164, negated_conjecture, (v5_pre_topc(k1_xboole_0,esk3_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160, c_0_161]), c_0_162])]), c_0_163])).
% 0.84/1.04  cnf(c_0_165, negated_conjecture, (v5_pre_topc(k1_xboole_0,esk3_0,esk4_0)|~v5_pre_topc(k1_xboole_0,esk3_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~v1_funct_2(k1_xboole_0,u1_struct_0(esk3_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101, c_0_124]), c_0_124]), c_0_124]), c_0_124]), c_0_122])])).
% 0.84/1.04  cnf(c_0_166, negated_conjecture, (v5_pre_topc(k1_xboole_0,esk3_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_164, c_0_79]), c_0_80]), c_0_81])])).
% 0.84/1.04  cnf(c_0_167, negated_conjecture, (v5_pre_topc(k1_xboole_0,esk3_0,esk4_0)|~v5_pre_topc(k1_xboole_0,esk3_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_165, c_0_157]), c_0_159])])).
% 0.84/1.04  cnf(c_0_168, negated_conjecture, (v5_pre_topc(k1_xboole_0,esk3_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_166, c_0_88]), c_0_81])])).
% 0.84/1.04  cnf(c_0_169, negated_conjecture, (~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk3_0)),g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~v5_pre_topc(k1_xboole_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_147, c_0_157])).
% 0.84/1.04  cnf(c_0_170, negated_conjecture, (v5_pre_topc(k1_xboole_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_167, c_0_168])])).
% 0.84/1.04  cnf(c_0_171, negated_conjecture, (v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk3_0)),X1)|~v5_pre_topc(k1_xboole_0,esk3_0,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk3_0))),u1_struct_0(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141, c_0_157]), c_0_156]), c_0_156]), c_0_71]), c_0_72]), c_0_156]), c_0_156]), c_0_122])])).
% 0.84/1.04  cnf(c_0_172, negated_conjecture, (~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk3_0)),g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_169, c_0_170])])).
% 0.84/1.04  cnf(c_0_173, negated_conjecture, (~v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171, c_0_168]), c_0_162])]), c_0_172])).
% 0.84/1.04  cnf(c_0_174, negated_conjecture, (~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_173, c_0_79]), c_0_80]), c_0_81])])).
% 0.84/1.04  cnf(c_0_175, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_174, c_0_88]), c_0_81])]), ['proof']).
% 0.84/1.04  # SZS output end CNFRefutation
% 0.84/1.04  # Proof object total steps             : 176
% 0.84/1.04  # Proof object clause steps            : 134
% 0.84/1.04  # Proof object formula steps           : 42
% 0.84/1.04  # Proof object conjectures             : 88
% 0.84/1.04  # Proof object clause conjectures      : 85
% 0.84/1.04  # Proof object formula conjectures     : 3
% 0.84/1.04  # Proof object initial clauses used    : 37
% 0.84/1.04  # Proof object initial formulas used   : 21
% 0.84/1.04  # Proof object generating inferences   : 72
% 0.84/1.04  # Proof object simplifying inferences  : 208
% 0.84/1.04  # Training examples: 0 positive, 0 negative
% 0.84/1.04  # Parsed axioms                        : 22
% 0.84/1.04  # Removed by relevancy pruning/SinE    : 0
% 0.84/1.04  # Initial clauses                      : 51
% 0.84/1.04  # Removed in clause preprocessing      : 1
% 0.84/1.04  # Initial clauses in saturation        : 50
% 0.84/1.04  # Processed clauses                    : 4557
% 0.84/1.04  # ...of these trivial                  : 8
% 0.84/1.04  # ...subsumed                          : 3147
% 0.84/1.04  # ...remaining for further processing  : 1402
% 0.84/1.04  # Other redundant clauses eliminated   : 147
% 0.84/1.04  # Clauses deleted for lack of memory   : 0
% 0.84/1.04  # Backward-subsumed                    : 250
% 0.84/1.04  # Backward-rewritten                   : 865
% 0.84/1.04  # Generated clauses                    : 37897
% 0.84/1.04  # ...of the previous two non-trivial   : 32031
% 0.84/1.04  # Contextual simplify-reflections      : 33
% 0.84/1.04  # Paramodulations                      : 37725
% 0.84/1.04  # Factorizations                       : 25
% 0.84/1.04  # Equation resolutions                 : 147
% 0.84/1.04  # Propositional unsat checks           : 0
% 0.84/1.04  #    Propositional check models        : 0
% 0.84/1.04  #    Propositional check unsatisfiable : 0
% 0.84/1.04  #    Propositional clauses             : 0
% 0.84/1.04  #    Propositional clauses after purity: 0
% 0.84/1.04  #    Propositional unsat core size     : 0
% 0.84/1.04  #    Propositional preprocessing time  : 0.000
% 0.84/1.04  #    Propositional encoding time       : 0.000
% 0.84/1.04  #    Propositional solver time         : 0.000
% 0.84/1.04  #    Success case prop preproc time    : 0.000
% 0.84/1.04  #    Success case prop encoding time   : 0.000
% 0.84/1.04  #    Success case prop solver time     : 0.000
% 0.84/1.04  # Current number of processed clauses  : 230
% 0.84/1.04  #    Positive orientable unit clauses  : 36
% 0.84/1.04  #    Positive unorientable unit clauses: 0
% 0.84/1.04  #    Negative unit clauses             : 3
% 0.84/1.04  #    Non-unit-clauses                  : 191
% 0.84/1.04  # Current number of unprocessed clauses: 6056
% 0.84/1.04  # ...number of literals in the above   : 40357
% 0.84/1.04  # Current number of archived formulas  : 0
% 0.84/1.04  # Current number of archived clauses   : 1164
% 0.84/1.04  # Clause-clause subsumption calls (NU) : 714743
% 0.84/1.04  # Rec. Clause-clause subsumption calls : 100737
% 0.84/1.04  # Non-unit clause-clause subsumptions  : 2594
% 0.84/1.04  # Unit Clause-clause subsumption calls : 1134
% 0.84/1.04  # Rewrite failures with RHS unbound    : 0
% 0.84/1.04  # BW rewrite match attempts            : 23
% 0.84/1.04  # BW rewrite match successes           : 9
% 0.84/1.04  # Condensation attempts                : 0
% 0.84/1.04  # Condensation successes               : 0
% 0.84/1.04  # Termbank termtop insertions          : 773941
% 0.84/1.04  
% 0.84/1.04  # -------------------------------------------------
% 0.84/1.04  # User time                : 0.683 s
% 0.84/1.04  # System time              : 0.013 s
% 0.84/1.04  # Total time               : 0.696 s
% 0.84/1.04  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
