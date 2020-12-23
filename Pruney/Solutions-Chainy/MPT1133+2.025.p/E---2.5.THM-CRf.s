%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:25 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  126 (6770 expanded)
%              Number of clauses        :   98 (2571 expanded)
%              Number of leaves         :   14 (1676 expanded)
%              Depth                    :   28
%              Number of atoms          :  510 (54392 expanded)
%              Number of equality atoms :   99 (4995 expanded)
%              Maximal formula depth    :   19 (   5 average)
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

fof(d1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => ( v1_funct_2(X3,X1,X2)
          <=> X1 = k1_relset_1(X1,X2,X3) ) )
        & ( X2 = k1_xboole_0
         => ( X1 = k1_xboole_0
            | ( v1_funct_2(X3,X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(rc1_subset_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ? [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
          & ~ v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_subset_1)).

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

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

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

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

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

fof(dt_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(c_0_14,negated_conjecture,(
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

fof(c_0_15,negated_conjecture,
    ( v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))))
    & esk4_0 = esk5_0
    & ( ~ v5_pre_topc(esk4_0,esk2_0,esk3_0)
      | ~ v5_pre_topc(esk5_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) )
    & ( v5_pre_topc(esk4_0,esk2_0,esk3_0)
      | v5_pre_topc(esk5_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_16,plain,(
    ! [X32,X33,X34] :
      ( ( ~ v1_funct_2(X34,X32,X33)
        | X32 = k1_relset_1(X32,X33,X34)
        | X33 = k1_xboole_0
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( X32 != k1_relset_1(X32,X33,X34)
        | v1_funct_2(X34,X32,X33)
        | X33 = k1_xboole_0
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( ~ v1_funct_2(X34,X32,X33)
        | X32 = k1_relset_1(X32,X33,X34)
        | X32 != k1_xboole_0
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( X32 != k1_relset_1(X32,X33,X34)
        | v1_funct_2(X34,X32,X33)
        | X32 != k1_xboole_0
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( ~ v1_funct_2(X34,X32,X33)
        | X34 = k1_xboole_0
        | X32 = k1_xboole_0
        | X33 != k1_xboole_0
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( X34 != k1_xboole_0
        | v1_funct_2(X34,X32,X33)
        | X32 = k1_xboole_0
        | X33 != k1_xboole_0
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( esk4_0 = esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X23,X24,X25] :
      ( ~ v1_xboole_0(X23)
      | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X24,X23)))
      | v1_xboole_0(X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

fof(c_0_21,plain,(
    ! [X7] :
      ( ( m1_subset_1(esk1_1(X7),k1_zfmisc_1(X7))
        | v1_xboole_0(X7) )
      & ( ~ v1_xboole_0(esk1_1(X7))
        | v1_xboole_0(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc1_subset_1])])])])])).

fof(c_0_22,plain,(
    ! [X54,X55,X56,X57] :
      ( ( ~ v5_pre_topc(X56,X54,X55)
        | v5_pre_topc(X57,X54,g1_pre_topc(u1_struct_0(X55),u1_pre_topc(X55)))
        | X56 != X57
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,u1_struct_0(X54),u1_struct_0(g1_pre_topc(u1_struct_0(X55),u1_pre_topc(X55))))
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X54),u1_struct_0(g1_pre_topc(u1_struct_0(X55),u1_pre_topc(X55))))))
        | ~ v1_funct_1(X56)
        | ~ v1_funct_2(X56,u1_struct_0(X54),u1_struct_0(X55))
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X54),u1_struct_0(X55))))
        | ~ v2_pre_topc(X55)
        | ~ l1_pre_topc(X55)
        | ~ v2_pre_topc(X54)
        | ~ l1_pre_topc(X54) )
      & ( ~ v5_pre_topc(X57,X54,g1_pre_topc(u1_struct_0(X55),u1_pre_topc(X55)))
        | v5_pre_topc(X56,X54,X55)
        | X56 != X57
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,u1_struct_0(X54),u1_struct_0(g1_pre_topc(u1_struct_0(X55),u1_pre_topc(X55))))
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X54),u1_struct_0(g1_pre_topc(u1_struct_0(X55),u1_pre_topc(X55))))))
        | ~ v1_funct_1(X56)
        | ~ v1_funct_2(X56,u1_struct_0(X54),u1_struct_0(X55))
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X54),u1_struct_0(X55))))
        | ~ v2_pre_topc(X55)
        | ~ l1_pre_topc(X55)
        | ~ v2_pre_topc(X54)
        | ~ l1_pre_topc(X54) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_pre_topc])])])])).

fof(c_0_23,plain,(
    ! [X29,X30,X31] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | k1_relset_1(X29,X30,X31) = k1_relat_1(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_24,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))) ),
    inference(rw,[status(thm)],[c_0_19,c_0_18])).

fof(c_0_27,plain,(
    ! [X5,X6] :
      ( ~ v1_xboole_0(X5)
      | X5 = X6
      | ~ v1_xboole_0(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_28,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( m1_subset_1(esk1_1(X1),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(esk1_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( ~ v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v5_pre_topc(esk5_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_32,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_33,plain,(
    ! [X50,X51,X52,X53] :
      ( ( ~ v5_pre_topc(X52,X50,X51)
        | v5_pre_topc(X53,g1_pre_topc(u1_struct_0(X50),u1_pre_topc(X50)),X51)
        | X52 != X53
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,u1_struct_0(g1_pre_topc(u1_struct_0(X50),u1_pre_topc(X50))),u1_struct_0(X51))
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X50),u1_pre_topc(X50))),u1_struct_0(X51))))
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,u1_struct_0(X50),u1_struct_0(X51))
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X51))))
        | ~ v2_pre_topc(X51)
        | ~ l1_pre_topc(X51)
        | ~ v2_pre_topc(X50)
        | ~ l1_pre_topc(X50) )
      & ( ~ v5_pre_topc(X53,g1_pre_topc(u1_struct_0(X50),u1_pre_topc(X50)),X51)
        | v5_pre_topc(X52,X50,X51)
        | X52 != X53
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,u1_struct_0(g1_pre_topc(u1_struct_0(X50),u1_pre_topc(X50))),u1_struct_0(X51))
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X50),u1_pre_topc(X50))),u1_struct_0(X51))))
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,u1_struct_0(X50),u1_struct_0(X51))
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X51))))
        | ~ v2_pre_topc(X51)
        | ~ l1_pre_topc(X51)
        | ~ v2_pre_topc(X50)
        | ~ l1_pre_topc(X50) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_pre_topc])])])])).

cnf(c_0_34,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,negated_conjecture,
    ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))),esk4_0) = u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])])).

cnf(c_0_36,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( ~ v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v5_pre_topc(esk4_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_31,c_0_18])).

cnf(c_0_39,plain,
    ( v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_41,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_43,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,negated_conjecture,
    ( k1_relat_1(esk4_0) = u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_25])])).

cnf(c_0_45,plain,
    ( X1 = k2_zfmisc_1(X2,X3)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_46,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_47,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | v5_pre_topc(esk5_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_48,negated_conjecture,
    ( ~ v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0)
    | ~ v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_26]),c_0_25])])).

cnf(c_0_49,plain,
    ( v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_51,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_52,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_54,negated_conjecture,
    ( k1_relset_1(X1,X2,esk4_0) = u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) = k1_xboole_0
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_44])).

cnf(c_0_55,plain,
    ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
    | ~ v1_xboole_0(X4)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_37])).

cnf(c_0_56,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_57,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_58,plain,
    ( v5_pre_topc(X1,X2,X3)
    | ~ v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_59,negated_conjecture,
    ( v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | v5_pre_topc(esk4_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_47,c_0_18])).

cnf(c_0_60,negated_conjecture,
    ( ~ v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_40]),c_0_50]),c_0_41]),c_0_51]),c_0_42]),c_0_52]),c_0_53])])).

cnf(c_0_61,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0) = u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_53])).

cnf(c_0_62,plain,
    ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,k1_xboole_0)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_63,plain,
    ( v5_pre_topc(X1,X2,X3)
    | ~ v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) ),
    inference(er,[status(thm)],[c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_40]),c_0_41]),c_0_42]),c_0_26]),c_0_25])]),c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_25])).

cnf(c_0_66,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) = u1_struct_0(esk2_0)
    | u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) = k1_xboole_0
    | u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_61]),c_0_52]),c_0_53])])).

cnf(c_0_67,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k2_zfmisc_1(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_56])).

cnf(c_0_68,negated_conjecture,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_40]),c_0_50]),c_0_41]),c_0_51]),c_0_42]),c_0_52]),c_0_53])]),c_0_60])).

cnf(c_0_69,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) = u1_struct_0(esk2_0)
    | u1_struct_0(esk3_0) = k1_xboole_0
    | v1_xboole_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_56])])).

fof(c_0_70,plain,(
    ! [X49] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X49),u1_pre_topc(X49)))
        | ~ v2_pre_topc(X49)
        | ~ l1_pre_topc(X49) )
      & ( v2_pre_topc(g1_pre_topc(u1_struct_0(X49),u1_pre_topc(X49)))
        | ~ v2_pre_topc(X49)
        | ~ l1_pre_topc(X49) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_pre_topc])])])).

cnf(c_0_71,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_56])).

cnf(c_0_72,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_67]),c_0_56])])).

cnf(c_0_73,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | v1_xboole_0(esk4_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_52]),c_0_53])])).

cnf(c_0_74,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

fof(c_0_75,plain,(
    ! [X46,X47] :
      ( ( v1_pre_topc(g1_pre_topc(X46,X47))
        | ~ m1_subset_1(X47,k1_zfmisc_1(k1_zfmisc_1(X46))) )
      & ( l1_pre_topc(g1_pre_topc(X46,X47))
        | ~ m1_subset_1(X47,k1_zfmisc_1(k1_zfmisc_1(X46))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).

cnf(c_0_76,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | v1_xboole_0(esk4_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_50]),c_0_51])])).

cnf(c_0_78,plain,
    ( l1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

fof(c_0_79,plain,(
    ! [X48] :
      ( ~ l1_pre_topc(X48)
      | m1_subset_1(u1_pre_topc(X48),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X48)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_80,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | m1_subset_1(k1_relset_1(X26,X27,X28),k1_zfmisc_1(X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).

cnf(c_0_81,negated_conjecture,
    ( ~ v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_49]),c_0_50]),c_0_51]),c_0_42]),c_0_26]),c_0_25])])).

cnf(c_0_82,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | ~ v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_53])).

cnf(c_0_83,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_76]),c_0_56])])).

cnf(c_0_84,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | v1_xboole_0(esk4_0)
    | ~ m1_subset_1(u1_pre_topc(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_85,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_86,plain,
    ( m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

fof(c_0_87,plain,(
    ! [X9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X9)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_88,negated_conjecture,
    ( ~ v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_39]),c_0_40]),c_0_50]),c_0_41]),c_0_51]),c_0_42]),c_0_52]),c_0_53])])).

cnf(c_0_89,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | ~ m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_90,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | v1_xboole_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_51])])).

cnf(c_0_91,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_92,plain,
    ( m1_subset_1(k1_relat_1(X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_86,c_0_34])).

cnf(c_0_93,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_94,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_59]),c_0_50]),c_0_51]),c_0_42]),c_0_26]),c_0_25])]),c_0_88])).

cnf(c_0_95,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | ~ m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_89])).

cnf(c_0_96,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_71,c_0_90])).

cnf(c_0_97,plain,
    ( v1_funct_2(X1,X2,X3)
    | k1_relat_1(X1) != X2
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_91,c_0_34])).

cnf(c_0_98,plain,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_83])).

cnf(c_0_99,plain,
    ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_100,negated_conjecture,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_94]),c_0_40]),c_0_50]),c_0_41]),c_0_51]),c_0_42]),c_0_52]),c_0_53])]),c_0_88])).

cnf(c_0_101,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_93])])).

cnf(c_0_102,plain,
    ( v1_funct_2(k1_xboole_0,X1,X2)
    | k1_relat_1(k1_xboole_0) != X1
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_97,c_0_93])).

cnf(c_0_103,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_104,negated_conjecture,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_101]),c_0_101]),c_0_93])])).

cnf(c_0_105,plain,
    ( v1_funct_2(k1_xboole_0,X1,X2)
    | k1_xboole_0 != X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_103])])).

cnf(c_0_106,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0) = u1_struct_0(esk2_0)
    | u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_53]),c_0_52])])).

cnf(c_0_107,plain,
    ( k1_relset_1(X1,X2,X3) = k1_relset_1(X4,X5,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_34])).

cnf(c_0_108,negated_conjecture,
    ( u1_struct_0(esk2_0) != k1_xboole_0
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_109,negated_conjecture,
    ( k1_relset_1(X1,X2,esk4_0) = u1_struct_0(esk2_0)
    | u1_struct_0(esk3_0) = k1_xboole_0
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_53])])).

cnf(c_0_110,negated_conjecture,
    ( u1_struct_0(esk2_0) != k1_xboole_0
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_74]),c_0_40]),c_0_41])])).

cnf(c_0_111,negated_conjecture,
    ( k1_relset_1(X1,k1_xboole_0,esk4_0) = u1_struct_0(esk2_0)
    | u1_struct_0(esk3_0) = k1_xboole_0
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_109,c_0_76])).

cnf(c_0_112,negated_conjecture,
    ( u1_struct_0(esk2_0) != k1_xboole_0
    | ~ m1_subset_1(u1_pre_topc(esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_110,c_0_78])).

cnf(c_0_113,negated_conjecture,
    ( k1_relset_1(X1,k1_xboole_0,k1_xboole_0) = u1_struct_0(esk2_0)
    | u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111,c_0_101]),c_0_101]),c_0_93])])).

cnf(c_0_114,negated_conjecture,
    ( u1_struct_0(esk2_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_85]),c_0_41])])).

cnf(c_0_115,negated_conjecture,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_101]),c_0_101]),c_0_93])])).

cnf(c_0_116,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_113]),c_0_103]),c_0_76]),c_0_93])]),c_0_114])).

cnf(c_0_117,plain,
    ( v1_funct_2(X1,X2,X3)
    | X2 = k1_xboole_0
    | X1 != k1_xboole_0
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_118,negated_conjecture,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_115,c_0_116])).

cnf(c_0_119,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(k1_xboole_0,X1,X2)
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_117,c_0_93])).

cnf(c_0_120,negated_conjecture,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_74]),c_0_50]),c_0_51])])).

cnf(c_0_121,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(k1_xboole_0,X1,k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_119])).

cnf(c_0_122,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) = k1_xboole_0
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_120,c_0_121])).

cnf(c_0_123,negated_conjecture,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_105]),c_0_122])).

cnf(c_0_124,negated_conjecture,
    ( ~ m1_subset_1(u1_pre_topc(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_123,c_0_78])).

cnf(c_0_125,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_85]),c_0_51])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:31:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.46  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.19/0.46  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.19/0.46  #
% 0.19/0.46  # Preprocessing time       : 0.044 s
% 0.19/0.46  
% 0.19/0.46  # Proof found!
% 0.19/0.46  # SZS status Theorem
% 0.19/0.46  # SZS output start CNFRefutation
% 0.19/0.46  fof(t64_pre_topc, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_pre_topc)).
% 0.19/0.46  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.19/0.46  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 0.19/0.46  fof(rc1_subset_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>?[X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))&~(v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_subset_1)).
% 0.19/0.46  fof(t63_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_pre_topc)).
% 0.19/0.46  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.46  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 0.19/0.46  fof(t62_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_pre_topc)).
% 0.19/0.46  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.46  fof(fc6_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))&v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_pre_topc)).
% 0.19/0.46  fof(dt_g1_pre_topc, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(v1_pre_topc(g1_pre_topc(X1,X2))&l1_pre_topc(g1_pre_topc(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 0.19/0.46  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.19/0.46  fof(dt_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 0.19/0.46  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.19/0.46  fof(c_0_14, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))))), inference(assume_negation,[status(cth)],[t64_pre_topc])).
% 0.19/0.46  fof(c_0_15, negated_conjecture, ((v2_pre_topc(esk2_0)&l1_pre_topc(esk2_0))&((v2_pre_topc(esk3_0)&l1_pre_topc(esk3_0))&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0)))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))))&(esk4_0=esk5_0&((~v5_pre_topc(esk4_0,esk2_0,esk3_0)|~v5_pre_topc(esk5_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))&(v5_pre_topc(esk4_0,esk2_0,esk3_0)|v5_pre_topc(esk5_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.19/0.46  fof(c_0_16, plain, ![X32, X33, X34]:((((~v1_funct_2(X34,X32,X33)|X32=k1_relset_1(X32,X33,X34)|X33=k1_xboole_0|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))&(X32!=k1_relset_1(X32,X33,X34)|v1_funct_2(X34,X32,X33)|X33=k1_xboole_0|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))))&((~v1_funct_2(X34,X32,X33)|X32=k1_relset_1(X32,X33,X34)|X32!=k1_xboole_0|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))&(X32!=k1_relset_1(X32,X33,X34)|v1_funct_2(X34,X32,X33)|X32!=k1_xboole_0|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))))&((~v1_funct_2(X34,X32,X33)|X34=k1_xboole_0|X32=k1_xboole_0|X33!=k1_xboole_0|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))&(X34!=k1_xboole_0|v1_funct_2(X34,X32,X33)|X32=k1_xboole_0|X33!=k1_xboole_0|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.19/0.46  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.46  cnf(c_0_18, negated_conjecture, (esk4_0=esk5_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.46  cnf(c_0_19, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.46  fof(c_0_20, plain, ![X23, X24, X25]:(~v1_xboole_0(X23)|(~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X24,X23)))|v1_xboole_0(X25))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 0.19/0.46  fof(c_0_21, plain, ![X7]:((m1_subset_1(esk1_1(X7),k1_zfmisc_1(X7))|v1_xboole_0(X7))&(~v1_xboole_0(esk1_1(X7))|v1_xboole_0(X7))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc1_subset_1])])])])])).
% 0.19/0.46  fof(c_0_22, plain, ![X54, X55, X56, X57]:((~v5_pre_topc(X56,X54,X55)|v5_pre_topc(X57,X54,g1_pre_topc(u1_struct_0(X55),u1_pre_topc(X55)))|X56!=X57|(~v1_funct_1(X57)|~v1_funct_2(X57,u1_struct_0(X54),u1_struct_0(g1_pre_topc(u1_struct_0(X55),u1_pre_topc(X55))))|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X54),u1_struct_0(g1_pre_topc(u1_struct_0(X55),u1_pre_topc(X55)))))))|(~v1_funct_1(X56)|~v1_funct_2(X56,u1_struct_0(X54),u1_struct_0(X55))|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X54),u1_struct_0(X55)))))|(~v2_pre_topc(X55)|~l1_pre_topc(X55))|(~v2_pre_topc(X54)|~l1_pre_topc(X54)))&(~v5_pre_topc(X57,X54,g1_pre_topc(u1_struct_0(X55),u1_pre_topc(X55)))|v5_pre_topc(X56,X54,X55)|X56!=X57|(~v1_funct_1(X57)|~v1_funct_2(X57,u1_struct_0(X54),u1_struct_0(g1_pre_topc(u1_struct_0(X55),u1_pre_topc(X55))))|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X54),u1_struct_0(g1_pre_topc(u1_struct_0(X55),u1_pre_topc(X55)))))))|(~v1_funct_1(X56)|~v1_funct_2(X56,u1_struct_0(X54),u1_struct_0(X55))|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X54),u1_struct_0(X55)))))|(~v2_pre_topc(X55)|~l1_pre_topc(X55))|(~v2_pre_topc(X54)|~l1_pre_topc(X54)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_pre_topc])])])])).
% 0.19/0.46  fof(c_0_23, plain, ![X29, X30, X31]:(~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|k1_relset_1(X29,X30,X31)=k1_relat_1(X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.46  cnf(c_0_24, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.46  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))))), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.46  cnf(c_0_26, negated_conjecture, (v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))), inference(rw,[status(thm)],[c_0_19, c_0_18])).
% 0.19/0.46  fof(c_0_27, plain, ![X5, X6]:(~v1_xboole_0(X5)|X5=X6|~v1_xboole_0(X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 0.19/0.46  cnf(c_0_28, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.46  cnf(c_0_29, plain, (m1_subset_1(esk1_1(X1),k1_zfmisc_1(X1))|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.46  cnf(c_0_30, plain, (v1_xboole_0(X1)|~v1_xboole_0(esk1_1(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.46  cnf(c_0_31, negated_conjecture, (~v5_pre_topc(esk4_0,esk2_0,esk3_0)|~v5_pre_topc(esk5_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.46  cnf(c_0_32, plain, (v5_pre_topc(X4,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|~v5_pre_topc(X1,X2,X3)|X1!=X4|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.46  fof(c_0_33, plain, ![X50, X51, X52, X53]:((~v5_pre_topc(X52,X50,X51)|v5_pre_topc(X53,g1_pre_topc(u1_struct_0(X50),u1_pre_topc(X50)),X51)|X52!=X53|(~v1_funct_1(X53)|~v1_funct_2(X53,u1_struct_0(g1_pre_topc(u1_struct_0(X50),u1_pre_topc(X50))),u1_struct_0(X51))|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X50),u1_pre_topc(X50))),u1_struct_0(X51)))))|(~v1_funct_1(X52)|~v1_funct_2(X52,u1_struct_0(X50),u1_struct_0(X51))|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X51)))))|(~v2_pre_topc(X51)|~l1_pre_topc(X51))|(~v2_pre_topc(X50)|~l1_pre_topc(X50)))&(~v5_pre_topc(X53,g1_pre_topc(u1_struct_0(X50),u1_pre_topc(X50)),X51)|v5_pre_topc(X52,X50,X51)|X52!=X53|(~v1_funct_1(X53)|~v1_funct_2(X53,u1_struct_0(g1_pre_topc(u1_struct_0(X50),u1_pre_topc(X50))),u1_struct_0(X51))|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X50),u1_pre_topc(X50))),u1_struct_0(X51)))))|(~v1_funct_1(X52)|~v1_funct_2(X52,u1_struct_0(X50),u1_struct_0(X51))|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X51)))))|(~v2_pre_topc(X51)|~l1_pre_topc(X51))|(~v2_pre_topc(X50)|~l1_pre_topc(X50)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_pre_topc])])])])).
% 0.19/0.46  cnf(c_0_34, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.46  cnf(c_0_35, negated_conjecture, (k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))),esk4_0)=u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])])).
% 0.19/0.46  cnf(c_0_36, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.46  cnf(c_0_37, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 0.19/0.46  cnf(c_0_38, negated_conjecture, (~v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v5_pre_topc(esk4_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_31, c_0_18])).
% 0.19/0.46  cnf(c_0_39, plain, (v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|~v5_pre_topc(X1,X2,X3)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_32])).
% 0.19/0.46  cnf(c_0_40, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.46  cnf(c_0_41, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.46  cnf(c_0_42, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.46  cnf(c_0_43, plain, (v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|~v5_pre_topc(X1,X2,X3)|X1!=X4|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.46  cnf(c_0_44, negated_conjecture, (k1_relat_1(esk4_0)=u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_25])])).
% 0.19/0.46  cnf(c_0_45, plain, (X1=k2_zfmisc_1(X2,X3)|~v1_xboole_0(X1)|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.46  cnf(c_0_46, plain, (v5_pre_topc(X4,X2,X3)|~v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|X4!=X1|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.46  cnf(c_0_47, negated_conjecture, (v5_pre_topc(esk4_0,esk2_0,esk3_0)|v5_pre_topc(esk5_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.46  cnf(c_0_48, negated_conjecture, (~v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0)|~v5_pre_topc(esk4_0,esk2_0,esk3_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_41]), c_0_42]), c_0_26]), c_0_25])])).
% 0.19/0.46  cnf(c_0_49, plain, (v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|~v5_pre_topc(X1,X2,X3)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_43])).
% 0.19/0.46  cnf(c_0_50, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.46  cnf(c_0_51, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.46  cnf(c_0_52, negated_conjecture, (v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.46  cnf(c_0_53, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.46  cnf(c_0_54, negated_conjecture, (k1_relset_1(X1,X2,esk4_0)=u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))=k1_xboole_0|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_34, c_0_44])).
% 0.19/0.46  cnf(c_0_55, plain, (k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)|~v1_xboole_0(X4)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_45, c_0_37])).
% 0.19/0.46  cnf(c_0_56, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.46  cnf(c_0_57, plain, (v5_pre_topc(X4,X2,X3)|~v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|X4!=X1|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.46  cnf(c_0_58, plain, (v5_pre_topc(X1,X2,X3)|~v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_46])).
% 0.19/0.46  cnf(c_0_59, negated_conjecture, (v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|v5_pre_topc(esk4_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_47, c_0_18])).
% 0.19/0.46  cnf(c_0_60, negated_conjecture, (~v5_pre_topc(esk4_0,esk2_0,esk3_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_40]), c_0_50]), c_0_41]), c_0_51]), c_0_42]), c_0_52]), c_0_53])])).
% 0.19/0.46  cnf(c_0_61, negated_conjecture, (k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)=u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_54, c_0_53])).
% 0.19/0.46  cnf(c_0_62, plain, (k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,k1_xboole_0)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.19/0.46  cnf(c_0_63, plain, (v5_pre_topc(X1,X2,X3)|~v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_57])).
% 0.19/0.46  cnf(c_0_64, negated_conjecture, (v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0))))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_40]), c_0_41]), c_0_42]), c_0_26]), c_0_25])]), c_0_60])).
% 0.19/0.46  cnf(c_0_65, negated_conjecture, (v1_xboole_0(esk4_0)|~v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))), inference(spm,[status(thm)],[c_0_28, c_0_25])).
% 0.19/0.46  cnf(c_0_66, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))=u1_struct_0(esk2_0)|u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))=k1_xboole_0|u1_struct_0(esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_61]), c_0_52]), c_0_53])])).
% 0.19/0.46  cnf(c_0_67, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k2_zfmisc_1(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_62, c_0_56])).
% 0.19/0.46  cnf(c_0_68, negated_conjecture, (~v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0))))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_40]), c_0_50]), c_0_41]), c_0_51]), c_0_42]), c_0_52]), c_0_53])]), c_0_60])).
% 0.19/0.46  cnf(c_0_69, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))=u1_struct_0(esk2_0)|u1_struct_0(esk3_0)=k1_xboole_0|v1_xboole_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_56])])).
% 0.19/0.46  fof(c_0_70, plain, ![X49]:((v1_pre_topc(g1_pre_topc(u1_struct_0(X49),u1_pre_topc(X49)))|(~v2_pre_topc(X49)|~l1_pre_topc(X49)))&(v2_pre_topc(g1_pre_topc(u1_struct_0(X49),u1_pre_topc(X49)))|(~v2_pre_topc(X49)|~l1_pre_topc(X49)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_pre_topc])])])).
% 0.19/0.46  cnf(c_0_71, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_36, c_0_56])).
% 0.19/0.46  cnf(c_0_72, plain, (v1_xboole_0(k2_zfmisc_1(X1,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_67]), c_0_56])])).
% 0.19/0.46  cnf(c_0_73, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|v1_xboole_0(esk4_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_52]), c_0_53])])).
% 0.19/0.46  cnf(c_0_74, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.19/0.46  fof(c_0_75, plain, ![X46, X47]:((v1_pre_topc(g1_pre_topc(X46,X47))|~m1_subset_1(X47,k1_zfmisc_1(k1_zfmisc_1(X46))))&(l1_pre_topc(g1_pre_topc(X46,X47))|~m1_subset_1(X47,k1_zfmisc_1(k1_zfmisc_1(X46))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).
% 0.19/0.46  cnf(c_0_76, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.19/0.46  cnf(c_0_77, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|v1_xboole_0(esk4_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_50]), c_0_51])])).
% 0.19/0.46  cnf(c_0_78, plain, (l1_pre_topc(g1_pre_topc(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.19/0.46  fof(c_0_79, plain, ![X48]:(~l1_pre_topc(X48)|m1_subset_1(u1_pre_topc(X48),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X48))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.19/0.46  fof(c_0_80, plain, ![X26, X27, X28]:(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|m1_subset_1(k1_relset_1(X26,X27,X28),k1_zfmisc_1(X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).
% 0.19/0.46  cnf(c_0_81, negated_conjecture, (~v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v5_pre_topc(esk4_0,esk2_0,esk3_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_49]), c_0_50]), c_0_51]), c_0_42]), c_0_26]), c_0_25])])).
% 0.19/0.46  cnf(c_0_82, negated_conjecture, (v1_xboole_0(esk4_0)|~v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_28, c_0_53])).
% 0.19/0.46  cnf(c_0_83, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_76]), c_0_56])])).
% 0.19/0.46  cnf(c_0_84, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|v1_xboole_0(esk4_0)|~m1_subset_1(u1_pre_topc(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.19/0.46  cnf(c_0_85, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.19/0.46  cnf(c_0_86, plain, (m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.19/0.46  fof(c_0_87, plain, ![X9]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X9)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.19/0.46  cnf(c_0_88, negated_conjecture, (~v5_pre_topc(esk4_0,esk2_0,esk3_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_39]), c_0_40]), c_0_50]), c_0_41]), c_0_51]), c_0_42]), c_0_52]), c_0_53])])).
% 0.19/0.46  cnf(c_0_89, negated_conjecture, (v1_xboole_0(esk4_0)|~m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.19/0.46  cnf(c_0_90, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|v1_xboole_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_51])])).
% 0.19/0.46  cnf(c_0_91, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.46  cnf(c_0_92, plain, (m1_subset_1(k1_relat_1(X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_86, c_0_34])).
% 0.19/0.46  cnf(c_0_93, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.19/0.46  cnf(c_0_94, negated_conjecture, (v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_59]), c_0_50]), c_0_51]), c_0_42]), c_0_26]), c_0_25])]), c_0_88])).
% 0.19/0.46  cnf(c_0_95, negated_conjecture, (esk4_0=k1_xboole_0|~m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_71, c_0_89])).
% 0.19/0.46  cnf(c_0_96, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_71, c_0_90])).
% 0.19/0.46  cnf(c_0_97, plain, (v1_funct_2(X1,X2,X3)|k1_relat_1(X1)!=X2|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_91, c_0_34])).
% 0.19/0.46  cnf(c_0_98, plain, (X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_71, c_0_83])).
% 0.19/0.46  cnf(c_0_99, plain, (m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 0.19/0.46  cnf(c_0_100, negated_conjecture, (~v2_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_94]), c_0_40]), c_0_50]), c_0_41]), c_0_51]), c_0_42]), c_0_52]), c_0_53])]), c_0_88])).
% 0.19/0.46  cnf(c_0_101, negated_conjecture, (esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_93])])).
% 0.19/0.46  cnf(c_0_102, plain, (v1_funct_2(k1_xboole_0,X1,X2)|k1_relat_1(k1_xboole_0)!=X1|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_97, c_0_93])).
% 0.19/0.46  cnf(c_0_103, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_98, c_0_99])).
% 0.19/0.46  cnf(c_0_104, negated_conjecture, (~v2_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v1_funct_2(k1_xboole_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_100, c_0_101]), c_0_101]), c_0_93])])).
% 0.19/0.46  cnf(c_0_105, plain, (v1_funct_2(k1_xboole_0,X1,X2)|k1_xboole_0!=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_102, c_0_103])])).
% 0.19/0.46  cnf(c_0_106, negated_conjecture, (k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)=u1_struct_0(esk2_0)|u1_struct_0(esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_53]), c_0_52])])).
% 0.19/0.46  cnf(c_0_107, plain, (k1_relset_1(X1,X2,X3)=k1_relset_1(X4,X5,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))), inference(spm,[status(thm)],[c_0_34, c_0_34])).
% 0.19/0.46  cnf(c_0_108, negated_conjecture, (u1_struct_0(esk2_0)!=k1_xboole_0|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(spm,[status(thm)],[c_0_104, c_0_105])).
% 0.19/0.46  cnf(c_0_109, negated_conjecture, (k1_relset_1(X1,X2,esk4_0)=u1_struct_0(esk2_0)|u1_struct_0(esk3_0)=k1_xboole_0|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_53])])).
% 0.19/0.46  cnf(c_0_110, negated_conjecture, (u1_struct_0(esk2_0)!=k1_xboole_0|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_74]), c_0_40]), c_0_41])])).
% 0.19/0.46  cnf(c_0_111, negated_conjecture, (k1_relset_1(X1,k1_xboole_0,esk4_0)=u1_struct_0(esk2_0)|u1_struct_0(esk3_0)=k1_xboole_0|~m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_109, c_0_76])).
% 0.19/0.46  cnf(c_0_112, negated_conjecture, (u1_struct_0(esk2_0)!=k1_xboole_0|~m1_subset_1(u1_pre_topc(esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))), inference(spm,[status(thm)],[c_0_110, c_0_78])).
% 0.19/0.46  cnf(c_0_113, negated_conjecture, (k1_relset_1(X1,k1_xboole_0,k1_xboole_0)=u1_struct_0(esk2_0)|u1_struct_0(esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111, c_0_101]), c_0_101]), c_0_93])])).
% 0.19/0.46  cnf(c_0_114, negated_conjecture, (u1_struct_0(esk2_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_85]), c_0_41])])).
% 0.19/0.46  cnf(c_0_115, negated_conjecture, (~v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_101]), c_0_101]), c_0_93])])).
% 0.19/0.46  cnf(c_0_116, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_113]), c_0_103]), c_0_76]), c_0_93])]), c_0_114])).
% 0.19/0.46  cnf(c_0_117, plain, (v1_funct_2(X1,X2,X3)|X2=k1_xboole_0|X1!=k1_xboole_0|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.46  cnf(c_0_118, negated_conjecture, (~v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),k1_xboole_0)), inference(rw,[status(thm)],[c_0_115, c_0_116])).
% 0.19/0.46  cnf(c_0_119, plain, (X1=k1_xboole_0|v1_funct_2(k1_xboole_0,X1,X2)|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_117, c_0_93])).
% 0.19/0.46  cnf(c_0_120, negated_conjecture, (~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_74]), c_0_50]), c_0_51])])).
% 0.19/0.46  cnf(c_0_121, plain, (X1=k1_xboole_0|v1_funct_2(k1_xboole_0,X1,k1_xboole_0)), inference(er,[status(thm)],[c_0_119])).
% 0.19/0.46  cnf(c_0_122, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))=k1_xboole_0|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(spm,[status(thm)],[c_0_120, c_0_121])).
% 0.19/0.46  cnf(c_0_123, negated_conjecture, (~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_105]), c_0_122])).
% 0.19/0.46  cnf(c_0_124, negated_conjecture, (~m1_subset_1(u1_pre_topc(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(spm,[status(thm)],[c_0_123, c_0_78])).
% 0.19/0.46  cnf(c_0_125, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_85]), c_0_51])]), ['proof']).
% 0.19/0.46  # SZS output end CNFRefutation
% 0.19/0.46  # Proof object total steps             : 126
% 0.19/0.46  # Proof object clause steps            : 98
% 0.19/0.46  # Proof object formula steps           : 28
% 0.19/0.46  # Proof object conjectures             : 60
% 0.19/0.46  # Proof object clause conjectures      : 57
% 0.19/0.46  # Proof object formula conjectures     : 3
% 0.19/0.46  # Proof object initial clauses used    : 30
% 0.19/0.46  # Proof object initial formulas used   : 14
% 0.19/0.46  # Proof object generating inferences   : 55
% 0.19/0.46  # Proof object simplifying inferences  : 127
% 0.19/0.46  # Training examples: 0 positive, 0 negative
% 0.19/0.46  # Parsed axioms                        : 22
% 0.19/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.46  # Initial clauses                      : 48
% 0.19/0.46  # Removed in clause preprocessing      : 2
% 0.19/0.46  # Initial clauses in saturation        : 46
% 0.19/0.46  # Processed clauses                    : 441
% 0.19/0.46  # ...of these trivial                  : 9
% 0.19/0.46  # ...subsumed                          : 105
% 0.19/0.46  # ...remaining for further processing  : 327
% 0.19/0.46  # Other redundant clauses eliminated   : 6
% 0.19/0.46  # Clauses deleted for lack of memory   : 0
% 0.19/0.46  # Backward-subsumed                    : 26
% 0.19/0.46  # Backward-rewritten                   : 113
% 0.19/0.46  # Generated clauses                    : 2060
% 0.19/0.46  # ...of the previous two non-trivial   : 1966
% 0.19/0.46  # Contextual simplify-reflections      : 13
% 0.19/0.46  # Paramodulations                      : 2040
% 0.19/0.46  # Factorizations                       : 12
% 0.19/0.46  # Equation resolutions                 : 8
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
% 0.19/0.46  # Current number of processed clauses  : 184
% 0.19/0.46  #    Positive orientable unit clauses  : 21
% 0.19/0.46  #    Positive unorientable unit clauses: 0
% 0.19/0.46  #    Negative unit clauses             : 3
% 0.19/0.46  #    Non-unit-clauses                  : 160
% 0.19/0.46  # Current number of unprocessed clauses: 1438
% 0.19/0.46  # ...number of literals in the above   : 7259
% 0.19/0.46  # Current number of archived formulas  : 0
% 0.19/0.46  # Current number of archived clauses   : 139
% 0.19/0.46  # Clause-clause subsumption calls (NU) : 18716
% 0.19/0.46  # Rec. Clause-clause subsumption calls : 5566
% 0.19/0.46  # Non-unit clause-clause subsumptions  : 139
% 0.19/0.46  # Unit Clause-clause subsumption calls : 1344
% 0.19/0.46  # Rewrite failures with RHS unbound    : 14
% 0.19/0.46  # BW rewrite match attempts            : 19
% 0.19/0.46  # BW rewrite match successes           : 13
% 0.19/0.46  # Condensation attempts                : 0
% 0.19/0.46  # Condensation successes               : 0
% 0.19/0.46  # Termbank termtop insertions          : 46023
% 0.19/0.46  
% 0.19/0.46  # -------------------------------------------------
% 0.19/0.46  # User time                : 0.117 s
% 0.19/0.46  # System time              : 0.007 s
% 0.19/0.46  # Total time               : 0.124 s
% 0.19/0.46  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
