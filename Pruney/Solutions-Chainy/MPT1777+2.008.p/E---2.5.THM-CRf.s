%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:57 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  117 (1552 expanded)
%              Number of clauses        :   80 ( 562 expanded)
%              Number of leaves         :   18 ( 381 expanded)
%              Depth                    :   15
%              Number of atoms          :  623 (15470 expanded)
%              Number of equality atoms :   55 (1565 expanded)
%              Maximal formula depth    :   27 (   6 average)
%              Maximal clause size      :   90 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t88_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                     => ( g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) = X4
                       => ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X4))
                           => ! [X7] :
                                ( m1_subset_1(X7,u1_struct_0(X3))
                               => ( ( X6 = X7
                                    & r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7) )
                                 => r1_tmap_1(X4,X2,X5,X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).

fof(t65_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( m1_pre_topc(X1,X2)
          <=> m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t11_tmap_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

fof(d5_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ! [X4] :
                  ( m1_pre_topc(X4,X1)
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                     => ( m1_pre_topc(X4,X3)
                       => k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

fof(t7_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X2)
             => m1_pre_topc(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(free_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3,X4] :
          ( g1_pre_topc(X1,X2) = g1_pre_topc(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(d4_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( m1_pre_topc(X4,X1)
                 => k2_tmap_1(X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(t67_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & v1_tsep_1(X4,X2)
                    & m1_pre_topc(X4,X2) )
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X4))
                         => ( X5 = X6
                           => ( r1_tmap_1(X2,X1,X3,X5)
                            <=> r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tmap_1)).

fof(t55_pre_topc,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

fof(t16_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = u1_struct_0(X2)
               => ( ( v1_tsep_1(X2,X1)
                    & m1_pre_topc(X2,X1) )
                <=> v3_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(d1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v2_pre_topc(X1)
      <=> ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
          & ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ( r1_tarski(X2,u1_pre_topc(X1))
               => r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)) ) )
          & ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X1))
                      & r2_hidden(X3,u1_pre_topc(X1)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v2_pre_topc(X2)
              & l1_pre_topc(X2) )
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & m1_pre_topc(X3,X1) )
               => ! [X4] :
                    ( ( ~ v2_struct_0(X4)
                      & m1_pre_topc(X4,X1) )
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                       => ( g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) = X4
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X4))
                             => ! [X7] :
                                  ( m1_subset_1(X7,u1_struct_0(X3))
                                 => ( ( X6 = X7
                                      & r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7) )
                                   => r1_tmap_1(X4,X2,X5,X6) ) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t88_tmap_1])).

fof(c_0_19,plain,(
    ! [X32,X33] :
      ( ( ~ m1_pre_topc(X32,X33)
        | m1_pre_topc(X32,g1_pre_topc(u1_struct_0(X33),u1_pre_topc(X33)))
        | ~ l1_pre_topc(X33)
        | ~ l1_pre_topc(X32) )
      & ( ~ m1_pre_topc(X32,g1_pre_topc(u1_struct_0(X33),u1_pre_topc(X33)))
        | m1_pre_topc(X32,X33)
        | ~ l1_pre_topc(X33)
        | ~ l1_pre_topc(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).

fof(c_0_20,plain,(
    ! [X22,X23] :
      ( ~ l1_pre_topc(X22)
      | ~ m1_pre_topc(X23,X22)
      | l1_pre_topc(X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & ~ v2_struct_0(esk5_0)
    & v2_pre_topc(esk5_0)
    & l1_pre_topc(esk5_0)
    & ~ v2_struct_0(esk6_0)
    & m1_pre_topc(esk6_0,esk4_0)
    & ~ v2_struct_0(esk7_0)
    & m1_pre_topc(esk7_0,esk4_0)
    & v1_funct_1(esk8_0)
    & v1_funct_2(esk8_0,u1_struct_0(esk7_0),u1_struct_0(esk5_0))
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk5_0))))
    & g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)) = esk7_0
    & m1_subset_1(esk9_0,u1_struct_0(esk7_0))
    & m1_subset_1(esk10_0,u1_struct_0(esk6_0))
    & esk9_0 = esk10_0
    & r1_tmap_1(esk6_0,esk5_0,k3_tmap_1(esk4_0,esk5_0,esk7_0,esk6_0,esk8_0),esk10_0)
    & ~ r1_tmap_1(esk7_0,esk5_0,esk8_0,esk9_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).

cnf(c_0_22,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( m1_pre_topc(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_26,plain,(
    ! [X43,X44] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X44),u1_pre_topc(X44)))
        | ~ m1_pre_topc(X44,X43)
        | ~ l1_pre_topc(X43) )
      & ( m1_pre_topc(g1_pre_topc(u1_struct_0(X44),u1_pre_topc(X44)),X43)
        | ~ m1_pre_topc(X44,X43)
        | ~ l1_pre_topc(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tmap_1])])])])).

fof(c_0_27,plain,(
    ! [X38,X39,X40,X41,X42] :
      ( v2_struct_0(X38)
      | ~ v2_pre_topc(X38)
      | ~ l1_pre_topc(X38)
      | v2_struct_0(X39)
      | ~ v2_pre_topc(X39)
      | ~ l1_pre_topc(X39)
      | ~ m1_pre_topc(X40,X38)
      | ~ m1_pre_topc(X41,X38)
      | ~ v1_funct_1(X42)
      | ~ v1_funct_2(X42,u1_struct_0(X40),u1_struct_0(X39))
      | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X40),u1_struct_0(X39))))
      | ~ m1_pre_topc(X41,X40)
      | k3_tmap_1(X38,X39,X40,X41,X42) = k2_partfun1(u1_struct_0(X40),u1_struct_0(X39),X42,u1_struct_0(X41)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).

fof(c_0_28,plain,(
    ! [X57,X58,X59] :
      ( ~ v2_pre_topc(X57)
      | ~ l1_pre_topc(X57)
      | ~ m1_pre_topc(X58,X57)
      | ~ m1_pre_topc(X59,X58)
      | m1_pre_topc(X59,X57) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

cnf(c_0_29,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)) = esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

fof(c_0_32,plain,(
    ! [X50] :
      ( ~ l1_pre_topc(X50)
      | m1_pre_topc(X50,X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

cnf(c_0_33,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( m1_pre_topc(X1,esk7_0)
    | ~ m1_pre_topc(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])])).

cnf(c_0_37,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( m1_pre_topc(esk7_0,X1)
    | ~ m1_pre_topc(esk6_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_30])).

fof(c_0_39,plain,(
    ! [X11,X12] :
      ( ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | ~ m1_pre_topc(X12,X11)
      | v2_pre_topc(X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

cnf(c_0_40,plain,
    ( k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X5)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(csr,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_2(esk8_0,u1_struct_0(esk7_0),u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_43,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_44,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_45,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_46,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_47,negated_conjecture,
    ( m1_pre_topc(esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_31])])).

cnf(c_0_48,negated_conjecture,
    ( m1_pre_topc(esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_37]),c_0_31])])).

cnf(c_0_49,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_50,negated_conjecture,
    ( m1_pre_topc(esk7_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_51,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_52,plain,(
    ! [X25,X26,X27,X28] :
      ( ( X25 = X27
        | g1_pre_topc(X25,X26) != g1_pre_topc(X27,X28)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(X25))) )
      & ( X26 = X28
        | g1_pre_topc(X25,X26) != g1_pre_topc(X27,X28)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(X25))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).

fof(c_0_53,plain,(
    ! [X24] :
      ( ~ l1_pre_topc(X24)
      | m1_subset_1(u1_pre_topc(X24),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X24)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_54,plain,(
    ! [X10] :
      ( ~ l1_pre_topc(X10)
      | ~ v1_pre_topc(X10)
      | X10 = g1_pre_topc(u1_struct_0(X10),u1_pre_topc(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

cnf(c_0_55,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_56,plain,(
    ! [X34,X35,X36,X37] :
      ( v2_struct_0(X34)
      | ~ v2_pre_topc(X34)
      | ~ l1_pre_topc(X34)
      | v2_struct_0(X35)
      | ~ v2_pre_topc(X35)
      | ~ l1_pre_topc(X35)
      | ~ v1_funct_1(X36)
      | ~ v1_funct_2(X36,u1_struct_0(X34),u1_struct_0(X35))
      | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(X35))))
      | ~ m1_pre_topc(X37,X34)
      | k2_tmap_1(X34,X35,X36,X37) = k2_partfun1(u1_struct_0(X34),u1_struct_0(X35),X36,u1_struct_0(X37)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_57,negated_conjecture,
    ( k3_tmap_1(X1,esk5_0,esk7_0,X2,esk8_0) = k2_partfun1(u1_struct_0(esk7_0),u1_struct_0(esk5_0),esk8_0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk7_0)
    | ~ m1_pre_topc(esk7_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45])]),c_0_46])).

cnf(c_0_58,negated_conjecture,
    ( m1_pre_topc(esk6_0,X1)
    | ~ m1_pre_topc(esk7_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_47])).

cnf(c_0_59,negated_conjecture,
    ( m1_pre_topc(esk7_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_48])).

cnf(c_0_60,negated_conjecture,
    ( v2_pre_topc(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_25])])).

cnf(c_0_61,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_50]),c_0_25])])).

cnf(c_0_62,plain,
    ( m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_63,plain,
    ( X1 = X2
    | g1_pre_topc(X3,X1) != g1_pre_topc(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_64,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_65,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_66,negated_conjecture,
    ( v1_pre_topc(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_24]),c_0_30]),c_0_25])])).

cnf(c_0_67,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_tmap_1(X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_68,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_69,negated_conjecture,
    ( k3_tmap_1(X1,esk5_0,esk7_0,esk6_0,esk8_0) = k2_partfun1(u1_struct_0(esk7_0),u1_struct_0(esk5_0),esk8_0,u1_struct_0(esk6_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk7_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59]),c_0_60]),c_0_61])])).

cnf(c_0_70,negated_conjecture,
    ( m1_pre_topc(X1,esk6_0)
    | ~ m1_pre_topc(X1,esk7_0)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_30]),c_0_31])])).

cnf(c_0_71,negated_conjecture,
    ( v2_pre_topc(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_24]),c_0_51]),c_0_25])])).

cnf(c_0_72,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_73,plain,
    ( u1_pre_topc(X1) = X2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_74,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_61])])).

cnf(c_0_75,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk7_0),u1_struct_0(esk5_0),esk8_0,u1_struct_0(X1)) = k2_tmap_1(esk7_0,esk5_0,esk8_0,X1)
    | ~ m1_pre_topc(X1,esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_60]),c_0_45]),c_0_61])]),c_0_46]),c_0_68])).

cnf(c_0_76,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk7_0),u1_struct_0(esk5_0),esk8_0,u1_struct_0(esk6_0)) = k3_tmap_1(esk6_0,esk5_0,esk7_0,esk6_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71]),c_0_31]),c_0_59]),c_0_61])]),c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( u1_pre_topc(esk7_0) = X1
    | g1_pre_topc(X2,X1) != esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_61])])).

fof(c_0_78,plain,(
    ! [X51,X52,X53,X54,X55,X56] :
      ( ( ~ r1_tmap_1(X52,X51,X53,X55)
        | r1_tmap_1(X54,X51,k2_tmap_1(X52,X51,X53,X54),X56)
        | X55 != X56
        | ~ m1_subset_1(X56,u1_struct_0(X54))
        | ~ m1_subset_1(X55,u1_struct_0(X52))
        | v2_struct_0(X54)
        | ~ v1_tsep_1(X54,X52)
        | ~ m1_pre_topc(X54,X52)
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,u1_struct_0(X52),u1_struct_0(X51))
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X52),u1_struct_0(X51))))
        | v2_struct_0(X52)
        | ~ v2_pre_topc(X52)
        | ~ l1_pre_topc(X52)
        | v2_struct_0(X51)
        | ~ v2_pre_topc(X51)
        | ~ l1_pre_topc(X51) )
      & ( ~ r1_tmap_1(X54,X51,k2_tmap_1(X52,X51,X53,X54),X56)
        | r1_tmap_1(X52,X51,X53,X55)
        | X55 != X56
        | ~ m1_subset_1(X56,u1_struct_0(X54))
        | ~ m1_subset_1(X55,u1_struct_0(X52))
        | v2_struct_0(X54)
        | ~ v1_tsep_1(X54,X52)
        | ~ m1_pre_topc(X54,X52)
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,u1_struct_0(X52),u1_struct_0(X51))
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X52),u1_struct_0(X51))))
        | v2_struct_0(X52)
        | ~ v2_pre_topc(X52)
        | ~ l1_pre_topc(X52)
        | v2_struct_0(X51)
        | ~ v2_pre_topc(X51)
        | ~ l1_pre_topc(X51) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t67_tmap_1])])])])])).

fof(c_0_79,plain,(
    ! [X29,X30,X31] :
      ( v2_struct_0(X29)
      | ~ l1_pre_topc(X29)
      | v2_struct_0(X30)
      | ~ m1_pre_topc(X30,X29)
      | ~ m1_subset_1(X31,u1_struct_0(X30))
      | m1_subset_1(X31,u1_struct_0(X29)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).

cnf(c_0_80,negated_conjecture,
    ( k3_tmap_1(esk6_0,esk5_0,esk7_0,esk6_0,esk8_0) = k2_tmap_1(esk7_0,esk5_0,esk8_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_47])])).

cnf(c_0_81,negated_conjecture,
    ( m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(esk6_0,X2)
    | ~ m1_pre_topc(X1,esk7_0)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_70])).

cnf(c_0_82,negated_conjecture,
    ( u1_pre_topc(esk6_0) = u1_pre_topc(esk7_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_30])).

cnf(c_0_83,plain,
    ( r1_tmap_1(X3,X2,X4,X6)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)
    | X6 != X5
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X6,u1_struct_0(X3))
    | ~ v1_tsep_1(X1,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_84,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_85,negated_conjecture,
    ( r1_tmap_1(esk6_0,esk5_0,k3_tmap_1(esk4_0,esk5_0,esk7_0,esk6_0,esk8_0),esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_86,negated_conjecture,
    ( esk9_0 = esk10_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_87,negated_conjecture,
    ( k3_tmap_1(X1,esk5_0,esk7_0,esk6_0,esk8_0) = k2_tmap_1(esk7_0,esk5_0,esk8_0,esk6_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk7_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_76]),c_0_80])).

cnf(c_0_88,negated_conjecture,
    ( m1_pre_topc(X1,esk4_0)
    | ~ m1_pre_topc(X1,esk7_0)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_24]),c_0_51]),c_0_25])])).

cnf(c_0_89,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_90,plain,(
    ! [X45,X46,X47] :
      ( ( ~ v1_tsep_1(X46,X45)
        | ~ m1_pre_topc(X46,X45)
        | v3_pre_topc(X47,X45)
        | X47 != u1_struct_0(X46)
        | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X45)))
        | ~ m1_pre_topc(X46,X45)
        | ~ v2_pre_topc(X45)
        | ~ l1_pre_topc(X45) )
      & ( v1_tsep_1(X46,X45)
        | ~ v3_pre_topc(X47,X45)
        | X47 != u1_struct_0(X46)
        | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X45)))
        | ~ m1_pre_topc(X46,X45)
        | ~ v2_pre_topc(X45)
        | ~ l1_pre_topc(X45) )
      & ( m1_pre_topc(X46,X45)
        | ~ v3_pre_topc(X47,X45)
        | X47 != u1_struct_0(X46)
        | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X45)))
        | ~ m1_pre_topc(X46,X45)
        | ~ v2_pre_topc(X45)
        | ~ l1_pre_topc(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tsep_1])])])])).

fof(c_0_91,plain,(
    ! [X48,X49] :
      ( ~ l1_pre_topc(X48)
      | ~ m1_pre_topc(X49,X48)
      | m1_subset_1(u1_struct_0(X49),k1_zfmisc_1(u1_struct_0(X48))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_92,plain,(
    ! [X13,X14,X15,X16] :
      ( ( r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))
        | ~ r1_tarski(X14,u1_pre_topc(X13))
        | r2_hidden(k5_setfam_1(u1_struct_0(X13),X14),u1_pre_topc(X13))
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ r2_hidden(X15,u1_pre_topc(X13))
        | ~ r2_hidden(X16,u1_pre_topc(X13))
        | r2_hidden(k9_subset_1(u1_struct_0(X13),X15,X16),u1_pre_topc(X13))
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk2_1(X13),k1_zfmisc_1(u1_struct_0(X13)))
        | m1_subset_1(esk1_1(X13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk3_1(X13),k1_zfmisc_1(u1_struct_0(X13)))
        | m1_subset_1(esk1_1(X13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( r2_hidden(esk2_1(X13),u1_pre_topc(X13))
        | m1_subset_1(esk1_1(X13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( r2_hidden(esk3_1(X13),u1_pre_topc(X13))
        | m1_subset_1(esk1_1(X13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X13),esk2_1(X13),esk3_1(X13)),u1_pre_topc(X13))
        | m1_subset_1(esk1_1(X13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk2_1(X13),k1_zfmisc_1(u1_struct_0(X13)))
        | r1_tarski(esk1_1(X13),u1_pre_topc(X13))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk3_1(X13),k1_zfmisc_1(u1_struct_0(X13)))
        | r1_tarski(esk1_1(X13),u1_pre_topc(X13))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( r2_hidden(esk2_1(X13),u1_pre_topc(X13))
        | r1_tarski(esk1_1(X13),u1_pre_topc(X13))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( r2_hidden(esk3_1(X13),u1_pre_topc(X13))
        | r1_tarski(esk1_1(X13),u1_pre_topc(X13))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X13),esk2_1(X13),esk3_1(X13)),u1_pre_topc(X13))
        | r1_tarski(esk1_1(X13),u1_pre_topc(X13))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk2_1(X13),k1_zfmisc_1(u1_struct_0(X13)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X13),esk1_1(X13)),u1_pre_topc(X13))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk3_1(X13),k1_zfmisc_1(u1_struct_0(X13)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X13),esk1_1(X13)),u1_pre_topc(X13))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( r2_hidden(esk2_1(X13),u1_pre_topc(X13))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X13),esk1_1(X13)),u1_pre_topc(X13))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( r2_hidden(esk3_1(X13),u1_pre_topc(X13))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X13),esk1_1(X13)),u1_pre_topc(X13))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X13),esk2_1(X13),esk3_1(X13)),u1_pre_topc(X13))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X13),esk1_1(X13)),u1_pre_topc(X13))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

cnf(c_0_93,plain,
    ( X1 = X2
    | g1_pre_topc(X1,X3) != g1_pre_topc(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_94,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(esk7_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_82]),c_0_31])])).

cnf(c_0_95,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk7_0)) = esk7_0 ),
    inference(rw,[status(thm)],[c_0_30,c_0_82])).

cnf(c_0_96,plain,
    ( r1_tmap_1(X1,X2,X3,X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X5)
    | ~ r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X4)
    | ~ v1_tsep_1(X5,X1)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ m1_pre_topc(X5,X1)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X4,u1_struct_0(X5)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_83]),c_0_84])).

cnf(c_0_97,negated_conjecture,
    ( r1_tmap_1(esk6_0,esk5_0,k3_tmap_1(esk4_0,esk5_0,esk7_0,esk6_0,esk8_0),esk9_0) ),
    inference(rw,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_98,negated_conjecture,
    ( k3_tmap_1(esk4_0,esk5_0,esk7_0,esk6_0,esk8_0) = k2_tmap_1(esk7_0,esk5_0,esk8_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_51]),c_0_25]),c_0_59]),c_0_61])]),c_0_89])).

cnf(c_0_99,negated_conjecture,
    ( m1_subset_1(esk10_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_100,plain,
    ( v1_tsep_1(X1,X2)
    | ~ v3_pre_topc(X3,X2)
    | X3 != u1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_101,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

fof(c_0_102,plain,(
    ! [X20,X21] :
      ( ( ~ v3_pre_topc(X21,X20)
        | r2_hidden(X21,u1_pre_topc(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ l1_pre_topc(X20) )
      & ( ~ r2_hidden(X21,u1_pre_topc(X20))
        | v3_pre_topc(X21,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_103,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_104,negated_conjecture,
    ( u1_struct_0(esk6_0) = X1
    | g1_pre_topc(X1,X2) != esk7_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_95])).

cnf(c_0_105,negated_conjecture,
    ( r1_tmap_1(esk7_0,esk5_0,esk8_0,X1)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X2,esk5_0,k2_tmap_1(esk7_0,esk5_0,esk8_0,X2),X1)
    | ~ v1_tsep_1(X2,esk7_0)
    | ~ m1_pre_topc(X2,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_41]),c_0_42]),c_0_43]),c_0_60]),c_0_44]),c_0_61]),c_0_45])]),c_0_46]),c_0_68])).

cnf(c_0_106,negated_conjecture,
    ( r1_tmap_1(esk6_0,esk5_0,k2_tmap_1(esk7_0,esk5_0,esk8_0,esk6_0),esk9_0) ),
    inference(rw,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_107,negated_conjecture,
    ( m1_subset_1(esk9_0,u1_struct_0(esk6_0)) ),
    inference(rw,[status(thm)],[c_0_99,c_0_86])).

cnf(c_0_108,negated_conjecture,
    ( ~ r1_tmap_1(esk7_0,esk5_0,esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_109,plain,
    ( v1_tsep_1(X1,X2)
    | ~ v3_pre_topc(u1_struct_0(X1),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_100]),c_0_101])).

cnf(c_0_110,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_111,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk6_0),u1_pre_topc(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_82]),c_0_71]),c_0_31])])).

cnf(c_0_112,negated_conjecture,
    ( u1_struct_0(esk6_0) = u1_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_104,c_0_74])).

cnf(c_0_113,negated_conjecture,
    ( ~ v1_tsep_1(esk6_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_47]),c_0_107])]),c_0_108]),c_0_72])).

cnf(c_0_114,plain,
    ( v1_tsep_1(X1,X2)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_101])).

cnf(c_0_115,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)) ),
    inference(rw,[status(thm)],[c_0_111,c_0_112])).

cnf(c_0_116,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_112]),c_0_115]),c_0_47]),c_0_60]),c_0_61])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:42:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.42  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.42  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.42  #
% 0.20/0.42  # Preprocessing time       : 0.030 s
% 0.20/0.42  # Presaturation interreduction done
% 0.20/0.42  
% 0.20/0.42  # Proof found!
% 0.20/0.42  # SZS status Theorem
% 0.20/0.42  # SZS output start CNFRefutation
% 0.20/0.42  fof(t88_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))=X4=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>((X6=X7&r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7))=>r1_tmap_1(X4,X2,X5,X6)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tmap_1)).
% 0.20/0.42  fof(t65_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X1,X2)<=>m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 0.20/0.42  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.20/0.42  fof(t11_tmap_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))&m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tmap_1)).
% 0.20/0.42  fof(d5_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(m1_pre_topc(X3,X1)=>![X4]:(m1_pre_topc(X4,X1)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(m1_pre_topc(X4,X3)=>k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 0.20/0.42  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.20/0.42  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.20/0.42  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.20/0.42  fof(free_g1_pre_topc, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3, X4]:(g1_pre_topc(X1,X2)=g1_pre_topc(X3,X4)=>(X1=X3&X2=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 0.20/0.42  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.20/0.42  fof(abstractness_v1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_pre_topc(X1)=>X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 0.20/0.42  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.20/0.42  fof(t67_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X4]:(((~(v2_struct_0(X4))&v1_tsep_1(X4,X2))&m1_pre_topc(X4,X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>(X5=X6=>(r1_tmap_1(X2,X1,X3,X5)<=>r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_tmap_1)).
% 0.20/0.42  fof(t55_pre_topc, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>m1_subset_1(X3,u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_pre_topc)).
% 0.20/0.42  fof(t16_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 0.20/0.42  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.20/0.42  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 0.20/0.42  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.20/0.42  fof(c_0_18, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))=X4=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>((X6=X7&r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7))=>r1_tmap_1(X4,X2,X5,X6))))))))))), inference(assume_negation,[status(cth)],[t88_tmap_1])).
% 0.20/0.42  fof(c_0_19, plain, ![X32, X33]:((~m1_pre_topc(X32,X33)|m1_pre_topc(X32,g1_pre_topc(u1_struct_0(X33),u1_pre_topc(X33)))|~l1_pre_topc(X33)|~l1_pre_topc(X32))&(~m1_pre_topc(X32,g1_pre_topc(u1_struct_0(X33),u1_pre_topc(X33)))|m1_pre_topc(X32,X33)|~l1_pre_topc(X33)|~l1_pre_topc(X32))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).
% 0.20/0.42  fof(c_0_20, plain, ![X22, X23]:(~l1_pre_topc(X22)|(~m1_pre_topc(X23,X22)|l1_pre_topc(X23))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.20/0.42  fof(c_0_21, negated_conjecture, (((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&(((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&l1_pre_topc(esk5_0))&((~v2_struct_0(esk6_0)&m1_pre_topc(esk6_0,esk4_0))&((~v2_struct_0(esk7_0)&m1_pre_topc(esk7_0,esk4_0))&(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,u1_struct_0(esk7_0),u1_struct_0(esk5_0)))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk5_0)))))&(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))=esk7_0&(m1_subset_1(esk9_0,u1_struct_0(esk7_0))&(m1_subset_1(esk10_0,u1_struct_0(esk6_0))&((esk9_0=esk10_0&r1_tmap_1(esk6_0,esk5_0,k3_tmap_1(esk4_0,esk5_0,esk7_0,esk6_0,esk8_0),esk10_0))&~r1_tmap_1(esk7_0,esk5_0,esk8_0,esk9_0)))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).
% 0.20/0.42  cnf(c_0_22, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.42  cnf(c_0_23, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.42  cnf(c_0_24, negated_conjecture, (m1_pre_topc(esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.42  cnf(c_0_25, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.42  fof(c_0_26, plain, ![X43, X44]:((v1_pre_topc(g1_pre_topc(u1_struct_0(X44),u1_pre_topc(X44)))|~m1_pre_topc(X44,X43)|~l1_pre_topc(X43))&(m1_pre_topc(g1_pre_topc(u1_struct_0(X44),u1_pre_topc(X44)),X43)|~m1_pre_topc(X44,X43)|~l1_pre_topc(X43))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tmap_1])])])])).
% 0.20/0.42  fof(c_0_27, plain, ![X38, X39, X40, X41, X42]:(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38)|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)|(~m1_pre_topc(X40,X38)|(~m1_pre_topc(X41,X38)|(~v1_funct_1(X42)|~v1_funct_2(X42,u1_struct_0(X40),u1_struct_0(X39))|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X40),u1_struct_0(X39))))|(~m1_pre_topc(X41,X40)|k3_tmap_1(X38,X39,X40,X41,X42)=k2_partfun1(u1_struct_0(X40),u1_struct_0(X39),X42,u1_struct_0(X41)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).
% 0.20/0.42  fof(c_0_28, plain, ![X57, X58, X59]:(~v2_pre_topc(X57)|~l1_pre_topc(X57)|(~m1_pre_topc(X58,X57)|(~m1_pre_topc(X59,X58)|m1_pre_topc(X59,X57)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.20/0.42  cnf(c_0_29, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.42  cnf(c_0_30, negated_conjecture, (g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))=esk7_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.42  cnf(c_0_31, negated_conjecture, (l1_pre_topc(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])])).
% 0.20/0.42  fof(c_0_32, plain, ![X50]:(~l1_pre_topc(X50)|m1_pre_topc(X50,X50)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.20/0.42  cnf(c_0_33, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.42  cnf(c_0_34, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.42  cnf(c_0_35, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.42  cnf(c_0_36, negated_conjecture, (m1_pre_topc(X1,esk7_0)|~m1_pre_topc(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])])).
% 0.20/0.42  cnf(c_0_37, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.42  cnf(c_0_38, negated_conjecture, (m1_pre_topc(esk7_0,X1)|~m1_pre_topc(esk6_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_33, c_0_30])).
% 0.20/0.42  fof(c_0_39, plain, ![X11, X12]:(~v2_pre_topc(X11)|~l1_pre_topc(X11)|(~m1_pre_topc(X12,X11)|v2_pre_topc(X12))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.20/0.42  cnf(c_0_40, plain, (k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|v2_struct_0(X1)|v2_struct_0(X2)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X5)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X3,X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(csr,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.42  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk5_0))))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.42  cnf(c_0_42, negated_conjecture, (v1_funct_2(esk8_0,u1_struct_0(esk7_0),u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.42  cnf(c_0_43, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.42  cnf(c_0_44, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.42  cnf(c_0_45, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.42  cnf(c_0_46, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.42  cnf(c_0_47, negated_conjecture, (m1_pre_topc(esk6_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_31])])).
% 0.20/0.42  cnf(c_0_48, negated_conjecture, (m1_pre_topc(esk7_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_37]), c_0_31])])).
% 0.20/0.42  cnf(c_0_49, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.42  cnf(c_0_50, negated_conjecture, (m1_pre_topc(esk7_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.42  cnf(c_0_51, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.42  fof(c_0_52, plain, ![X25, X26, X27, X28]:((X25=X27|g1_pre_topc(X25,X26)!=g1_pre_topc(X27,X28)|~m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(X25))))&(X26=X28|g1_pre_topc(X25,X26)!=g1_pre_topc(X27,X28)|~m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(X25))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).
% 0.20/0.42  fof(c_0_53, plain, ![X24]:(~l1_pre_topc(X24)|m1_subset_1(u1_pre_topc(X24),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X24))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.20/0.42  fof(c_0_54, plain, ![X10]:(~l1_pre_topc(X10)|(~v1_pre_topc(X10)|X10=g1_pre_topc(u1_struct_0(X10),u1_pre_topc(X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).
% 0.20/0.42  cnf(c_0_55, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.42  fof(c_0_56, plain, ![X34, X35, X36, X37]:(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|(~v1_funct_1(X36)|~v1_funct_2(X36,u1_struct_0(X34),u1_struct_0(X35))|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(X35))))|(~m1_pre_topc(X37,X34)|k2_tmap_1(X34,X35,X36,X37)=k2_partfun1(u1_struct_0(X34),u1_struct_0(X35),X36,u1_struct_0(X37)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.20/0.42  cnf(c_0_57, negated_conjecture, (k3_tmap_1(X1,esk5_0,esk7_0,X2,esk8_0)=k2_partfun1(u1_struct_0(esk7_0),u1_struct_0(esk5_0),esk8_0,u1_struct_0(X2))|v2_struct_0(X1)|~m1_pre_topc(X2,esk7_0)|~m1_pre_topc(esk7_0,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42]), c_0_43]), c_0_44]), c_0_45])]), c_0_46])).
% 0.20/0.42  cnf(c_0_58, negated_conjecture, (m1_pre_topc(esk6_0,X1)|~m1_pre_topc(esk7_0,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_35, c_0_47])).
% 0.20/0.42  cnf(c_0_59, negated_conjecture, (m1_pre_topc(esk7_0,esk7_0)), inference(spm,[status(thm)],[c_0_36, c_0_48])).
% 0.20/0.42  cnf(c_0_60, negated_conjecture, (v2_pre_topc(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), c_0_25])])).
% 0.20/0.42  cnf(c_0_61, negated_conjecture, (l1_pre_topc(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_50]), c_0_25])])).
% 0.20/0.42  cnf(c_0_62, plain, (m1_pre_topc(X1,X2)|~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.42  cnf(c_0_63, plain, (X1=X2|g1_pre_topc(X3,X1)!=g1_pre_topc(X4,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.42  cnf(c_0_64, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.20/0.42  cnf(c_0_65, plain, (X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)|~v1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.42  cnf(c_0_66, negated_conjecture, (v1_pre_topc(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_24]), c_0_30]), c_0_25])])).
% 0.20/0.42  cnf(c_0_67, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.20/0.42  cnf(c_0_68, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.42  cnf(c_0_69, negated_conjecture, (k3_tmap_1(X1,esk5_0,esk7_0,esk6_0,esk8_0)=k2_partfun1(u1_struct_0(esk7_0),u1_struct_0(esk5_0),esk8_0,u1_struct_0(esk6_0))|v2_struct_0(X1)|~m1_pre_topc(esk7_0,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59]), c_0_60]), c_0_61])])).
% 0.20/0.42  cnf(c_0_70, negated_conjecture, (m1_pre_topc(X1,esk6_0)|~m1_pre_topc(X1,esk7_0)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_30]), c_0_31])])).
% 0.20/0.42  cnf(c_0_71, negated_conjecture, (v2_pre_topc(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_24]), c_0_51]), c_0_25])])).
% 0.20/0.42  cnf(c_0_72, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.42  cnf(c_0_73, plain, (u1_pre_topc(X1)=X2|g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))!=g1_pre_topc(X3,X2)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.20/0.42  cnf(c_0_74, negated_conjecture, (g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_61])])).
% 0.20/0.42  cnf(c_0_75, negated_conjecture, (k2_partfun1(u1_struct_0(esk7_0),u1_struct_0(esk5_0),esk8_0,u1_struct_0(X1))=k2_tmap_1(esk7_0,esk5_0,esk8_0,X1)|~m1_pre_topc(X1,esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_41]), c_0_42]), c_0_43]), c_0_44]), c_0_60]), c_0_45]), c_0_61])]), c_0_46]), c_0_68])).
% 0.20/0.42  cnf(c_0_76, negated_conjecture, (k2_partfun1(u1_struct_0(esk7_0),u1_struct_0(esk5_0),esk8_0,u1_struct_0(esk6_0))=k3_tmap_1(esk6_0,esk5_0,esk7_0,esk6_0,esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71]), c_0_31]), c_0_59]), c_0_61])]), c_0_72])).
% 0.20/0.42  cnf(c_0_77, negated_conjecture, (u1_pre_topc(esk7_0)=X1|g1_pre_topc(X2,X1)!=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_61])])).
% 0.20/0.42  fof(c_0_78, plain, ![X51, X52, X53, X54, X55, X56]:((~r1_tmap_1(X52,X51,X53,X55)|r1_tmap_1(X54,X51,k2_tmap_1(X52,X51,X53,X54),X56)|X55!=X56|~m1_subset_1(X56,u1_struct_0(X54))|~m1_subset_1(X55,u1_struct_0(X52))|(v2_struct_0(X54)|~v1_tsep_1(X54,X52)|~m1_pre_topc(X54,X52))|(~v1_funct_1(X53)|~v1_funct_2(X53,u1_struct_0(X52),u1_struct_0(X51))|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X52),u1_struct_0(X51)))))|(v2_struct_0(X52)|~v2_pre_topc(X52)|~l1_pre_topc(X52))|(v2_struct_0(X51)|~v2_pre_topc(X51)|~l1_pre_topc(X51)))&(~r1_tmap_1(X54,X51,k2_tmap_1(X52,X51,X53,X54),X56)|r1_tmap_1(X52,X51,X53,X55)|X55!=X56|~m1_subset_1(X56,u1_struct_0(X54))|~m1_subset_1(X55,u1_struct_0(X52))|(v2_struct_0(X54)|~v1_tsep_1(X54,X52)|~m1_pre_topc(X54,X52))|(~v1_funct_1(X53)|~v1_funct_2(X53,u1_struct_0(X52),u1_struct_0(X51))|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X52),u1_struct_0(X51)))))|(v2_struct_0(X52)|~v2_pre_topc(X52)|~l1_pre_topc(X52))|(v2_struct_0(X51)|~v2_pre_topc(X51)|~l1_pre_topc(X51)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t67_tmap_1])])])])])).
% 0.20/0.42  fof(c_0_79, plain, ![X29, X30, X31]:(v2_struct_0(X29)|~l1_pre_topc(X29)|(v2_struct_0(X30)|~m1_pre_topc(X30,X29)|(~m1_subset_1(X31,u1_struct_0(X30))|m1_subset_1(X31,u1_struct_0(X29))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).
% 0.20/0.42  cnf(c_0_80, negated_conjecture, (k3_tmap_1(esk6_0,esk5_0,esk7_0,esk6_0,esk8_0)=k2_tmap_1(esk7_0,esk5_0,esk8_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_47])])).
% 0.20/0.42  cnf(c_0_81, negated_conjecture, (m1_pre_topc(X1,X2)|~m1_pre_topc(esk6_0,X2)|~m1_pre_topc(X1,esk7_0)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_35, c_0_70])).
% 0.20/0.42  cnf(c_0_82, negated_conjecture, (u1_pre_topc(esk6_0)=u1_pre_topc(esk7_0)), inference(spm,[status(thm)],[c_0_77, c_0_30])).
% 0.20/0.42  cnf(c_0_83, plain, (r1_tmap_1(X3,X2,X4,X6)|v2_struct_0(X1)|v2_struct_0(X3)|v2_struct_0(X2)|~r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|X6!=X5|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X6,u1_struct_0(X3))|~v1_tsep_1(X1,X3)|~m1_pre_topc(X1,X3)|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.20/0.42  cnf(c_0_84, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(X3,u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.20/0.42  cnf(c_0_85, negated_conjecture, (r1_tmap_1(esk6_0,esk5_0,k3_tmap_1(esk4_0,esk5_0,esk7_0,esk6_0,esk8_0),esk10_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.42  cnf(c_0_86, negated_conjecture, (esk9_0=esk10_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.42  cnf(c_0_87, negated_conjecture, (k3_tmap_1(X1,esk5_0,esk7_0,esk6_0,esk8_0)=k2_tmap_1(esk7_0,esk5_0,esk8_0,esk6_0)|v2_struct_0(X1)|~m1_pre_topc(esk7_0,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_76]), c_0_80])).
% 0.20/0.42  cnf(c_0_88, negated_conjecture, (m1_pre_topc(X1,esk4_0)|~m1_pre_topc(X1,esk7_0)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_24]), c_0_51]), c_0_25])])).
% 0.20/0.42  cnf(c_0_89, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.42  fof(c_0_90, plain, ![X45, X46, X47]:((~v1_tsep_1(X46,X45)|~m1_pre_topc(X46,X45)|v3_pre_topc(X47,X45)|X47!=u1_struct_0(X46)|~m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X45)))|~m1_pre_topc(X46,X45)|(~v2_pre_topc(X45)|~l1_pre_topc(X45)))&((v1_tsep_1(X46,X45)|~v3_pre_topc(X47,X45)|X47!=u1_struct_0(X46)|~m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X45)))|~m1_pre_topc(X46,X45)|(~v2_pre_topc(X45)|~l1_pre_topc(X45)))&(m1_pre_topc(X46,X45)|~v3_pre_topc(X47,X45)|X47!=u1_struct_0(X46)|~m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X45)))|~m1_pre_topc(X46,X45)|(~v2_pre_topc(X45)|~l1_pre_topc(X45))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tsep_1])])])])).
% 0.20/0.42  fof(c_0_91, plain, ![X48, X49]:(~l1_pre_topc(X48)|(~m1_pre_topc(X49,X48)|m1_subset_1(u1_struct_0(X49),k1_zfmisc_1(u1_struct_0(X48))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.20/0.42  fof(c_0_92, plain, ![X13, X14, X15, X16]:((((r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))|~v2_pre_topc(X13)|~l1_pre_topc(X13))&(~m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))|(~r1_tarski(X14,u1_pre_topc(X13))|r2_hidden(k5_setfam_1(u1_struct_0(X13),X14),u1_pre_topc(X13)))|~v2_pre_topc(X13)|~l1_pre_topc(X13)))&(~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))|(~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X13)))|(~r2_hidden(X15,u1_pre_topc(X13))|~r2_hidden(X16,u1_pre_topc(X13))|r2_hidden(k9_subset_1(u1_struct_0(X13),X15,X16),u1_pre_topc(X13))))|~v2_pre_topc(X13)|~l1_pre_topc(X13)))&(((m1_subset_1(esk2_1(X13),k1_zfmisc_1(u1_struct_0(X13)))|(m1_subset_1(esk1_1(X13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))|~r2_hidden(u1_struct_0(X13),u1_pre_topc(X13)))|v2_pre_topc(X13)|~l1_pre_topc(X13))&((m1_subset_1(esk3_1(X13),k1_zfmisc_1(u1_struct_0(X13)))|(m1_subset_1(esk1_1(X13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))|~r2_hidden(u1_struct_0(X13),u1_pre_topc(X13)))|v2_pre_topc(X13)|~l1_pre_topc(X13))&(((r2_hidden(esk2_1(X13),u1_pre_topc(X13))|(m1_subset_1(esk1_1(X13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))|~r2_hidden(u1_struct_0(X13),u1_pre_topc(X13)))|v2_pre_topc(X13)|~l1_pre_topc(X13))&(r2_hidden(esk3_1(X13),u1_pre_topc(X13))|(m1_subset_1(esk1_1(X13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))|~r2_hidden(u1_struct_0(X13),u1_pre_topc(X13)))|v2_pre_topc(X13)|~l1_pre_topc(X13)))&(~r2_hidden(k9_subset_1(u1_struct_0(X13),esk2_1(X13),esk3_1(X13)),u1_pre_topc(X13))|(m1_subset_1(esk1_1(X13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))|~r2_hidden(u1_struct_0(X13),u1_pre_topc(X13)))|v2_pre_topc(X13)|~l1_pre_topc(X13)))))&(((m1_subset_1(esk2_1(X13),k1_zfmisc_1(u1_struct_0(X13)))|(r1_tarski(esk1_1(X13),u1_pre_topc(X13))|~r2_hidden(u1_struct_0(X13),u1_pre_topc(X13)))|v2_pre_topc(X13)|~l1_pre_topc(X13))&((m1_subset_1(esk3_1(X13),k1_zfmisc_1(u1_struct_0(X13)))|(r1_tarski(esk1_1(X13),u1_pre_topc(X13))|~r2_hidden(u1_struct_0(X13),u1_pre_topc(X13)))|v2_pre_topc(X13)|~l1_pre_topc(X13))&(((r2_hidden(esk2_1(X13),u1_pre_topc(X13))|(r1_tarski(esk1_1(X13),u1_pre_topc(X13))|~r2_hidden(u1_struct_0(X13),u1_pre_topc(X13)))|v2_pre_topc(X13)|~l1_pre_topc(X13))&(r2_hidden(esk3_1(X13),u1_pre_topc(X13))|(r1_tarski(esk1_1(X13),u1_pre_topc(X13))|~r2_hidden(u1_struct_0(X13),u1_pre_topc(X13)))|v2_pre_topc(X13)|~l1_pre_topc(X13)))&(~r2_hidden(k9_subset_1(u1_struct_0(X13),esk2_1(X13),esk3_1(X13)),u1_pre_topc(X13))|(r1_tarski(esk1_1(X13),u1_pre_topc(X13))|~r2_hidden(u1_struct_0(X13),u1_pre_topc(X13)))|v2_pre_topc(X13)|~l1_pre_topc(X13)))))&((m1_subset_1(esk2_1(X13),k1_zfmisc_1(u1_struct_0(X13)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X13),esk1_1(X13)),u1_pre_topc(X13))|~r2_hidden(u1_struct_0(X13),u1_pre_topc(X13)))|v2_pre_topc(X13)|~l1_pre_topc(X13))&((m1_subset_1(esk3_1(X13),k1_zfmisc_1(u1_struct_0(X13)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X13),esk1_1(X13)),u1_pre_topc(X13))|~r2_hidden(u1_struct_0(X13),u1_pre_topc(X13)))|v2_pre_topc(X13)|~l1_pre_topc(X13))&(((r2_hidden(esk2_1(X13),u1_pre_topc(X13))|(~r2_hidden(k5_setfam_1(u1_struct_0(X13),esk1_1(X13)),u1_pre_topc(X13))|~r2_hidden(u1_struct_0(X13),u1_pre_topc(X13)))|v2_pre_topc(X13)|~l1_pre_topc(X13))&(r2_hidden(esk3_1(X13),u1_pre_topc(X13))|(~r2_hidden(k5_setfam_1(u1_struct_0(X13),esk1_1(X13)),u1_pre_topc(X13))|~r2_hidden(u1_struct_0(X13),u1_pre_topc(X13)))|v2_pre_topc(X13)|~l1_pre_topc(X13)))&(~r2_hidden(k9_subset_1(u1_struct_0(X13),esk2_1(X13),esk3_1(X13)),u1_pre_topc(X13))|(~r2_hidden(k5_setfam_1(u1_struct_0(X13),esk1_1(X13)),u1_pre_topc(X13))|~r2_hidden(u1_struct_0(X13),u1_pre_topc(X13)))|v2_pre_topc(X13)|~l1_pre_topc(X13)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 0.20/0.42  cnf(c_0_93, plain, (X1=X2|g1_pre_topc(X1,X3)!=g1_pre_topc(X2,X4)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.42  cnf(c_0_94, negated_conjecture, (m1_subset_1(u1_pre_topc(esk7_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_82]), c_0_31])])).
% 0.20/0.42  cnf(c_0_95, negated_conjecture, (g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk7_0))=esk7_0), inference(rw,[status(thm)],[c_0_30, c_0_82])).
% 0.20/0.42  cnf(c_0_96, plain, (r1_tmap_1(X1,X2,X3,X4)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X5)|~r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X4)|~v1_tsep_1(X5,X1)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(X3)|~m1_pre_topc(X5,X1)|~v2_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X1)|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X4,u1_struct_0(X5))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_83]), c_0_84])).
% 0.20/0.42  cnf(c_0_97, negated_conjecture, (r1_tmap_1(esk6_0,esk5_0,k3_tmap_1(esk4_0,esk5_0,esk7_0,esk6_0,esk8_0),esk9_0)), inference(rw,[status(thm)],[c_0_85, c_0_86])).
% 0.20/0.42  cnf(c_0_98, negated_conjecture, (k3_tmap_1(esk4_0,esk5_0,esk7_0,esk6_0,esk8_0)=k2_tmap_1(esk7_0,esk5_0,esk8_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_51]), c_0_25]), c_0_59]), c_0_61])]), c_0_89])).
% 0.20/0.42  cnf(c_0_99, negated_conjecture, (m1_subset_1(esk10_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.42  cnf(c_0_100, plain, (v1_tsep_1(X1,X2)|~v3_pre_topc(X3,X2)|X3!=u1_struct_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.20/0.42  cnf(c_0_101, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_91])).
% 0.20/0.42  fof(c_0_102, plain, ![X20, X21]:((~v3_pre_topc(X21,X20)|r2_hidden(X21,u1_pre_topc(X20))|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|~l1_pre_topc(X20))&(~r2_hidden(X21,u1_pre_topc(X20))|v3_pre_topc(X21,X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|~l1_pre_topc(X20))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.20/0.42  cnf(c_0_103, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_92])).
% 0.20/0.42  cnf(c_0_104, negated_conjecture, (u1_struct_0(esk6_0)=X1|g1_pre_topc(X1,X2)!=esk7_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_95])).
% 0.20/0.42  cnf(c_0_105, negated_conjecture, (r1_tmap_1(esk7_0,esk5_0,esk8_0,X1)|v2_struct_0(X2)|~r1_tmap_1(X2,esk5_0,k2_tmap_1(esk7_0,esk5_0,esk8_0,X2),X1)|~v1_tsep_1(X2,esk7_0)|~m1_pre_topc(X2,esk7_0)|~m1_subset_1(X1,u1_struct_0(X2))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_41]), c_0_42]), c_0_43]), c_0_60]), c_0_44]), c_0_61]), c_0_45])]), c_0_46]), c_0_68])).
% 0.20/0.42  cnf(c_0_106, negated_conjecture, (r1_tmap_1(esk6_0,esk5_0,k2_tmap_1(esk7_0,esk5_0,esk8_0,esk6_0),esk9_0)), inference(rw,[status(thm)],[c_0_97, c_0_98])).
% 0.20/0.42  cnf(c_0_107, negated_conjecture, (m1_subset_1(esk9_0,u1_struct_0(esk6_0))), inference(rw,[status(thm)],[c_0_99, c_0_86])).
% 0.20/0.42  cnf(c_0_108, negated_conjecture, (~r1_tmap_1(esk7_0,esk5_0,esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.42  cnf(c_0_109, plain, (v1_tsep_1(X1,X2)|~v3_pre_topc(u1_struct_0(X1),X2)|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_100]), c_0_101])).
% 0.20/0.42  cnf(c_0_110, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_102])).
% 0.20/0.42  cnf(c_0_111, negated_conjecture, (r2_hidden(u1_struct_0(esk6_0),u1_pre_topc(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_82]), c_0_71]), c_0_31])])).
% 0.20/0.42  cnf(c_0_112, negated_conjecture, (u1_struct_0(esk6_0)=u1_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_104, c_0_74])).
% 0.20/0.42  cnf(c_0_113, negated_conjecture, (~v1_tsep_1(esk6_0,esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_47]), c_0_107])]), c_0_108]), c_0_72])).
% 0.20/0.42  cnf(c_0_114, plain, (v1_tsep_1(X1,X2)|~r2_hidden(u1_struct_0(X1),u1_pre_topc(X2))|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_110]), c_0_101])).
% 0.20/0.42  cnf(c_0_115, negated_conjecture, (r2_hidden(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))), inference(rw,[status(thm)],[c_0_111, c_0_112])).
% 0.20/0.42  cnf(c_0_116, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_114]), c_0_112]), c_0_115]), c_0_47]), c_0_60]), c_0_61])]), ['proof']).
% 0.20/0.42  # SZS output end CNFRefutation
% 0.20/0.42  # Proof object total steps             : 117
% 0.20/0.42  # Proof object clause steps            : 80
% 0.20/0.42  # Proof object formula steps           : 37
% 0.20/0.42  # Proof object conjectures             : 57
% 0.20/0.42  # Proof object clause conjectures      : 54
% 0.20/0.42  # Proof object formula conjectures     : 3
% 0.20/0.42  # Proof object initial clauses used    : 38
% 0.20/0.42  # Proof object initial formulas used   : 18
% 0.20/0.42  # Proof object generating inferences   : 32
% 0.20/0.42  # Proof object simplifying inferences  : 101
% 0.20/0.42  # Training examples: 0 positive, 0 negative
% 0.20/0.42  # Parsed axioms                        : 20
% 0.20/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.42  # Initial clauses                      : 62
% 0.20/0.42  # Removed in clause preprocessing      : 2
% 0.20/0.42  # Initial clauses in saturation        : 60
% 0.20/0.42  # Processed clauses                    : 468
% 0.20/0.42  # ...of these trivial                  : 28
% 0.20/0.42  # ...subsumed                          : 147
% 0.20/0.42  # ...remaining for further processing  : 293
% 0.20/0.42  # Other redundant clauses eliminated   : 4
% 0.20/0.42  # Clauses deleted for lack of memory   : 0
% 0.20/0.42  # Backward-subsumed                    : 6
% 0.20/0.42  # Backward-rewritten                   : 20
% 0.20/0.42  # Generated clauses                    : 1140
% 0.20/0.42  # ...of the previous two non-trivial   : 714
% 0.20/0.42  # Contextual simplify-reflections      : 27
% 0.20/0.42  # Paramodulations                      : 1132
% 0.20/0.42  # Factorizations                       : 0
% 0.20/0.42  # Equation resolutions                 : 8
% 0.20/0.42  # Propositional unsat checks           : 0
% 0.20/0.42  #    Propositional check models        : 0
% 0.20/0.42  #    Propositional check unsatisfiable : 0
% 0.20/0.42  #    Propositional clauses             : 0
% 0.20/0.42  #    Propositional clauses after purity: 0
% 0.20/0.42  #    Propositional unsat core size     : 0
% 0.20/0.42  #    Propositional preprocessing time  : 0.000
% 0.20/0.42  #    Propositional encoding time       : 0.000
% 0.20/0.42  #    Propositional solver time         : 0.000
% 0.20/0.42  #    Success case prop preproc time    : 0.000
% 0.20/0.42  #    Success case prop encoding time   : 0.000
% 0.20/0.42  #    Success case prop solver time     : 0.000
% 0.20/0.42  # Current number of processed clauses  : 203
% 0.20/0.42  #    Positive orientable unit clauses  : 38
% 0.20/0.42  #    Positive unorientable unit clauses: 0
% 0.20/0.42  #    Negative unit clauses             : 6
% 0.20/0.42  #    Non-unit-clauses                  : 159
% 0.20/0.42  # Current number of unprocessed clauses: 350
% 0.20/0.42  # ...number of literals in the above   : 1483
% 0.20/0.42  # Current number of archived formulas  : 0
% 0.20/0.42  # Current number of archived clauses   : 87
% 0.20/0.42  # Clause-clause subsumption calls (NU) : 9614
% 0.20/0.42  # Rec. Clause-clause subsumption calls : 3454
% 0.20/0.42  # Non-unit clause-clause subsumptions  : 179
% 0.20/0.42  # Unit Clause-clause subsumption calls : 440
% 0.20/0.42  # Rewrite failures with RHS unbound    : 0
% 0.20/0.42  # BW rewrite match attempts            : 38
% 0.20/0.42  # BW rewrite match successes           : 10
% 0.20/0.42  # Condensation attempts                : 0
% 0.20/0.42  # Condensation successes               : 0
% 0.20/0.42  # Termbank termtop insertions          : 35395
% 0.20/0.42  
% 0.20/0.42  # -------------------------------------------------
% 0.20/0.42  # User time                : 0.066 s
% 0.20/0.42  # System time              : 0.007 s
% 0.20/0.42  # Total time               : 0.073 s
% 0.20/0.42  # Maximum resident set size: 1616 pages
%------------------------------------------------------------------------------
