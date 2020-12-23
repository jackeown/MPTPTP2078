%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:05 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :  241 (1992 expanded)
%              Number of clauses        :  164 ( 524 expanded)
%              Number of leaves         :   20 ( 616 expanded)
%              Depth                    :   26
%              Number of atoms          : 1357 (23612 expanded)
%              Number of equality atoms :  459 (3987 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal clause size      :   30 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)
                  & v8_pre_topc(X1)
                  & v1_compts_1(X0) )
               => v3_tops_2(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v5_pre_topc(X2,X0,X1)
                    & v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)
                    & v8_pre_topc(X1)
                    & v1_compts_1(X0) )
                 => v3_tops_2(X2,X0,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_2(X2,X0,X1)
              & v5_pre_topc(X2,X0,X1)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)
              & v8_pre_topc(X1)
              & v1_compts_1(X0)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_2(X2,X0,X1)
              & v5_pre_topc(X2,X0,X1)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)
              & v8_pre_topc(X1)
              & v1_compts_1(X0)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v3_tops_2(X2,X0,X1)
          & v5_pre_topc(X2,X0,X1)
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
          & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)
          & v8_pre_topc(X1)
          & v1_compts_1(X0)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ~ v3_tops_2(sK4,X0,X1)
        & v5_pre_topc(sK4,X0,X1)
        & v2_funct_1(sK4)
        & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) = k2_struct_0(X1)
        & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) = k2_struct_0(X0)
        & v8_pre_topc(X1)
        & v1_compts_1(X0)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_2(X2,X0,X1)
              & v5_pre_topc(X2,X0,X1)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)
              & v8_pre_topc(X1)
              & v1_compts_1(X0)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ~ v3_tops_2(X2,X0,sK3)
            & v5_pre_topc(X2,X0,sK3)
            & v2_funct_1(X2)
            & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2) = k2_struct_0(sK3)
            & k1_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2) = k2_struct_0(X0)
            & v8_pre_topc(sK3)
            & v1_compts_1(X0)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v3_tops_2(X2,X0,X1)
                & v5_pre_topc(X2,X0,X1)
                & v2_funct_1(X2)
                & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)
                & v8_pre_topc(X1)
                & v1_compts_1(X0)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_2(X2,sK2,X1)
              & v5_pre_topc(X2,sK2,X1)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & k1_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2) = k2_struct_0(sK2)
              & v8_pre_topc(X1)
              & v1_compts_1(sK2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ~ v3_tops_2(sK4,sK2,sK3)
    & v5_pre_topc(sK4,sK2,sK3)
    & v2_funct_1(sK4)
    & k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3)
    & k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2)
    & v8_pre_topc(sK3)
    & v1_compts_1(sK2)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f42,f58,f57,f56])).

fof(f99,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f59])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f98,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f59])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v3_tops_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( v4_pre_topc(X3,X0)
                      <=> v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) ) )
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( ( v4_pre_topc(X3,X0)
                      <=> v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) )
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( ( v4_pre_topc(X3,X0)
                      <=> v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) )
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tops_2(X2,X0,X1)
                  | ? [X3] :
                      ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                        | ~ v4_pre_topc(X3,X0) )
                      & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                        | v4_pre_topc(X3,X0) )
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v2_funct_1(X2)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                  | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) )
                & ( ( ! [X3] :
                        ( ( ( v4_pre_topc(X3,X0)
                            | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) )
                          & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                            | ~ v4_pre_topc(X3,X0) ) )
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    & v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                  | ~ v3_tops_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tops_2(X2,X0,X1)
                  | ? [X3] :
                      ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                        | ~ v4_pre_topc(X3,X0) )
                      & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                        | v4_pre_topc(X3,X0) )
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v2_funct_1(X2)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                  | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) )
                & ( ( ! [X3] :
                        ( ( ( v4_pre_topc(X3,X0)
                            | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) )
                          & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                            | ~ v4_pre_topc(X3,X0) ) )
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    & v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                  | ~ v3_tops_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f51])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tops_2(X2,X0,X1)
                  | ? [X3] :
                      ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                        | ~ v4_pre_topc(X3,X0) )
                      & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                        | v4_pre_topc(X3,X0) )
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v2_funct_1(X2)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                  | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) )
                & ( ( ! [X4] :
                        ( ( ( v4_pre_topc(X4,X0)
                            | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1) )
                          & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1)
                            | ~ v4_pre_topc(X4,X0) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                  | ~ v3_tops_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f52])).

fof(f54,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
            | ~ v4_pre_topc(X3,X0) )
          & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
            | v4_pre_topc(X3,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2)),X1)
          | ~ v4_pre_topc(sK1(X0,X1,X2),X0) )
        & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2)),X1)
          | v4_pre_topc(sK1(X0,X1,X2),X0) )
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tops_2(X2,X0,X1)
                  | ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2)),X1)
                      | ~ v4_pre_topc(sK1(X0,X1,X2),X0) )
                    & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2)),X1)
                      | v4_pre_topc(sK1(X0,X1,X2),X0) )
                    & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v2_funct_1(X2)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                  | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) )
                & ( ( ! [X4] :
                        ( ( ( v4_pre_topc(X4,X0)
                            | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1) )
                          & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1)
                            | ~ v4_pre_topc(X4,X0) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                  | ~ v3_tops_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f53,f54])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v3_tops_2(X2,X0,X1)
      | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f94,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f96,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f97,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f104,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f103,plain,(
    k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f102,plain,(
    k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f106,plain,(
    ~ v3_tops_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f93,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f82,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f81,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( v4_pre_topc(X3,X1)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      | ~ v4_pre_topc(X3,X1)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f47])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
        & v4_pre_topc(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
                    & v4_pre_topc(sK0(X0,X1,X2),X1)
                    & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f48,f49])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f105,plain,(
    v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( v3_tops_2(X2,X0,X1)
      | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2)),X1)
      | ~ v4_pre_topc(sK1(X0,X1,X2),X0)
      | ~ v2_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v5_pre_topc(X2,X0,X1)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & v8_pre_topc(X1)
                  & v1_compts_1(X0) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( v4_pre_topc(X3,X0)
                     => v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v5_pre_topc(X2,X0,X1)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ v8_pre_topc(X1)
              | ~ v1_compts_1(X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v5_pre_topc(X2,X0,X1)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ v8_pre_topc(X1)
              | ~ v1_compts_1(X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v5_pre_topc(X2,X0,X1)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ v8_pre_topc(X1)
      | ~ v1_compts_1(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f101,plain,(
    v8_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f95,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f100,plain,(
    v1_compts_1(sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f92,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v3_tops_2(X2,X0,X1)
      | v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2)),X1)
      | v4_pre_topc(sK1(X0,X1,X2),X0)
      | ~ v2_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_3924,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3932,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4679,plain,
    ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_3924,c_3932])).

cnf(c_40,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_25,plain,
    ( v3_tops_2(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_44,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_880,plain,
    ( v3_tops_2(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_44])).

cnf(c_881,plain,
    ( v3_tops_2(X0,X1,sK3)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | m1_subset_1(sK1(X1,sK3,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(sK3)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_880])).

cnf(c_42,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_885,plain,
    ( ~ l1_pre_topc(X1)
    | m1_subset_1(sK1(X1,sK3,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | v3_tops_2(X0,X1,sK3)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(sK3)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_881,c_42])).

cnf(c_886,plain,
    ( v3_tops_2(X0,X1,sK3)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | m1_subset_1(sK1(X1,sK3,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(sK3)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_885])).

cnf(c_1592,plain,
    ( v3_tops_2(X0,X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | m1_subset_1(sK1(X1,sK3,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(sK3)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(X1)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_40,c_886])).

cnf(c_1593,plain,
    ( v3_tops_2(sK4,X0,sK3)
    | m1_subset_1(sK1(X0,sK3,sK4),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(sK4)
    | ~ v2_funct_1(sK4)
    | k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | k1_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1592])).

cnf(c_41,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_34,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1597,plain,
    ( v3_tops_2(sK4,X0,sK3)
    | m1_subset_1(sK1(X0,sK3,sK4),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
    | ~ l1_pre_topc(X0)
    | k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | k1_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1593,c_41,c_34])).

cnf(c_3914,plain,
    ( k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | k1_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | v3_tops_2(sK4,X0,sK3) = iProver_top
    | m1_subset_1(sK1(X0,sK3,sK4),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1597])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3931,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4375,plain,
    ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_3924,c_3931])).

cnf(c_35,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_4423,plain,
    ( k2_struct_0(sK3) = k2_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_4375,c_35])).

cnf(c_5149,plain,
    ( k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_relat_1(sK4)
    | k1_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | v3_tops_2(sK4,X0,sK3) = iProver_top
    | m1_subset_1(sK1(X0,sK3,sK4),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3914,c_4423])).

cnf(c_5153,plain,
    ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_relat_1(sK4)
    | k2_struct_0(sK2) != k1_relat_1(sK4)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | v3_tops_2(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(sK1(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4679,c_5149])).

cnf(c_36,negated_conjecture,
    ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_4813,plain,
    ( k2_struct_0(sK2) = k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_4679,c_36])).

cnf(c_5154,plain,
    ( u1_struct_0(sK2) != u1_struct_0(sK2)
    | k2_relat_1(sK4) != k2_relat_1(sK4)
    | k1_relat_1(sK4) != k1_relat_1(sK4)
    | v3_tops_2(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(sK1(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5153,c_4375,c_4813])).

cnf(c_5155,plain,
    ( v3_tops_2(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(sK1(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5154])).

cnf(c_32,negated_conjecture,
    ( ~ v3_tops_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_2265,plain,
    ( m1_subset_1(sK1(X0,sK3,sK4),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
    | ~ l1_pre_topc(X0)
    | k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | k1_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | sK3 != sK3
    | sK2 != X0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_1597])).

cnf(c_2266,plain,
    ( m1_subset_1(sK1(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_pre_topc(sK2)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_2265])).

cnf(c_45,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2268,plain,
    ( m1_subset_1(sK1(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2266,c_45,c_39,c_36,c_35])).

cnf(c_2270,plain,
    ( u1_struct_0(sK2) != u1_struct_0(sK2)
    | m1_subset_1(sK1(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2268])).

cnf(c_3117,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4083,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3117])).

cnf(c_8446,plain,
    ( m1_subset_1(sK1(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5155,c_2270,c_4083])).

cnf(c_3922,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_22,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_21,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_595,plain,
    ( ~ l1_pre_topc(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_22,c_21])).

cnf(c_3921,plain,
    ( k2_struct_0(X0) = u1_struct_0(X0)
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_595])).

cnf(c_5752,plain,
    ( k2_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_3922,c_3921])).

cnf(c_5753,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_5752,c_4813])).

cnf(c_8450,plain,
    ( m1_subset_1(sK1(sK2,sK3,sK4),k1_zfmisc_1(k1_relat_1(sK4))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8446,c_5753])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_3934,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_8452,plain,
    ( r1_tarski(sK1(sK2,sK3,sK4),k1_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8450,c_3934])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1860,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_34])).

cnf(c_1861,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_1860])).

cnf(c_1223,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_34])).

cnf(c_1224,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_1223])).

cnf(c_1863,plain,
    ( ~ v1_relat_1(sK4)
    | ~ r1_tarski(X0,k1_relat_1(sK4))
    | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1861,c_41,c_1224])).

cnf(c_1864,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_1863])).

cnf(c_1881,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X3,k1_relat_1(sK4))
    | k10_relat_1(sK4,k9_relat_1(sK4,X3)) = X3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_1864])).

cnf(c_1882,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_tarski(X2,k1_relat_1(sK4))
    | k10_relat_1(sK4,k9_relat_1(sK4,X2)) = X2 ),
    inference(unflattening,[status(thm)],[c_1881])).

cnf(c_3113,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK4))
    | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1882])).

cnf(c_3908,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3113])).

cnf(c_54,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_3115,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1882])).

cnf(c_3159,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3115])).

cnf(c_3163,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3113])).

cnf(c_3114,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_1882])).

cnf(c_4056,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ sP1_iProver_split ),
    inference(instantiation,[status(thm)],[c_3114])).

cnf(c_4057,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4056])).

cnf(c_4670,plain,
    ( r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
    | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3908,c_54,c_3159,c_3163,c_4057])).

cnf(c_4671,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4670])).

cnf(c_8844,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,sK1(sK2,sK3,sK4))) = sK1(sK2,sK3,sK4) ),
    inference(superposition,[status(thm)],[c_8452,c_4671])).

cnf(c_3923,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_5751,plain,
    ( k2_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_3923,c_3921])).

cnf(c_5754,plain,
    ( u1_struct_0(sK3) = k2_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_5751,c_4423])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_3930,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4808,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_3924,c_3930])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3933,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5295,plain,
    ( m1_subset_1(k9_relat_1(sK4,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4808,c_3933])).

cnf(c_5650,plain,
    ( m1_subset_1(k9_relat_1(sK4,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5295,c_54])).

cnf(c_5926,plain,
    ( m1_subset_1(k9_relat_1(sK4,X0),k1_zfmisc_1(k2_relat_1(sK4))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5754,c_5650])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v4_pre_topc(X3,X2)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1382,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | ~ v4_pre_topc(X3,X2)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_40])).

cnf(c_1383,plain,
    ( ~ v5_pre_topc(sK4,X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X2),X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1382])).

cnf(c_1387,plain,
    ( ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X2),X0)
    | ~ v4_pre_topc(X2,X1)
    | ~ v5_pre_topc(sK4,X0,X1)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1383,c_41])).

cnf(c_1388,plain,
    ( ~ v5_pre_topc(sK4,X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X2),X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_1387])).

cnf(c_3920,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | v5_pre_topc(sK4,X1,X0) != iProver_top
    | v4_pre_topc(X2,X0) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK4,X2),X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1388])).

cnf(c_4998,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK3)
    | v5_pre_topc(sK4,sK2,X0) != iProver_top
    | v4_pre_topc(X1,X0) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(X0),sK4,X1),sK2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3920])).

cnf(c_48,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_4051,plain,
    ( ~ v5_pre_topc(sK4,sK2,X0)
    | ~ v4_pre_topc(X1,X0)
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(X0),sK4,X1),sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1388])).

cnf(c_4052,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | v5_pre_topc(sK4,sK2,X0) != iProver_top
    | v4_pre_topc(X1,X0) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(X0),sK4,X1),sK2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4051])).

cnf(c_6925,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(X0),sK4,X1),sK2) = iProver_top
    | v4_pre_topc(X1,X0) != iProver_top
    | v5_pre_topc(sK4,sK2,X0) != iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4998,c_48,c_4052,c_4083])).

cnf(c_6926,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK3)
    | v5_pre_topc(sK4,sK2,X0) != iProver_top
    | v4_pre_topc(X1,X0) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(X0),sK4,X1),sK2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6925])).

cnf(c_6931,plain,
    ( u1_struct_0(X0) != k2_relat_1(sK4)
    | v5_pre_topc(sK4,sK2,X0) != iProver_top
    | v4_pre_topc(X1,X0) != iProver_top
    | v4_pre_topc(k8_relset_1(k1_relat_1(sK4),u1_struct_0(X0),sK4,X1),sK2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6926,c_5753,c_5754])).

cnf(c_6936,plain,
    ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v4_pre_topc(X0,sK3) != iProver_top
    | v4_pre_topc(k8_relset_1(k1_relat_1(sK4),u1_struct_0(sK3),sK4,X0),sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),u1_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5754,c_6931])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_3929,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4746,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k10_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_3924,c_3929])).

cnf(c_5767,plain,
    ( k8_relset_1(k1_relat_1(sK4),u1_struct_0(sK3),sK4,X0) = k10_relat_1(sK4,X0) ),
    inference(demodulation,[status(thm)],[c_5753,c_4746])).

cnf(c_5784,plain,
    ( k8_relset_1(k1_relat_1(sK4),k2_relat_1(sK4),sK4,X0) = k10_relat_1(sK4,X0) ),
    inference(light_normalisation,[status(thm)],[c_5767,c_5754])).

cnf(c_6937,plain,
    ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v4_pre_topc(X0,sK3) != iProver_top
    | v4_pre_topc(k10_relat_1(sK4,X0),sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_relat_1(sK4))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6936,c_5754,c_5784])).

cnf(c_51,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_33,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_58,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_5775,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),u1_struct_0(sK3)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5753,c_3924])).

cnf(c_5776,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5775,c_5754])).

cnf(c_7253,plain,
    ( v4_pre_topc(X0,sK3) != iProver_top
    | v4_pre_topc(k10_relat_1(sK4,X0),sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_relat_1(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6937,c_51,c_58,c_5776])).

cnf(c_7261,plain,
    ( v4_pre_topc(k10_relat_1(sK4,k9_relat_1(sK4,X0)),sK2) = iProver_top
    | v4_pre_topc(k9_relat_1(sK4,X0),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5926,c_7253])).

cnf(c_10107,plain,
    ( v4_pre_topc(sK1(sK2,sK3,sK4),sK2) = iProver_top
    | v4_pre_topc(k9_relat_1(sK4,sK1(sK2,sK3,sK4)),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8844,c_7261])).

cnf(c_23,plain,
    ( v3_tops_2(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK1(X1,X2,X0)),X2)
    | ~ v4_pre_topc(sK1(X1,X2,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_957,plain,
    ( v3_tops_2(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK1(X1,X2,X0)),X2)
    | ~ v4_pre_topc(sK1(X1,X2,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_44])).

cnf(c_958,plain,
    ( v3_tops_2(X0,X1,sK3)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,sK1(X1,sK3,X0)),sK3)
    | ~ v4_pre_topc(sK1(X1,sK3,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(sK3)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_957])).

cnf(c_962,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | ~ v4_pre_topc(sK1(X1,sK3,X0),X1)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,sK1(X1,sK3,X0)),sK3)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | v3_tops_2(X0,X1,sK3)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(sK3)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_958,c_42])).

cnf(c_963,plain,
    ( v3_tops_2(X0,X1,sK3)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,sK1(X1,sK3,X0)),sK3)
    | ~ v4_pre_topc(sK1(X1,sK3,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(sK3)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_962])).

cnf(c_1520,plain,
    ( v3_tops_2(X0,X1,sK3)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,sK1(X1,sK3,X0)),sK3)
    | ~ v4_pre_topc(sK1(X1,sK3,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(sK3)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(X1)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_40,c_963])).

cnf(c_1521,plain,
    ( v3_tops_2(sK4,X0,sK3)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK1(X0,sK3,sK4)),sK3)
    | ~ v4_pre_topc(sK1(X0,sK3,sK4),X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(sK4)
    | ~ v2_funct_1(sK4)
    | k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | k1_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1520])).

cnf(c_1525,plain,
    ( v3_tops_2(sK4,X0,sK3)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK1(X0,sK3,sK4)),sK3)
    | ~ v4_pre_topc(sK1(X0,sK3,sK4),X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
    | ~ l1_pre_topc(X0)
    | k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | k1_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1521,c_41,c_34])).

cnf(c_3916,plain,
    ( k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | k1_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | v3_tops_2(sK4,X0,sK3) = iProver_top
    | v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK1(X0,sK3,sK4)),sK3) != iProver_top
    | v4_pre_topc(sK1(X0,sK3,sK4),X0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1525])).

cnf(c_5056,plain,
    ( k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_relat_1(sK4)
    | k1_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | v3_tops_2(sK4,X0,sK3) = iProver_top
    | v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK1(X0,sK3,sK4)),sK3) != iProver_top
    | v4_pre_topc(sK1(X0,sK3,sK4),X0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3916,c_4423])).

cnf(c_5060,plain,
    ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_relat_1(sK4)
    | k2_struct_0(sK2) != k1_relat_1(sK4)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | v3_tops_2(sK4,sK2,sK3) = iProver_top
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4)),sK3) != iProver_top
    | v4_pre_topc(sK1(sK2,sK3,sK4),sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4679,c_5056])).

cnf(c_5061,plain,
    ( u1_struct_0(sK2) != u1_struct_0(sK2)
    | k2_relat_1(sK4) != k2_relat_1(sK4)
    | k1_relat_1(sK4) != k1_relat_1(sK4)
    | v3_tops_2(sK4,sK2,sK3) = iProver_top
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4)),sK3) != iProver_top
    | v4_pre_topc(sK1(sK2,sK3,sK4),sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5060,c_4375,c_4813])).

cnf(c_5062,plain,
    ( v3_tops_2(sK4,sK2,sK3) = iProver_top
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4)),sK3) != iProver_top
    | v4_pre_topc(sK1(sK2,sK3,sK4),sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5061])).

cnf(c_5063,plain,
    ( v3_tops_2(sK4,sK2,sK3) = iProver_top
    | v4_pre_topc(sK1(sK2,sK3,sK4),sK2) != iProver_top
    | v4_pre_topc(k9_relat_1(sK4,sK1(sK2,sK3,sK4)),sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5062,c_4808])).

cnf(c_2296,plain,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK1(X0,sK3,sK4)),sK3)
    | ~ v4_pre_topc(sK1(X0,sK3,sK4),X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
    | ~ l1_pre_topc(X0)
    | k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | k1_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | sK3 != sK3
    | sK2 != X0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_1525])).

cnf(c_2297,plain,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4)),sK3)
    | ~ v4_pre_topc(sK1(sK2,sK3,sK4),sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_pre_topc(sK2)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_2296])).

cnf(c_2299,plain,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4)),sK3)
    | ~ v4_pre_topc(sK1(sK2,sK3,sK4),sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2297,c_45,c_39,c_36,c_35])).

cnf(c_2301,plain,
    ( u1_struct_0(sK2) != u1_struct_0(sK2)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4)),sK3) != iProver_top
    | v4_pre_topc(sK1(sK2,sK3,sK4),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2299])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v4_pre_topc(X3,X1)
    | v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_compts_1(X1)
    | ~ v8_pre_topc(X2)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_37,negated_conjecture,
    ( v8_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_637,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v4_pre_topc(X3,X1)
    | v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_compts_1(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_37])).

cnf(c_638,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | ~ v5_pre_topc(X0,X1,sK3)
    | ~ v4_pre_topc(X2,X1)
    | v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,X2),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK3)
    | ~ v1_compts_1(X1)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_637])).

cnf(c_43,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_642,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,X2),sK3)
    | ~ v4_pre_topc(X2,X1)
    | ~ v5_pre_topc(X0,X1,sK3)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | ~ v1_compts_1(X1)
    | ~ v1_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_638,c_44,c_43,c_42])).

cnf(c_643,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | ~ v5_pre_topc(X0,X1,sK3)
    | ~ v4_pre_topc(X2,X1)
    | v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,X2),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_642])).

cnf(c_38,negated_conjecture,
    ( v1_compts_1(sK2) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_683,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | ~ v5_pre_topc(X0,X1,sK3)
    | ~ v4_pre_topc(X2,X1)
    | v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,X2),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(sK3)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_643,c_38])).

cnf(c_684,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v5_pre_topc(X0,sK2,sK3)
    | ~ v4_pre_topc(X1,sK2)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0,X1),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(X0)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0) != k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_683])).

cnf(c_46,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_688,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v5_pre_topc(X0,sK2,sK3)
    | ~ v4_pre_topc(X1,sK2)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0,X1),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0) != k2_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_684,c_46,c_45])).

cnf(c_1747,plain,
    ( ~ v5_pre_topc(X0,sK2,sK3)
    | ~ v4_pre_topc(X1,sK2)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0,X1),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0) != k2_struct_0(sK3)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_40,c_688])).

cnf(c_1748,plain,
    ( ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v4_pre_topc(X0,sK2)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK4)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1747])).

cnf(c_1752,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0),sK3)
    | ~ v4_pre_topc(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1748,c_41,c_39,c_35,c_33])).

cnf(c_1753,plain,
    ( ~ v4_pre_topc(X0,sK2)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(renaming,[status(thm)],[c_1752])).

cnf(c_4411,plain,
    ( v4_pre_topc(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4)),sK3)
    | ~ v4_pre_topc(sK1(sK2,sK3,sK4),sK2)
    | ~ m1_subset_1(sK1(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_1753])).

cnf(c_4412,plain,
    ( v4_pre_topc(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4)),sK3) = iProver_top
    | v4_pre_topc(sK1(sK2,sK3,sK4),sK2) != iProver_top
    | m1_subset_1(sK1(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4411])).

cnf(c_6920,plain,
    ( v4_pre_topc(sK1(sK2,sK3,sK4),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5063,c_2270,c_2301,c_4083,c_4412])).

cnf(c_24,plain,
    ( v3_tops_2(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK1(X1,X2,X0)),X2)
    | v4_pre_topc(sK1(X1,X2,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_917,plain,
    ( v3_tops_2(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK1(X1,X2,X0)),X2)
    | v4_pre_topc(sK1(X1,X2,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_44])).

cnf(c_918,plain,
    ( v3_tops_2(X0,X1,sK3)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,sK1(X1,sK3,X0)),sK3)
    | v4_pre_topc(sK1(X1,sK3,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(sK3)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_917])).

cnf(c_922,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | v4_pre_topc(sK1(X1,sK3,X0),X1)
    | v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,sK1(X1,sK3,X0)),sK3)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | v3_tops_2(X0,X1,sK3)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(sK3)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_918,c_42])).

cnf(c_923,plain,
    ( v3_tops_2(X0,X1,sK3)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,sK1(X1,sK3,X0)),sK3)
    | v4_pre_topc(sK1(X1,sK3,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(sK3)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_922])).

cnf(c_1556,plain,
    ( v3_tops_2(X0,X1,sK3)
    | v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,sK1(X1,sK3,X0)),sK3)
    | v4_pre_topc(sK1(X1,sK3,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(sK3)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(X1)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_40,c_923])).

cnf(c_1557,plain,
    ( v3_tops_2(sK4,X0,sK3)
    | v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK1(X0,sK3,sK4)),sK3)
    | v4_pre_topc(sK1(X0,sK3,sK4),X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(sK4)
    | ~ v2_funct_1(sK4)
    | k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | k1_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1556])).

cnf(c_1561,plain,
    ( v3_tops_2(sK4,X0,sK3)
    | v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK1(X0,sK3,sK4)),sK3)
    | v4_pre_topc(sK1(X0,sK3,sK4),X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
    | ~ l1_pre_topc(X0)
    | k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | k1_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1557,c_41,c_34])).

cnf(c_3915,plain,
    ( k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | k1_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | v3_tops_2(sK4,X0,sK3) = iProver_top
    | v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK1(X0,sK3,sK4)),sK3) = iProver_top
    | v4_pre_topc(sK1(X0,sK3,sK4),X0) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1561])).

cnf(c_5396,plain,
    ( k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_relat_1(sK4)
    | k1_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | v3_tops_2(sK4,X0,sK3) = iProver_top
    | v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK1(X0,sK3,sK4)),sK3) = iProver_top
    | v4_pre_topc(sK1(X0,sK3,sK4),X0) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3915,c_4423])).

cnf(c_5400,plain,
    ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_relat_1(sK4)
    | k2_struct_0(sK2) != k1_relat_1(sK4)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | v3_tops_2(sK4,sK2,sK3) = iProver_top
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4)),sK3) = iProver_top
    | v4_pre_topc(sK1(sK2,sK3,sK4),sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4679,c_5396])).

cnf(c_5401,plain,
    ( u1_struct_0(sK2) != u1_struct_0(sK2)
    | k2_relat_1(sK4) != k2_relat_1(sK4)
    | k1_relat_1(sK4) != k1_relat_1(sK4)
    | v3_tops_2(sK4,sK2,sK3) = iProver_top
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4)),sK3) = iProver_top
    | v4_pre_topc(sK1(sK2,sK3,sK4),sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5400,c_4375,c_4813])).

cnf(c_5402,plain,
    ( v3_tops_2(sK4,sK2,sK3) = iProver_top
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4)),sK3) = iProver_top
    | v4_pre_topc(sK1(sK2,sK3,sK4),sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5401])).

cnf(c_5403,plain,
    ( v3_tops_2(sK4,sK2,sK3) = iProver_top
    | v4_pre_topc(sK1(sK2,sK3,sK4),sK2) = iProver_top
    | v4_pre_topc(k9_relat_1(sK4,sK1(sK2,sK3,sK4)),sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5402,c_4808])).

cnf(c_59,plain,
    ( v3_tops_2(sK4,sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10107,c_6920,c_5403,c_59,c_54,c_48])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:54:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.65/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.65/0.97  
% 3.65/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.65/0.97  
% 3.65/0.97  ------  iProver source info
% 3.65/0.97  
% 3.65/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.65/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.65/0.97  git: non_committed_changes: false
% 3.65/0.97  git: last_make_outside_of_git: false
% 3.65/0.97  
% 3.65/0.97  ------ 
% 3.65/0.97  
% 3.65/0.97  ------ Input Options
% 3.65/0.97  
% 3.65/0.97  --out_options                           all
% 3.65/0.97  --tptp_safe_out                         true
% 3.65/0.97  --problem_path                          ""
% 3.65/0.97  --include_path                          ""
% 3.65/0.97  --clausifier                            res/vclausify_rel
% 3.65/0.97  --clausifier_options                    ""
% 3.65/0.97  --stdin                                 false
% 3.65/0.97  --stats_out                             all
% 3.65/0.97  
% 3.65/0.97  ------ General Options
% 3.65/0.97  
% 3.65/0.97  --fof                                   false
% 3.65/0.97  --time_out_real                         305.
% 3.65/0.97  --time_out_virtual                      -1.
% 3.65/0.97  --symbol_type_check                     false
% 3.65/0.97  --clausify_out                          false
% 3.65/0.97  --sig_cnt_out                           false
% 3.65/0.97  --trig_cnt_out                          false
% 3.65/0.97  --trig_cnt_out_tolerance                1.
% 3.65/0.97  --trig_cnt_out_sk_spl                   false
% 3.65/0.97  --abstr_cl_out                          false
% 3.65/0.97  
% 3.65/0.97  ------ Global Options
% 3.65/0.97  
% 3.65/0.97  --schedule                              default
% 3.65/0.97  --add_important_lit                     false
% 3.65/0.97  --prop_solver_per_cl                    1000
% 3.65/0.97  --min_unsat_core                        false
% 3.65/0.97  --soft_assumptions                      false
% 3.65/0.97  --soft_lemma_size                       3
% 3.65/0.97  --prop_impl_unit_size                   0
% 3.65/0.97  --prop_impl_unit                        []
% 3.65/0.97  --share_sel_clauses                     true
% 3.65/0.97  --reset_solvers                         false
% 3.65/0.97  --bc_imp_inh                            [conj_cone]
% 3.65/0.97  --conj_cone_tolerance                   3.
% 3.65/0.97  --extra_neg_conj                        none
% 3.65/0.97  --large_theory_mode                     true
% 3.65/0.97  --prolific_symb_bound                   200
% 3.65/0.97  --lt_threshold                          2000
% 3.65/0.97  --clause_weak_htbl                      true
% 3.65/0.97  --gc_record_bc_elim                     false
% 3.65/0.97  
% 3.65/0.97  ------ Preprocessing Options
% 3.65/0.97  
% 3.65/0.97  --preprocessing_flag                    true
% 3.65/0.97  --time_out_prep_mult                    0.1
% 3.65/0.97  --splitting_mode                        input
% 3.65/0.97  --splitting_grd                         true
% 3.65/0.97  --splitting_cvd                         false
% 3.65/0.97  --splitting_cvd_svl                     false
% 3.65/0.97  --splitting_nvd                         32
% 3.65/0.97  --sub_typing                            true
% 3.65/0.97  --prep_gs_sim                           true
% 3.65/0.97  --prep_unflatten                        true
% 3.65/0.97  --prep_res_sim                          true
% 3.65/0.97  --prep_upred                            true
% 3.65/0.97  --prep_sem_filter                       exhaustive
% 3.65/0.97  --prep_sem_filter_out                   false
% 3.65/0.97  --pred_elim                             true
% 3.65/0.97  --res_sim_input                         true
% 3.65/0.97  --eq_ax_congr_red                       true
% 3.65/0.97  --pure_diseq_elim                       true
% 3.65/0.97  --brand_transform                       false
% 3.65/0.97  --non_eq_to_eq                          false
% 3.65/0.97  --prep_def_merge                        true
% 3.65/0.97  --prep_def_merge_prop_impl              false
% 3.65/0.97  --prep_def_merge_mbd                    true
% 3.65/0.97  --prep_def_merge_tr_red                 false
% 3.65/0.97  --prep_def_merge_tr_cl                  false
% 3.65/0.97  --smt_preprocessing                     true
% 3.65/0.97  --smt_ac_axioms                         fast
% 3.65/0.97  --preprocessed_out                      false
% 3.65/0.97  --preprocessed_stats                    false
% 3.65/0.97  
% 3.65/0.97  ------ Abstraction refinement Options
% 3.65/0.97  
% 3.65/0.97  --abstr_ref                             []
% 3.65/0.97  --abstr_ref_prep                        false
% 3.65/0.97  --abstr_ref_until_sat                   false
% 3.65/0.97  --abstr_ref_sig_restrict                funpre
% 3.65/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.65/0.97  --abstr_ref_under                       []
% 3.65/0.97  
% 3.65/0.97  ------ SAT Options
% 3.65/0.97  
% 3.65/0.97  --sat_mode                              false
% 3.65/0.97  --sat_fm_restart_options                ""
% 3.65/0.97  --sat_gr_def                            false
% 3.65/0.97  --sat_epr_types                         true
% 3.65/0.97  --sat_non_cyclic_types                  false
% 3.65/0.97  --sat_finite_models                     false
% 3.65/0.97  --sat_fm_lemmas                         false
% 3.65/0.97  --sat_fm_prep                           false
% 3.65/0.97  --sat_fm_uc_incr                        true
% 3.65/0.97  --sat_out_model                         small
% 3.65/0.97  --sat_out_clauses                       false
% 3.65/0.97  
% 3.65/0.97  ------ QBF Options
% 3.65/0.97  
% 3.65/0.97  --qbf_mode                              false
% 3.65/0.97  --qbf_elim_univ                         false
% 3.65/0.97  --qbf_dom_inst                          none
% 3.65/0.97  --qbf_dom_pre_inst                      false
% 3.65/0.97  --qbf_sk_in                             false
% 3.65/0.97  --qbf_pred_elim                         true
% 3.65/0.97  --qbf_split                             512
% 3.65/0.97  
% 3.65/0.97  ------ BMC1 Options
% 3.65/0.97  
% 3.65/0.97  --bmc1_incremental                      false
% 3.65/0.97  --bmc1_axioms                           reachable_all
% 3.65/0.97  --bmc1_min_bound                        0
% 3.65/0.97  --bmc1_max_bound                        -1
% 3.65/0.97  --bmc1_max_bound_default                -1
% 3.65/0.97  --bmc1_symbol_reachability              true
% 3.65/0.97  --bmc1_property_lemmas                  false
% 3.65/0.97  --bmc1_k_induction                      false
% 3.65/0.97  --bmc1_non_equiv_states                 false
% 3.65/0.97  --bmc1_deadlock                         false
% 3.65/0.97  --bmc1_ucm                              false
% 3.65/0.97  --bmc1_add_unsat_core                   none
% 3.65/0.97  --bmc1_unsat_core_children              false
% 3.65/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.65/0.97  --bmc1_out_stat                         full
% 3.65/0.97  --bmc1_ground_init                      false
% 3.65/0.97  --bmc1_pre_inst_next_state              false
% 3.65/0.97  --bmc1_pre_inst_state                   false
% 3.65/0.97  --bmc1_pre_inst_reach_state             false
% 3.65/0.97  --bmc1_out_unsat_core                   false
% 3.65/0.97  --bmc1_aig_witness_out                  false
% 3.65/0.97  --bmc1_verbose                          false
% 3.65/0.97  --bmc1_dump_clauses_tptp                false
% 3.65/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.65/0.97  --bmc1_dump_file                        -
% 3.65/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.65/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.65/0.97  --bmc1_ucm_extend_mode                  1
% 3.65/0.97  --bmc1_ucm_init_mode                    2
% 3.65/0.97  --bmc1_ucm_cone_mode                    none
% 3.65/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.65/0.97  --bmc1_ucm_relax_model                  4
% 3.65/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.65/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.65/0.97  --bmc1_ucm_layered_model                none
% 3.65/0.97  --bmc1_ucm_max_lemma_size               10
% 3.65/0.97  
% 3.65/0.97  ------ AIG Options
% 3.65/0.97  
% 3.65/0.97  --aig_mode                              false
% 3.65/0.97  
% 3.65/0.97  ------ Instantiation Options
% 3.65/0.97  
% 3.65/0.97  --instantiation_flag                    true
% 3.65/0.97  --inst_sos_flag                         true
% 3.65/0.97  --inst_sos_phase                        true
% 3.65/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.65/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.65/0.97  --inst_lit_sel_side                     num_symb
% 3.65/0.97  --inst_solver_per_active                1400
% 3.65/0.97  --inst_solver_calls_frac                1.
% 3.65/0.97  --inst_passive_queue_type               priority_queues
% 3.65/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.65/0.97  --inst_passive_queues_freq              [25;2]
% 3.65/0.97  --inst_dismatching                      true
% 3.65/0.97  --inst_eager_unprocessed_to_passive     true
% 3.65/0.97  --inst_prop_sim_given                   true
% 3.65/0.97  --inst_prop_sim_new                     false
% 3.65/0.97  --inst_subs_new                         false
% 3.65/0.97  --inst_eq_res_simp                      false
% 3.65/0.97  --inst_subs_given                       false
% 3.65/0.97  --inst_orphan_elimination               true
% 3.65/0.97  --inst_learning_loop_flag               true
% 3.65/0.97  --inst_learning_start                   3000
% 3.65/0.97  --inst_learning_factor                  2
% 3.65/0.97  --inst_start_prop_sim_after_learn       3
% 3.65/0.97  --inst_sel_renew                        solver
% 3.65/0.97  --inst_lit_activity_flag                true
% 3.65/0.97  --inst_restr_to_given                   false
% 3.65/0.97  --inst_activity_threshold               500
% 3.65/0.97  --inst_out_proof                        true
% 3.65/0.97  
% 3.65/0.97  ------ Resolution Options
% 3.65/0.97  
% 3.65/0.97  --resolution_flag                       true
% 3.65/0.97  --res_lit_sel                           adaptive
% 3.65/0.97  --res_lit_sel_side                      none
% 3.65/0.97  --res_ordering                          kbo
% 3.65/0.97  --res_to_prop_solver                    active
% 3.65/0.97  --res_prop_simpl_new                    false
% 3.65/0.97  --res_prop_simpl_given                  true
% 3.65/0.97  --res_passive_queue_type                priority_queues
% 3.65/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.65/0.97  --res_passive_queues_freq               [15;5]
% 3.65/0.97  --res_forward_subs                      full
% 3.65/0.97  --res_backward_subs                     full
% 3.65/0.97  --res_forward_subs_resolution           true
% 3.65/0.97  --res_backward_subs_resolution          true
% 3.65/0.97  --res_orphan_elimination                true
% 3.65/0.97  --res_time_limit                        2.
% 3.65/0.97  --res_out_proof                         true
% 3.65/0.97  
% 3.65/0.97  ------ Superposition Options
% 3.65/0.97  
% 3.65/0.97  --superposition_flag                    true
% 3.65/0.97  --sup_passive_queue_type                priority_queues
% 3.65/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.65/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.65/0.97  --demod_completeness_check              fast
% 3.65/0.97  --demod_use_ground                      true
% 3.65/0.97  --sup_to_prop_solver                    passive
% 3.65/0.97  --sup_prop_simpl_new                    true
% 3.65/0.97  --sup_prop_simpl_given                  true
% 3.65/0.97  --sup_fun_splitting                     true
% 3.65/0.97  --sup_smt_interval                      50000
% 3.65/0.97  
% 3.65/0.97  ------ Superposition Simplification Setup
% 3.65/0.97  
% 3.65/0.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.65/0.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.65/0.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.65/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.65/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.65/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.65/0.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.65/0.97  --sup_immed_triv                        [TrivRules]
% 3.65/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/0.97  --sup_immed_bw_main                     []
% 3.65/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.65/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.65/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/0.97  --sup_input_bw                          []
% 3.65/0.97  
% 3.65/0.97  ------ Combination Options
% 3.65/0.97  
% 3.65/0.97  --comb_res_mult                         3
% 3.65/0.97  --comb_sup_mult                         2
% 3.65/0.97  --comb_inst_mult                        10
% 3.65/0.97  
% 3.65/0.97  ------ Debug Options
% 3.65/0.97  
% 3.65/0.97  --dbg_backtrace                         false
% 3.65/0.97  --dbg_dump_prop_clauses                 false
% 3.65/0.97  --dbg_dump_prop_clauses_file            -
% 3.65/0.97  --dbg_out_stat                          false
% 3.65/0.97  ------ Parsing...
% 3.65/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.65/0.97  
% 3.65/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 10 0s  sf_e  pe_s  pe_e 
% 3.65/0.97  
% 3.65/0.97  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.65/0.97  
% 3.65/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/0.97  ------ Proving...
% 3.65/0.97  ------ Problem Properties 
% 3.65/0.97  
% 3.65/0.97  
% 3.65/0.97  clauses                                 34
% 3.65/0.97  conjectures                             7
% 3.65/0.97  EPR                                     7
% 3.65/0.97  Horn                                    29
% 3.65/0.97  unary                                   8
% 3.65/0.97  binary                                  12
% 3.65/0.97  lits                                    118
% 3.65/0.97  lits eq                                 34
% 3.65/0.97  fd_pure                                 0
% 3.65/0.97  fd_pseudo                               0
% 3.65/0.97  fd_cond                                 0
% 3.65/0.97  fd_pseudo_cond                          1
% 3.65/0.97  AC symbols                              0
% 3.65/0.97  
% 3.65/0.97  ------ Schedule dynamic 5 is on 
% 3.65/0.97  
% 3.65/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.65/0.97  
% 3.65/0.97  
% 3.65/0.97  ------ 
% 3.65/0.97  Current options:
% 3.65/0.97  ------ 
% 3.65/0.97  
% 3.65/0.97  ------ Input Options
% 3.65/0.97  
% 3.65/0.97  --out_options                           all
% 3.65/0.97  --tptp_safe_out                         true
% 3.65/0.97  --problem_path                          ""
% 3.65/0.97  --include_path                          ""
% 3.65/0.97  --clausifier                            res/vclausify_rel
% 3.65/0.97  --clausifier_options                    ""
% 3.65/0.97  --stdin                                 false
% 3.65/0.97  --stats_out                             all
% 3.65/0.97  
% 3.65/0.97  ------ General Options
% 3.65/0.97  
% 3.65/0.97  --fof                                   false
% 3.65/0.97  --time_out_real                         305.
% 3.65/0.97  --time_out_virtual                      -1.
% 3.65/0.97  --symbol_type_check                     false
% 3.65/0.97  --clausify_out                          false
% 3.65/0.97  --sig_cnt_out                           false
% 3.65/0.97  --trig_cnt_out                          false
% 3.65/0.97  --trig_cnt_out_tolerance                1.
% 3.65/0.97  --trig_cnt_out_sk_spl                   false
% 3.65/0.97  --abstr_cl_out                          false
% 3.65/0.97  
% 3.65/0.97  ------ Global Options
% 3.65/0.97  
% 3.65/0.97  --schedule                              default
% 3.65/0.97  --add_important_lit                     false
% 3.65/0.97  --prop_solver_per_cl                    1000
% 3.65/0.97  --min_unsat_core                        false
% 3.65/0.97  --soft_assumptions                      false
% 3.65/0.97  --soft_lemma_size                       3
% 3.65/0.97  --prop_impl_unit_size                   0
% 3.65/0.97  --prop_impl_unit                        []
% 3.65/0.97  --share_sel_clauses                     true
% 3.65/0.97  --reset_solvers                         false
% 3.65/0.97  --bc_imp_inh                            [conj_cone]
% 3.65/0.97  --conj_cone_tolerance                   3.
% 3.65/0.97  --extra_neg_conj                        none
% 3.65/0.97  --large_theory_mode                     true
% 3.65/0.97  --prolific_symb_bound                   200
% 3.65/0.97  --lt_threshold                          2000
% 3.65/0.97  --clause_weak_htbl                      true
% 3.65/0.97  --gc_record_bc_elim                     false
% 3.65/0.97  
% 3.65/0.97  ------ Preprocessing Options
% 3.65/0.97  
% 3.65/0.97  --preprocessing_flag                    true
% 3.65/0.97  --time_out_prep_mult                    0.1
% 3.65/0.97  --splitting_mode                        input
% 3.65/0.97  --splitting_grd                         true
% 3.65/0.97  --splitting_cvd                         false
% 3.65/0.97  --splitting_cvd_svl                     false
% 3.65/0.97  --splitting_nvd                         32
% 3.65/0.97  --sub_typing                            true
% 3.65/0.97  --prep_gs_sim                           true
% 3.65/0.97  --prep_unflatten                        true
% 3.65/0.97  --prep_res_sim                          true
% 3.65/0.97  --prep_upred                            true
% 3.65/0.97  --prep_sem_filter                       exhaustive
% 3.65/0.97  --prep_sem_filter_out                   false
% 3.65/0.97  --pred_elim                             true
% 3.65/0.97  --res_sim_input                         true
% 3.65/0.97  --eq_ax_congr_red                       true
% 3.65/0.97  --pure_diseq_elim                       true
% 3.65/0.97  --brand_transform                       false
% 3.65/0.97  --non_eq_to_eq                          false
% 3.65/0.97  --prep_def_merge                        true
% 3.65/0.97  --prep_def_merge_prop_impl              false
% 3.65/0.97  --prep_def_merge_mbd                    true
% 3.65/0.97  --prep_def_merge_tr_red                 false
% 3.65/0.97  --prep_def_merge_tr_cl                  false
% 3.65/0.97  --smt_preprocessing                     true
% 3.65/0.97  --smt_ac_axioms                         fast
% 3.65/0.97  --preprocessed_out                      false
% 3.65/0.97  --preprocessed_stats                    false
% 3.65/0.97  
% 3.65/0.97  ------ Abstraction refinement Options
% 3.65/0.97  
% 3.65/0.97  --abstr_ref                             []
% 3.65/0.97  --abstr_ref_prep                        false
% 3.65/0.97  --abstr_ref_until_sat                   false
% 3.65/0.97  --abstr_ref_sig_restrict                funpre
% 3.65/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.65/0.97  --abstr_ref_under                       []
% 3.65/0.97  
% 3.65/0.97  ------ SAT Options
% 3.65/0.97  
% 3.65/0.97  --sat_mode                              false
% 3.65/0.97  --sat_fm_restart_options                ""
% 3.65/0.97  --sat_gr_def                            false
% 3.65/0.97  --sat_epr_types                         true
% 3.65/0.97  --sat_non_cyclic_types                  false
% 3.65/0.97  --sat_finite_models                     false
% 3.65/0.97  --sat_fm_lemmas                         false
% 3.65/0.97  --sat_fm_prep                           false
% 3.65/0.97  --sat_fm_uc_incr                        true
% 3.65/0.97  --sat_out_model                         small
% 3.65/0.97  --sat_out_clauses                       false
% 3.65/0.97  
% 3.65/0.97  ------ QBF Options
% 3.65/0.97  
% 3.65/0.97  --qbf_mode                              false
% 3.65/0.97  --qbf_elim_univ                         false
% 3.65/0.97  --qbf_dom_inst                          none
% 3.65/0.97  --qbf_dom_pre_inst                      false
% 3.65/0.97  --qbf_sk_in                             false
% 3.65/0.97  --qbf_pred_elim                         true
% 3.65/0.97  --qbf_split                             512
% 3.65/0.97  
% 3.65/0.97  ------ BMC1 Options
% 3.65/0.97  
% 3.65/0.97  --bmc1_incremental                      false
% 3.65/0.97  --bmc1_axioms                           reachable_all
% 3.65/0.97  --bmc1_min_bound                        0
% 3.65/0.97  --bmc1_max_bound                        -1
% 3.65/0.97  --bmc1_max_bound_default                -1
% 3.65/0.97  --bmc1_symbol_reachability              true
% 3.65/0.97  --bmc1_property_lemmas                  false
% 3.65/0.97  --bmc1_k_induction                      false
% 3.65/0.97  --bmc1_non_equiv_states                 false
% 3.65/0.97  --bmc1_deadlock                         false
% 3.65/0.97  --bmc1_ucm                              false
% 3.65/0.97  --bmc1_add_unsat_core                   none
% 3.65/0.97  --bmc1_unsat_core_children              false
% 3.65/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.65/0.97  --bmc1_out_stat                         full
% 3.65/0.97  --bmc1_ground_init                      false
% 3.65/0.97  --bmc1_pre_inst_next_state              false
% 3.65/0.97  --bmc1_pre_inst_state                   false
% 3.65/0.97  --bmc1_pre_inst_reach_state             false
% 3.65/0.97  --bmc1_out_unsat_core                   false
% 3.65/0.97  --bmc1_aig_witness_out                  false
% 3.65/0.97  --bmc1_verbose                          false
% 3.65/0.97  --bmc1_dump_clauses_tptp                false
% 3.65/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.65/0.97  --bmc1_dump_file                        -
% 3.65/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.65/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.65/0.97  --bmc1_ucm_extend_mode                  1
% 3.65/0.97  --bmc1_ucm_init_mode                    2
% 3.65/0.97  --bmc1_ucm_cone_mode                    none
% 3.65/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.65/0.97  --bmc1_ucm_relax_model                  4
% 3.65/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.65/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.65/0.97  --bmc1_ucm_layered_model                none
% 3.65/0.97  --bmc1_ucm_max_lemma_size               10
% 3.65/0.97  
% 3.65/0.97  ------ AIG Options
% 3.65/0.97  
% 3.65/0.97  --aig_mode                              false
% 3.65/0.97  
% 3.65/0.97  ------ Instantiation Options
% 3.65/0.97  
% 3.65/0.97  --instantiation_flag                    true
% 3.65/0.97  --inst_sos_flag                         true
% 3.65/0.97  --inst_sos_phase                        true
% 3.65/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.65/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.65/0.97  --inst_lit_sel_side                     none
% 3.65/0.97  --inst_solver_per_active                1400
% 3.65/0.97  --inst_solver_calls_frac                1.
% 3.65/0.97  --inst_passive_queue_type               priority_queues
% 3.65/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.65/0.97  --inst_passive_queues_freq              [25;2]
% 3.65/0.97  --inst_dismatching                      true
% 3.65/0.97  --inst_eager_unprocessed_to_passive     true
% 3.65/0.97  --inst_prop_sim_given                   true
% 3.65/0.97  --inst_prop_sim_new                     false
% 3.65/0.97  --inst_subs_new                         false
% 3.65/0.97  --inst_eq_res_simp                      false
% 3.65/0.97  --inst_subs_given                       false
% 3.65/0.97  --inst_orphan_elimination               true
% 3.65/0.97  --inst_learning_loop_flag               true
% 3.65/0.97  --inst_learning_start                   3000
% 3.65/0.97  --inst_learning_factor                  2
% 3.65/0.97  --inst_start_prop_sim_after_learn       3
% 3.65/0.97  --inst_sel_renew                        solver
% 3.65/0.97  --inst_lit_activity_flag                true
% 3.65/0.97  --inst_restr_to_given                   false
% 3.65/0.97  --inst_activity_threshold               500
% 3.65/0.97  --inst_out_proof                        true
% 3.65/0.97  
% 3.65/0.97  ------ Resolution Options
% 3.65/0.97  
% 3.65/0.97  --resolution_flag                       false
% 3.65/0.97  --res_lit_sel                           adaptive
% 3.65/0.97  --res_lit_sel_side                      none
% 3.65/0.97  --res_ordering                          kbo
% 3.65/0.97  --res_to_prop_solver                    active
% 3.65/0.97  --res_prop_simpl_new                    false
% 3.65/0.97  --res_prop_simpl_given                  true
% 3.65/0.97  --res_passive_queue_type                priority_queues
% 3.65/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.65/0.97  --res_passive_queues_freq               [15;5]
% 3.65/0.97  --res_forward_subs                      full
% 3.65/0.97  --res_backward_subs                     full
% 3.65/0.97  --res_forward_subs_resolution           true
% 3.65/0.97  --res_backward_subs_resolution          true
% 3.65/0.97  --res_orphan_elimination                true
% 3.65/0.97  --res_time_limit                        2.
% 3.65/0.97  --res_out_proof                         true
% 3.65/0.97  
% 3.65/0.97  ------ Superposition Options
% 3.65/0.97  
% 3.65/0.97  --superposition_flag                    true
% 3.65/0.97  --sup_passive_queue_type                priority_queues
% 3.65/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.65/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.65/0.97  --demod_completeness_check              fast
% 3.65/0.97  --demod_use_ground                      true
% 3.65/0.97  --sup_to_prop_solver                    passive
% 3.65/0.97  --sup_prop_simpl_new                    true
% 3.65/0.97  --sup_prop_simpl_given                  true
% 3.65/0.97  --sup_fun_splitting                     true
% 3.65/0.97  --sup_smt_interval                      50000
% 3.65/0.97  
% 3.65/0.97  ------ Superposition Simplification Setup
% 3.65/0.97  
% 3.65/0.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.65/0.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.65/0.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.65/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.65/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.65/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.65/0.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.65/0.97  --sup_immed_triv                        [TrivRules]
% 3.65/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/0.97  --sup_immed_bw_main                     []
% 3.65/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.65/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.65/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/0.97  --sup_input_bw                          []
% 3.65/0.97  
% 3.65/0.97  ------ Combination Options
% 3.65/0.97  
% 3.65/0.97  --comb_res_mult                         3
% 3.65/0.97  --comb_sup_mult                         2
% 3.65/0.97  --comb_inst_mult                        10
% 3.65/0.97  
% 3.65/0.97  ------ Debug Options
% 3.65/0.97  
% 3.65/0.97  --dbg_backtrace                         false
% 3.65/0.97  --dbg_dump_prop_clauses                 false
% 3.65/0.97  --dbg_dump_prop_clauses_file            -
% 3.65/0.97  --dbg_out_stat                          false
% 3.65/0.97  
% 3.65/0.97  
% 3.65/0.97  
% 3.65/0.97  
% 3.65/0.97  ------ Proving...
% 3.65/0.97  
% 3.65/0.97  
% 3.65/0.97  % SZS status Theorem for theBenchmark.p
% 3.65/0.97  
% 3.65/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.65/0.97  
% 3.65/0.97  fof(f18,conjecture,(
% 3.65/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) & v8_pre_topc(X1) & v1_compts_1(X0)) => v3_tops_2(X2,X0,X1)))))),
% 3.65/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.97  
% 3.65/0.97  fof(f19,negated_conjecture,(
% 3.65/0.97    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) & v8_pre_topc(X1) & v1_compts_1(X0)) => v3_tops_2(X2,X0,X1)))))),
% 3.65/0.97    inference(negated_conjecture,[],[f18])).
% 3.65/0.97  
% 3.65/0.97  fof(f41,plain,(
% 3.65/0.97    ? [X0] : (? [X1] : (? [X2] : ((~v3_tops_2(X2,X0,X1) & (v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) & v8_pre_topc(X1) & v1_compts_1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.65/0.97    inference(ennf_transformation,[],[f19])).
% 3.65/0.97  
% 3.65/0.97  fof(f42,plain,(
% 3.65/0.97    ? [X0] : (? [X1] : (? [X2] : (~v3_tops_2(X2,X0,X1) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) & v8_pre_topc(X1) & v1_compts_1(X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.65/0.97    inference(flattening,[],[f41])).
% 3.65/0.97  
% 3.65/0.97  fof(f58,plain,(
% 3.65/0.97    ( ! [X0,X1] : (? [X2] : (~v3_tops_2(X2,X0,X1) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) & v8_pre_topc(X1) & v1_compts_1(X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~v3_tops_2(sK4,X0,X1) & v5_pre_topc(sK4,X0,X1) & v2_funct_1(sK4) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) = k2_struct_0(X0) & v8_pre_topc(X1) & v1_compts_1(X0) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 3.65/0.97    introduced(choice_axiom,[])).
% 3.65/0.97  
% 3.65/0.97  fof(f57,plain,(
% 3.65/0.97    ( ! [X0] : (? [X1] : (? [X2] : (~v3_tops_2(X2,X0,X1) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) & v8_pre_topc(X1) & v1_compts_1(X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (~v3_tops_2(X2,X0,sK3) & v5_pre_topc(X2,X0,sK3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2) = k2_struct_0(sK3) & k1_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2) = k2_struct_0(X0) & v8_pre_topc(sK3) & v1_compts_1(X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 3.65/0.97    introduced(choice_axiom,[])).
% 3.65/0.97  
% 3.65/0.97  fof(f56,plain,(
% 3.65/0.97    ? [X0] : (? [X1] : (? [X2] : (~v3_tops_2(X2,X0,X1) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) & v8_pre_topc(X1) & v1_compts_1(X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v3_tops_2(X2,sK2,X1) & v5_pre_topc(X2,sK2,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2) = k2_struct_0(sK2) & v8_pre_topc(X1) & v1_compts_1(sK2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2))),
% 3.65/0.97    introduced(choice_axiom,[])).
% 3.65/0.97  
% 3.65/0.97  fof(f59,plain,(
% 3.65/0.97    ((~v3_tops_2(sK4,sK2,sK3) & v5_pre_topc(sK4,sK2,sK3) & v2_funct_1(sK4) & k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3) & k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2) & v8_pre_topc(sK3) & v1_compts_1(sK2) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2)),
% 3.65/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f42,f58,f57,f56])).
% 3.65/0.97  
% 3.65/0.97  fof(f99,plain,(
% 3.65/0.97    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 3.65/0.97    inference(cnf_transformation,[],[f59])).
% 3.65/0.97  
% 3.65/0.97  fof(f7,axiom,(
% 3.65/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.65/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.97  
% 3.65/0.97  fof(f26,plain,(
% 3.65/0.97    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.65/0.97    inference(ennf_transformation,[],[f7])).
% 3.65/0.97  
% 3.65/0.97  fof(f69,plain,(
% 3.65/0.97    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.65/0.97    inference(cnf_transformation,[],[f26])).
% 3.65/0.97  
% 3.65/0.97  fof(f98,plain,(
% 3.65/0.97    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 3.65/0.97    inference(cnf_transformation,[],[f59])).
% 3.65/0.97  
% 3.65/0.97  fof(f16,axiom,(
% 3.65/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X3,X0) <=> v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))))))),
% 3.65/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.97  
% 3.65/0.97  fof(f37,plain,(
% 3.65/0.97    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (! [X3] : ((v4_pre_topc(X3,X0) <=> v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | v2_struct_0(X1))) | ~l1_pre_topc(X0))),
% 3.65/0.97    inference(ennf_transformation,[],[f16])).
% 3.65/0.97  
% 3.65/0.97  fof(f38,plain,(
% 3.65/0.97    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (! [X3] : ((v4_pre_topc(X3,X0) <=> v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0))),
% 3.65/0.97    inference(flattening,[],[f37])).
% 3.65/0.97  
% 3.65/0.97  fof(f51,plain,(
% 3.65/0.97    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | (? [X3] : (((~v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) | ~v4_pre_topc(X3,X0)) & (v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) | v4_pre_topc(X3,X0))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0))) & ((! [X3] : (((v4_pre_topc(X3,X0) | ~v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)) & (v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) | ~v4_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0))),
% 3.65/0.97    inference(nnf_transformation,[],[f38])).
% 3.65/0.97  
% 3.65/0.97  fof(f52,plain,(
% 3.65/0.97    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | ? [X3] : ((~v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) | ~v4_pre_topc(X3,X0)) & (v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) | v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)) & ((! [X3] : (((v4_pre_topc(X3,X0) | ~v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)) & (v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) | ~v4_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0))),
% 3.65/0.97    inference(flattening,[],[f51])).
% 3.65/0.97  
% 3.65/0.97  fof(f53,plain,(
% 3.65/0.97    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | ? [X3] : ((~v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) | ~v4_pre_topc(X3,X0)) & (v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) | v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)) & ((! [X4] : (((v4_pre_topc(X4,X0) | ~v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1)) & (v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1) | ~v4_pre_topc(X4,X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0))),
% 3.65/0.97    inference(rectify,[],[f52])).
% 3.65/0.97  
% 3.65/0.97  fof(f54,plain,(
% 3.65/0.97    ! [X2,X1,X0] : (? [X3] : ((~v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) | ~v4_pre_topc(X3,X0)) & (v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) | v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => ((~v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2)),X1) | ~v4_pre_topc(sK1(X0,X1,X2),X0)) & (v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2)),X1) | v4_pre_topc(sK1(X0,X1,X2),X0)) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.65/0.97    introduced(choice_axiom,[])).
% 3.65/0.97  
% 3.65/0.97  fof(f55,plain,(
% 3.65/0.97    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | ((~v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2)),X1) | ~v4_pre_topc(sK1(X0,X1,X2),X0)) & (v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2)),X1) | v4_pre_topc(sK1(X0,X1,X2),X0)) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)) & ((! [X4] : (((v4_pre_topc(X4,X0) | ~v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1)) & (v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1) | ~v4_pre_topc(X4,X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0))),
% 3.65/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f53,f54])).
% 3.65/0.97  
% 3.65/0.97  fof(f88,plain,(
% 3.65/0.97    ( ! [X2,X0,X1] : (v3_tops_2(X2,X0,X1) | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0)) )),
% 3.65/0.97    inference(cnf_transformation,[],[f55])).
% 3.65/0.97  
% 3.65/0.97  fof(f94,plain,(
% 3.65/0.97    ~v2_struct_0(sK3)),
% 3.65/0.97    inference(cnf_transformation,[],[f59])).
% 3.65/0.97  
% 3.65/0.97  fof(f96,plain,(
% 3.65/0.97    l1_pre_topc(sK3)),
% 3.65/0.97    inference(cnf_transformation,[],[f59])).
% 3.65/0.97  
% 3.65/0.97  fof(f97,plain,(
% 3.65/0.97    v1_funct_1(sK4)),
% 3.65/0.97    inference(cnf_transformation,[],[f59])).
% 3.65/0.97  
% 3.65/0.97  fof(f104,plain,(
% 3.65/0.97    v2_funct_1(sK4)),
% 3.65/0.97    inference(cnf_transformation,[],[f59])).
% 3.65/0.97  
% 3.65/0.97  fof(f8,axiom,(
% 3.65/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 3.65/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.97  
% 3.65/0.97  fof(f27,plain,(
% 3.65/0.97    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.65/0.97    inference(ennf_transformation,[],[f8])).
% 3.65/0.97  
% 3.65/0.97  fof(f70,plain,(
% 3.65/0.97    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.65/0.97    inference(cnf_transformation,[],[f27])).
% 3.65/0.97  
% 3.65/0.97  fof(f103,plain,(
% 3.65/0.97    k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3)),
% 3.65/0.97    inference(cnf_transformation,[],[f59])).
% 3.65/0.97  
% 3.65/0.97  fof(f102,plain,(
% 3.65/0.97    k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2)),
% 3.65/0.97    inference(cnf_transformation,[],[f59])).
% 3.65/0.97  
% 3.65/0.97  fof(f106,plain,(
% 3.65/0.97    ~v3_tops_2(sK4,sK2,sK3)),
% 3.65/0.97    inference(cnf_transformation,[],[f59])).
% 3.65/0.97  
% 3.65/0.97  fof(f93,plain,(
% 3.65/0.97    l1_pre_topc(sK2)),
% 3.65/0.97    inference(cnf_transformation,[],[f59])).
% 3.65/0.97  
% 3.65/0.97  fof(f15,axiom,(
% 3.65/0.97    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.65/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.97  
% 3.65/0.97  fof(f36,plain,(
% 3.65/0.97    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.65/0.97    inference(ennf_transformation,[],[f15])).
% 3.65/0.97  
% 3.65/0.97  fof(f82,plain,(
% 3.65/0.97    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.65/0.97    inference(cnf_transformation,[],[f36])).
% 3.65/0.97  
% 3.65/0.97  fof(f14,axiom,(
% 3.65/0.97    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 3.65/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.97  
% 3.65/0.97  fof(f35,plain,(
% 3.65/0.97    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 3.65/0.97    inference(ennf_transformation,[],[f14])).
% 3.65/0.97  
% 3.65/0.97  fof(f81,plain,(
% 3.65/0.97    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.65/0.97    inference(cnf_transformation,[],[f35])).
% 3.65/0.97  
% 3.65/0.97  fof(f2,axiom,(
% 3.65/0.97    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.65/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.97  
% 3.65/0.97  fof(f45,plain,(
% 3.65/0.97    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.65/0.97    inference(nnf_transformation,[],[f2])).
% 3.65/0.97  
% 3.65/0.97  fof(f63,plain,(
% 3.65/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.65/0.97    inference(cnf_transformation,[],[f45])).
% 3.65/0.97  
% 3.65/0.97  fof(f4,axiom,(
% 3.65/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.65/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.97  
% 3.65/0.97  fof(f23,plain,(
% 3.65/0.97    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.65/0.97    inference(ennf_transformation,[],[f4])).
% 3.65/0.97  
% 3.65/0.97  fof(f66,plain,(
% 3.65/0.97    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.65/0.97    inference(cnf_transformation,[],[f23])).
% 3.65/0.97  
% 3.65/0.97  fof(f3,axiom,(
% 3.65/0.97    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 3.65/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.97  
% 3.65/0.97  fof(f21,plain,(
% 3.65/0.97    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.65/0.97    inference(ennf_transformation,[],[f3])).
% 3.65/0.97  
% 3.65/0.97  fof(f22,plain,(
% 3.65/0.97    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.65/0.97    inference(flattening,[],[f21])).
% 3.65/0.97  
% 3.65/0.97  fof(f65,plain,(
% 3.65/0.97    ( ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.65/0.97    inference(cnf_transformation,[],[f22])).
% 3.65/0.97  
% 3.65/0.97  fof(f9,axiom,(
% 3.65/0.97    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.65/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.97  
% 3.65/0.97  fof(f28,plain,(
% 3.65/0.97    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.65/0.97    inference(ennf_transformation,[],[f9])).
% 3.65/0.97  
% 3.65/0.97  fof(f71,plain,(
% 3.65/0.97    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.65/0.97    inference(cnf_transformation,[],[f28])).
% 3.65/0.97  
% 3.65/0.97  fof(f6,axiom,(
% 3.65/0.97    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 3.65/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.97  
% 3.65/0.97  fof(f25,plain,(
% 3.65/0.97    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.65/0.97    inference(ennf_transformation,[],[f6])).
% 3.65/0.97  
% 3.65/0.97  fof(f68,plain,(
% 3.65/0.97    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.65/0.97    inference(cnf_transformation,[],[f25])).
% 3.65/0.97  
% 3.65/0.97  fof(f13,axiom,(
% 3.65/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v4_pre_topc(X3,X1) => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)))))))),
% 3.65/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.97  
% 3.65/0.97  fof(f33,plain,(
% 3.65/0.97    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.65/0.97    inference(ennf_transformation,[],[f13])).
% 3.65/0.97  
% 3.65/0.97  fof(f34,plain,(
% 3.65/0.97    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.65/0.97    inference(flattening,[],[f33])).
% 3.65/0.97  
% 3.65/0.97  fof(f47,plain,(
% 3.65/0.97    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.65/0.97    inference(nnf_transformation,[],[f34])).
% 3.65/0.97  
% 3.65/0.97  fof(f48,plain,(
% 3.65/0.97    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.65/0.97    inference(rectify,[],[f47])).
% 3.65/0.97  
% 3.65/0.97  fof(f49,plain,(
% 3.65/0.97    ! [X2,X1,X0] : (? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) & v4_pre_topc(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 3.65/0.97    introduced(choice_axiom,[])).
% 3.65/0.97  
% 3.65/0.97  fof(f50,plain,(
% 3.65/0.97    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) & v4_pre_topc(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.65/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f48,f49])).
% 3.65/0.97  
% 3.65/0.97  fof(f77,plain,(
% 3.65/0.97    ( ! [X4,X2,X0,X1] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.65/0.97    inference(cnf_transformation,[],[f50])).
% 3.65/0.97  
% 3.65/0.97  fof(f10,axiom,(
% 3.65/0.97    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 3.65/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.97  
% 3.65/0.97  fof(f29,plain,(
% 3.65/0.97    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.65/0.97    inference(ennf_transformation,[],[f10])).
% 3.65/0.97  
% 3.65/0.97  fof(f72,plain,(
% 3.65/0.97    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.65/0.97    inference(cnf_transformation,[],[f29])).
% 3.65/0.97  
% 3.65/0.97  fof(f105,plain,(
% 3.65/0.97    v5_pre_topc(sK4,sK2,sK3)),
% 3.65/0.97    inference(cnf_transformation,[],[f59])).
% 3.65/0.97  
% 3.65/0.97  fof(f90,plain,(
% 3.65/0.97    ( ! [X2,X0,X1] : (v3_tops_2(X2,X0,X1) | ~v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2)),X1) | ~v4_pre_topc(sK1(X0,X1,X2),X0) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0)) )),
% 3.65/0.97    inference(cnf_transformation,[],[f55])).
% 3.65/0.97  
% 3.65/0.97  fof(f17,axiom,(
% 3.65/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v5_pre_topc(X2,X0,X1) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & v8_pre_topc(X1) & v1_compts_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X3,X0) => v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)))))))),
% 3.65/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.97  
% 3.65/0.97  fof(f39,plain,(
% 3.65/0.97    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) | ~v4_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | (~v5_pre_topc(X2,X0,X1) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~v8_pre_topc(X1) | ~v1_compts_1(X0))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.65/0.97    inference(ennf_transformation,[],[f17])).
% 3.65/0.97  
% 3.65/0.97  fof(f40,plain,(
% 3.65/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v5_pre_topc(X2,X0,X1) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~v8_pre_topc(X1) | ~v1_compts_1(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.65/0.97    inference(flattening,[],[f39])).
% 3.65/0.97  
% 3.65/0.97  fof(f91,plain,(
% 3.65/0.97    ( ! [X2,X0,X3,X1] : (v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v5_pre_topc(X2,X0,X1) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~v8_pre_topc(X1) | ~v1_compts_1(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.65/0.97    inference(cnf_transformation,[],[f40])).
% 3.65/0.97  
% 3.65/0.97  fof(f101,plain,(
% 3.65/0.97    v8_pre_topc(sK3)),
% 3.65/0.97    inference(cnf_transformation,[],[f59])).
% 3.65/0.97  
% 3.65/0.97  fof(f95,plain,(
% 3.65/0.97    v2_pre_topc(sK3)),
% 3.65/0.97    inference(cnf_transformation,[],[f59])).
% 3.65/0.97  
% 3.65/0.97  fof(f100,plain,(
% 3.65/0.97    v1_compts_1(sK2)),
% 3.65/0.97    inference(cnf_transformation,[],[f59])).
% 3.65/0.97  
% 3.65/0.97  fof(f92,plain,(
% 3.65/0.97    v2_pre_topc(sK2)),
% 3.65/0.97    inference(cnf_transformation,[],[f59])).
% 3.65/0.97  
% 3.65/0.97  fof(f89,plain,(
% 3.65/0.97    ( ! [X2,X0,X1] : (v3_tops_2(X2,X0,X1) | v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2)),X1) | v4_pre_topc(sK1(X0,X1,X2),X0) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0)) )),
% 3.65/0.97    inference(cnf_transformation,[],[f55])).
% 3.65/0.97  
% 3.65/0.97  cnf(c_39,negated_conjecture,
% 3.65/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 3.65/0.97      inference(cnf_transformation,[],[f99]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_3924,plain,
% 3.65/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 3.65/0.97      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_9,plain,
% 3.65/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.65/0.97      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.65/0.97      inference(cnf_transformation,[],[f69]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_3932,plain,
% 3.65/0.97      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.65/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.65/0.97      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_4679,plain,
% 3.65/0.97      ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k1_relat_1(sK4) ),
% 3.65/0.97      inference(superposition,[status(thm)],[c_3924,c_3932]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_40,negated_conjecture,
% 3.65/0.97      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 3.65/0.97      inference(cnf_transformation,[],[f98]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_25,plain,
% 3.65/0.97      ( v3_tops_2(X0,X1,X2)
% 3.65/0.97      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.65/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.65/0.97      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.97      | v2_struct_0(X2)
% 3.65/0.97      | ~ l1_pre_topc(X2)
% 3.65/0.97      | ~ l1_pre_topc(X1)
% 3.65/0.97      | ~ v1_funct_1(X0)
% 3.65/0.97      | ~ v2_funct_1(X0)
% 3.65/0.97      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 3.65/0.97      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1) ),
% 3.65/0.97      inference(cnf_transformation,[],[f88]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_44,negated_conjecture,
% 3.65/0.97      ( ~ v2_struct_0(sK3) ),
% 3.65/0.97      inference(cnf_transformation,[],[f94]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_880,plain,
% 3.65/0.97      ( v3_tops_2(X0,X1,X2)
% 3.65/0.97      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.65/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.65/0.97      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.97      | ~ l1_pre_topc(X1)
% 3.65/0.97      | ~ l1_pre_topc(X2)
% 3.65/0.97      | ~ v1_funct_1(X0)
% 3.65/0.97      | ~ v2_funct_1(X0)
% 3.65/0.97      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 3.65/0.97      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
% 3.65/0.97      | sK3 != X2 ),
% 3.65/0.97      inference(resolution_lifted,[status(thm)],[c_25,c_44]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_881,plain,
% 3.65/0.97      ( v3_tops_2(X0,X1,sK3)
% 3.65/0.97      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
% 3.65/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
% 3.65/0.97      | m1_subset_1(sK1(X1,sK3,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.97      | ~ l1_pre_topc(X1)
% 3.65/0.97      | ~ l1_pre_topc(sK3)
% 3.65/0.97      | ~ v1_funct_1(X0)
% 3.65/0.97      | ~ v2_funct_1(X0)
% 3.65/0.97      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(sK3)
% 3.65/0.97      | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(X1) ),
% 3.65/0.97      inference(unflattening,[status(thm)],[c_880]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_42,negated_conjecture,
% 3.65/0.97      ( l1_pre_topc(sK3) ),
% 3.65/0.97      inference(cnf_transformation,[],[f96]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_885,plain,
% 3.65/0.97      ( ~ l1_pre_topc(X1)
% 3.65/0.97      | m1_subset_1(sK1(X1,sK3,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
% 3.65/0.97      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
% 3.65/0.97      | v3_tops_2(X0,X1,sK3)
% 3.65/0.97      | ~ v1_funct_1(X0)
% 3.65/0.97      | ~ v2_funct_1(X0)
% 3.65/0.97      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(sK3)
% 3.65/0.97      | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(X1) ),
% 3.65/0.97      inference(global_propositional_subsumption,
% 3.65/0.97                [status(thm)],
% 3.65/0.97                [c_881,c_42]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_886,plain,
% 3.65/0.97      ( v3_tops_2(X0,X1,sK3)
% 3.65/0.97      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
% 3.65/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
% 3.65/0.97      | m1_subset_1(sK1(X1,sK3,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.97      | ~ l1_pre_topc(X1)
% 3.65/0.97      | ~ v1_funct_1(X0)
% 3.65/0.97      | ~ v2_funct_1(X0)
% 3.65/0.97      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(sK3)
% 3.65/0.97      | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(X1) ),
% 3.65/0.97      inference(renaming,[status(thm)],[c_885]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_1592,plain,
% 3.65/0.97      ( v3_tops_2(X0,X1,sK3)
% 3.65/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
% 3.65/0.97      | m1_subset_1(sK1(X1,sK3,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.97      | ~ l1_pre_topc(X1)
% 3.65/0.97      | ~ v1_funct_1(X0)
% 3.65/0.97      | ~ v2_funct_1(X0)
% 3.65/0.97      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(sK3)
% 3.65/0.97      | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(X1)
% 3.65/0.97      | u1_struct_0(X1) != u1_struct_0(sK2)
% 3.65/0.97      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 3.65/0.97      | sK4 != X0 ),
% 3.65/0.97      inference(resolution_lifted,[status(thm)],[c_40,c_886]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_1593,plain,
% 3.65/0.97      ( v3_tops_2(sK4,X0,sK3)
% 3.65/0.97      | m1_subset_1(sK1(X0,sK3,sK4),k1_zfmisc_1(u1_struct_0(X0)))
% 3.65/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
% 3.65/0.97      | ~ l1_pre_topc(X0)
% 3.65/0.97      | ~ v1_funct_1(sK4)
% 3.65/0.97      | ~ v2_funct_1(sK4)
% 3.65/0.97      | k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
% 3.65/0.97      | k1_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(X0)
% 3.65/0.97      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 3.65/0.97      inference(unflattening,[status(thm)],[c_1592]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_41,negated_conjecture,
% 3.65/0.97      ( v1_funct_1(sK4) ),
% 3.65/0.97      inference(cnf_transformation,[],[f97]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_34,negated_conjecture,
% 3.65/0.97      ( v2_funct_1(sK4) ),
% 3.65/0.97      inference(cnf_transformation,[],[f104]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_1597,plain,
% 3.65/0.97      ( v3_tops_2(sK4,X0,sK3)
% 3.65/0.97      | m1_subset_1(sK1(X0,sK3,sK4),k1_zfmisc_1(u1_struct_0(X0)))
% 3.65/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
% 3.65/0.97      | ~ l1_pre_topc(X0)
% 3.65/0.97      | k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
% 3.65/0.97      | k1_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(X0)
% 3.65/0.97      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 3.65/0.97      inference(global_propositional_subsumption,
% 3.65/0.97                [status(thm)],
% 3.65/0.97                [c_1593,c_41,c_34]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_3914,plain,
% 3.65/0.97      ( k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
% 3.65/0.97      | k1_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(X0)
% 3.65/0.97      | u1_struct_0(X0) != u1_struct_0(sK2)
% 3.65/0.97      | v3_tops_2(sK4,X0,sK3) = iProver_top
% 3.65/0.97      | m1_subset_1(sK1(X0,sK3,sK4),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.65/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
% 3.65/0.97      | l1_pre_topc(X0) != iProver_top ),
% 3.65/0.97      inference(predicate_to_equality,[status(thm)],[c_1597]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_10,plain,
% 3.65/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.65/0.97      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.65/0.97      inference(cnf_transformation,[],[f70]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_3931,plain,
% 3.65/0.97      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.65/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.65/0.97      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_4375,plain,
% 3.65/0.97      ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_relat_1(sK4) ),
% 3.65/0.97      inference(superposition,[status(thm)],[c_3924,c_3931]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_35,negated_conjecture,
% 3.65/0.97      ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3) ),
% 3.65/0.97      inference(cnf_transformation,[],[f103]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_4423,plain,
% 3.65/0.97      ( k2_struct_0(sK3) = k2_relat_1(sK4) ),
% 3.65/0.97      inference(demodulation,[status(thm)],[c_4375,c_35]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_5149,plain,
% 3.65/0.97      ( k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_relat_1(sK4)
% 3.65/0.97      | k1_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(X0)
% 3.65/0.97      | u1_struct_0(X0) != u1_struct_0(sK2)
% 3.65/0.97      | v3_tops_2(sK4,X0,sK3) = iProver_top
% 3.65/0.97      | m1_subset_1(sK1(X0,sK3,sK4),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.65/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
% 3.65/0.97      | l1_pre_topc(X0) != iProver_top ),
% 3.65/0.97      inference(light_normalisation,[status(thm)],[c_3914,c_4423]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_5153,plain,
% 3.65/0.97      ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_relat_1(sK4)
% 3.65/0.97      | k2_struct_0(sK2) != k1_relat_1(sK4)
% 3.65/0.97      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 3.65/0.97      | v3_tops_2(sK4,sK2,sK3) = iProver_top
% 3.65/0.97      | m1_subset_1(sK1(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.65/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.65/0.97      | l1_pre_topc(sK2) != iProver_top ),
% 3.65/0.97      inference(superposition,[status(thm)],[c_4679,c_5149]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_36,negated_conjecture,
% 3.65/0.97      ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2) ),
% 3.65/0.97      inference(cnf_transformation,[],[f102]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_4813,plain,
% 3.65/0.97      ( k2_struct_0(sK2) = k1_relat_1(sK4) ),
% 3.65/0.97      inference(demodulation,[status(thm)],[c_4679,c_36]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_5154,plain,
% 3.65/0.97      ( u1_struct_0(sK2) != u1_struct_0(sK2)
% 3.65/0.97      | k2_relat_1(sK4) != k2_relat_1(sK4)
% 3.65/0.97      | k1_relat_1(sK4) != k1_relat_1(sK4)
% 3.65/0.97      | v3_tops_2(sK4,sK2,sK3) = iProver_top
% 3.65/0.97      | m1_subset_1(sK1(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.65/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.65/0.97      | l1_pre_topc(sK2) != iProver_top ),
% 3.65/0.97      inference(light_normalisation,[status(thm)],[c_5153,c_4375,c_4813]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_5155,plain,
% 3.65/0.97      ( v3_tops_2(sK4,sK2,sK3) = iProver_top
% 3.65/0.97      | m1_subset_1(sK1(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.65/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.65/0.97      | l1_pre_topc(sK2) != iProver_top ),
% 3.65/0.97      inference(equality_resolution_simp,[status(thm)],[c_5154]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_32,negated_conjecture,
% 3.65/0.97      ( ~ v3_tops_2(sK4,sK2,sK3) ),
% 3.65/0.97      inference(cnf_transformation,[],[f106]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_2265,plain,
% 3.65/0.97      ( m1_subset_1(sK1(X0,sK3,sK4),k1_zfmisc_1(u1_struct_0(X0)))
% 3.65/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
% 3.65/0.97      | ~ l1_pre_topc(X0)
% 3.65/0.97      | k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
% 3.65/0.97      | k1_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(X0)
% 3.65/0.97      | u1_struct_0(X0) != u1_struct_0(sK2)
% 3.65/0.97      | sK3 != sK3
% 3.65/0.97      | sK2 != X0
% 3.65/0.97      | sK4 != sK4 ),
% 3.65/0.97      inference(resolution_lifted,[status(thm)],[c_32,c_1597]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_2266,plain,
% 3.65/0.97      ( m1_subset_1(sK1(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.65/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 3.65/0.97      | ~ l1_pre_topc(sK2)
% 3.65/0.97      | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
% 3.65/0.97      | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
% 3.65/0.97      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 3.65/0.97      inference(unflattening,[status(thm)],[c_2265]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_45,negated_conjecture,
% 3.65/0.97      ( l1_pre_topc(sK2) ),
% 3.65/0.97      inference(cnf_transformation,[],[f93]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_2268,plain,
% 3.65/0.97      ( m1_subset_1(sK1(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.65/0.97      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 3.65/0.97      inference(global_propositional_subsumption,
% 3.65/0.97                [status(thm)],
% 3.65/0.97                [c_2266,c_45,c_39,c_36,c_35]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_2270,plain,
% 3.65/0.97      ( u1_struct_0(sK2) != u1_struct_0(sK2)
% 3.65/0.97      | m1_subset_1(sK1(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.65/0.97      inference(predicate_to_equality,[status(thm)],[c_2268]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_3117,plain,( X0 = X0 ),theory(equality) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_4083,plain,
% 3.65/0.97      ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
% 3.65/0.97      inference(instantiation,[status(thm)],[c_3117]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_8446,plain,
% 3.65/0.97      ( m1_subset_1(sK1(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.65/0.97      inference(global_propositional_subsumption,
% 3.65/0.97                [status(thm)],
% 3.65/0.97                [c_5155,c_2270,c_4083]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_3922,plain,
% 3.65/0.97      ( l1_pre_topc(sK2) = iProver_top ),
% 3.65/0.97      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_22,plain,
% 3.65/0.97      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 3.65/0.97      inference(cnf_transformation,[],[f82]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_21,plain,
% 3.65/0.97      ( ~ l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 3.65/0.97      inference(cnf_transformation,[],[f81]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_595,plain,
% 3.65/0.97      ( ~ l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 3.65/0.97      inference(resolution,[status(thm)],[c_22,c_21]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_3921,plain,
% 3.65/0.97      ( k2_struct_0(X0) = u1_struct_0(X0)
% 3.65/0.97      | l1_pre_topc(X0) != iProver_top ),
% 3.65/0.97      inference(predicate_to_equality,[status(thm)],[c_595]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_5752,plain,
% 3.65/0.97      ( k2_struct_0(sK2) = u1_struct_0(sK2) ),
% 3.65/0.97      inference(superposition,[status(thm)],[c_3922,c_3921]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_5753,plain,
% 3.65/0.97      ( u1_struct_0(sK2) = k1_relat_1(sK4) ),
% 3.65/0.97      inference(light_normalisation,[status(thm)],[c_5752,c_4813]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_8450,plain,
% 3.65/0.97      ( m1_subset_1(sK1(sK2,sK3,sK4),k1_zfmisc_1(k1_relat_1(sK4))) = iProver_top ),
% 3.65/0.97      inference(light_normalisation,[status(thm)],[c_8446,c_5753]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_4,plain,
% 3.65/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.65/0.97      inference(cnf_transformation,[],[f63]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_3934,plain,
% 3.65/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.65/0.97      | r1_tarski(X0,X1) = iProver_top ),
% 3.65/0.97      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_8452,plain,
% 3.65/0.97      ( r1_tarski(sK1(sK2,sK3,sK4),k1_relat_1(sK4)) = iProver_top ),
% 3.65/0.97      inference(superposition,[status(thm)],[c_8450,c_3934]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_6,plain,
% 3.65/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.65/0.97      | v1_relat_1(X0) ),
% 3.65/0.97      inference(cnf_transformation,[],[f66]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_5,plain,
% 3.65/0.97      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.65/0.97      | ~ v1_relat_1(X1)
% 3.65/0.97      | ~ v1_funct_1(X1)
% 3.65/0.97      | ~ v2_funct_1(X1)
% 3.65/0.97      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
% 3.65/0.97      inference(cnf_transformation,[],[f65]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_1860,plain,
% 3.65/0.97      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.65/0.97      | ~ v1_relat_1(X1)
% 3.65/0.97      | ~ v1_funct_1(X1)
% 3.65/0.97      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
% 3.65/0.97      | sK4 != X1 ),
% 3.65/0.97      inference(resolution_lifted,[status(thm)],[c_5,c_34]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_1861,plain,
% 3.65/0.97      ( ~ r1_tarski(X0,k1_relat_1(sK4))
% 3.65/0.97      | ~ v1_relat_1(sK4)
% 3.65/0.97      | ~ v1_funct_1(sK4)
% 3.65/0.97      | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
% 3.65/0.97      inference(unflattening,[status(thm)],[c_1860]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_1223,plain,
% 3.65/0.97      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.65/0.97      | ~ v1_relat_1(X1)
% 3.65/0.97      | ~ v1_funct_1(X1)
% 3.65/0.97      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
% 3.65/0.97      | sK4 != X1 ),
% 3.65/0.97      inference(resolution_lifted,[status(thm)],[c_5,c_34]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_1224,plain,
% 3.65/0.97      ( ~ r1_tarski(X0,k1_relat_1(sK4))
% 3.65/0.97      | ~ v1_relat_1(sK4)
% 3.65/0.97      | ~ v1_funct_1(sK4)
% 3.65/0.97      | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
% 3.65/0.97      inference(unflattening,[status(thm)],[c_1223]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_1863,plain,
% 3.65/0.97      ( ~ v1_relat_1(sK4)
% 3.65/0.97      | ~ r1_tarski(X0,k1_relat_1(sK4))
% 3.65/0.97      | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
% 3.65/0.97      inference(global_propositional_subsumption,
% 3.65/0.97                [status(thm)],
% 3.65/0.97                [c_1861,c_41,c_1224]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_1864,plain,
% 3.65/0.97      ( ~ r1_tarski(X0,k1_relat_1(sK4))
% 3.65/0.97      | ~ v1_relat_1(sK4)
% 3.65/0.97      | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
% 3.65/0.97      inference(renaming,[status(thm)],[c_1863]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_1881,plain,
% 3.65/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.65/0.97      | ~ r1_tarski(X3,k1_relat_1(sK4))
% 3.65/0.97      | k10_relat_1(sK4,k9_relat_1(sK4,X3)) = X3
% 3.65/0.97      | sK4 != X0 ),
% 3.65/0.97      inference(resolution_lifted,[status(thm)],[c_6,c_1864]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_1882,plain,
% 3.65/0.97      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.65/0.97      | ~ r1_tarski(X2,k1_relat_1(sK4))
% 3.65/0.97      | k10_relat_1(sK4,k9_relat_1(sK4,X2)) = X2 ),
% 3.65/0.97      inference(unflattening,[status(thm)],[c_1881]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_3113,plain,
% 3.65/0.97      ( ~ r1_tarski(X0,k1_relat_1(sK4))
% 3.65/0.97      | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
% 3.65/0.97      | ~ sP0_iProver_split ),
% 3.65/0.97      inference(splitting,
% 3.65/0.97                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.65/0.97                [c_1882]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_3908,plain,
% 3.65/0.97      ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
% 3.65/0.97      | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
% 3.65/0.97      | sP0_iProver_split != iProver_top ),
% 3.65/0.97      inference(predicate_to_equality,[status(thm)],[c_3113]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_54,plain,
% 3.65/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 3.65/0.97      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_3115,plain,
% 3.65/0.97      ( sP1_iProver_split | sP0_iProver_split ),
% 3.65/0.97      inference(splitting,
% 3.65/0.97                [splitting(split),new_symbols(definition,[])],
% 3.65/0.97                [c_1882]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_3159,plain,
% 3.65/0.97      ( sP1_iProver_split = iProver_top
% 3.65/0.97      | sP0_iProver_split = iProver_top ),
% 3.65/0.97      inference(predicate_to_equality,[status(thm)],[c_3115]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_3163,plain,
% 3.65/0.97      ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
% 3.65/0.97      | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
% 3.65/0.97      | sP0_iProver_split != iProver_top ),
% 3.65/0.97      inference(predicate_to_equality,[status(thm)],[c_3113]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_3114,plain,
% 3.65/0.97      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.65/0.97      | ~ sP1_iProver_split ),
% 3.65/0.97      inference(splitting,
% 3.65/0.97                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 3.65/0.97                [c_1882]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_4056,plain,
% 3.65/0.97      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 3.65/0.97      | ~ sP1_iProver_split ),
% 3.65/0.97      inference(instantiation,[status(thm)],[c_3114]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_4057,plain,
% 3.65/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.65/0.97      | sP1_iProver_split != iProver_top ),
% 3.65/0.97      inference(predicate_to_equality,[status(thm)],[c_4056]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_4670,plain,
% 3.65/0.97      ( r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
% 3.65/0.97      | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
% 3.65/0.97      inference(global_propositional_subsumption,
% 3.65/0.97                [status(thm)],
% 3.65/0.97                [c_3908,c_54,c_3159,c_3163,c_4057]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_4671,plain,
% 3.65/0.97      ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
% 3.65/0.97      | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top ),
% 3.65/0.97      inference(renaming,[status(thm)],[c_4670]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_8844,plain,
% 3.65/0.97      ( k10_relat_1(sK4,k9_relat_1(sK4,sK1(sK2,sK3,sK4))) = sK1(sK2,sK3,sK4) ),
% 3.65/0.97      inference(superposition,[status(thm)],[c_8452,c_4671]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_3923,plain,
% 3.65/0.97      ( l1_pre_topc(sK3) = iProver_top ),
% 3.65/0.97      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_5751,plain,
% 3.65/0.97      ( k2_struct_0(sK3) = u1_struct_0(sK3) ),
% 3.65/0.97      inference(superposition,[status(thm)],[c_3923,c_3921]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_5754,plain,
% 3.65/0.97      ( u1_struct_0(sK3) = k2_relat_1(sK4) ),
% 3.65/0.97      inference(light_normalisation,[status(thm)],[c_5751,c_4423]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_11,plain,
% 3.65/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.65/0.97      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.65/0.97      inference(cnf_transformation,[],[f71]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_3930,plain,
% 3.65/0.97      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.65/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.65/0.97      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_4808,plain,
% 3.65/0.97      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k9_relat_1(sK4,X0) ),
% 3.65/0.97      inference(superposition,[status(thm)],[c_3924,c_3930]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_8,plain,
% 3.65/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.65/0.97      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
% 3.65/0.97      inference(cnf_transformation,[],[f68]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_3933,plain,
% 3.65/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.65/0.97      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
% 3.65/0.97      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_5295,plain,
% 3.65/0.97      ( m1_subset_1(k9_relat_1(sK4,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 3.65/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top ),
% 3.65/0.97      inference(superposition,[status(thm)],[c_4808,c_3933]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_5650,plain,
% 3.65/0.97      ( m1_subset_1(k9_relat_1(sK4,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.65/0.97      inference(global_propositional_subsumption,
% 3.65/0.97                [status(thm)],
% 3.65/0.97                [c_5295,c_54]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_5926,plain,
% 3.65/0.97      ( m1_subset_1(k9_relat_1(sK4,X0),k1_zfmisc_1(k2_relat_1(sK4))) = iProver_top ),
% 3.65/0.97      inference(demodulation,[status(thm)],[c_5754,c_5650]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_20,plain,
% 3.65/0.97      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.65/0.97      | ~ v5_pre_topc(X0,X1,X2)
% 3.65/0.97      | ~ v4_pre_topc(X3,X2)
% 3.65/0.97      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
% 3.65/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.65/0.97      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 3.65/0.97      | ~ l1_pre_topc(X2)
% 3.65/0.97      | ~ l1_pre_topc(X1)
% 3.65/0.97      | ~ v1_funct_1(X0) ),
% 3.65/0.97      inference(cnf_transformation,[],[f77]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_1382,plain,
% 3.65/0.97      ( ~ v5_pre_topc(X0,X1,X2)
% 3.65/0.97      | ~ v4_pre_topc(X3,X2)
% 3.65/0.97      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
% 3.65/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.65/0.97      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 3.65/0.97      | ~ l1_pre_topc(X1)
% 3.65/0.97      | ~ l1_pre_topc(X2)
% 3.65/0.97      | ~ v1_funct_1(X0)
% 3.65/0.97      | u1_struct_0(X2) != u1_struct_0(sK3)
% 3.65/0.97      | u1_struct_0(X1) != u1_struct_0(sK2)
% 3.65/0.97      | sK4 != X0 ),
% 3.65/0.97      inference(resolution_lifted,[status(thm)],[c_20,c_40]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_1383,plain,
% 3.65/0.97      ( ~ v5_pre_topc(sK4,X0,X1)
% 3.65/0.97      | ~ v4_pre_topc(X2,X1)
% 3.65/0.97      | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X2),X0)
% 3.65/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.65/0.97      | ~ l1_pre_topc(X0)
% 3.65/0.97      | ~ l1_pre_topc(X1)
% 3.65/0.97      | ~ v1_funct_1(sK4)
% 3.65/0.97      | u1_struct_0(X1) != u1_struct_0(sK3)
% 3.65/0.97      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 3.65/0.97      inference(unflattening,[status(thm)],[c_1382]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_1387,plain,
% 3.65/0.97      ( ~ l1_pre_topc(X1)
% 3.65/0.97      | ~ l1_pre_topc(X0)
% 3.65/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.65/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.97      | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X2),X0)
% 3.65/0.97      | ~ v4_pre_topc(X2,X1)
% 3.65/0.97      | ~ v5_pre_topc(sK4,X0,X1)
% 3.65/0.97      | u1_struct_0(X1) != u1_struct_0(sK3)
% 3.65/0.97      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 3.65/0.97      inference(global_propositional_subsumption,
% 3.65/0.97                [status(thm)],
% 3.65/0.97                [c_1383,c_41]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_1388,plain,
% 3.65/0.97      ( ~ v5_pre_topc(sK4,X0,X1)
% 3.65/0.97      | ~ v4_pre_topc(X2,X1)
% 3.65/0.97      | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X2),X0)
% 3.65/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.65/0.97      | ~ l1_pre_topc(X1)
% 3.65/0.97      | ~ l1_pre_topc(X0)
% 3.65/0.97      | u1_struct_0(X1) != u1_struct_0(sK3)
% 3.65/0.97      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 3.65/0.97      inference(renaming,[status(thm)],[c_1387]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_3920,plain,
% 3.65/0.97      ( u1_struct_0(X0) != u1_struct_0(sK3)
% 3.65/0.97      | u1_struct_0(X1) != u1_struct_0(sK2)
% 3.65/0.97      | v5_pre_topc(sK4,X1,X0) != iProver_top
% 3.65/0.97      | v4_pre_topc(X2,X0) != iProver_top
% 3.65/0.97      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK4,X2),X1) = iProver_top
% 3.65/0.97      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.65/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 3.65/0.97      | l1_pre_topc(X0) != iProver_top
% 3.65/0.97      | l1_pre_topc(X1) != iProver_top ),
% 3.65/0.97      inference(predicate_to_equality,[status(thm)],[c_1388]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_4998,plain,
% 3.65/0.97      ( u1_struct_0(X0) != u1_struct_0(sK3)
% 3.65/0.97      | v5_pre_topc(sK4,sK2,X0) != iProver_top
% 3.65/0.97      | v4_pre_topc(X1,X0) != iProver_top
% 3.65/0.97      | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(X0),sK4,X1),sK2) = iProver_top
% 3.65/0.97      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.65/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
% 3.65/0.97      | l1_pre_topc(X0) != iProver_top
% 3.65/0.97      | l1_pre_topc(sK2) != iProver_top ),
% 3.65/0.97      inference(equality_resolution,[status(thm)],[c_3920]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_48,plain,
% 3.65/0.97      ( l1_pre_topc(sK2) = iProver_top ),
% 3.65/0.97      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_4051,plain,
% 3.65/0.97      ( ~ v5_pre_topc(sK4,sK2,X0)
% 3.65/0.97      | ~ v4_pre_topc(X1,X0)
% 3.65/0.97      | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(X0),sK4,X1),sK2)
% 3.65/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.65/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 3.65/0.97      | ~ l1_pre_topc(X0)
% 3.65/0.97      | ~ l1_pre_topc(sK2)
% 3.65/0.97      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.65/0.97      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 3.65/0.97      inference(instantiation,[status(thm)],[c_1388]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_4052,plain,
% 3.65/0.97      ( u1_struct_0(X0) != u1_struct_0(sK3)
% 3.65/0.97      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 3.65/0.97      | v5_pre_topc(sK4,sK2,X0) != iProver_top
% 3.65/0.97      | v4_pre_topc(X1,X0) != iProver_top
% 3.65/0.97      | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(X0),sK4,X1),sK2) = iProver_top
% 3.65/0.97      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.65/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
% 3.65/0.97      | l1_pre_topc(X0) != iProver_top
% 3.65/0.97      | l1_pre_topc(sK2) != iProver_top ),
% 3.65/0.97      inference(predicate_to_equality,[status(thm)],[c_4051]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_6925,plain,
% 3.65/0.97      ( l1_pre_topc(X0) != iProver_top
% 3.65/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
% 3.65/0.97      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.65/0.97      | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(X0),sK4,X1),sK2) = iProver_top
% 3.65/0.97      | v4_pre_topc(X1,X0) != iProver_top
% 3.65/0.97      | v5_pre_topc(sK4,sK2,X0) != iProver_top
% 3.65/0.97      | u1_struct_0(X0) != u1_struct_0(sK3) ),
% 3.65/0.97      inference(global_propositional_subsumption,
% 3.65/0.97                [status(thm)],
% 3.65/0.97                [c_4998,c_48,c_4052,c_4083]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_6926,plain,
% 3.65/0.97      ( u1_struct_0(X0) != u1_struct_0(sK3)
% 3.65/0.97      | v5_pre_topc(sK4,sK2,X0) != iProver_top
% 3.65/0.97      | v4_pre_topc(X1,X0) != iProver_top
% 3.65/0.97      | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(X0),sK4,X1),sK2) = iProver_top
% 3.65/0.97      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.65/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
% 3.65/0.97      | l1_pre_topc(X0) != iProver_top ),
% 3.65/0.97      inference(renaming,[status(thm)],[c_6925]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_6931,plain,
% 3.65/0.97      ( u1_struct_0(X0) != k2_relat_1(sK4)
% 3.65/0.97      | v5_pre_topc(sK4,sK2,X0) != iProver_top
% 3.65/0.97      | v4_pre_topc(X1,X0) != iProver_top
% 3.65/0.97      | v4_pre_topc(k8_relset_1(k1_relat_1(sK4),u1_struct_0(X0),sK4,X1),sK2) = iProver_top
% 3.65/0.97      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.65/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),u1_struct_0(X0)))) != iProver_top
% 3.65/0.97      | l1_pre_topc(X0) != iProver_top ),
% 3.65/0.97      inference(light_normalisation,[status(thm)],[c_6926,c_5753,c_5754]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_6936,plain,
% 3.65/0.97      ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 3.65/0.97      | v4_pre_topc(X0,sK3) != iProver_top
% 3.65/0.97      | v4_pre_topc(k8_relset_1(k1_relat_1(sK4),u1_struct_0(sK3),sK4,X0),sK2) = iProver_top
% 3.65/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.65/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.65/0.97      | l1_pre_topc(sK3) != iProver_top ),
% 3.65/0.97      inference(superposition,[status(thm)],[c_5754,c_6931]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_12,plain,
% 3.65/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.65/0.97      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 3.65/0.97      inference(cnf_transformation,[],[f72]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_3929,plain,
% 3.65/0.97      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 3.65/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.65/0.97      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_4746,plain,
% 3.65/0.97      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k10_relat_1(sK4,X0) ),
% 3.65/0.97      inference(superposition,[status(thm)],[c_3924,c_3929]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_5767,plain,
% 3.65/0.97      ( k8_relset_1(k1_relat_1(sK4),u1_struct_0(sK3),sK4,X0) = k10_relat_1(sK4,X0) ),
% 3.65/0.97      inference(demodulation,[status(thm)],[c_5753,c_4746]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_5784,plain,
% 3.65/0.97      ( k8_relset_1(k1_relat_1(sK4),k2_relat_1(sK4),sK4,X0) = k10_relat_1(sK4,X0) ),
% 3.65/0.97      inference(light_normalisation,[status(thm)],[c_5767,c_5754]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_6937,plain,
% 3.65/0.97      ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 3.65/0.97      | v4_pre_topc(X0,sK3) != iProver_top
% 3.65/0.97      | v4_pre_topc(k10_relat_1(sK4,X0),sK2) = iProver_top
% 3.65/0.97      | m1_subset_1(X0,k1_zfmisc_1(k2_relat_1(sK4))) != iProver_top
% 3.65/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)))) != iProver_top
% 3.65/0.97      | l1_pre_topc(sK3) != iProver_top ),
% 3.65/0.97      inference(light_normalisation,[status(thm)],[c_6936,c_5754,c_5784]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_51,plain,
% 3.65/0.97      ( l1_pre_topc(sK3) = iProver_top ),
% 3.65/0.97      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_33,negated_conjecture,
% 3.65/0.97      ( v5_pre_topc(sK4,sK2,sK3) ),
% 3.65/0.97      inference(cnf_transformation,[],[f105]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_58,plain,
% 3.65/0.97      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 3.65/0.97      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_5775,plain,
% 3.65/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),u1_struct_0(sK3)))) = iProver_top ),
% 3.65/0.97      inference(demodulation,[status(thm)],[c_5753,c_3924]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_5776,plain,
% 3.65/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)))) = iProver_top ),
% 3.65/0.97      inference(light_normalisation,[status(thm)],[c_5775,c_5754]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_7253,plain,
% 3.65/0.97      ( v4_pre_topc(X0,sK3) != iProver_top
% 3.65/0.97      | v4_pre_topc(k10_relat_1(sK4,X0),sK2) = iProver_top
% 3.65/0.97      | m1_subset_1(X0,k1_zfmisc_1(k2_relat_1(sK4))) != iProver_top ),
% 3.65/0.97      inference(global_propositional_subsumption,
% 3.65/0.97                [status(thm)],
% 3.65/0.97                [c_6937,c_51,c_58,c_5776]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_7261,plain,
% 3.65/0.97      ( v4_pre_topc(k10_relat_1(sK4,k9_relat_1(sK4,X0)),sK2) = iProver_top
% 3.65/0.97      | v4_pre_topc(k9_relat_1(sK4,X0),sK3) != iProver_top ),
% 3.65/0.97      inference(superposition,[status(thm)],[c_5926,c_7253]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_10107,plain,
% 3.65/0.97      ( v4_pre_topc(sK1(sK2,sK3,sK4),sK2) = iProver_top
% 3.65/0.97      | v4_pre_topc(k9_relat_1(sK4,sK1(sK2,sK3,sK4)),sK3) != iProver_top ),
% 3.65/0.97      inference(superposition,[status(thm)],[c_8844,c_7261]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_23,plain,
% 3.65/0.97      ( v3_tops_2(X0,X1,X2)
% 3.65/0.97      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.65/0.97      | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK1(X1,X2,X0)),X2)
% 3.65/0.97      | ~ v4_pre_topc(sK1(X1,X2,X0),X1)
% 3.65/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.65/0.97      | v2_struct_0(X2)
% 3.65/0.97      | ~ l1_pre_topc(X2)
% 3.65/0.97      | ~ l1_pre_topc(X1)
% 3.65/0.97      | ~ v1_funct_1(X0)
% 3.65/0.97      | ~ v2_funct_1(X0)
% 3.65/0.97      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 3.65/0.97      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1) ),
% 3.65/0.97      inference(cnf_transformation,[],[f90]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_957,plain,
% 3.65/0.97      ( v3_tops_2(X0,X1,X2)
% 3.65/0.97      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.65/0.97      | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK1(X1,X2,X0)),X2)
% 3.65/0.97      | ~ v4_pre_topc(sK1(X1,X2,X0),X1)
% 3.65/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.65/0.97      | ~ l1_pre_topc(X1)
% 3.65/0.97      | ~ l1_pre_topc(X2)
% 3.65/0.97      | ~ v1_funct_1(X0)
% 3.65/0.97      | ~ v2_funct_1(X0)
% 3.65/0.97      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 3.65/0.97      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
% 3.65/0.97      | sK3 != X2 ),
% 3.65/0.97      inference(resolution_lifted,[status(thm)],[c_23,c_44]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_958,plain,
% 3.65/0.97      ( v3_tops_2(X0,X1,sK3)
% 3.65/0.97      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
% 3.65/0.97      | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,sK1(X1,sK3,X0)),sK3)
% 3.65/0.97      | ~ v4_pre_topc(sK1(X1,sK3,X0),X1)
% 3.65/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
% 3.65/0.97      | ~ l1_pre_topc(X1)
% 3.65/0.97      | ~ l1_pre_topc(sK3)
% 3.65/0.97      | ~ v1_funct_1(X0)
% 3.65/0.97      | ~ v2_funct_1(X0)
% 3.65/0.97      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(sK3)
% 3.65/0.97      | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(X1) ),
% 3.65/0.97      inference(unflattening,[status(thm)],[c_957]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_962,plain,
% 3.65/0.97      ( ~ l1_pre_topc(X1)
% 3.65/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
% 3.65/0.97      | ~ v4_pre_topc(sK1(X1,sK3,X0),X1)
% 3.65/0.97      | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,sK1(X1,sK3,X0)),sK3)
% 3.65/0.97      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
% 3.65/0.97      | v3_tops_2(X0,X1,sK3)
% 3.65/0.97      | ~ v1_funct_1(X0)
% 3.65/0.97      | ~ v2_funct_1(X0)
% 3.65/0.97      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(sK3)
% 3.65/0.97      | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(X1) ),
% 3.65/0.97      inference(global_propositional_subsumption,
% 3.65/0.97                [status(thm)],
% 3.65/0.97                [c_958,c_42]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_963,plain,
% 3.65/0.97      ( v3_tops_2(X0,X1,sK3)
% 3.65/0.97      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
% 3.65/0.97      | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,sK1(X1,sK3,X0)),sK3)
% 3.65/0.97      | ~ v4_pre_topc(sK1(X1,sK3,X0),X1)
% 3.65/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
% 3.65/0.97      | ~ l1_pre_topc(X1)
% 3.65/0.97      | ~ v1_funct_1(X0)
% 3.65/0.97      | ~ v2_funct_1(X0)
% 3.65/0.97      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(sK3)
% 3.65/0.97      | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(X1) ),
% 3.65/0.97      inference(renaming,[status(thm)],[c_962]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_1520,plain,
% 3.65/0.97      ( v3_tops_2(X0,X1,sK3)
% 3.65/0.97      | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,sK1(X1,sK3,X0)),sK3)
% 3.65/0.97      | ~ v4_pre_topc(sK1(X1,sK3,X0),X1)
% 3.65/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
% 3.65/0.97      | ~ l1_pre_topc(X1)
% 3.65/0.97      | ~ v1_funct_1(X0)
% 3.65/0.97      | ~ v2_funct_1(X0)
% 3.65/0.97      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(sK3)
% 3.65/0.97      | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(X1)
% 3.65/0.97      | u1_struct_0(X1) != u1_struct_0(sK2)
% 3.65/0.97      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 3.65/0.97      | sK4 != X0 ),
% 3.65/0.97      inference(resolution_lifted,[status(thm)],[c_40,c_963]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_1521,plain,
% 3.65/0.97      ( v3_tops_2(sK4,X0,sK3)
% 3.65/0.97      | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK1(X0,sK3,sK4)),sK3)
% 3.65/0.97      | ~ v4_pre_topc(sK1(X0,sK3,sK4),X0)
% 3.65/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
% 3.65/0.97      | ~ l1_pre_topc(X0)
% 3.65/0.97      | ~ v1_funct_1(sK4)
% 3.65/0.97      | ~ v2_funct_1(sK4)
% 3.65/0.97      | k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
% 3.65/0.97      | k1_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(X0)
% 3.65/0.97      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 3.65/0.97      inference(unflattening,[status(thm)],[c_1520]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_1525,plain,
% 3.65/0.97      ( v3_tops_2(sK4,X0,sK3)
% 3.65/0.97      | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK1(X0,sK3,sK4)),sK3)
% 3.65/0.97      | ~ v4_pre_topc(sK1(X0,sK3,sK4),X0)
% 3.65/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
% 3.65/0.97      | ~ l1_pre_topc(X0)
% 3.65/0.97      | k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
% 3.65/0.97      | k1_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(X0)
% 3.65/0.97      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 3.65/0.97      inference(global_propositional_subsumption,
% 3.65/0.97                [status(thm)],
% 3.65/0.97                [c_1521,c_41,c_34]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_3916,plain,
% 3.65/0.97      ( k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
% 3.65/0.97      | k1_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(X0)
% 3.65/0.97      | u1_struct_0(X0) != u1_struct_0(sK2)
% 3.65/0.97      | v3_tops_2(sK4,X0,sK3) = iProver_top
% 3.65/0.97      | v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK1(X0,sK3,sK4)),sK3) != iProver_top
% 3.65/0.97      | v4_pre_topc(sK1(X0,sK3,sK4),X0) != iProver_top
% 3.65/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
% 3.65/0.97      | l1_pre_topc(X0) != iProver_top ),
% 3.65/0.97      inference(predicate_to_equality,[status(thm)],[c_1525]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_5056,plain,
% 3.65/0.97      ( k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_relat_1(sK4)
% 3.65/0.97      | k1_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(X0)
% 3.65/0.97      | u1_struct_0(X0) != u1_struct_0(sK2)
% 3.65/0.97      | v3_tops_2(sK4,X0,sK3) = iProver_top
% 3.65/0.97      | v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK1(X0,sK3,sK4)),sK3) != iProver_top
% 3.65/0.97      | v4_pre_topc(sK1(X0,sK3,sK4),X0) != iProver_top
% 3.65/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
% 3.65/0.97      | l1_pre_topc(X0) != iProver_top ),
% 3.65/0.97      inference(light_normalisation,[status(thm)],[c_3916,c_4423]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_5060,plain,
% 3.65/0.97      ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_relat_1(sK4)
% 3.65/0.97      | k2_struct_0(sK2) != k1_relat_1(sK4)
% 3.65/0.97      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 3.65/0.97      | v3_tops_2(sK4,sK2,sK3) = iProver_top
% 3.65/0.97      | v4_pre_topc(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4)),sK3) != iProver_top
% 3.65/0.97      | v4_pre_topc(sK1(sK2,sK3,sK4),sK2) != iProver_top
% 3.65/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.65/0.97      | l1_pre_topc(sK2) != iProver_top ),
% 3.65/0.97      inference(superposition,[status(thm)],[c_4679,c_5056]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_5061,plain,
% 3.65/0.97      ( u1_struct_0(sK2) != u1_struct_0(sK2)
% 3.65/0.97      | k2_relat_1(sK4) != k2_relat_1(sK4)
% 3.65/0.97      | k1_relat_1(sK4) != k1_relat_1(sK4)
% 3.65/0.97      | v3_tops_2(sK4,sK2,sK3) = iProver_top
% 3.65/0.97      | v4_pre_topc(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4)),sK3) != iProver_top
% 3.65/0.97      | v4_pre_topc(sK1(sK2,sK3,sK4),sK2) != iProver_top
% 3.65/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.65/0.97      | l1_pre_topc(sK2) != iProver_top ),
% 3.65/0.97      inference(light_normalisation,[status(thm)],[c_5060,c_4375,c_4813]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_5062,plain,
% 3.65/0.97      ( v3_tops_2(sK4,sK2,sK3) = iProver_top
% 3.65/0.97      | v4_pre_topc(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4)),sK3) != iProver_top
% 3.65/0.97      | v4_pre_topc(sK1(sK2,sK3,sK4),sK2) != iProver_top
% 3.65/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.65/0.97      | l1_pre_topc(sK2) != iProver_top ),
% 3.65/0.97      inference(equality_resolution_simp,[status(thm)],[c_5061]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_5063,plain,
% 3.65/0.97      ( v3_tops_2(sK4,sK2,sK3) = iProver_top
% 3.65/0.97      | v4_pre_topc(sK1(sK2,sK3,sK4),sK2) != iProver_top
% 3.65/0.97      | v4_pre_topc(k9_relat_1(sK4,sK1(sK2,sK3,sK4)),sK3) != iProver_top
% 3.65/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.65/0.97      | l1_pre_topc(sK2) != iProver_top ),
% 3.65/0.97      inference(demodulation,[status(thm)],[c_5062,c_4808]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_2296,plain,
% 3.65/0.97      ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK1(X0,sK3,sK4)),sK3)
% 3.65/0.97      | ~ v4_pre_topc(sK1(X0,sK3,sK4),X0)
% 3.65/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
% 3.65/0.97      | ~ l1_pre_topc(X0)
% 3.65/0.97      | k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
% 3.65/0.97      | k1_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(X0)
% 3.65/0.97      | u1_struct_0(X0) != u1_struct_0(sK2)
% 3.65/0.97      | sK3 != sK3
% 3.65/0.97      | sK2 != X0
% 3.65/0.97      | sK4 != sK4 ),
% 3.65/0.97      inference(resolution_lifted,[status(thm)],[c_32,c_1525]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_2297,plain,
% 3.65/0.97      ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4)),sK3)
% 3.65/0.97      | ~ v4_pre_topc(sK1(sK2,sK3,sK4),sK2)
% 3.65/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 3.65/0.97      | ~ l1_pre_topc(sK2)
% 3.65/0.97      | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
% 3.65/0.97      | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
% 3.65/0.97      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 3.65/0.97      inference(unflattening,[status(thm)],[c_2296]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_2299,plain,
% 3.65/0.97      ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4)),sK3)
% 3.65/0.97      | ~ v4_pre_topc(sK1(sK2,sK3,sK4),sK2)
% 3.65/0.97      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 3.65/0.97      inference(global_propositional_subsumption,
% 3.65/0.97                [status(thm)],
% 3.65/0.97                [c_2297,c_45,c_39,c_36,c_35]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_2301,plain,
% 3.65/0.97      ( u1_struct_0(sK2) != u1_struct_0(sK2)
% 3.65/0.97      | v4_pre_topc(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4)),sK3) != iProver_top
% 3.65/0.97      | v4_pre_topc(sK1(sK2,sK3,sK4),sK2) != iProver_top ),
% 3.65/0.97      inference(predicate_to_equality,[status(thm)],[c_2299]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_31,plain,
% 3.65/0.97      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.65/0.97      | ~ v5_pre_topc(X0,X1,X2)
% 3.65/0.97      | ~ v4_pre_topc(X3,X1)
% 3.65/0.97      | v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X2)
% 3.65/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.65/0.97      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.97      | ~ v2_pre_topc(X2)
% 3.65/0.97      | ~ v2_pre_topc(X1)
% 3.65/0.97      | ~ v1_compts_1(X1)
% 3.65/0.97      | ~ v8_pre_topc(X2)
% 3.65/0.97      | v2_struct_0(X2)
% 3.65/0.97      | ~ l1_pre_topc(X2)
% 3.65/0.97      | ~ l1_pre_topc(X1)
% 3.65/0.97      | ~ v1_funct_1(X0)
% 3.65/0.97      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 3.65/0.97      inference(cnf_transformation,[],[f91]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_37,negated_conjecture,
% 3.65/0.97      ( v8_pre_topc(sK3) ),
% 3.65/0.97      inference(cnf_transformation,[],[f101]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_637,plain,
% 3.65/0.97      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.65/0.97      | ~ v5_pre_topc(X0,X1,X2)
% 3.65/0.97      | ~ v4_pre_topc(X3,X1)
% 3.65/0.97      | v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X2)
% 3.65/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.65/0.97      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.97      | ~ v2_pre_topc(X1)
% 3.65/0.97      | ~ v2_pre_topc(X2)
% 3.65/0.97      | ~ v1_compts_1(X1)
% 3.65/0.97      | v2_struct_0(X2)
% 3.65/0.97      | ~ l1_pre_topc(X1)
% 3.65/0.97      | ~ l1_pre_topc(X2)
% 3.65/0.97      | ~ v1_funct_1(X0)
% 3.65/0.97      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 3.65/0.97      | sK3 != X2 ),
% 3.65/0.97      inference(resolution_lifted,[status(thm)],[c_31,c_37]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_638,plain,
% 3.65/0.97      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
% 3.65/0.97      | ~ v5_pre_topc(X0,X1,sK3)
% 3.65/0.97      | ~ v4_pre_topc(X2,X1)
% 3.65/0.97      | v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,X2),sK3)
% 3.65/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
% 3.65/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.97      | ~ v2_pre_topc(X1)
% 3.65/0.97      | ~ v2_pre_topc(sK3)
% 3.65/0.97      | ~ v1_compts_1(X1)
% 3.65/0.97      | v2_struct_0(sK3)
% 3.65/0.97      | ~ l1_pre_topc(X1)
% 3.65/0.97      | ~ l1_pre_topc(sK3)
% 3.65/0.97      | ~ v1_funct_1(X0)
% 3.65/0.97      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(sK3) ),
% 3.65/0.97      inference(unflattening,[status(thm)],[c_637]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_43,negated_conjecture,
% 3.65/0.97      ( v2_pre_topc(sK3) ),
% 3.65/0.97      inference(cnf_transformation,[],[f95]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_642,plain,
% 3.65/0.97      ( ~ l1_pre_topc(X1)
% 3.65/0.97      | ~ v2_pre_topc(X1)
% 3.65/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
% 3.65/0.97      | v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,X2),sK3)
% 3.65/0.97      | ~ v4_pre_topc(X2,X1)
% 3.65/0.97      | ~ v5_pre_topc(X0,X1,sK3)
% 3.65/0.97      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
% 3.65/0.97      | ~ v1_compts_1(X1)
% 3.65/0.97      | ~ v1_funct_1(X0)
% 3.65/0.97      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(sK3) ),
% 3.65/0.97      inference(global_propositional_subsumption,
% 3.65/0.97                [status(thm)],
% 3.65/0.97                [c_638,c_44,c_43,c_42]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_643,plain,
% 3.65/0.97      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
% 3.65/0.97      | ~ v5_pre_topc(X0,X1,sK3)
% 3.65/0.97      | ~ v4_pre_topc(X2,X1)
% 3.65/0.97      | v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,X2),sK3)
% 3.65/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
% 3.65/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.97      | ~ v2_pre_topc(X1)
% 3.65/0.97      | ~ v1_compts_1(X1)
% 3.65/0.97      | ~ l1_pre_topc(X1)
% 3.65/0.97      | ~ v1_funct_1(X0)
% 3.65/0.97      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(sK3) ),
% 3.65/0.97      inference(renaming,[status(thm)],[c_642]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_38,negated_conjecture,
% 3.65/0.97      ( v1_compts_1(sK2) ),
% 3.65/0.97      inference(cnf_transformation,[],[f100]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_683,plain,
% 3.65/0.97      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
% 3.65/0.97      | ~ v5_pre_topc(X0,X1,sK3)
% 3.65/0.97      | ~ v4_pre_topc(X2,X1)
% 3.65/0.97      | v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,X2),sK3)
% 3.65/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
% 3.65/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.97      | ~ v2_pre_topc(X1)
% 3.65/0.97      | ~ l1_pre_topc(X1)
% 3.65/0.97      | ~ v1_funct_1(X0)
% 3.65/0.97      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(sK3)
% 3.65/0.97      | sK2 != X1 ),
% 3.65/0.97      inference(resolution_lifted,[status(thm)],[c_643,c_38]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_684,plain,
% 3.65/0.97      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3))
% 3.65/0.97      | ~ v5_pre_topc(X0,sK2,sK3)
% 3.65/0.97      | ~ v4_pre_topc(X1,sK2)
% 3.65/0.97      | v4_pre_topc(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0,X1),sK3)
% 3.65/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 3.65/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.65/0.97      | ~ v2_pre_topc(sK2)
% 3.65/0.97      | ~ l1_pre_topc(sK2)
% 3.65/0.97      | ~ v1_funct_1(X0)
% 3.65/0.97      | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0) != k2_struct_0(sK3) ),
% 3.65/0.97      inference(unflattening,[status(thm)],[c_683]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_46,negated_conjecture,
% 3.65/0.97      ( v2_pre_topc(sK2) ),
% 3.65/0.97      inference(cnf_transformation,[],[f92]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_688,plain,
% 3.65/0.97      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3))
% 3.65/0.97      | ~ v5_pre_topc(X0,sK2,sK3)
% 3.65/0.97      | ~ v4_pre_topc(X1,sK2)
% 3.65/0.97      | v4_pre_topc(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0,X1),sK3)
% 3.65/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 3.65/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.65/0.97      | ~ v1_funct_1(X0)
% 3.65/0.97      | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0) != k2_struct_0(sK3) ),
% 3.65/0.97      inference(global_propositional_subsumption,
% 3.65/0.97                [status(thm)],
% 3.65/0.97                [c_684,c_46,c_45]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_1747,plain,
% 3.65/0.97      ( ~ v5_pre_topc(X0,sK2,sK3)
% 3.65/0.97      | ~ v4_pre_topc(X1,sK2)
% 3.65/0.97      | v4_pre_topc(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0,X1),sK3)
% 3.65/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 3.65/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.65/0.97      | ~ v1_funct_1(X0)
% 3.65/0.97      | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0) != k2_struct_0(sK3)
% 3.65/0.97      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 3.65/0.97      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 3.65/0.97      | sK4 != X0 ),
% 3.65/0.97      inference(resolution_lifted,[status(thm)],[c_40,c_688]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_1748,plain,
% 3.65/0.97      ( ~ v5_pre_topc(sK4,sK2,sK3)
% 3.65/0.97      | ~ v4_pre_topc(X0,sK2)
% 3.65/0.97      | v4_pre_topc(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0),sK3)
% 3.65/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.65/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 3.65/0.97      | ~ v1_funct_1(sK4)
% 3.65/0.97      | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
% 3.65/0.97      inference(unflattening,[status(thm)],[c_1747]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_1752,plain,
% 3.65/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.65/0.97      | v4_pre_topc(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0),sK3)
% 3.65/0.97      | ~ v4_pre_topc(X0,sK2) ),
% 3.65/0.97      inference(global_propositional_subsumption,
% 3.65/0.97                [status(thm)],
% 3.65/0.97                [c_1748,c_41,c_39,c_35,c_33]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_1753,plain,
% 3.65/0.97      ( ~ v4_pre_topc(X0,sK2)
% 3.65/0.97      | v4_pre_topc(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0),sK3)
% 3.65/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.65/0.97      inference(renaming,[status(thm)],[c_1752]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_4411,plain,
% 3.65/0.97      ( v4_pre_topc(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4)),sK3)
% 3.65/0.97      | ~ v4_pre_topc(sK1(sK2,sK3,sK4),sK2)
% 3.65/0.97      | ~ m1_subset_1(sK1(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.65/0.97      inference(instantiation,[status(thm)],[c_1753]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_4412,plain,
% 3.65/0.97      ( v4_pre_topc(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4)),sK3) = iProver_top
% 3.65/0.97      | v4_pre_topc(sK1(sK2,sK3,sK4),sK2) != iProver_top
% 3.65/0.97      | m1_subset_1(sK1(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.65/0.97      inference(predicate_to_equality,[status(thm)],[c_4411]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_6920,plain,
% 3.65/0.97      ( v4_pre_topc(sK1(sK2,sK3,sK4),sK2) != iProver_top ),
% 3.65/0.97      inference(global_propositional_subsumption,
% 3.65/0.97                [status(thm)],
% 3.65/0.97                [c_5063,c_2270,c_2301,c_4083,c_4412]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_24,plain,
% 3.65/0.97      ( v3_tops_2(X0,X1,X2)
% 3.65/0.97      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.65/0.97      | v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK1(X1,X2,X0)),X2)
% 3.65/0.97      | v4_pre_topc(sK1(X1,X2,X0),X1)
% 3.65/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.65/0.97      | v2_struct_0(X2)
% 3.65/0.97      | ~ l1_pre_topc(X2)
% 3.65/0.97      | ~ l1_pre_topc(X1)
% 3.65/0.97      | ~ v1_funct_1(X0)
% 3.65/0.97      | ~ v2_funct_1(X0)
% 3.65/0.97      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 3.65/0.97      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1) ),
% 3.65/0.97      inference(cnf_transformation,[],[f89]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_917,plain,
% 3.65/0.97      ( v3_tops_2(X0,X1,X2)
% 3.65/0.97      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.65/0.97      | v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK1(X1,X2,X0)),X2)
% 3.65/0.97      | v4_pre_topc(sK1(X1,X2,X0),X1)
% 3.65/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.65/0.97      | ~ l1_pre_topc(X1)
% 3.65/0.97      | ~ l1_pre_topc(X2)
% 3.65/0.97      | ~ v1_funct_1(X0)
% 3.65/0.97      | ~ v2_funct_1(X0)
% 3.65/0.97      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 3.65/0.97      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
% 3.65/0.97      | sK3 != X2 ),
% 3.65/0.97      inference(resolution_lifted,[status(thm)],[c_24,c_44]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_918,plain,
% 3.65/0.97      ( v3_tops_2(X0,X1,sK3)
% 3.65/0.97      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
% 3.65/0.97      | v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,sK1(X1,sK3,X0)),sK3)
% 3.65/0.97      | v4_pre_topc(sK1(X1,sK3,X0),X1)
% 3.65/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
% 3.65/0.97      | ~ l1_pre_topc(X1)
% 3.65/0.97      | ~ l1_pre_topc(sK3)
% 3.65/0.97      | ~ v1_funct_1(X0)
% 3.65/0.97      | ~ v2_funct_1(X0)
% 3.65/0.97      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(sK3)
% 3.65/0.97      | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(X1) ),
% 3.65/0.97      inference(unflattening,[status(thm)],[c_917]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_922,plain,
% 3.65/0.97      ( ~ l1_pre_topc(X1)
% 3.65/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
% 3.65/0.97      | v4_pre_topc(sK1(X1,sK3,X0),X1)
% 3.65/0.97      | v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,sK1(X1,sK3,X0)),sK3)
% 3.65/0.97      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
% 3.65/0.97      | v3_tops_2(X0,X1,sK3)
% 3.65/0.97      | ~ v1_funct_1(X0)
% 3.65/0.97      | ~ v2_funct_1(X0)
% 3.65/0.97      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(sK3)
% 3.65/0.97      | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(X1) ),
% 3.65/0.97      inference(global_propositional_subsumption,
% 3.65/0.97                [status(thm)],
% 3.65/0.97                [c_918,c_42]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_923,plain,
% 3.65/0.97      ( v3_tops_2(X0,X1,sK3)
% 3.65/0.97      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
% 3.65/0.97      | v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,sK1(X1,sK3,X0)),sK3)
% 3.65/0.97      | v4_pre_topc(sK1(X1,sK3,X0),X1)
% 3.65/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
% 3.65/0.97      | ~ l1_pre_topc(X1)
% 3.65/0.97      | ~ v1_funct_1(X0)
% 3.65/0.97      | ~ v2_funct_1(X0)
% 3.65/0.97      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(sK3)
% 3.65/0.97      | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(X1) ),
% 3.65/0.97      inference(renaming,[status(thm)],[c_922]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_1556,plain,
% 3.65/0.97      ( v3_tops_2(X0,X1,sK3)
% 3.65/0.97      | v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,sK1(X1,sK3,X0)),sK3)
% 3.65/0.97      | v4_pre_topc(sK1(X1,sK3,X0),X1)
% 3.65/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
% 3.65/0.97      | ~ l1_pre_topc(X1)
% 3.65/0.97      | ~ v1_funct_1(X0)
% 3.65/0.97      | ~ v2_funct_1(X0)
% 3.65/0.97      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(sK3)
% 3.65/0.97      | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(X1)
% 3.65/0.97      | u1_struct_0(X1) != u1_struct_0(sK2)
% 3.65/0.97      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 3.65/0.97      | sK4 != X0 ),
% 3.65/0.97      inference(resolution_lifted,[status(thm)],[c_40,c_923]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_1557,plain,
% 3.65/0.97      ( v3_tops_2(sK4,X0,sK3)
% 3.65/0.97      | v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK1(X0,sK3,sK4)),sK3)
% 3.65/0.97      | v4_pre_topc(sK1(X0,sK3,sK4),X0)
% 3.65/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
% 3.65/0.97      | ~ l1_pre_topc(X0)
% 3.65/0.97      | ~ v1_funct_1(sK4)
% 3.65/0.97      | ~ v2_funct_1(sK4)
% 3.65/0.97      | k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
% 3.65/0.97      | k1_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(X0)
% 3.65/0.97      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 3.65/0.97      inference(unflattening,[status(thm)],[c_1556]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_1561,plain,
% 3.65/0.97      ( v3_tops_2(sK4,X0,sK3)
% 3.65/0.97      | v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK1(X0,sK3,sK4)),sK3)
% 3.65/0.97      | v4_pre_topc(sK1(X0,sK3,sK4),X0)
% 3.65/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
% 3.65/0.97      | ~ l1_pre_topc(X0)
% 3.65/0.97      | k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
% 3.65/0.97      | k1_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(X0)
% 3.65/0.97      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 3.65/0.97      inference(global_propositional_subsumption,
% 3.65/0.97                [status(thm)],
% 3.65/0.97                [c_1557,c_41,c_34]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_3915,plain,
% 3.65/0.97      ( k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
% 3.65/0.97      | k1_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(X0)
% 3.65/0.97      | u1_struct_0(X0) != u1_struct_0(sK2)
% 3.65/0.97      | v3_tops_2(sK4,X0,sK3) = iProver_top
% 3.65/0.97      | v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK1(X0,sK3,sK4)),sK3) = iProver_top
% 3.65/0.97      | v4_pre_topc(sK1(X0,sK3,sK4),X0) = iProver_top
% 3.65/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
% 3.65/0.97      | l1_pre_topc(X0) != iProver_top ),
% 3.65/0.97      inference(predicate_to_equality,[status(thm)],[c_1561]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_5396,plain,
% 3.65/0.97      ( k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_relat_1(sK4)
% 3.65/0.97      | k1_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(X0)
% 3.65/0.97      | u1_struct_0(X0) != u1_struct_0(sK2)
% 3.65/0.97      | v3_tops_2(sK4,X0,sK3) = iProver_top
% 3.65/0.97      | v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK1(X0,sK3,sK4)),sK3) = iProver_top
% 3.65/0.97      | v4_pre_topc(sK1(X0,sK3,sK4),X0) = iProver_top
% 3.65/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
% 3.65/0.97      | l1_pre_topc(X0) != iProver_top ),
% 3.65/0.97      inference(light_normalisation,[status(thm)],[c_3915,c_4423]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_5400,plain,
% 3.65/0.97      ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_relat_1(sK4)
% 3.65/0.97      | k2_struct_0(sK2) != k1_relat_1(sK4)
% 3.65/0.97      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 3.65/0.97      | v3_tops_2(sK4,sK2,sK3) = iProver_top
% 3.65/0.97      | v4_pre_topc(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4)),sK3) = iProver_top
% 3.65/0.97      | v4_pre_topc(sK1(sK2,sK3,sK4),sK2) = iProver_top
% 3.65/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.65/0.97      | l1_pre_topc(sK2) != iProver_top ),
% 3.65/0.97      inference(superposition,[status(thm)],[c_4679,c_5396]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_5401,plain,
% 3.65/0.97      ( u1_struct_0(sK2) != u1_struct_0(sK2)
% 3.65/0.97      | k2_relat_1(sK4) != k2_relat_1(sK4)
% 3.65/0.97      | k1_relat_1(sK4) != k1_relat_1(sK4)
% 3.65/0.97      | v3_tops_2(sK4,sK2,sK3) = iProver_top
% 3.65/0.97      | v4_pre_topc(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4)),sK3) = iProver_top
% 3.65/0.97      | v4_pre_topc(sK1(sK2,sK3,sK4),sK2) = iProver_top
% 3.65/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.65/0.97      | l1_pre_topc(sK2) != iProver_top ),
% 3.65/0.97      inference(light_normalisation,[status(thm)],[c_5400,c_4375,c_4813]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_5402,plain,
% 3.65/0.97      ( v3_tops_2(sK4,sK2,sK3) = iProver_top
% 3.65/0.97      | v4_pre_topc(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4)),sK3) = iProver_top
% 3.65/0.97      | v4_pre_topc(sK1(sK2,sK3,sK4),sK2) = iProver_top
% 3.65/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.65/0.97      | l1_pre_topc(sK2) != iProver_top ),
% 3.65/0.97      inference(equality_resolution_simp,[status(thm)],[c_5401]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_5403,plain,
% 3.65/0.97      ( v3_tops_2(sK4,sK2,sK3) = iProver_top
% 3.65/0.97      | v4_pre_topc(sK1(sK2,sK3,sK4),sK2) = iProver_top
% 3.65/0.97      | v4_pre_topc(k9_relat_1(sK4,sK1(sK2,sK3,sK4)),sK3) = iProver_top
% 3.65/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.65/0.97      | l1_pre_topc(sK2) != iProver_top ),
% 3.65/0.97      inference(demodulation,[status(thm)],[c_5402,c_4808]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(c_59,plain,
% 3.65/0.97      ( v3_tops_2(sK4,sK2,sK3) != iProver_top ),
% 3.65/0.97      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.65/0.97  
% 3.65/0.97  cnf(contradiction,plain,
% 3.65/0.97      ( $false ),
% 3.65/0.97      inference(minisat,
% 3.65/0.97                [status(thm)],
% 3.65/0.97                [c_10107,c_6920,c_5403,c_59,c_54,c_48]) ).
% 3.65/0.97  
% 3.65/0.97  
% 3.65/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.65/0.97  
% 3.65/0.97  ------                               Statistics
% 3.65/0.97  
% 3.65/0.97  ------ General
% 3.65/0.97  
% 3.65/0.97  abstr_ref_over_cycles:                  0
% 3.65/0.97  abstr_ref_under_cycles:                 0
% 3.65/0.97  gc_basic_clause_elim:                   0
% 3.65/0.97  forced_gc_time:                         0
% 3.65/0.97  parsing_time:                           0.022
% 3.65/0.97  unif_index_cands_time:                  0.
% 3.65/0.97  unif_index_add_time:                    0.
% 3.65/0.97  orderings_time:                         0.
% 3.65/0.97  out_proof_time:                         0.02
% 3.65/0.97  total_time:                             0.476
% 3.65/0.97  num_of_symbols:                         67
% 3.65/0.97  num_of_terms:                           7906
% 3.65/0.97  
% 3.65/0.97  ------ Preprocessing
% 3.65/0.97  
% 3.65/0.97  num_of_splits:                          2
% 3.65/0.97  num_of_split_atoms:                     2
% 3.65/0.97  num_of_reused_defs:                     0
% 3.65/0.97  num_eq_ax_congr_red:                    31
% 3.65/0.97  num_of_sem_filtered_clauses:            1
% 3.65/0.97  num_of_subtypes:                        0
% 3.65/0.97  monotx_restored_types:                  0
% 3.65/0.97  sat_num_of_epr_types:                   0
% 3.65/0.97  sat_num_of_non_cyclic_types:            0
% 3.65/0.97  sat_guarded_non_collapsed_types:        0
% 3.65/0.97  num_pure_diseq_elim:                    0
% 3.65/0.97  simp_replaced_by:                       0
% 3.65/0.97  res_preprocessed:                       189
% 3.65/0.97  prep_upred:                             0
% 3.65/0.97  prep_unflattend:                        43
% 3.65/0.97  smt_new_axioms:                         0
% 3.65/0.97  pred_elim_cands:                        6
% 3.65/0.97  pred_elim:                              11
% 3.65/0.97  pred_elim_cl:                           14
% 3.65/0.97  pred_elim_cycles:                       17
% 3.65/0.97  merged_defs:                            8
% 3.65/0.97  merged_defs_ncl:                        0
% 3.65/0.97  bin_hyper_res:                          8
% 3.65/0.97  prep_cycles:                            4
% 3.65/0.97  pred_elim_time:                         0.082
% 3.65/0.97  splitting_time:                         0.
% 3.65/0.97  sem_filter_time:                        0.
% 3.65/0.97  monotx_time:                            0.001
% 3.65/0.97  subtype_inf_time:                       0.
% 3.65/0.97  
% 3.65/0.97  ------ Problem properties
% 3.65/0.97  
% 3.65/0.97  clauses:                                34
% 3.65/0.97  conjectures:                            7
% 3.65/0.97  epr:                                    7
% 3.65/0.97  horn:                                   29
% 3.65/0.97  ground:                                 8
% 3.65/0.97  unary:                                  8
% 3.65/0.97  binary:                                 12
% 3.65/0.97  lits:                                   118
% 3.65/0.97  lits_eq:                                34
% 3.65/0.97  fd_pure:                                0
% 3.65/0.97  fd_pseudo:                              0
% 3.65/0.97  fd_cond:                                0
% 3.65/0.97  fd_pseudo_cond:                         1
% 3.65/0.97  ac_symbols:                             0
% 3.65/0.97  
% 3.65/0.97  ------ Propositional Solver
% 3.65/0.97  
% 3.65/0.97  prop_solver_calls:                      32
% 3.65/0.97  prop_fast_solver_calls:                 2720
% 3.65/0.97  smt_solver_calls:                       0
% 3.65/0.97  smt_fast_solver_calls:                  0
% 3.65/0.97  prop_num_of_clauses:                    3734
% 3.65/0.97  prop_preprocess_simplified:             9736
% 3.65/0.97  prop_fo_subsumed:                       110
% 3.65/0.97  prop_solver_time:                       0.
% 3.65/0.97  smt_solver_time:                        0.
% 3.65/0.97  smt_fast_solver_time:                   0.
% 3.65/0.97  prop_fast_solver_time:                  0.
% 3.65/0.97  prop_unsat_core_time:                   0.
% 3.65/0.97  
% 3.65/0.97  ------ QBF
% 3.65/0.97  
% 3.65/0.97  qbf_q_res:                              0
% 3.65/0.97  qbf_num_tautologies:                    0
% 3.65/0.97  qbf_prep_cycles:                        0
% 3.65/0.97  
% 3.65/0.97  ------ BMC1
% 3.65/0.97  
% 3.65/0.97  bmc1_current_bound:                     -1
% 3.65/0.97  bmc1_last_solved_bound:                 -1
% 3.65/0.97  bmc1_unsat_core_size:                   -1
% 3.65/0.97  bmc1_unsat_core_parents_size:           -1
% 3.65/0.97  bmc1_merge_next_fun:                    0
% 3.65/0.97  bmc1_unsat_core_clauses_time:           0.
% 3.65/0.97  
% 3.65/0.97  ------ Instantiation
% 3.65/0.97  
% 3.65/0.97  inst_num_of_clauses:                    1036
% 3.65/0.97  inst_num_in_passive:                    141
% 3.65/0.97  inst_num_in_active:                     631
% 3.65/0.97  inst_num_in_unprocessed:                264
% 3.65/0.97  inst_num_of_loops:                      670
% 3.65/0.97  inst_num_of_learning_restarts:          0
% 3.65/0.97  inst_num_moves_active_passive:          34
% 3.65/0.97  inst_lit_activity:                      0
% 3.65/0.97  inst_lit_activity_moves:                0
% 3.65/0.97  inst_num_tautologies:                   0
% 3.65/0.97  inst_num_prop_implied:                  0
% 3.65/0.97  inst_num_existing_simplified:           0
% 3.65/0.97  inst_num_eq_res_simplified:             0
% 3.65/0.97  inst_num_child_elim:                    0
% 3.65/0.97  inst_num_of_dismatching_blockings:      342
% 3.65/0.97  inst_num_of_non_proper_insts:           1634
% 3.65/0.97  inst_num_of_duplicates:                 0
% 3.65/0.97  inst_inst_num_from_inst_to_res:         0
% 3.65/0.97  inst_dismatching_checking_time:         0.
% 3.65/0.97  
% 3.65/0.97  ------ Resolution
% 3.65/0.97  
% 3.65/0.97  res_num_of_clauses:                     0
% 3.65/0.97  res_num_in_passive:                     0
% 3.65/0.97  res_num_in_active:                      0
% 3.65/0.97  res_num_of_loops:                       193
% 3.65/0.97  res_forward_subset_subsumed:            160
% 3.65/0.97  res_backward_subset_subsumed:           0
% 3.65/0.97  res_forward_subsumed:                   0
% 3.65/0.97  res_backward_subsumed:                  0
% 3.65/0.97  res_forward_subsumption_resolution:     1
% 3.65/0.97  res_backward_subsumption_resolution:    0
% 3.65/0.97  res_clause_to_clause_subsumption:       451
% 3.65/0.97  res_orphan_elimination:                 0
% 3.65/0.97  res_tautology_del:                      260
% 3.65/0.97  res_num_eq_res_simplified:              0
% 3.65/0.97  res_num_sel_changes:                    0
% 3.65/0.97  res_moves_from_active_to_pass:          0
% 3.65/0.97  
% 3.65/0.97  ------ Superposition
% 3.65/0.97  
% 3.65/0.97  sup_time_total:                         0.
% 3.65/0.97  sup_time_generating:                    0.
% 3.65/0.97  sup_time_sim_full:                      0.
% 3.65/0.97  sup_time_sim_immed:                     0.
% 3.65/0.97  
% 3.65/0.97  sup_num_of_clauses:                     136
% 3.65/0.97  sup_num_in_active:                      104
% 3.65/0.97  sup_num_in_passive:                     32
% 3.65/0.97  sup_num_of_loops:                       132
% 3.65/0.97  sup_fw_superposition:                   98
% 3.65/0.97  sup_bw_superposition:                   63
% 3.65/0.97  sup_immediate_simplified:               82
% 3.65/0.97  sup_given_eliminated:                   0
% 3.65/0.97  comparisons_done:                       0
% 3.65/0.97  comparisons_avoided:                    0
% 3.65/0.97  
% 3.65/0.97  ------ Simplifications
% 3.65/0.97  
% 3.65/0.97  
% 3.65/0.97  sim_fw_subset_subsumed:                 15
% 3.65/0.97  sim_bw_subset_subsumed:                 5
% 3.65/0.97  sim_fw_subsumed:                        9
% 3.65/0.97  sim_bw_subsumed:                        1
% 3.65/0.97  sim_fw_subsumption_res:                 0
% 3.65/0.97  sim_bw_subsumption_res:                 0
% 3.65/0.97  sim_tautology_del:                      1
% 3.65/0.97  sim_eq_tautology_del:                   3
% 3.65/0.97  sim_eq_res_simp:                        5
% 3.65/0.97  sim_fw_demodulated:                     5
% 3.65/0.97  sim_bw_demodulated:                     29
% 3.65/0.97  sim_light_normalised:                   73
% 3.65/0.97  sim_joinable_taut:                      0
% 3.65/0.97  sim_joinable_simp:                      0
% 3.65/0.97  sim_ac_normalised:                      0
% 3.65/0.97  sim_smt_subsumption:                    0
% 3.65/0.97  
%------------------------------------------------------------------------------
