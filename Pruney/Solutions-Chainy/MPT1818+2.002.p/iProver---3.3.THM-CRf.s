%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:22 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 506 expanded)
%              Number of clauses        :   73 (  76 expanded)
%              Number of leaves         :   10 ( 183 expanded)
%              Depth                    :   12
%              Number of atoms          : 1215 (17223 expanded)
%              Number of equality atoms :   35 ( 494 expanded)
%              Maximal formula depth    :   26 (   7 average)
%              Maximal clause size      :   80 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,plain,(
    ! [X1,X4,X2,X0,X3] :
      ( sP0(X1,X4,X2,X0,X3)
    <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
        & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
        & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f17,plain,(
    ! [X1,X4,X2,X0,X3] :
      ( ( sP0(X1,X4,X2,X0,X3)
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
        | ~ sP0(X1,X4,X2,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f18,plain,(
    ! [X1,X4,X2,X0,X3] :
      ( ( sP0(X1,X4,X2,X0,X3)
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
        | ~ sP0(X1,X4,X2,X0,X3) ) ) ),
    inference(flattening,[],[f17])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
        | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
        | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
        | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) )
      & ( ( m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
          & v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
          & m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
          & v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
          & v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
          & v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f18])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X3,X0,X2,X4))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f12,plain,(
    ! [X3,X0,X2,X4,X1] :
      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v5_pre_topc(X2,X0,X1)
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
      <=> sP0(X1,X4,X2,X0,X3) )
      | ~ sP1(X3,X0,X2,X4,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f14,plain,(
    ! [X3,X0,X2,X4,X1] :
      ( ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v5_pre_topc(X2,X0,X1)
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X2) )
          | ~ sP0(X1,X4,X2,X0,X3) )
        & ( sP0(X1,X4,X2,X0,X3)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          | ~ v5_pre_topc(X2,X0,X1)
          | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          | ~ v1_funct_1(X2) ) )
      | ~ sP1(X3,X0,X2,X4,X1) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f15,plain,(
    ! [X3,X0,X2,X4,X1] :
      ( ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v5_pre_topc(X2,X0,X1)
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X2) )
          | ~ sP0(X1,X4,X2,X0,X3) )
        & ( sP0(X1,X4,X2,X0,X3)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          | ~ v5_pre_topc(X2,X0,X1)
          | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          | ~ v1_funct_1(X2) ) )
      | ~ sP1(X3,X0,X2,X4,X1) ) ),
    inference(flattening,[],[f14])).

fof(f16,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
            & v5_pre_topc(X2,X1,X4)
            & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
            & v1_funct_1(X2) )
          | ~ sP0(X4,X3,X2,X1,X0) )
        & ( sP0(X4,X3,X2,X1,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
          | ~ v5_pre_topc(X2,X1,X4)
          | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
          | ~ v1_funct_1(X2) ) )
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(rectify,[],[f15])).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X4,X3,X2,X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
      | ~ v5_pre_topc(X2,X1,X4)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
      | ~ v1_funct_1(X2)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X1,X4)
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( r4_tsep_1(X0,X3,X4)
                          & k1_tsep_1(X0,X3,X4) = X0 )
                       => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v5_pre_topc(X2,X0,X1)
                            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X2) )
                        <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                            & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) )
                      <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      | ~ r4_tsep_1(X0,X3,X4)
                      | k1_tsep_1(X0,X3,X4) != X0
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) )
                      <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      | ~ r4_tsep_1(X0,X3,X4)
                      | k1_tsep_1(X0,X3,X4) != X0
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( sP1(X3,X0,X2,X4,X1)
                      | ~ r4_tsep_1(X0,X3,X4)
                      | k1_tsep_1(X0,X3,X4) != X0
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f6,f12,f11])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X3,X0,X2,X4,X1)
      | ~ r4_tsep_1(X0,X3,X4)
      | k1_tsep_1(X0,X3,X4) != X0
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v1_tsep_1(X1,X0) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_tsep_1(X2,X0) )
             => r4_tsep_1(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_tsep_1(X0,X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_tsep_1(X2,X0) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_tsep_1(X0,X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_tsep_1(X2,X0) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r4_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_tsep_1(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_tsep_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & v1_tsep_1(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( k1_tsep_1(X0,X3,X4) = X0
                       => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v5_pre_topc(X2,X0,X1)
                            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X2) )
                        <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                            & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_tsep_1(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_pre_topc(X4,X0)
                          & v1_tsep_1(X4,X0)
                          & ~ v2_struct_0(X4) )
                       => ( k1_tsep_1(X0,X3,X4) = X0
                         => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                              & v5_pre_topc(X2,X0,X1)
                              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                              & v1_funct_1(X2) )
                          <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                              & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                              & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                              & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                              & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                              & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) )
                      <~> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & v1_tsep_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) )
                      <~> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & v1_tsep_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
                        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        | ~ v5_pre_topc(X2,X0,X1)
                        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                        | ~ v1_funct_1(X2) )
                      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                        | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) ) )
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & v1_tsep_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
                        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        | ~ v5_pre_topc(X2,X0,X1)
                        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                        | ~ v1_funct_1(X2) )
                      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                        | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) ) )
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & v1_tsep_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
            | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
            | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
            | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
            | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
            | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
            | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
            | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
            | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            | ~ v5_pre_topc(X2,X0,X1)
            | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
            | ~ v1_funct_1(X2) )
          & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
              & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
              & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
              & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
              & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
              & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
              & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
              & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
            | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v5_pre_topc(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) ) )
          & k1_tsep_1(X0,X3,X4) = X0
          & m1_pre_topc(X4,X0)
          & v1_tsep_1(X4,X0)
          & ~ v2_struct_0(X4) )
     => ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1))))
          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,sK6),sK6,X1)
          | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,sK6),u1_struct_0(sK6),u1_struct_0(X1))
          | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,sK6))
          | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
          | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
          | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          | ~ v5_pre_topc(X2,X0,X1)
          | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          | ~ v1_funct_1(X2) )
        & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1))))
            & v5_pre_topc(k2_tmap_1(X0,X1,X2,sK6),sK6,X1)
            & v1_funct_2(k2_tmap_1(X0,X1,X2,sK6),u1_struct_0(sK6),u1_struct_0(X1))
            & v1_funct_1(k2_tmap_1(X0,X1,X2,sK6))
            & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
            & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
            & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
          | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v5_pre_topc(X2,X0,X1)
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X2) ) )
        & k1_tsep_1(X0,X3,sK6) = X0
        & m1_pre_topc(sK6,X0)
        & v1_tsep_1(sK6,X0)
        & ~ v2_struct_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                | ~ v5_pre_topc(X2,X0,X1)
                | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                | ~ v1_funct_1(X2) )
              & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                  & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                  & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                  & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                  & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                  & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                  & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                  & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v5_pre_topc(X2,X0,X1)
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) ) )
              & k1_tsep_1(X0,X3,X4) = X0
              & m1_pre_topc(X4,X0)
              & v1_tsep_1(X4,X0)
              & ~ v2_struct_0(X4) )
          & m1_pre_topc(X3,X0)
          & v1_tsep_1(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
              | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
              | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
              | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
              | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
              | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,sK5),sK5,X1)
              | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,sK5),u1_struct_0(sK5),u1_struct_0(X1))
              | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,sK5))
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v5_pre_topc(X2,X0,X1)
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
            & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                & m1_subset_1(k2_tmap_1(X0,X1,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
                & v5_pre_topc(k2_tmap_1(X0,X1,X2,sK5),sK5,X1)
                & v1_funct_2(k2_tmap_1(X0,X1,X2,sK5),u1_struct_0(sK5),u1_struct_0(X1))
                & v1_funct_1(k2_tmap_1(X0,X1,X2,sK5)) )
              | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v5_pre_topc(X2,X0,X1)
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) ) )
            & k1_tsep_1(X0,sK5,X4) = X0
            & m1_pre_topc(X4,X0)
            & v1_tsep_1(X4,X0)
            & ~ v2_struct_0(X4) )
        & m1_pre_topc(sK5,X0)
        & v1_tsep_1(sK5,X0)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                    | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                    | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                    | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                    | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                    | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                    | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
                    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                    | ~ v5_pre_topc(X2,X0,X1)
                    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                    | ~ v1_funct_1(X2) )
                  & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                      & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                      & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                      & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                      & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                      & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                    | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v5_pre_topc(X2,X0,X1)
                      & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X2) ) )
                  & k1_tsep_1(X0,X3,X4) = X0
                  & m1_pre_topc(X4,X0)
                  & v1_tsep_1(X4,X0)
                  & ~ v2_struct_0(X4) )
              & m1_pre_topc(X3,X0)
              & v1_tsep_1(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                  | ~ v5_pre_topc(k2_tmap_1(X0,X1,sK4,X4),X4,X1)
                  | ~ v1_funct_2(k2_tmap_1(X0,X1,sK4,X4),u1_struct_0(X4),u1_struct_0(X1))
                  | ~ v1_funct_1(k2_tmap_1(X0,X1,sK4,X4))
                  | ~ m1_subset_1(k2_tmap_1(X0,X1,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                  | ~ v5_pre_topc(k2_tmap_1(X0,X1,sK4,X3),X3,X1)
                  | ~ v1_funct_2(k2_tmap_1(X0,X1,sK4,X3),u1_struct_0(X3),u1_struct_0(X1))
                  | ~ v1_funct_1(k2_tmap_1(X0,X1,sK4,X3))
                  | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  | ~ v5_pre_topc(sK4,X0,X1)
                  | ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
                  | ~ v1_funct_1(sK4) )
                & ( ( m1_subset_1(k2_tmap_1(X0,X1,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                    & v5_pre_topc(k2_tmap_1(X0,X1,sK4,X4),X4,X1)
                    & v1_funct_2(k2_tmap_1(X0,X1,sK4,X4),u1_struct_0(X4),u1_struct_0(X1))
                    & v1_funct_1(k2_tmap_1(X0,X1,sK4,X4))
                    & m1_subset_1(k2_tmap_1(X0,X1,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    & v5_pre_topc(k2_tmap_1(X0,X1,sK4,X3),X3,X1)
                    & v1_funct_2(k2_tmap_1(X0,X1,sK4,X3),u1_struct_0(X3),u1_struct_0(X1))
                    & v1_funct_1(k2_tmap_1(X0,X1,sK4,X3)) )
                  | ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                    & v5_pre_topc(sK4,X0,X1)
                    & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
                    & v1_funct_1(sK4) ) )
                & k1_tsep_1(X0,X3,X4) = X0
                & m1_pre_topc(X4,X0)
                & v1_tsep_1(X4,X0)
                & ~ v2_struct_0(X4) )
            & m1_pre_topc(X3,X0)
            & v1_tsep_1(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
                        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        | ~ v5_pre_topc(X2,X0,X1)
                        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                        | ~ v1_funct_1(X2) )
                      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                        | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) ) )
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & v1_tsep_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ( ~ m1_subset_1(k2_tmap_1(X0,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
                      | ~ v5_pre_topc(k2_tmap_1(X0,sK3,X2,X4),X4,sK3)
                      | ~ v1_funct_2(k2_tmap_1(X0,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3))
                      | ~ v1_funct_1(k2_tmap_1(X0,sK3,X2,X4))
                      | ~ m1_subset_1(k2_tmap_1(X0,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                      | ~ v5_pre_topc(k2_tmap_1(X0,sK3,X2,X3),X3,sK3)
                      | ~ v1_funct_2(k2_tmap_1(X0,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3))
                      | ~ v1_funct_1(k2_tmap_1(X0,sK3,X2,X3))
                      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
                      | ~ v5_pre_topc(X2,X0,sK3)
                      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3))
                      | ~ v1_funct_1(X2) )
                    & ( ( m1_subset_1(k2_tmap_1(X0,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
                        & v5_pre_topc(k2_tmap_1(X0,sK3,X2,X4),X4,sK3)
                        & v1_funct_2(k2_tmap_1(X0,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3))
                        & v1_funct_1(k2_tmap_1(X0,sK3,X2,X4))
                        & m1_subset_1(k2_tmap_1(X0,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                        & v5_pre_topc(k2_tmap_1(X0,sK3,X2,X3),X3,sK3)
                        & v1_funct_2(k2_tmap_1(X0,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3))
                        & v1_funct_1(k2_tmap_1(X0,sK3,X2,X3)) )
                      | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
                        & v5_pre_topc(X2,X0,sK3)
                        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3))
                        & v1_funct_1(X2) ) )
                    & k1_tsep_1(X0,X3,X4) = X0
                    & m1_pre_topc(X4,X0)
                    & v1_tsep_1(X4,X0)
                    & ~ v2_struct_0(X4) )
                & m1_pre_topc(X3,X0)
                & v1_tsep_1(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
                          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X2,X0,X1)
                          | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          | ~ v1_funct_1(X2) )
                        & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                            & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                          | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v5_pre_topc(X2,X0,X1)
                            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X2) ) )
                        & k1_tsep_1(X0,X3,X4) = X0
                        & m1_pre_topc(X4,X0)
                        & v1_tsep_1(X4,X0)
                        & ~ v2_struct_0(X4) )
                    & m1_pre_topc(X3,X0)
                    & v1_tsep_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1)
                        | ~ v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(sK2,X1,X2,X4))
                        | ~ m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1)
                        | ~ v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(sK2,X1,X2,X3))
                        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                        | ~ v5_pre_topc(X2,sK2,X1)
                        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
                        | ~ v1_funct_1(X2) )
                      & ( ( m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(sK2,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(sK2,X1,X2,X3)) )
                        | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                          & v5_pre_topc(X2,sK2,X1)
                          & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
                          & v1_funct_1(X2) ) )
                      & k1_tsep_1(sK2,X3,X4) = sK2
                      & m1_pre_topc(X4,sK2)
                      & v1_tsep_1(X4,sK2)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,sK2)
                  & v1_tsep_1(X3,sK2)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK4) )
    & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
        & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
        & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
        & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
        & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
        & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
        & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) )
      | ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        & v5_pre_topc(sK4,sK2,sK3)
        & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
        & v1_funct_1(sK4) ) )
    & k1_tsep_1(sK2,sK5,sK6) = sK2
    & m1_pre_topc(sK6,sK2)
    & v1_tsep_1(sK6,sK2)
    & ~ v2_struct_0(sK6)
    & m1_pre_topc(sK5,sK2)
    & v1_tsep_1(sK5,sK2)
    & ~ v2_struct_0(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f21,f26,f25,f24,f23,f22])).

fof(f59,plain,(
    k1_tsep_1(sK2,sK5,sK6) = sK2 ),
    inference(cnf_transformation,[],[f27])).

fof(f92,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f51,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f27])).

fof(f52,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f90,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f86,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f82,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f78,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f74,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f70,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f66,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f62,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f58,plain,(
    m1_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f57,plain,(
    v1_tsep_1(sK6,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f56,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f27])).

fof(f55,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f54,plain,(
    v1_tsep_1(sK5,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f53,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f27])).

fof(f49,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f48,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f46,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_6,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2074,plain,
    ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
    | m1_subset_1(k2_tmap_1(X2_50,X0_50,X0_51,X1_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_4037,plain,
    ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
    inference(instantiation,[status(thm)],[c_2074])).

cnf(c_7,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2073,plain,
    ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
    | v5_pre_topc(k2_tmap_1(X2_50,X0_50,X0_51,X1_50),X1_50,X0_50) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_4038,plain,
    ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) ),
    inference(instantiation,[status(thm)],[c_2073])).

cnf(c_8,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2072,plain,
    ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
    | v1_funct_2(k2_tmap_1(X2_50,X0_50,X0_51,X1_50),u1_struct_0(X1_50),u1_struct_0(X0_50)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_4039,plain,
    ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2072])).

cnf(c_10,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2070,plain,
    ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
    | m1_subset_1(k2_tmap_1(X2_50,X0_50,X0_51,X3_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X0_50)))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_4040,plain,
    ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(instantiation,[status(thm)],[c_2070])).

cnf(c_11,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2069,plain,
    ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
    | v5_pre_topc(k2_tmap_1(X2_50,X0_50,X0_51,X3_50),X3_50,X0_50) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_4041,plain,
    ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) ),
    inference(instantiation,[status(thm)],[c_2069])).

cnf(c_12,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_2068,plain,
    ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
    | v1_funct_2(k2_tmap_1(X2_50,X0_50,X0_51,X3_50),u1_struct_0(X3_50),u1_struct_0(X0_50)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_4042,plain,
    ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2068])).

cnf(c_9,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2071,plain,
    ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
    | v1_funct_1(k2_tmap_1(X2_50,X0_50,X0_51,X1_50)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_4043,plain,
    ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(instantiation,[status(thm)],[c_2071])).

cnf(c_13,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_2067,plain,
    ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
    | v1_funct_1(k2_tmap_1(X2_50,X0_50,X0_51,X3_50)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_4044,plain,
    ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_2067])).

cnf(c_5,plain,
    ( sP0(X0,X1,X2,X3,X4)
    | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
    | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
    | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
    | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
    | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
    | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
    | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2075,plain,
    ( sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
    | ~ v1_funct_2(k2_tmap_1(X2_50,X0_50,X0_51,X1_50),u1_struct_0(X1_50),u1_struct_0(X0_50))
    | ~ v1_funct_2(k2_tmap_1(X2_50,X0_50,X0_51,X3_50),u1_struct_0(X3_50),u1_struct_0(X0_50))
    | ~ v5_pre_topc(k2_tmap_1(X2_50,X0_50,X0_51,X1_50),X1_50,X0_50)
    | ~ v5_pre_topc(k2_tmap_1(X2_50,X0_50,X0_51,X3_50),X3_50,X0_50)
    | ~ m1_subset_1(k2_tmap_1(X2_50,X0_50,X0_51,X1_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50))))
    | ~ m1_subset_1(k2_tmap_1(X2_50,X0_50,X0_51,X3_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X0_50))))
    | ~ v1_funct_1(k2_tmap_1(X2_50,X0_50,X0_51,X1_50))
    | ~ v1_funct_1(k2_tmap_1(X2_50,X0_50,X0_51,X3_50)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_3558,plain,
    ( sP0(sK3,sK6,sK4,sK2,X0_50)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0_50),u1_struct_0(X0_50),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0_50),X0_50,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_50))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(instantiation,[status(thm)],[c_2075])).

cnf(c_3885,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(instantiation,[status(thm)],[c_3558])).

cnf(c_4,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | sP0(X4,X3,X2,X1,X0)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
    | ~ v5_pre_topc(X2,X1,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_2076,plain,
    ( ~ sP1(X0_50,X1_50,X0_51,X2_50,X3_50)
    | sP0(X3_50,X2_50,X0_51,X1_50,X0_50)
    | ~ v1_funct_2(X0_51,u1_struct_0(X1_50),u1_struct_0(X3_50))
    | ~ v5_pre_topc(X0_51,X1_50,X3_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X3_50))))
    | ~ v1_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_3231,plain,
    ( ~ sP1(X0_50,sK2,sK4,X1_50,sK3)
    | sP0(sK3,X1_50,sK4,sK2,X0_50)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2076])).

cnf(c_3456,plain,
    ( ~ sP1(sK5,sK2,sK4,sK6,sK3)
    | sP0(sK3,sK6,sK4,sK2,sK5)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_3231])).

cnf(c_1,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | v5_pre_topc(X2,X1,X4) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_2079,plain,
    ( ~ sP1(X0_50,X1_50,X0_51,X2_50,X3_50)
    | ~ sP0(X3_50,X2_50,X0_51,X1_50,X0_50)
    | v5_pre_topc(X0_51,X1_50,X3_50) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_3435,plain,
    ( ~ sP1(sK5,sK2,X0_51,sK6,X0_50)
    | ~ sP0(X0_50,sK6,X0_51,sK2,sK5)
    | v5_pre_topc(X0_51,sK2,X0_50) ),
    inference(instantiation,[status(thm)],[c_2079])).

cnf(c_3440,plain,
    ( ~ sP1(sK5,sK2,sK4,sK6,sK3)
    | ~ sP0(sK3,sK6,sK4,sK2,sK5)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_3435])).

cnf(c_14,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ r4_tsep_1(X1,X0,X3)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ v1_funct_1(X2)
    | k1_tsep_1(X1,X0,X3) != X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_15,plain,
    ( r4_tsep_1(X0,X1,X2)
    | ~ v1_tsep_1(X2,X0)
    | ~ v1_tsep_1(X1,X0)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_638,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
    | ~ v1_tsep_1(X5,X6)
    | ~ v1_tsep_1(X7,X6)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X5,X6)
    | ~ m1_pre_topc(X7,X6)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X6)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X6)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X6)
    | ~ v1_funct_1(X2)
    | X5 != X3
    | X7 != X0
    | X6 != X1
    | k1_tsep_1(X1,X0,X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_15])).

cnf(c_639,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
    | ~ v1_tsep_1(X0,X1)
    | ~ v1_tsep_1(X3,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X4)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X2)
    | k1_tsep_1(X1,X0,X3) != X1 ),
    inference(unflattening,[status(thm)],[c_638])).

cnf(c_2041,plain,
    ( sP1(X0_50,X1_50,X0_51,X2_50,X3_50)
    | ~ v1_funct_2(X0_51,u1_struct_0(X1_50),u1_struct_0(X3_50))
    | ~ v1_tsep_1(X0_50,X1_50)
    | ~ v1_tsep_1(X2_50,X1_50)
    | ~ m1_pre_topc(X0_50,X1_50)
    | ~ m1_pre_topc(X2_50,X1_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X3_50))))
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X3_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X3_50)
    | v2_struct_0(X1_50)
    | v2_struct_0(X3_50)
    | v2_struct_0(X0_50)
    | v2_struct_0(X2_50)
    | ~ v1_funct_1(X0_51)
    | k1_tsep_1(X1_50,X0_50,X2_50) != X1_50 ),
    inference(subtyping,[status(esa)],[c_639])).

cnf(c_3241,plain,
    ( sP1(sK5,sK2,X0_51,X0_50,X1_50)
    | ~ v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(X1_50))
    | ~ v1_tsep_1(X0_50,sK2)
    | ~ v1_tsep_1(sK5,sK2)
    | ~ m1_pre_topc(X0_50,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1_50))))
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X1_50)
    | v2_struct_0(X0_50)
    | v2_struct_0(sK5)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_51)
    | k1_tsep_1(sK2,sK5,X0_50) != sK2 ),
    inference(instantiation,[status(thm)],[c_2041])).

cnf(c_3336,plain,
    ( sP1(sK5,sK2,X0_51,sK6,X0_50)
    | ~ v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(X0_50))
    | ~ v1_tsep_1(sK5,sK2)
    | ~ v1_tsep_1(sK6,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK6,sK2)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_50))))
    | ~ v2_pre_topc(X0_50)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_50)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_50)
    | v2_struct_0(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_51)
    | k1_tsep_1(sK2,sK5,sK6) != sK2 ),
    inference(instantiation,[status(thm)],[c_3241])).

cnf(c_3338,plain,
    ( sP1(sK5,sK2,sK4,sK6,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_tsep_1(sK5,sK2)
    | ~ v1_tsep_1(sK6,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK6,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(sK4)
    | k1_tsep_1(sK2,sK5,sK6) != sK2 ),
    inference(instantiation,[status(thm)],[c_3336])).

cnf(c_49,negated_conjecture,
    ( k1_tsep_1(sK2,sK5,sK6) = sK2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2058,negated_conjecture,
    ( k1_tsep_1(sK2,sK5,sK6) = sK2 ),
    inference(subtyping,[status(esa)],[c_49])).

cnf(c_16,negated_conjecture,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_58,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_57,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_56,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_425,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_58,c_57,c_56])).

cnf(c_426,negated_conjecture,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(renaming,[status(thm)],[c_425])).

cnf(c_18,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_22,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_30,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_34,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_38,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_42,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_46,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_50,negated_conjecture,
    ( m1_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_51,negated_conjecture,
    ( v1_tsep_1(sK6,sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_52,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_53,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_54,negated_conjecture,
    ( v1_tsep_1(sK5,sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_55,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_59,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_60,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_61,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_62,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_63,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_64,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4037,c_4038,c_4039,c_4040,c_4041,c_4042,c_4043,c_4044,c_3885,c_3456,c_3440,c_3338,c_2058,c_426,c_18,c_22,c_26,c_30,c_34,c_38,c_42,c_46,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_62,c_63,c_64])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:23:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.06/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/0.99  
% 2.06/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.06/0.99  
% 2.06/0.99  ------  iProver source info
% 2.06/0.99  
% 2.06/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.06/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.06/0.99  git: non_committed_changes: false
% 2.06/0.99  git: last_make_outside_of_git: false
% 2.06/0.99  
% 2.06/0.99  ------ 
% 2.06/0.99  
% 2.06/0.99  ------ Input Options
% 2.06/0.99  
% 2.06/0.99  --out_options                           all
% 2.06/0.99  --tptp_safe_out                         true
% 2.06/0.99  --problem_path                          ""
% 2.06/0.99  --include_path                          ""
% 2.06/0.99  --clausifier                            res/vclausify_rel
% 2.06/0.99  --clausifier_options                    --mode clausify
% 2.06/0.99  --stdin                                 false
% 2.06/0.99  --stats_out                             all
% 2.06/0.99  
% 2.06/0.99  ------ General Options
% 2.06/0.99  
% 2.06/0.99  --fof                                   false
% 2.06/0.99  --time_out_real                         305.
% 2.06/0.99  --time_out_virtual                      -1.
% 2.06/0.99  --symbol_type_check                     false
% 2.06/0.99  --clausify_out                          false
% 2.06/0.99  --sig_cnt_out                           false
% 2.06/0.99  --trig_cnt_out                          false
% 2.06/0.99  --trig_cnt_out_tolerance                1.
% 2.06/0.99  --trig_cnt_out_sk_spl                   false
% 2.06/0.99  --abstr_cl_out                          false
% 2.06/0.99  
% 2.06/0.99  ------ Global Options
% 2.06/0.99  
% 2.06/0.99  --schedule                              default
% 2.06/0.99  --add_important_lit                     false
% 2.06/0.99  --prop_solver_per_cl                    1000
% 2.06/0.99  --min_unsat_core                        false
% 2.06/0.99  --soft_assumptions                      false
% 2.06/0.99  --soft_lemma_size                       3
% 2.06/0.99  --prop_impl_unit_size                   0
% 2.06/0.99  --prop_impl_unit                        []
% 2.06/0.99  --share_sel_clauses                     true
% 2.06/0.99  --reset_solvers                         false
% 2.06/0.99  --bc_imp_inh                            [conj_cone]
% 2.06/0.99  --conj_cone_tolerance                   3.
% 2.06/0.99  --extra_neg_conj                        none
% 2.06/0.99  --large_theory_mode                     true
% 2.06/0.99  --prolific_symb_bound                   200
% 2.06/0.99  --lt_threshold                          2000
% 2.06/0.99  --clause_weak_htbl                      true
% 2.06/0.99  --gc_record_bc_elim                     false
% 2.06/0.99  
% 2.06/0.99  ------ Preprocessing Options
% 2.06/0.99  
% 2.06/0.99  --preprocessing_flag                    true
% 2.06/0.99  --time_out_prep_mult                    0.1
% 2.06/0.99  --splitting_mode                        input
% 2.06/0.99  --splitting_grd                         true
% 2.06/0.99  --splitting_cvd                         false
% 2.06/0.99  --splitting_cvd_svl                     false
% 2.06/0.99  --splitting_nvd                         32
% 2.06/0.99  --sub_typing                            true
% 2.06/0.99  --prep_gs_sim                           true
% 2.06/0.99  --prep_unflatten                        true
% 2.06/0.99  --prep_res_sim                          true
% 2.06/0.99  --prep_upred                            true
% 2.06/0.99  --prep_sem_filter                       exhaustive
% 2.06/0.99  --prep_sem_filter_out                   false
% 2.06/0.99  --pred_elim                             true
% 2.06/0.99  --res_sim_input                         true
% 2.06/0.99  --eq_ax_congr_red                       true
% 2.06/0.99  --pure_diseq_elim                       true
% 2.06/0.99  --brand_transform                       false
% 2.06/0.99  --non_eq_to_eq                          false
% 2.06/0.99  --prep_def_merge                        true
% 2.06/0.99  --prep_def_merge_prop_impl              false
% 2.06/0.99  --prep_def_merge_mbd                    true
% 2.06/0.99  --prep_def_merge_tr_red                 false
% 2.06/0.99  --prep_def_merge_tr_cl                  false
% 2.06/0.99  --smt_preprocessing                     true
% 2.06/0.99  --smt_ac_axioms                         fast
% 2.06/0.99  --preprocessed_out                      false
% 2.06/0.99  --preprocessed_stats                    false
% 2.06/0.99  
% 2.06/0.99  ------ Abstraction refinement Options
% 2.06/0.99  
% 2.06/0.99  --abstr_ref                             []
% 2.06/0.99  --abstr_ref_prep                        false
% 2.06/0.99  --abstr_ref_until_sat                   false
% 2.06/0.99  --abstr_ref_sig_restrict                funpre
% 2.06/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.06/0.99  --abstr_ref_under                       []
% 2.06/0.99  
% 2.06/0.99  ------ SAT Options
% 2.06/0.99  
% 2.06/0.99  --sat_mode                              false
% 2.06/0.99  --sat_fm_restart_options                ""
% 2.06/0.99  --sat_gr_def                            false
% 2.06/0.99  --sat_epr_types                         true
% 2.06/0.99  --sat_non_cyclic_types                  false
% 2.06/0.99  --sat_finite_models                     false
% 2.06/0.99  --sat_fm_lemmas                         false
% 2.06/0.99  --sat_fm_prep                           false
% 2.06/0.99  --sat_fm_uc_incr                        true
% 2.06/0.99  --sat_out_model                         small
% 2.06/0.99  --sat_out_clauses                       false
% 2.06/0.99  
% 2.06/0.99  ------ QBF Options
% 2.06/0.99  
% 2.06/0.99  --qbf_mode                              false
% 2.06/0.99  --qbf_elim_univ                         false
% 2.06/0.99  --qbf_dom_inst                          none
% 2.06/0.99  --qbf_dom_pre_inst                      false
% 2.06/0.99  --qbf_sk_in                             false
% 2.06/0.99  --qbf_pred_elim                         true
% 2.06/0.99  --qbf_split                             512
% 2.06/0.99  
% 2.06/0.99  ------ BMC1 Options
% 2.06/0.99  
% 2.06/0.99  --bmc1_incremental                      false
% 2.06/0.99  --bmc1_axioms                           reachable_all
% 2.06/0.99  --bmc1_min_bound                        0
% 2.06/0.99  --bmc1_max_bound                        -1
% 2.06/0.99  --bmc1_max_bound_default                -1
% 2.06/0.99  --bmc1_symbol_reachability              true
% 2.06/0.99  --bmc1_property_lemmas                  false
% 2.06/0.99  --bmc1_k_induction                      false
% 2.06/0.99  --bmc1_non_equiv_states                 false
% 2.06/0.99  --bmc1_deadlock                         false
% 2.06/0.99  --bmc1_ucm                              false
% 2.06/0.99  --bmc1_add_unsat_core                   none
% 2.06/0.99  --bmc1_unsat_core_children              false
% 2.06/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.06/0.99  --bmc1_out_stat                         full
% 2.06/0.99  --bmc1_ground_init                      false
% 2.06/0.99  --bmc1_pre_inst_next_state              false
% 2.06/0.99  --bmc1_pre_inst_state                   false
% 2.06/0.99  --bmc1_pre_inst_reach_state             false
% 2.06/0.99  --bmc1_out_unsat_core                   false
% 2.06/0.99  --bmc1_aig_witness_out                  false
% 2.06/0.99  --bmc1_verbose                          false
% 2.06/0.99  --bmc1_dump_clauses_tptp                false
% 2.06/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.06/0.99  --bmc1_dump_file                        -
% 2.06/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.06/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.06/0.99  --bmc1_ucm_extend_mode                  1
% 2.06/0.99  --bmc1_ucm_init_mode                    2
% 2.06/0.99  --bmc1_ucm_cone_mode                    none
% 2.06/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.06/0.99  --bmc1_ucm_relax_model                  4
% 2.06/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.06/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.06/0.99  --bmc1_ucm_layered_model                none
% 2.06/0.99  --bmc1_ucm_max_lemma_size               10
% 2.06/0.99  
% 2.06/0.99  ------ AIG Options
% 2.06/0.99  
% 2.06/0.99  --aig_mode                              false
% 2.06/0.99  
% 2.06/0.99  ------ Instantiation Options
% 2.06/0.99  
% 2.06/0.99  --instantiation_flag                    true
% 2.06/0.99  --inst_sos_flag                         false
% 2.06/0.99  --inst_sos_phase                        true
% 2.06/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.06/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.06/0.99  --inst_lit_sel_side                     num_symb
% 2.06/0.99  --inst_solver_per_active                1400
% 2.06/0.99  --inst_solver_calls_frac                1.
% 2.06/0.99  --inst_passive_queue_type               priority_queues
% 2.06/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.06/0.99  --inst_passive_queues_freq              [25;2]
% 2.06/0.99  --inst_dismatching                      true
% 2.06/0.99  --inst_eager_unprocessed_to_passive     true
% 2.06/0.99  --inst_prop_sim_given                   true
% 2.06/0.99  --inst_prop_sim_new                     false
% 2.06/0.99  --inst_subs_new                         false
% 2.06/0.99  --inst_eq_res_simp                      false
% 2.06/0.99  --inst_subs_given                       false
% 2.06/0.99  --inst_orphan_elimination               true
% 2.06/0.99  --inst_learning_loop_flag               true
% 2.06/0.99  --inst_learning_start                   3000
% 2.06/0.99  --inst_learning_factor                  2
% 2.06/0.99  --inst_start_prop_sim_after_learn       3
% 2.06/0.99  --inst_sel_renew                        solver
% 2.06/0.99  --inst_lit_activity_flag                true
% 2.06/0.99  --inst_restr_to_given                   false
% 2.06/0.99  --inst_activity_threshold               500
% 2.06/0.99  --inst_out_proof                        true
% 2.06/0.99  
% 2.06/0.99  ------ Resolution Options
% 2.06/0.99  
% 2.06/0.99  --resolution_flag                       true
% 2.06/0.99  --res_lit_sel                           adaptive
% 2.06/0.99  --res_lit_sel_side                      none
% 2.06/0.99  --res_ordering                          kbo
% 2.06/0.99  --res_to_prop_solver                    active
% 2.06/0.99  --res_prop_simpl_new                    false
% 2.06/0.99  --res_prop_simpl_given                  true
% 2.06/0.99  --res_passive_queue_type                priority_queues
% 2.06/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.06/1.00  --res_passive_queues_freq               [15;5]
% 2.06/1.00  --res_forward_subs                      full
% 2.06/1.00  --res_backward_subs                     full
% 2.06/1.00  --res_forward_subs_resolution           true
% 2.06/1.00  --res_backward_subs_resolution          true
% 2.06/1.00  --res_orphan_elimination                true
% 2.06/1.00  --res_time_limit                        2.
% 2.06/1.00  --res_out_proof                         true
% 2.06/1.00  
% 2.06/1.00  ------ Superposition Options
% 2.06/1.00  
% 2.06/1.00  --superposition_flag                    true
% 2.06/1.00  --sup_passive_queue_type                priority_queues
% 2.06/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.06/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.06/1.00  --demod_completeness_check              fast
% 2.06/1.00  --demod_use_ground                      true
% 2.06/1.00  --sup_to_prop_solver                    passive
% 2.06/1.00  --sup_prop_simpl_new                    true
% 2.06/1.00  --sup_prop_simpl_given                  true
% 2.06/1.00  --sup_fun_splitting                     false
% 2.06/1.00  --sup_smt_interval                      50000
% 2.06/1.00  
% 2.06/1.00  ------ Superposition Simplification Setup
% 2.06/1.00  
% 2.06/1.00  --sup_indices_passive                   []
% 2.06/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.06/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/1.00  --sup_full_bw                           [BwDemod]
% 2.06/1.00  --sup_immed_triv                        [TrivRules]
% 2.06/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.06/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/1.00  --sup_immed_bw_main                     []
% 2.06/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.06/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.06/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.06/1.00  
% 2.06/1.00  ------ Combination Options
% 2.06/1.00  
% 2.06/1.00  --comb_res_mult                         3
% 2.06/1.00  --comb_sup_mult                         2
% 2.06/1.00  --comb_inst_mult                        10
% 2.06/1.00  
% 2.06/1.00  ------ Debug Options
% 2.06/1.00  
% 2.06/1.00  --dbg_backtrace                         false
% 2.06/1.00  --dbg_dump_prop_clauses                 false
% 2.06/1.00  --dbg_dump_prop_clauses_file            -
% 2.06/1.00  --dbg_out_stat                          false
% 2.06/1.00  ------ Parsing...
% 2.06/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.06/1.00  
% 2.06/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.06/1.00  
% 2.06/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.06/1.00  
% 2.06/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.06/1.00  ------ Proving...
% 2.06/1.00  ------ Problem Properties 
% 2.06/1.00  
% 2.06/1.00  
% 2.06/1.00  clauses                                 40
% 2.06/1.00  conjectures                             25
% 2.06/1.00  EPR                                     15
% 2.06/1.00  Horn                                    31
% 2.06/1.00  unary                                   16
% 2.06/1.00  binary                                  16
% 2.06/1.00  lits                                    101
% 2.06/1.00  lits eq                                 2
% 2.06/1.00  fd_pure                                 0
% 2.06/1.00  fd_pseudo                               0
% 2.06/1.00  fd_cond                                 0
% 2.06/1.00  fd_pseudo_cond                          0
% 2.06/1.00  AC symbols                              0
% 2.06/1.00  
% 2.06/1.00  ------ Schedule dynamic 5 is on 
% 2.06/1.00  
% 2.06/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.06/1.00  
% 2.06/1.00  
% 2.06/1.00  ------ 
% 2.06/1.00  Current options:
% 2.06/1.00  ------ 
% 2.06/1.00  
% 2.06/1.00  ------ Input Options
% 2.06/1.00  
% 2.06/1.00  --out_options                           all
% 2.06/1.00  --tptp_safe_out                         true
% 2.06/1.00  --problem_path                          ""
% 2.06/1.00  --include_path                          ""
% 2.06/1.00  --clausifier                            res/vclausify_rel
% 2.06/1.00  --clausifier_options                    --mode clausify
% 2.06/1.00  --stdin                                 false
% 2.06/1.00  --stats_out                             all
% 2.06/1.00  
% 2.06/1.00  ------ General Options
% 2.06/1.00  
% 2.06/1.00  --fof                                   false
% 2.06/1.00  --time_out_real                         305.
% 2.06/1.00  --time_out_virtual                      -1.
% 2.06/1.00  --symbol_type_check                     false
% 2.06/1.00  --clausify_out                          false
% 2.06/1.00  --sig_cnt_out                           false
% 2.06/1.00  --trig_cnt_out                          false
% 2.06/1.00  --trig_cnt_out_tolerance                1.
% 2.06/1.00  --trig_cnt_out_sk_spl                   false
% 2.06/1.00  --abstr_cl_out                          false
% 2.06/1.00  
% 2.06/1.00  ------ Global Options
% 2.06/1.00  
% 2.06/1.00  --schedule                              default
% 2.06/1.00  --add_important_lit                     false
% 2.06/1.00  --prop_solver_per_cl                    1000
% 2.06/1.00  --min_unsat_core                        false
% 2.06/1.00  --soft_assumptions                      false
% 2.06/1.00  --soft_lemma_size                       3
% 2.06/1.00  --prop_impl_unit_size                   0
% 2.06/1.00  --prop_impl_unit                        []
% 2.06/1.00  --share_sel_clauses                     true
% 2.06/1.00  --reset_solvers                         false
% 2.06/1.00  --bc_imp_inh                            [conj_cone]
% 2.06/1.00  --conj_cone_tolerance                   3.
% 2.06/1.00  --extra_neg_conj                        none
% 2.06/1.00  --large_theory_mode                     true
% 2.06/1.00  --prolific_symb_bound                   200
% 2.06/1.00  --lt_threshold                          2000
% 2.06/1.00  --clause_weak_htbl                      true
% 2.06/1.00  --gc_record_bc_elim                     false
% 2.06/1.00  
% 2.06/1.00  ------ Preprocessing Options
% 2.06/1.00  
% 2.06/1.00  --preprocessing_flag                    true
% 2.06/1.00  --time_out_prep_mult                    0.1
% 2.06/1.00  --splitting_mode                        input
% 2.06/1.00  --splitting_grd                         true
% 2.06/1.00  --splitting_cvd                         false
% 2.06/1.00  --splitting_cvd_svl                     false
% 2.06/1.00  --splitting_nvd                         32
% 2.06/1.00  --sub_typing                            true
% 2.06/1.00  --prep_gs_sim                           true
% 2.06/1.00  --prep_unflatten                        true
% 2.06/1.00  --prep_res_sim                          true
% 2.06/1.00  --prep_upred                            true
% 2.06/1.00  --prep_sem_filter                       exhaustive
% 2.06/1.00  --prep_sem_filter_out                   false
% 2.06/1.00  --pred_elim                             true
% 2.06/1.00  --res_sim_input                         true
% 2.06/1.00  --eq_ax_congr_red                       true
% 2.06/1.00  --pure_diseq_elim                       true
% 2.06/1.00  --brand_transform                       false
% 2.06/1.00  --non_eq_to_eq                          false
% 2.06/1.00  --prep_def_merge                        true
% 2.06/1.00  --prep_def_merge_prop_impl              false
% 2.06/1.00  --prep_def_merge_mbd                    true
% 2.06/1.00  --prep_def_merge_tr_red                 false
% 2.06/1.00  --prep_def_merge_tr_cl                  false
% 2.06/1.00  --smt_preprocessing                     true
% 2.06/1.00  --smt_ac_axioms                         fast
% 2.06/1.00  --preprocessed_out                      false
% 2.06/1.00  --preprocessed_stats                    false
% 2.06/1.00  
% 2.06/1.00  ------ Abstraction refinement Options
% 2.06/1.00  
% 2.06/1.00  --abstr_ref                             []
% 2.06/1.00  --abstr_ref_prep                        false
% 2.06/1.00  --abstr_ref_until_sat                   false
% 2.06/1.00  --abstr_ref_sig_restrict                funpre
% 2.06/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.06/1.00  --abstr_ref_under                       []
% 2.06/1.00  
% 2.06/1.00  ------ SAT Options
% 2.06/1.00  
% 2.06/1.00  --sat_mode                              false
% 2.06/1.00  --sat_fm_restart_options                ""
% 2.06/1.00  --sat_gr_def                            false
% 2.06/1.00  --sat_epr_types                         true
% 2.06/1.00  --sat_non_cyclic_types                  false
% 2.06/1.00  --sat_finite_models                     false
% 2.06/1.00  --sat_fm_lemmas                         false
% 2.06/1.00  --sat_fm_prep                           false
% 2.06/1.00  --sat_fm_uc_incr                        true
% 2.06/1.00  --sat_out_model                         small
% 2.06/1.00  --sat_out_clauses                       false
% 2.06/1.00  
% 2.06/1.00  ------ QBF Options
% 2.06/1.00  
% 2.06/1.00  --qbf_mode                              false
% 2.06/1.00  --qbf_elim_univ                         false
% 2.06/1.00  --qbf_dom_inst                          none
% 2.06/1.00  --qbf_dom_pre_inst                      false
% 2.06/1.00  --qbf_sk_in                             false
% 2.06/1.00  --qbf_pred_elim                         true
% 2.06/1.00  --qbf_split                             512
% 2.06/1.00  
% 2.06/1.00  ------ BMC1 Options
% 2.06/1.00  
% 2.06/1.00  --bmc1_incremental                      false
% 2.06/1.00  --bmc1_axioms                           reachable_all
% 2.06/1.00  --bmc1_min_bound                        0
% 2.06/1.00  --bmc1_max_bound                        -1
% 2.06/1.00  --bmc1_max_bound_default                -1
% 2.06/1.00  --bmc1_symbol_reachability              true
% 2.06/1.00  --bmc1_property_lemmas                  false
% 2.06/1.00  --bmc1_k_induction                      false
% 2.06/1.00  --bmc1_non_equiv_states                 false
% 2.06/1.00  --bmc1_deadlock                         false
% 2.06/1.00  --bmc1_ucm                              false
% 2.06/1.00  --bmc1_add_unsat_core                   none
% 2.06/1.00  --bmc1_unsat_core_children              false
% 2.06/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.06/1.00  --bmc1_out_stat                         full
% 2.06/1.00  --bmc1_ground_init                      false
% 2.06/1.00  --bmc1_pre_inst_next_state              false
% 2.06/1.00  --bmc1_pre_inst_state                   false
% 2.06/1.00  --bmc1_pre_inst_reach_state             false
% 2.06/1.00  --bmc1_out_unsat_core                   false
% 2.06/1.00  --bmc1_aig_witness_out                  false
% 2.06/1.00  --bmc1_verbose                          false
% 2.06/1.00  --bmc1_dump_clauses_tptp                false
% 2.06/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.06/1.00  --bmc1_dump_file                        -
% 2.06/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.06/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.06/1.00  --bmc1_ucm_extend_mode                  1
% 2.06/1.00  --bmc1_ucm_init_mode                    2
% 2.06/1.00  --bmc1_ucm_cone_mode                    none
% 2.06/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.06/1.00  --bmc1_ucm_relax_model                  4
% 2.06/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.06/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.06/1.00  --bmc1_ucm_layered_model                none
% 2.06/1.00  --bmc1_ucm_max_lemma_size               10
% 2.06/1.00  
% 2.06/1.00  ------ AIG Options
% 2.06/1.00  
% 2.06/1.00  --aig_mode                              false
% 2.06/1.00  
% 2.06/1.00  ------ Instantiation Options
% 2.06/1.00  
% 2.06/1.00  --instantiation_flag                    true
% 2.06/1.00  --inst_sos_flag                         false
% 2.06/1.00  --inst_sos_phase                        true
% 2.06/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.06/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.06/1.00  --inst_lit_sel_side                     none
% 2.06/1.00  --inst_solver_per_active                1400
% 2.06/1.00  --inst_solver_calls_frac                1.
% 2.06/1.00  --inst_passive_queue_type               priority_queues
% 2.06/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.06/1.00  --inst_passive_queues_freq              [25;2]
% 2.06/1.00  --inst_dismatching                      true
% 2.06/1.00  --inst_eager_unprocessed_to_passive     true
% 2.06/1.00  --inst_prop_sim_given                   true
% 2.06/1.00  --inst_prop_sim_new                     false
% 2.06/1.00  --inst_subs_new                         false
% 2.06/1.00  --inst_eq_res_simp                      false
% 2.06/1.00  --inst_subs_given                       false
% 2.06/1.00  --inst_orphan_elimination               true
% 2.06/1.00  --inst_learning_loop_flag               true
% 2.06/1.00  --inst_learning_start                   3000
% 2.06/1.00  --inst_learning_factor                  2
% 2.06/1.00  --inst_start_prop_sim_after_learn       3
% 2.06/1.00  --inst_sel_renew                        solver
% 2.06/1.00  --inst_lit_activity_flag                true
% 2.06/1.00  --inst_restr_to_given                   false
% 2.06/1.00  --inst_activity_threshold               500
% 2.06/1.00  --inst_out_proof                        true
% 2.06/1.00  
% 2.06/1.00  ------ Resolution Options
% 2.06/1.00  
% 2.06/1.00  --resolution_flag                       false
% 2.06/1.00  --res_lit_sel                           adaptive
% 2.06/1.00  --res_lit_sel_side                      none
% 2.06/1.00  --res_ordering                          kbo
% 2.06/1.00  --res_to_prop_solver                    active
% 2.06/1.00  --res_prop_simpl_new                    false
% 2.06/1.00  --res_prop_simpl_given                  true
% 2.06/1.00  --res_passive_queue_type                priority_queues
% 2.06/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.06/1.00  --res_passive_queues_freq               [15;5]
% 2.06/1.00  --res_forward_subs                      full
% 2.06/1.00  --res_backward_subs                     full
% 2.06/1.00  --res_forward_subs_resolution           true
% 2.06/1.00  --res_backward_subs_resolution          true
% 2.06/1.00  --res_orphan_elimination                true
% 2.06/1.00  --res_time_limit                        2.
% 2.06/1.00  --res_out_proof                         true
% 2.06/1.00  
% 2.06/1.00  ------ Superposition Options
% 2.06/1.00  
% 2.06/1.00  --superposition_flag                    true
% 2.06/1.00  --sup_passive_queue_type                priority_queues
% 2.06/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.06/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.06/1.00  --demod_completeness_check              fast
% 2.06/1.00  --demod_use_ground                      true
% 2.06/1.00  --sup_to_prop_solver                    passive
% 2.06/1.00  --sup_prop_simpl_new                    true
% 2.06/1.00  --sup_prop_simpl_given                  true
% 2.06/1.00  --sup_fun_splitting                     false
% 2.06/1.00  --sup_smt_interval                      50000
% 2.06/1.00  
% 2.06/1.00  ------ Superposition Simplification Setup
% 2.06/1.00  
% 2.06/1.00  --sup_indices_passive                   []
% 2.06/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.06/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/1.00  --sup_full_bw                           [BwDemod]
% 2.06/1.00  --sup_immed_triv                        [TrivRules]
% 2.06/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.06/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/1.00  --sup_immed_bw_main                     []
% 2.06/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.06/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.06/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.06/1.00  
% 2.06/1.00  ------ Combination Options
% 2.06/1.00  
% 2.06/1.00  --comb_res_mult                         3
% 2.06/1.00  --comb_sup_mult                         2
% 2.06/1.00  --comb_inst_mult                        10
% 2.06/1.00  
% 2.06/1.00  ------ Debug Options
% 2.06/1.00  
% 2.06/1.00  --dbg_backtrace                         false
% 2.06/1.00  --dbg_dump_prop_clauses                 false
% 2.06/1.00  --dbg_dump_prop_clauses_file            -
% 2.06/1.00  --dbg_out_stat                          false
% 2.06/1.00  
% 2.06/1.00  
% 2.06/1.00  
% 2.06/1.00  
% 2.06/1.00  ------ Proving...
% 2.06/1.00  
% 2.06/1.00  
% 2.06/1.00  % SZS status Theorem for theBenchmark.p
% 2.06/1.00  
% 2.06/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.06/1.00  
% 2.06/1.00  fof(f11,plain,(
% 2.06/1.00    ! [X1,X4,X2,X0,X3] : (sP0(X1,X4,X2,X0,X3) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 2.06/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.06/1.00  
% 2.06/1.00  fof(f17,plain,(
% 2.06/1.00    ! [X1,X4,X2,X0,X3] : ((sP0(X1,X4,X2,X0,X3) | (~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~sP0(X1,X4,X2,X0,X3)))),
% 2.06/1.00    inference(nnf_transformation,[],[f11])).
% 2.06/1.00  
% 2.06/1.00  fof(f18,plain,(
% 2.06/1.00    ! [X1,X4,X2,X0,X3] : ((sP0(X1,X4,X2,X0,X3) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~sP0(X1,X4,X2,X0,X3)))),
% 2.06/1.00    inference(flattening,[],[f17])).
% 2.06/1.00  
% 2.06/1.00  fof(f19,plain,(
% 2.06/1.00    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) & ((m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) & v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) & m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) & v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) & v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) & v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) | ~sP0(X0,X1,X2,X3,X4)))),
% 2.06/1.00    inference(rectify,[],[f18])).
% 2.06/1.00  
% 2.06/1.00  fof(f40,plain,(
% 2.06/1.00    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~sP0(X0,X1,X2,X3,X4)) )),
% 2.06/1.00    inference(cnf_transformation,[],[f19])).
% 2.06/1.00  
% 2.06/1.00  fof(f39,plain,(
% 2.06/1.00    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) | ~sP0(X0,X1,X2,X3,X4)) )),
% 2.06/1.00    inference(cnf_transformation,[],[f19])).
% 2.06/1.00  
% 2.06/1.00  fof(f38,plain,(
% 2.06/1.00    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 2.06/1.00    inference(cnf_transformation,[],[f19])).
% 2.06/1.00  
% 2.06/1.00  fof(f36,plain,(
% 2.06/1.00    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) | ~sP0(X0,X1,X2,X3,X4)) )),
% 2.06/1.00    inference(cnf_transformation,[],[f19])).
% 2.06/1.00  
% 2.06/1.00  fof(f35,plain,(
% 2.06/1.00    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) | ~sP0(X0,X1,X2,X3,X4)) )),
% 2.06/1.00    inference(cnf_transformation,[],[f19])).
% 2.06/1.00  
% 2.06/1.00  fof(f34,plain,(
% 2.06/1.00    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 2.06/1.00    inference(cnf_transformation,[],[f19])).
% 2.06/1.00  
% 2.06/1.00  fof(f37,plain,(
% 2.06/1.00    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 2.06/1.00    inference(cnf_transformation,[],[f19])).
% 2.06/1.00  
% 2.06/1.00  fof(f33,plain,(
% 2.06/1.00    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 2.06/1.00    inference(cnf_transformation,[],[f19])).
% 2.06/1.00  
% 2.06/1.00  fof(f41,plain,(
% 2.06/1.00    ( ! [X4,X2,X0,X3,X1] : (sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) )),
% 2.06/1.00    inference(cnf_transformation,[],[f19])).
% 2.06/1.00  
% 2.06/1.00  fof(f12,plain,(
% 2.06/1.00    ! [X3,X0,X2,X4,X1] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> sP0(X1,X4,X2,X0,X3)) | ~sP1(X3,X0,X2,X4,X1))),
% 2.06/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.06/1.00  
% 2.06/1.00  fof(f14,plain,(
% 2.06/1.00    ! [X3,X0,X2,X4,X1] : ((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) | ~sP0(X1,X4,X2,X0,X3)) & (sP0(X1,X4,X2,X0,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)))) | ~sP1(X3,X0,X2,X4,X1))),
% 2.06/1.00    inference(nnf_transformation,[],[f12])).
% 2.06/1.00  
% 2.06/1.00  fof(f15,plain,(
% 2.06/1.00    ! [X3,X0,X2,X4,X1] : ((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) | ~sP0(X1,X4,X2,X0,X3)) & (sP0(X1,X4,X2,X0,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~sP1(X3,X0,X2,X4,X1))),
% 2.06/1.00    inference(flattening,[],[f14])).
% 2.06/1.00  
% 2.06/1.00  fof(f16,plain,(
% 2.06/1.00    ! [X0,X1,X2,X3,X4] : ((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4)))) & v5_pre_topc(X2,X1,X4) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4)) & v1_funct_1(X2)) | ~sP0(X4,X3,X2,X1,X0)) & (sP0(X4,X3,X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4)))) | ~v5_pre_topc(X2,X1,X4) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4)) | ~v1_funct_1(X2))) | ~sP1(X0,X1,X2,X3,X4))),
% 2.06/1.00    inference(rectify,[],[f15])).
% 2.06/1.00  
% 2.06/1.00  fof(f28,plain,(
% 2.06/1.00    ( ! [X4,X2,X0,X3,X1] : (sP0(X4,X3,X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4)))) | ~v5_pre_topc(X2,X1,X4) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4)) | ~v1_funct_1(X2) | ~sP1(X0,X1,X2,X3,X4)) )),
% 2.06/1.00    inference(cnf_transformation,[],[f16])).
% 2.06/1.00  
% 2.06/1.00  fof(f31,plain,(
% 2.06/1.00    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(X2,X1,X4) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 2.06/1.00    inference(cnf_transformation,[],[f16])).
% 2.06/1.00  
% 2.06/1.00  fof(f1,axiom,(
% 2.06/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 2.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/1.00  
% 2.06/1.00  fof(f5,plain,(
% 2.06/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) | (~r4_tsep_1(X0,X3,X4) | k1_tsep_1(X0,X3,X4) != X0)) | (~m1_pre_topc(X4,X0) | v2_struct_0(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.06/1.00    inference(ennf_transformation,[],[f1])).
% 2.06/1.00  
% 2.06/1.00  fof(f6,plain,(
% 2.06/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) | ~r4_tsep_1(X0,X3,X4) | k1_tsep_1(X0,X3,X4) != X0 | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.06/1.00    inference(flattening,[],[f5])).
% 2.06/1.00  
% 2.06/1.00  fof(f13,plain,(
% 2.06/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (sP1(X3,X0,X2,X4,X1) | ~r4_tsep_1(X0,X3,X4) | k1_tsep_1(X0,X3,X4) != X0 | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.06/1.00    inference(definition_folding,[],[f6,f12,f11])).
% 2.06/1.00  
% 2.06/1.00  fof(f42,plain,(
% 2.06/1.00    ( ! [X4,X2,X0,X3,X1] : (sP1(X3,X0,X2,X4,X1) | ~r4_tsep_1(X0,X3,X4) | k1_tsep_1(X0,X3,X4) != X0 | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.06/1.00    inference(cnf_transformation,[],[f13])).
% 2.06/1.00  
% 2.06/1.00  fof(f2,axiom,(
% 2.06/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) => r4_tsep_1(X0,X1,X2))))),
% 2.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/1.00  
% 2.06/1.00  fof(f7,plain,(
% 2.06/1.00    ! [X0] : (! [X1] : (! [X2] : (r4_tsep_1(X0,X1,X2) | (~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0))) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.06/1.00    inference(ennf_transformation,[],[f2])).
% 2.06/1.00  
% 2.06/1.00  fof(f8,plain,(
% 2.06/1.00    ! [X0] : (! [X1] : (! [X2] : (r4_tsep_1(X0,X1,X2) | ~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.06/1.00    inference(flattening,[],[f7])).
% 2.06/1.00  
% 2.06/1.00  fof(f43,plain,(
% 2.06/1.00    ( ! [X2,X0,X1] : (r4_tsep_1(X0,X1,X2) | ~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.06/1.00    inference(cnf_transformation,[],[f8])).
% 2.06/1.00  
% 2.06/1.00  fof(f3,conjecture,(
% 2.06/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & v1_tsep_1(X4,X0) & ~v2_struct_0(X4)) => (k1_tsep_1(X0,X3,X4) = X0 => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 2.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/1.00  
% 2.06/1.00  fof(f4,negated_conjecture,(
% 2.06/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & v1_tsep_1(X4,X0) & ~v2_struct_0(X4)) => (k1_tsep_1(X0,X3,X4) = X0 => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 2.06/1.00    inference(negated_conjecture,[],[f3])).
% 2.06/1.00  
% 2.06/1.00  fof(f9,plain,(
% 2.06/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & k1_tsep_1(X0,X3,X4) = X0) & (m1_pre_topc(X4,X0) & v1_tsep_1(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.06/1.00    inference(ennf_transformation,[],[f4])).
% 2.06/1.00  
% 2.06/1.00  fof(f10,plain,(
% 2.06/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & v1_tsep_1(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.06/1.00    inference(flattening,[],[f9])).
% 2.06/1.00  
% 2.06/1.00  fof(f20,plain,(
% 2.06/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & v1_tsep_1(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.06/1.00    inference(nnf_transformation,[],[f10])).
% 2.06/1.00  
% 2.06/1.00  fof(f21,plain,(
% 2.06/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & v1_tsep_1(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.06/1.00    inference(flattening,[],[f20])).
% 2.06/1.00  
% 2.06/1.00  fof(f26,plain,(
% 2.06/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & v1_tsep_1(X4,X0) & ~v2_struct_0(X4)) => ((~m1_subset_1(k2_tmap_1(X0,X1,X2,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,sK6),sK6,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,sK6),u1_struct_0(sK6),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,sK6)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,sK6),sK6,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,sK6),u1_struct_0(sK6),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,sK6)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & k1_tsep_1(X0,X3,sK6) = X0 & m1_pre_topc(sK6,X0) & v1_tsep_1(sK6,X0) & ~v2_struct_0(sK6))) )),
% 2.06/1.00    introduced(choice_axiom,[])).
% 2.06/1.00  
% 2.06/1.00  fof(f25,plain,(
% 2.06/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & v1_tsep_1(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,sK5),sK5,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,sK5),u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,sK5)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,sK5),sK5,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,sK5),u1_struct_0(sK5),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,sK5))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & k1_tsep_1(X0,sK5,X4) = X0 & m1_pre_topc(X4,X0) & v1_tsep_1(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(sK5,X0) & v1_tsep_1(sK5,X0) & ~v2_struct_0(sK5))) )),
% 2.06/1.00    introduced(choice_axiom,[])).
% 2.06/1.00  
% 2.06/1.00  fof(f24,plain,(
% 2.06/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & v1_tsep_1(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,sK4,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,sK4,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,sK4,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,sK4,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,sK4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,sK4,X3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(sK4,X0,X1) | ~v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(X0,X1,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,sK4,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,sK4,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,sK4,X4)) & m1_subset_1(k2_tmap_1(X0,X1,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,sK4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,sK4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,sK4,X3))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(sK4,X0,X1) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & v1_tsep_1(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 2.06/1.00    introduced(choice_axiom,[])).
% 2.06/1.00  
% 2.06/1.00  fof(f23,plain,(
% 2.06/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & v1_tsep_1(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(X0,sK3,X2,X4),X4,sK3) | ~v1_funct_2(k2_tmap_1(X0,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(X0,sK3,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(X0,sK3,X2,X3),X3,sK3) | ~v1_funct_2(k2_tmap_1(X0,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(X0,sK3,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v5_pre_topc(X2,X0,sK3) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(X0,sK3,X2,X4),X4,sK3) & v1_funct_2(k2_tmap_1(X0,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(X0,sK3,X2,X4)) & m1_subset_1(k2_tmap_1(X0,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(X0,sK3,X2,X3),X3,sK3) & v1_funct_2(k2_tmap_1(X0,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(X0,sK3,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v5_pre_topc(X2,X0,sK3) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X2))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & v1_tsep_1(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 2.06/1.00    introduced(choice_axiom,[])).
% 2.06/1.00  
% 2.06/1.00  fof(f22,plain,(
% 2.06/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & v1_tsep_1(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK2,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK2,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~v5_pre_topc(X2,sK2,X1) | ~v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK2,X1,X2,X4)) & m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK2,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v5_pre_topc(X2,sK2,X1) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2))) & k1_tsep_1(sK2,X3,X4) = sK2 & m1_pre_topc(X4,sK2) & v1_tsep_1(X4,sK2) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK2) & v1_tsep_1(X3,sK2) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.06/1.00    introduced(choice_axiom,[])).
% 2.06/1.00  
% 2.06/1.00  fof(f27,plain,(
% 2.06/1.00    (((((~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))) & k1_tsep_1(sK2,sK5,sK6) = sK2 & m1_pre_topc(sK6,sK2) & v1_tsep_1(sK6,sK2) & ~v2_struct_0(sK6)) & m1_pre_topc(sK5,sK2) & v1_tsep_1(sK5,sK2) & ~v2_struct_0(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.06/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f21,f26,f25,f24,f23,f22])).
% 2.06/1.00  
% 2.06/1.00  fof(f59,plain,(
% 2.06/1.00    k1_tsep_1(sK2,sK5,sK6) = sK2),
% 2.06/1.00    inference(cnf_transformation,[],[f27])).
% 2.06/1.00  
% 2.06/1.00  fof(f92,plain,(
% 2.06/1.00    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 2.06/1.00    inference(cnf_transformation,[],[f27])).
% 2.06/1.00  
% 2.06/1.00  fof(f50,plain,(
% 2.06/1.00    v1_funct_1(sK4)),
% 2.06/1.00    inference(cnf_transformation,[],[f27])).
% 2.06/1.00  
% 2.06/1.00  fof(f51,plain,(
% 2.06/1.00    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 2.06/1.00    inference(cnf_transformation,[],[f27])).
% 2.06/1.00  
% 2.06/1.00  fof(f52,plain,(
% 2.06/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 2.06/1.00    inference(cnf_transformation,[],[f27])).
% 2.06/1.00  
% 2.06/1.00  fof(f90,plain,(
% 2.06/1.00    m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | v5_pre_topc(sK4,sK2,sK3)),
% 2.06/1.00    inference(cnf_transformation,[],[f27])).
% 2.06/1.00  
% 2.06/1.00  fof(f86,plain,(
% 2.06/1.00    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | v5_pre_topc(sK4,sK2,sK3)),
% 2.06/1.00    inference(cnf_transformation,[],[f27])).
% 2.06/1.00  
% 2.06/1.00  fof(f82,plain,(
% 2.06/1.00    v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | v5_pre_topc(sK4,sK2,sK3)),
% 2.06/1.00    inference(cnf_transformation,[],[f27])).
% 2.06/1.00  
% 2.06/1.00  fof(f78,plain,(
% 2.06/1.00    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | v5_pre_topc(sK4,sK2,sK3)),
% 2.06/1.00    inference(cnf_transformation,[],[f27])).
% 2.06/1.00  
% 2.06/1.00  fof(f74,plain,(
% 2.06/1.00    m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | v5_pre_topc(sK4,sK2,sK3)),
% 2.06/1.00    inference(cnf_transformation,[],[f27])).
% 2.06/1.00  
% 2.06/1.00  fof(f70,plain,(
% 2.06/1.00    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | v5_pre_topc(sK4,sK2,sK3)),
% 2.06/1.00    inference(cnf_transformation,[],[f27])).
% 2.06/1.00  
% 2.06/1.00  fof(f66,plain,(
% 2.06/1.00    v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | v5_pre_topc(sK4,sK2,sK3)),
% 2.06/1.00    inference(cnf_transformation,[],[f27])).
% 2.06/1.00  
% 2.06/1.00  fof(f62,plain,(
% 2.06/1.00    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | v5_pre_topc(sK4,sK2,sK3)),
% 2.06/1.00    inference(cnf_transformation,[],[f27])).
% 2.06/1.00  
% 2.06/1.00  fof(f58,plain,(
% 2.06/1.00    m1_pre_topc(sK6,sK2)),
% 2.06/1.00    inference(cnf_transformation,[],[f27])).
% 2.06/1.00  
% 2.06/1.00  fof(f57,plain,(
% 2.06/1.00    v1_tsep_1(sK6,sK2)),
% 2.06/1.00    inference(cnf_transformation,[],[f27])).
% 2.06/1.00  
% 2.06/1.00  fof(f56,plain,(
% 2.06/1.00    ~v2_struct_0(sK6)),
% 2.06/1.00    inference(cnf_transformation,[],[f27])).
% 2.06/1.00  
% 2.06/1.00  fof(f55,plain,(
% 2.06/1.00    m1_pre_topc(sK5,sK2)),
% 2.06/1.00    inference(cnf_transformation,[],[f27])).
% 2.06/1.00  
% 2.06/1.00  fof(f54,plain,(
% 2.06/1.00    v1_tsep_1(sK5,sK2)),
% 2.06/1.00    inference(cnf_transformation,[],[f27])).
% 2.06/1.00  
% 2.06/1.00  fof(f53,plain,(
% 2.06/1.00    ~v2_struct_0(sK5)),
% 2.06/1.00    inference(cnf_transformation,[],[f27])).
% 2.06/1.00  
% 2.06/1.00  fof(f49,plain,(
% 2.06/1.00    l1_pre_topc(sK3)),
% 2.06/1.00    inference(cnf_transformation,[],[f27])).
% 2.06/1.00  
% 2.06/1.00  fof(f48,plain,(
% 2.06/1.00    v2_pre_topc(sK3)),
% 2.06/1.00    inference(cnf_transformation,[],[f27])).
% 2.06/1.00  
% 2.06/1.00  fof(f47,plain,(
% 2.06/1.00    ~v2_struct_0(sK3)),
% 2.06/1.00    inference(cnf_transformation,[],[f27])).
% 2.06/1.00  
% 2.06/1.00  fof(f46,plain,(
% 2.06/1.00    l1_pre_topc(sK2)),
% 2.06/1.00    inference(cnf_transformation,[],[f27])).
% 2.06/1.00  
% 2.06/1.00  fof(f45,plain,(
% 2.06/1.00    v2_pre_topc(sK2)),
% 2.06/1.00    inference(cnf_transformation,[],[f27])).
% 2.06/1.00  
% 2.06/1.00  fof(f44,plain,(
% 2.06/1.00    ~v2_struct_0(sK2)),
% 2.06/1.00    inference(cnf_transformation,[],[f27])).
% 2.06/1.00  
% 2.06/1.00  cnf(c_6,plain,
% 2.06/1.00      ( ~ sP0(X0,X1,X2,X3,X4)
% 2.06/1.00      | m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ),
% 2.06/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_2074,plain,
% 2.06/1.00      ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
% 2.06/1.00      | m1_subset_1(k2_tmap_1(X2_50,X0_50,X0_51,X1_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) ),
% 2.06/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_4037,plain,
% 2.06/1.00      ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
% 2.06/1.00      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
% 2.06/1.00      inference(instantiation,[status(thm)],[c_2074]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_7,plain,
% 2.06/1.00      ( ~ sP0(X0,X1,X2,X3,X4)
% 2.06/1.00      | v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) ),
% 2.06/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_2073,plain,
% 2.06/1.00      ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
% 2.06/1.00      | v5_pre_topc(k2_tmap_1(X2_50,X0_50,X0_51,X1_50),X1_50,X0_50) ),
% 2.06/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_4038,plain,
% 2.06/1.00      ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
% 2.06/1.00      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) ),
% 2.06/1.00      inference(instantiation,[status(thm)],[c_2073]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_8,plain,
% 2.06/1.00      ( ~ sP0(X0,X1,X2,X3,X4)
% 2.06/1.00      | v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) ),
% 2.06/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_2072,plain,
% 2.06/1.00      ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
% 2.06/1.00      | v1_funct_2(k2_tmap_1(X2_50,X0_50,X0_51,X1_50),u1_struct_0(X1_50),u1_struct_0(X0_50)) ),
% 2.06/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_4039,plain,
% 2.06/1.00      ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
% 2.06/1.00      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) ),
% 2.06/1.00      inference(instantiation,[status(thm)],[c_2072]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_10,plain,
% 2.06/1.00      ( ~ sP0(X0,X1,X2,X3,X4)
% 2.06/1.00      | m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) ),
% 2.06/1.00      inference(cnf_transformation,[],[f36]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_2070,plain,
% 2.06/1.00      ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
% 2.06/1.00      | m1_subset_1(k2_tmap_1(X2_50,X0_50,X0_51,X3_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X0_50)))) ),
% 2.06/1.00      inference(subtyping,[status(esa)],[c_10]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_4040,plain,
% 2.06/1.00      ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
% 2.06/1.00      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 2.06/1.00      inference(instantiation,[status(thm)],[c_2070]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_11,plain,
% 2.06/1.00      ( ~ sP0(X0,X1,X2,X3,X4)
% 2.06/1.00      | v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) ),
% 2.06/1.00      inference(cnf_transformation,[],[f35]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_2069,plain,
% 2.06/1.00      ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
% 2.06/1.00      | v5_pre_topc(k2_tmap_1(X2_50,X0_50,X0_51,X3_50),X3_50,X0_50) ),
% 2.06/1.00      inference(subtyping,[status(esa)],[c_11]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_4041,plain,
% 2.06/1.00      ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
% 2.06/1.00      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) ),
% 2.06/1.00      inference(instantiation,[status(thm)],[c_2069]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_12,plain,
% 2.06/1.00      ( ~ sP0(X0,X1,X2,X3,X4)
% 2.06/1.00      | v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) ),
% 2.06/1.00      inference(cnf_transformation,[],[f34]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_2068,plain,
% 2.06/1.00      ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
% 2.06/1.00      | v1_funct_2(k2_tmap_1(X2_50,X0_50,X0_51,X3_50),u1_struct_0(X3_50),u1_struct_0(X0_50)) ),
% 2.06/1.00      inference(subtyping,[status(esa)],[c_12]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_4042,plain,
% 2.06/1.00      ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
% 2.06/1.00      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) ),
% 2.06/1.00      inference(instantiation,[status(thm)],[c_2068]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_9,plain,
% 2.06/1.00      ( ~ sP0(X0,X1,X2,X3,X4) | v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) ),
% 2.06/1.00      inference(cnf_transformation,[],[f37]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_2071,plain,
% 2.06/1.00      ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
% 2.06/1.00      | v1_funct_1(k2_tmap_1(X2_50,X0_50,X0_51,X1_50)) ),
% 2.06/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_4043,plain,
% 2.06/1.00      ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
% 2.06/1.00      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
% 2.06/1.00      inference(instantiation,[status(thm)],[c_2071]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_13,plain,
% 2.06/1.00      ( ~ sP0(X0,X1,X2,X3,X4) | v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) ),
% 2.06/1.00      inference(cnf_transformation,[],[f33]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_2067,plain,
% 2.06/1.00      ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
% 2.06/1.00      | v1_funct_1(k2_tmap_1(X2_50,X0_50,X0_51,X3_50)) ),
% 2.06/1.00      inference(subtyping,[status(esa)],[c_13]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_4044,plain,
% 2.06/1.00      ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
% 2.06/1.00      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
% 2.06/1.00      inference(instantiation,[status(thm)],[c_2067]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_5,plain,
% 2.06/1.00      ( sP0(X0,X1,X2,X3,X4)
% 2.06/1.00      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
% 2.06/1.00      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
% 2.06/1.00      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
% 2.06/1.00      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
% 2.06/1.00      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
% 2.06/1.00      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
% 2.06/1.00      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
% 2.06/1.00      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) ),
% 2.06/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_2075,plain,
% 2.06/1.00      ( sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
% 2.06/1.00      | ~ v1_funct_2(k2_tmap_1(X2_50,X0_50,X0_51,X1_50),u1_struct_0(X1_50),u1_struct_0(X0_50))
% 2.06/1.00      | ~ v1_funct_2(k2_tmap_1(X2_50,X0_50,X0_51,X3_50),u1_struct_0(X3_50),u1_struct_0(X0_50))
% 2.06/1.00      | ~ v5_pre_topc(k2_tmap_1(X2_50,X0_50,X0_51,X1_50),X1_50,X0_50)
% 2.06/1.00      | ~ v5_pre_topc(k2_tmap_1(X2_50,X0_50,X0_51,X3_50),X3_50,X0_50)
% 2.06/1.00      | ~ m1_subset_1(k2_tmap_1(X2_50,X0_50,X0_51,X1_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50))))
% 2.06/1.00      | ~ m1_subset_1(k2_tmap_1(X2_50,X0_50,X0_51,X3_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X0_50))))
% 2.06/1.00      | ~ v1_funct_1(k2_tmap_1(X2_50,X0_50,X0_51,X1_50))
% 2.06/1.00      | ~ v1_funct_1(k2_tmap_1(X2_50,X0_50,X0_51,X3_50)) ),
% 2.06/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_3558,plain,
% 2.06/1.00      ( sP0(sK3,sK6,sK4,sK2,X0_50)
% 2.06/1.00      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0_50),u1_struct_0(X0_50),u1_struct_0(sK3))
% 2.06/1.00      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 2.06/1.00      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0_50),X0_50,sK3)
% 2.06/1.00      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 2.06/1.00      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK3))))
% 2.06/1.00      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 2.06/1.00      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_50))
% 2.06/1.00      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
% 2.06/1.00      inference(instantiation,[status(thm)],[c_2075]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_3885,plain,
% 2.06/1.00      ( sP0(sK3,sK6,sK4,sK2,sK5)
% 2.06/1.00      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 2.06/1.00      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 2.06/1.00      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 2.06/1.00      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 2.06/1.00      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 2.06/1.00      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 2.06/1.00      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 2.06/1.00      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
% 2.06/1.00      inference(instantiation,[status(thm)],[c_3558]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_4,plain,
% 2.06/1.00      ( ~ sP1(X0,X1,X2,X3,X4)
% 2.06/1.00      | sP0(X4,X3,X2,X1,X0)
% 2.06/1.00      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
% 2.06/1.00      | ~ v5_pre_topc(X2,X1,X4)
% 2.06/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 2.06/1.00      | ~ v1_funct_1(X2) ),
% 2.06/1.00      inference(cnf_transformation,[],[f28]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_2076,plain,
% 2.06/1.00      ( ~ sP1(X0_50,X1_50,X0_51,X2_50,X3_50)
% 2.06/1.00      | sP0(X3_50,X2_50,X0_51,X1_50,X0_50)
% 2.06/1.00      | ~ v1_funct_2(X0_51,u1_struct_0(X1_50),u1_struct_0(X3_50))
% 2.06/1.00      | ~ v5_pre_topc(X0_51,X1_50,X3_50)
% 2.06/1.00      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X3_50))))
% 2.06/1.00      | ~ v1_funct_1(X0_51) ),
% 2.06/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_3231,plain,
% 2.06/1.00      ( ~ sP1(X0_50,sK2,sK4,X1_50,sK3)
% 2.06/1.00      | sP0(sK3,X1_50,sK4,sK2,X0_50)
% 2.06/1.00      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 2.06/1.00      | ~ v5_pre_topc(sK4,sK2,sK3)
% 2.06/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 2.06/1.00      | ~ v1_funct_1(sK4) ),
% 2.06/1.00      inference(instantiation,[status(thm)],[c_2076]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_3456,plain,
% 2.06/1.00      ( ~ sP1(sK5,sK2,sK4,sK6,sK3)
% 2.06/1.00      | sP0(sK3,sK6,sK4,sK2,sK5)
% 2.06/1.00      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 2.06/1.00      | ~ v5_pre_topc(sK4,sK2,sK3)
% 2.06/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 2.06/1.00      | ~ v1_funct_1(sK4) ),
% 2.06/1.00      inference(instantiation,[status(thm)],[c_3231]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_1,plain,
% 2.06/1.00      ( ~ sP1(X0,X1,X2,X3,X4)
% 2.06/1.00      | ~ sP0(X4,X3,X2,X1,X0)
% 2.06/1.00      | v5_pre_topc(X2,X1,X4) ),
% 2.06/1.00      inference(cnf_transformation,[],[f31]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_2079,plain,
% 2.06/1.00      ( ~ sP1(X0_50,X1_50,X0_51,X2_50,X3_50)
% 2.06/1.00      | ~ sP0(X3_50,X2_50,X0_51,X1_50,X0_50)
% 2.06/1.00      | v5_pre_topc(X0_51,X1_50,X3_50) ),
% 2.06/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_3435,plain,
% 2.06/1.00      ( ~ sP1(sK5,sK2,X0_51,sK6,X0_50)
% 2.06/1.00      | ~ sP0(X0_50,sK6,X0_51,sK2,sK5)
% 2.06/1.00      | v5_pre_topc(X0_51,sK2,X0_50) ),
% 2.06/1.00      inference(instantiation,[status(thm)],[c_2079]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_3440,plain,
% 2.06/1.00      ( ~ sP1(sK5,sK2,sK4,sK6,sK3)
% 2.06/1.00      | ~ sP0(sK3,sK6,sK4,sK2,sK5)
% 2.06/1.00      | v5_pre_topc(sK4,sK2,sK3) ),
% 2.06/1.00      inference(instantiation,[status(thm)],[c_3435]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_14,plain,
% 2.06/1.00      ( sP1(X0,X1,X2,X3,X4)
% 2.06/1.00      | ~ r4_tsep_1(X1,X0,X3)
% 2.06/1.00      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
% 2.06/1.00      | ~ m1_pre_topc(X3,X1)
% 2.06/1.00      | ~ m1_pre_topc(X0,X1)
% 2.06/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 2.06/1.00      | ~ v2_pre_topc(X4)
% 2.06/1.00      | ~ v2_pre_topc(X1)
% 2.06/1.00      | ~ l1_pre_topc(X4)
% 2.06/1.00      | ~ l1_pre_topc(X1)
% 2.06/1.00      | v2_struct_0(X1)
% 2.06/1.00      | v2_struct_0(X4)
% 2.06/1.00      | v2_struct_0(X0)
% 2.06/1.00      | v2_struct_0(X3)
% 2.06/1.00      | ~ v1_funct_1(X2)
% 2.06/1.00      | k1_tsep_1(X1,X0,X3) != X1 ),
% 2.06/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_15,plain,
% 2.06/1.00      ( r4_tsep_1(X0,X1,X2)
% 2.06/1.00      | ~ v1_tsep_1(X2,X0)
% 2.06/1.00      | ~ v1_tsep_1(X1,X0)
% 2.06/1.00      | ~ m1_pre_topc(X2,X0)
% 2.06/1.00      | ~ m1_pre_topc(X1,X0)
% 2.06/1.00      | ~ v2_pre_topc(X0)
% 2.06/1.00      | ~ l1_pre_topc(X0)
% 2.06/1.00      | v2_struct_0(X0) ),
% 2.06/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_638,plain,
% 2.06/1.00      ( sP1(X0,X1,X2,X3,X4)
% 2.06/1.00      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
% 2.06/1.00      | ~ v1_tsep_1(X5,X6)
% 2.06/1.00      | ~ v1_tsep_1(X7,X6)
% 2.06/1.00      | ~ m1_pre_topc(X3,X1)
% 2.06/1.00      | ~ m1_pre_topc(X0,X1)
% 2.06/1.00      | ~ m1_pre_topc(X5,X6)
% 2.06/1.00      | ~ m1_pre_topc(X7,X6)
% 2.06/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 2.06/1.00      | ~ v2_pre_topc(X1)
% 2.06/1.00      | ~ v2_pre_topc(X4)
% 2.06/1.00      | ~ v2_pre_topc(X6)
% 2.06/1.00      | ~ l1_pre_topc(X1)
% 2.06/1.00      | ~ l1_pre_topc(X4)
% 2.06/1.00      | ~ l1_pre_topc(X6)
% 2.06/1.00      | v2_struct_0(X4)
% 2.06/1.00      | v2_struct_0(X1)
% 2.06/1.00      | v2_struct_0(X3)
% 2.06/1.00      | v2_struct_0(X0)
% 2.06/1.00      | v2_struct_0(X6)
% 2.06/1.00      | ~ v1_funct_1(X2)
% 2.06/1.00      | X5 != X3
% 2.06/1.00      | X7 != X0
% 2.06/1.00      | X6 != X1
% 2.06/1.00      | k1_tsep_1(X1,X0,X3) != X1 ),
% 2.06/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_15]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_639,plain,
% 2.06/1.00      ( sP1(X0,X1,X2,X3,X4)
% 2.06/1.00      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
% 2.06/1.00      | ~ v1_tsep_1(X0,X1)
% 2.06/1.00      | ~ v1_tsep_1(X3,X1)
% 2.06/1.00      | ~ m1_pre_topc(X3,X1)
% 2.06/1.00      | ~ m1_pre_topc(X0,X1)
% 2.06/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 2.06/1.00      | ~ v2_pre_topc(X1)
% 2.06/1.00      | ~ v2_pre_topc(X4)
% 2.06/1.00      | ~ l1_pre_topc(X1)
% 2.06/1.00      | ~ l1_pre_topc(X4)
% 2.06/1.00      | v2_struct_0(X4)
% 2.06/1.00      | v2_struct_0(X1)
% 2.06/1.00      | v2_struct_0(X3)
% 2.06/1.00      | v2_struct_0(X0)
% 2.06/1.00      | ~ v1_funct_1(X2)
% 2.06/1.00      | k1_tsep_1(X1,X0,X3) != X1 ),
% 2.06/1.00      inference(unflattening,[status(thm)],[c_638]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_2041,plain,
% 2.06/1.00      ( sP1(X0_50,X1_50,X0_51,X2_50,X3_50)
% 2.06/1.00      | ~ v1_funct_2(X0_51,u1_struct_0(X1_50),u1_struct_0(X3_50))
% 2.06/1.00      | ~ v1_tsep_1(X0_50,X1_50)
% 2.06/1.00      | ~ v1_tsep_1(X2_50,X1_50)
% 2.06/1.00      | ~ m1_pre_topc(X0_50,X1_50)
% 2.06/1.00      | ~ m1_pre_topc(X2_50,X1_50)
% 2.06/1.00      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X3_50))))
% 2.06/1.00      | ~ v2_pre_topc(X1_50)
% 2.06/1.00      | ~ v2_pre_topc(X3_50)
% 2.06/1.00      | ~ l1_pre_topc(X1_50)
% 2.06/1.00      | ~ l1_pre_topc(X3_50)
% 2.06/1.00      | v2_struct_0(X1_50)
% 2.06/1.00      | v2_struct_0(X3_50)
% 2.06/1.00      | v2_struct_0(X0_50)
% 2.06/1.00      | v2_struct_0(X2_50)
% 2.06/1.00      | ~ v1_funct_1(X0_51)
% 2.06/1.00      | k1_tsep_1(X1_50,X0_50,X2_50) != X1_50 ),
% 2.06/1.00      inference(subtyping,[status(esa)],[c_639]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_3241,plain,
% 2.06/1.00      ( sP1(sK5,sK2,X0_51,X0_50,X1_50)
% 2.06/1.00      | ~ v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(X1_50))
% 2.06/1.00      | ~ v1_tsep_1(X0_50,sK2)
% 2.06/1.00      | ~ v1_tsep_1(sK5,sK2)
% 2.06/1.00      | ~ m1_pre_topc(X0_50,sK2)
% 2.06/1.00      | ~ m1_pre_topc(sK5,sK2)
% 2.06/1.00      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1_50))))
% 2.06/1.00      | ~ v2_pre_topc(X1_50)
% 2.06/1.00      | ~ v2_pre_topc(sK2)
% 2.06/1.00      | ~ l1_pre_topc(X1_50)
% 2.06/1.00      | ~ l1_pre_topc(sK2)
% 2.06/1.00      | v2_struct_0(X1_50)
% 2.06/1.00      | v2_struct_0(X0_50)
% 2.06/1.00      | v2_struct_0(sK5)
% 2.06/1.00      | v2_struct_0(sK2)
% 2.06/1.00      | ~ v1_funct_1(X0_51)
% 2.06/1.00      | k1_tsep_1(sK2,sK5,X0_50) != sK2 ),
% 2.06/1.00      inference(instantiation,[status(thm)],[c_2041]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_3336,plain,
% 2.06/1.00      ( sP1(sK5,sK2,X0_51,sK6,X0_50)
% 2.06/1.00      | ~ v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(X0_50))
% 2.06/1.00      | ~ v1_tsep_1(sK5,sK2)
% 2.06/1.00      | ~ v1_tsep_1(sK6,sK2)
% 2.06/1.00      | ~ m1_pre_topc(sK5,sK2)
% 2.06/1.00      | ~ m1_pre_topc(sK6,sK2)
% 2.06/1.00      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_50))))
% 2.06/1.00      | ~ v2_pre_topc(X0_50)
% 2.06/1.00      | ~ v2_pre_topc(sK2)
% 2.06/1.00      | ~ l1_pre_topc(X0_50)
% 2.06/1.00      | ~ l1_pre_topc(sK2)
% 2.06/1.00      | v2_struct_0(X0_50)
% 2.06/1.00      | v2_struct_0(sK5)
% 2.06/1.00      | v2_struct_0(sK6)
% 2.06/1.00      | v2_struct_0(sK2)
% 2.06/1.00      | ~ v1_funct_1(X0_51)
% 2.06/1.00      | k1_tsep_1(sK2,sK5,sK6) != sK2 ),
% 2.06/1.00      inference(instantiation,[status(thm)],[c_3241]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_3338,plain,
% 2.06/1.00      ( sP1(sK5,sK2,sK4,sK6,sK3)
% 2.06/1.00      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 2.06/1.00      | ~ v1_tsep_1(sK5,sK2)
% 2.06/1.00      | ~ v1_tsep_1(sK6,sK2)
% 2.06/1.00      | ~ m1_pre_topc(sK5,sK2)
% 2.06/1.00      | ~ m1_pre_topc(sK6,sK2)
% 2.06/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 2.06/1.00      | ~ v2_pre_topc(sK3)
% 2.06/1.00      | ~ v2_pre_topc(sK2)
% 2.06/1.00      | ~ l1_pre_topc(sK3)
% 2.06/1.00      | ~ l1_pre_topc(sK2)
% 2.06/1.00      | v2_struct_0(sK5)
% 2.06/1.00      | v2_struct_0(sK6)
% 2.06/1.00      | v2_struct_0(sK3)
% 2.06/1.00      | v2_struct_0(sK2)
% 2.06/1.00      | ~ v1_funct_1(sK4)
% 2.06/1.00      | k1_tsep_1(sK2,sK5,sK6) != sK2 ),
% 2.06/1.00      inference(instantiation,[status(thm)],[c_3336]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_49,negated_conjecture,
% 2.06/1.00      ( k1_tsep_1(sK2,sK5,sK6) = sK2 ),
% 2.06/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_2058,negated_conjecture,
% 2.06/1.00      ( k1_tsep_1(sK2,sK5,sK6) = sK2 ),
% 2.06/1.00      inference(subtyping,[status(esa)],[c_49]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_16,negated_conjecture,
% 2.06/1.00      ( ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 2.06/1.00      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 2.06/1.00      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 2.06/1.00      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 2.06/1.00      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 2.06/1.00      | ~ v5_pre_topc(sK4,sK2,sK3)
% 2.06/1.00      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 2.06/1.00      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 2.06/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 2.06/1.00      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 2.06/1.00      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
% 2.06/1.00      | ~ v1_funct_1(sK4) ),
% 2.06/1.00      inference(cnf_transformation,[],[f92]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_58,negated_conjecture,
% 2.06/1.00      ( v1_funct_1(sK4) ),
% 2.06/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_57,negated_conjecture,
% 2.06/1.00      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 2.06/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_56,negated_conjecture,
% 2.06/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 2.06/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_425,plain,
% 2.06/1.00      ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
% 2.06/1.00      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 2.06/1.00      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 2.06/1.00      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 2.06/1.00      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 2.06/1.00      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 2.06/1.00      | ~ v5_pre_topc(sK4,sK2,sK3)
% 2.06/1.00      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 2.06/1.00      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
% 2.06/1.00      inference(global_propositional_subsumption,
% 2.06/1.00                [status(thm)],
% 2.06/1.00                [c_16,c_58,c_57,c_56]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_426,negated_conjecture,
% 2.06/1.00      ( ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 2.06/1.00      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 2.06/1.00      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 2.06/1.00      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 2.06/1.00      | ~ v5_pre_topc(sK4,sK2,sK3)
% 2.06/1.00      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 2.06/1.00      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 2.06/1.00      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 2.06/1.00      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
% 2.06/1.00      inference(renaming,[status(thm)],[c_425]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_18,negated_conjecture,
% 2.06/1.00      ( v5_pre_topc(sK4,sK2,sK3)
% 2.06/1.00      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
% 2.06/1.00      inference(cnf_transformation,[],[f90]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_22,negated_conjecture,
% 2.06/1.00      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 2.06/1.00      | v5_pre_topc(sK4,sK2,sK3) ),
% 2.06/1.00      inference(cnf_transformation,[],[f86]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_26,negated_conjecture,
% 2.06/1.00      ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 2.06/1.00      | v5_pre_topc(sK4,sK2,sK3) ),
% 2.06/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_30,negated_conjecture,
% 2.06/1.00      ( v5_pre_topc(sK4,sK2,sK3)
% 2.06/1.00      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
% 2.06/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_34,negated_conjecture,
% 2.06/1.00      ( v5_pre_topc(sK4,sK2,sK3)
% 2.06/1.00      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 2.06/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_38,negated_conjecture,
% 2.06/1.00      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 2.06/1.00      | v5_pre_topc(sK4,sK2,sK3) ),
% 2.06/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_42,negated_conjecture,
% 2.06/1.00      ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 2.06/1.00      | v5_pre_topc(sK4,sK2,sK3) ),
% 2.06/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_46,negated_conjecture,
% 2.06/1.00      ( v5_pre_topc(sK4,sK2,sK3)
% 2.06/1.00      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
% 2.06/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_50,negated_conjecture,
% 2.06/1.00      ( m1_pre_topc(sK6,sK2) ),
% 2.06/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_51,negated_conjecture,
% 2.06/1.00      ( v1_tsep_1(sK6,sK2) ),
% 2.06/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_52,negated_conjecture,
% 2.06/1.00      ( ~ v2_struct_0(sK6) ),
% 2.06/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_53,negated_conjecture,
% 2.06/1.00      ( m1_pre_topc(sK5,sK2) ),
% 2.06/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_54,negated_conjecture,
% 2.06/1.00      ( v1_tsep_1(sK5,sK2) ),
% 2.06/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_55,negated_conjecture,
% 2.06/1.00      ( ~ v2_struct_0(sK5) ),
% 2.06/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_59,negated_conjecture,
% 2.06/1.00      ( l1_pre_topc(sK3) ),
% 2.06/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_60,negated_conjecture,
% 2.06/1.00      ( v2_pre_topc(sK3) ),
% 2.06/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_61,negated_conjecture,
% 2.06/1.00      ( ~ v2_struct_0(sK3) ),
% 2.06/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_62,negated_conjecture,
% 2.06/1.00      ( l1_pre_topc(sK2) ),
% 2.06/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_63,negated_conjecture,
% 2.06/1.00      ( v2_pre_topc(sK2) ),
% 2.06/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_64,negated_conjecture,
% 2.06/1.00      ( ~ v2_struct_0(sK2) ),
% 2.06/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(contradiction,plain,
% 2.06/1.00      ( $false ),
% 2.06/1.00      inference(minisat,
% 2.06/1.00                [status(thm)],
% 2.06/1.00                [c_4037,c_4038,c_4039,c_4040,c_4041,c_4042,c_4043,c_4044,
% 2.06/1.00                 c_3885,c_3456,c_3440,c_3338,c_2058,c_426,c_18,c_22,c_26,
% 2.06/1.00                 c_30,c_34,c_38,c_42,c_46,c_50,c_51,c_52,c_53,c_54,c_55,
% 2.06/1.00                 c_56,c_57,c_58,c_59,c_60,c_61,c_62,c_63,c_64]) ).
% 2.06/1.00  
% 2.06/1.00  
% 2.06/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.06/1.00  
% 2.06/1.00  ------                               Statistics
% 2.06/1.00  
% 2.06/1.00  ------ General
% 2.06/1.00  
% 2.06/1.00  abstr_ref_over_cycles:                  0
% 2.06/1.00  abstr_ref_under_cycles:                 0
% 2.06/1.00  gc_basic_clause_elim:                   0
% 2.06/1.00  forced_gc_time:                         0
% 2.06/1.00  parsing_time:                           0.013
% 2.06/1.00  unif_index_cands_time:                  0.
% 2.06/1.00  unif_index_add_time:                    0.
% 2.06/1.00  orderings_time:                         0.
% 2.06/1.00  out_proof_time:                         0.012
% 2.06/1.00  total_time:                             0.156
% 2.06/1.00  num_of_symbols:                         55
% 2.06/1.00  num_of_terms:                           2439
% 2.06/1.00  
% 2.06/1.00  ------ Preprocessing
% 2.06/1.00  
% 2.06/1.00  num_of_splits:                          0
% 2.06/1.00  num_of_split_atoms:                     0
% 2.06/1.00  num_of_reused_defs:                     0
% 2.06/1.00  num_eq_ax_congr_red:                    33
% 2.06/1.00  num_of_sem_filtered_clauses:            1
% 2.06/1.00  num_of_subtypes:                        5
% 2.06/1.00  monotx_restored_types:                  0
% 2.06/1.00  sat_num_of_epr_types:                   0
% 2.06/1.00  sat_num_of_non_cyclic_types:            0
% 2.06/1.00  sat_guarded_non_collapsed_types:        0
% 2.06/1.00  num_pure_diseq_elim:                    0
% 2.06/1.00  simp_replaced_by:                       0
% 2.06/1.00  res_preprocessed:                       202
% 2.06/1.00  prep_upred:                             0
% 2.06/1.00  prep_unflattend:                        123
% 2.06/1.00  smt_new_axioms:                         0
% 2.06/1.00  pred_elim_cands:                        11
% 2.06/1.00  pred_elim:                              1
% 2.06/1.00  pred_elim_cl:                           1
% 2.06/1.00  pred_elim_cycles:                       5
% 2.06/1.00  merged_defs:                            0
% 2.06/1.00  merged_defs_ncl:                        0
% 2.06/1.00  bin_hyper_res:                          0
% 2.06/1.00  prep_cycles:                            4
% 2.06/1.00  pred_elim_time:                         0.026
% 2.06/1.00  splitting_time:                         0.
% 2.06/1.00  sem_filter_time:                        0.
% 2.06/1.00  monotx_time:                            0.
% 2.06/1.00  subtype_inf_time:                       0.
% 2.06/1.00  
% 2.06/1.00  ------ Problem properties
% 2.06/1.00  
% 2.06/1.00  clauses:                                40
% 2.06/1.00  conjectures:                            25
% 2.06/1.00  epr:                                    15
% 2.06/1.00  horn:                                   31
% 2.06/1.00  ground:                                 25
% 2.06/1.00  unary:                                  16
% 2.06/1.00  binary:                                 16
% 2.06/1.00  lits:                                   101
% 2.06/1.00  lits_eq:                                2
% 2.06/1.00  fd_pure:                                0
% 2.06/1.00  fd_pseudo:                              0
% 2.06/1.00  fd_cond:                                0
% 2.06/1.00  fd_pseudo_cond:                         0
% 2.06/1.00  ac_symbols:                             0
% 2.06/1.00  
% 2.06/1.00  ------ Propositional Solver
% 2.06/1.00  
% 2.06/1.00  prop_solver_calls:                      26
% 2.06/1.00  prop_fast_solver_calls:                 1472
% 2.06/1.00  smt_solver_calls:                       0
% 2.06/1.00  smt_fast_solver_calls:                  0
% 2.06/1.00  prop_num_of_clauses:                    736
% 2.06/1.00  prop_preprocess_simplified:             5475
% 2.06/1.00  prop_fo_subsumed:                       27
% 2.06/1.00  prop_solver_time:                       0.
% 2.06/1.00  smt_solver_time:                        0.
% 2.06/1.00  smt_fast_solver_time:                   0.
% 2.06/1.00  prop_fast_solver_time:                  0.
% 2.06/1.00  prop_unsat_core_time:                   0.
% 2.06/1.00  
% 2.06/1.00  ------ QBF
% 2.06/1.00  
% 2.06/1.00  qbf_q_res:                              0
% 2.06/1.00  qbf_num_tautologies:                    0
% 2.06/1.00  qbf_prep_cycles:                        0
% 2.06/1.00  
% 2.06/1.00  ------ BMC1
% 2.06/1.00  
% 2.06/1.00  bmc1_current_bound:                     -1
% 2.06/1.00  bmc1_last_solved_bound:                 -1
% 2.06/1.00  bmc1_unsat_core_size:                   -1
% 2.06/1.00  bmc1_unsat_core_parents_size:           -1
% 2.06/1.00  bmc1_merge_next_fun:                    0
% 2.06/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.06/1.00  
% 2.06/1.00  ------ Instantiation
% 2.06/1.00  
% 2.06/1.00  inst_num_of_clauses:                    237
% 2.06/1.00  inst_num_in_passive:                    61
% 2.06/1.00  inst_num_in_active:                     164
% 2.06/1.00  inst_num_in_unprocessed:                11
% 2.06/1.00  inst_num_of_loops:                      188
% 2.06/1.00  inst_num_of_learning_restarts:          0
% 2.06/1.00  inst_num_moves_active_passive:          19
% 2.06/1.00  inst_lit_activity:                      0
% 2.06/1.00  inst_lit_activity_moves:                0
% 2.06/1.00  inst_num_tautologies:                   0
% 2.06/1.00  inst_num_prop_implied:                  0
% 2.06/1.00  inst_num_existing_simplified:           0
% 2.06/1.00  inst_num_eq_res_simplified:             0
% 2.06/1.00  inst_num_child_elim:                    0
% 2.06/1.00  inst_num_of_dismatching_blockings:      15
% 2.06/1.00  inst_num_of_non_proper_insts:           138
% 2.06/1.00  inst_num_of_duplicates:                 0
% 2.06/1.00  inst_inst_num_from_inst_to_res:         0
% 2.06/1.00  inst_dismatching_checking_time:         0.
% 2.06/1.00  
% 2.06/1.00  ------ Resolution
% 2.06/1.00  
% 2.06/1.00  res_num_of_clauses:                     0
% 2.06/1.00  res_num_in_passive:                     0
% 2.06/1.00  res_num_in_active:                      0
% 2.06/1.00  res_num_of_loops:                       206
% 2.06/1.00  res_forward_subset_subsumed:            14
% 2.06/1.00  res_backward_subset_subsumed:           0
% 2.06/1.00  res_forward_subsumed:                   0
% 2.06/1.00  res_backward_subsumed:                  0
% 2.06/1.00  res_forward_subsumption_resolution:     0
% 2.06/1.00  res_backward_subsumption_resolution:    0
% 2.06/1.00  res_clause_to_clause_subsumption:       119
% 2.06/1.00  res_orphan_elimination:                 0
% 2.06/1.00  res_tautology_del:                      42
% 2.06/1.00  res_num_eq_res_simplified:              0
% 2.06/1.00  res_num_sel_changes:                    0
% 2.06/1.00  res_moves_from_active_to_pass:          0
% 2.06/1.00  
% 2.06/1.00  ------ Superposition
% 2.06/1.00  
% 2.06/1.00  sup_time_total:                         0.
% 2.06/1.00  sup_time_generating:                    0.
% 2.06/1.00  sup_time_sim_full:                      0.
% 2.06/1.00  sup_time_sim_immed:                     0.
% 2.06/1.00  
% 2.06/1.00  sup_num_of_clauses:                     41
% 2.06/1.00  sup_num_in_active:                      36
% 2.06/1.00  sup_num_in_passive:                     5
% 2.06/1.00  sup_num_of_loops:                       36
% 2.06/1.00  sup_fw_superposition:                   0
% 2.06/1.00  sup_bw_superposition:                   1
% 2.06/1.00  sup_immediate_simplified:               0
% 2.06/1.00  sup_given_eliminated:                   0
% 2.06/1.00  comparisons_done:                       0
% 2.06/1.00  comparisons_avoided:                    0
% 2.06/1.00  
% 2.06/1.00  ------ Simplifications
% 2.06/1.00  
% 2.06/1.00  
% 2.06/1.00  sim_fw_subset_subsumed:                 0
% 2.06/1.00  sim_bw_subset_subsumed:                 0
% 2.06/1.00  sim_fw_subsumed:                        0
% 2.06/1.00  sim_bw_subsumed:                        0
% 2.06/1.00  sim_fw_subsumption_res:                 0
% 2.06/1.00  sim_bw_subsumption_res:                 0
% 2.06/1.00  sim_tautology_del:                      1
% 2.06/1.00  sim_eq_tautology_del:                   0
% 2.06/1.00  sim_eq_res_simp:                        0
% 2.06/1.00  sim_fw_demodulated:                     0
% 2.06/1.00  sim_bw_demodulated:                     0
% 2.06/1.00  sim_light_normalised:                   0
% 2.06/1.00  sim_joinable_taut:                      0
% 2.06/1.00  sim_joinable_simp:                      0
% 2.06/1.00  sim_ac_normalised:                      0
% 2.06/1.00  sim_smt_subsumption:                    0
% 2.06/1.00  
%------------------------------------------------------------------------------
