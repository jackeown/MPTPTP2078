%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1812+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:37 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :  191 (1249 expanded)
%              Number of leaves         :   23 ( 501 expanded)
%              Depth                    :   36
%              Number of atoms          : 1545 (41566 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (13836)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
fof(f385,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f196,f205,f220,f225,f257,f265,f269,f282,f286,f300,f313,f317,f340,f384])).

fof(f384,plain,
    ( ~ spl11_2
    | spl11_3
    | ~ spl11_4
    | ~ spl11_5 ),
    inference(avatar_contradiction_clause,[],[f383])).

fof(f383,plain,
    ( $false
    | ~ spl11_2
    | spl11_3
    | ~ spl11_4
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f382,f66])).

fof(f66,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
      | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3)
      | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6))
      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
      | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
      | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
      | ~ v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
      | ~ v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
      | ~ v1_funct_1(sK6) )
    & ( ( m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3)
        & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
        & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6))
        & m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
        & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
        & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
        & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6)) )
      | ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
        & v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
        & v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
        & v1_funct_1(sK6) ) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    & v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    & v1_funct_1(sK6)
    & m1_pre_topc(sK5,sK2)
    & v1_tsep_1(sK5,sK2)
    & ~ v2_struct_0(sK5)
    & m1_pre_topc(sK4,sK2)
    & v1_tsep_1(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f47,f52,f51,f50,f49,f48])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          | ~ v1_funct_1(X4) )
                        & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                            & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
                          | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(X4) ) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & m1_pre_topc(X3,X0)
                    & v1_tsep_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & v1_tsep_1(X2,X0)
                & ~ v2_struct_0(X2) )
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
                      ( ( ~ m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),X3,X1)
                        | ~ v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4))
                        | ~ m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),X2,X1)
                        | ~ v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4))
                        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))))
                        | ~ v5_pre_topc(X4,k1_tsep_1(sK2,X2,X3),X1)
                        | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))
                        | ~ v1_funct_1(X4) )
                      & ( ( m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4)) )
                        | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(sK2,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK2)
                  & v1_tsep_1(X3,sK2)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK2)
              & v1_tsep_1(X2,sK2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ( ~ m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),X3,X1)
                      | ~ v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4))
                      | ~ m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),X2,X1)
                      | ~ v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X4,k1_tsep_1(sK2,X2,X3),X1)
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                    & ( ( m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),X3,X1)
                        & v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4))
                        & m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),X2,X1)
                        & v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4)) )
                      | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))))
                        & v5_pre_topc(X4,k1_tsep_1(sK2,X2,X3),X1)
                        & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))
                        & v1_funct_1(X4) ) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))))
                    & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK2)
                & v1_tsep_1(X3,sK2)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK2)
            & v1_tsep_1(X2,sK2)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4),X3,sK3)
                    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(sK3))
                    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4))
                    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
                    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4),X2,sK3)
                    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(sK3))
                    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4))
                    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3))))
                    | ~ v5_pre_topc(X4,k1_tsep_1(sK2,X2,X3),sK3)
                    | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3))
                    | ~ v1_funct_1(X4) )
                  & ( ( m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                      & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4),X3,sK3)
                      & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(sK3))
                      & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4))
                      & m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
                      & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4),X2,sK3)
                      & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(sK3))
                      & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4)) )
                    | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3))))
                      & v5_pre_topc(X4,k1_tsep_1(sK2,X2,X3),sK3)
                      & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3))
                      & v1_funct_1(X4) ) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3))))
                  & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK2)
              & v1_tsep_1(X3,sK2)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK2)
          & v1_tsep_1(X2,sK2)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                  | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4),X3,sK3)
                  | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(sK3))
                  | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4))
                  | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
                  | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4),X2,sK3)
                  | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(sK3))
                  | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4))
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3))))
                  | ~ v5_pre_topc(X4,k1_tsep_1(sK2,X2,X3),sK3)
                  | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3))
                  | ~ v1_funct_1(X4) )
                & ( ( m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                    & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4),X3,sK3)
                    & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(sK3))
                    & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4))
                    & m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
                    & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4),X2,sK3)
                    & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(sK3))
                    & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4)) )
                  | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3))))
                    & v5_pre_topc(X4,k1_tsep_1(sK2,X2,X3),sK3)
                    & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3))
                    & v1_funct_1(X4) ) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3))))
                & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK2)
            & v1_tsep_1(X3,sK2)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK2)
        & v1_tsep_1(X2,sK2)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4),X3,sK3)
                | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4),u1_struct_0(X3),u1_struct_0(sK3))
                | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4))
                | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
                | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4),sK4,sK3)
                | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4),u1_struct_0(sK4),u1_struct_0(sK3))
                | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4))
                | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3))))
                | ~ v5_pre_topc(X4,k1_tsep_1(sK2,sK4,X3),sK3)
                | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3))
                | ~ v1_funct_1(X4) )
              & ( ( m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                  & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4),X3,sK3)
                  & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4),u1_struct_0(X3),u1_struct_0(sK3))
                  & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4))
                  & m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
                  & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4),sK4,sK3)
                  & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4),u1_struct_0(sK4),u1_struct_0(sK3))
                  & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4)) )
                | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3))))
                  & v5_pre_topc(X4,k1_tsep_1(sK2,sK4,X3),sK3)
                  & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3))
                  & v1_funct_1(X4) ) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3))))
              & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK2)
          & v1_tsep_1(X3,sK2)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK4,sK2)
      & v1_tsep_1(sK4,sK2)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
              | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4),X3,sK3)
              | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4),u1_struct_0(X3),u1_struct_0(sK3))
              | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4))
              | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
              | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4),sK4,sK3)
              | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4),u1_struct_0(sK4),u1_struct_0(sK3))
              | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4))
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3))))
              | ~ v5_pre_topc(X4,k1_tsep_1(sK2,sK4,X3),sK3)
              | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3))
              | ~ v1_funct_1(X4) )
            & ( ( m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4),X3,sK3)
                & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4),u1_struct_0(X3),u1_struct_0(sK3))
                & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4))
                & m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
                & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4),sK4,sK3)
                & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4),u1_struct_0(sK4),u1_struct_0(sK3))
                & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4)) )
              | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3))))
                & v5_pre_topc(X4,k1_tsep_1(sK2,sK4,X3),sK3)
                & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3))
                & v1_funct_1(X4) ) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3))))
            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK2)
        & v1_tsep_1(X3,sK2)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
            | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4),sK5,sK3)
            | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4),u1_struct_0(sK5),u1_struct_0(sK3))
            | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4))
            | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
            | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4),sK4,sK3)
            | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4),u1_struct_0(sK4),u1_struct_0(sK3))
            | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4))
            | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
            | ~ v5_pre_topc(X4,k1_tsep_1(sK2,sK4,sK5),sK3)
            | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
            | ~ v1_funct_1(X4) )
          & ( ( m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
              & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4),sK5,sK3)
              & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4),u1_struct_0(sK5),u1_struct_0(sK3))
              & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4))
              & m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
              & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4),sK4,sK3)
              & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4),u1_struct_0(sK4),u1_struct_0(sK3))
              & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4)) )
            | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
              & v5_pre_topc(X4,k1_tsep_1(sK2,sK4,sK5),sK3)
              & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
              & v1_funct_1(X4) ) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK5,sK2)
      & v1_tsep_1(sK5,sK2)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X4] :
        ( ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
          | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4),sK5,sK3)
          | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4),u1_struct_0(sK5),u1_struct_0(sK3))
          | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4))
          | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
          | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4),sK4,sK3)
          | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4),u1_struct_0(sK4),u1_struct_0(sK3))
          | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
          | ~ v5_pre_topc(X4,k1_tsep_1(sK2,sK4,sK5),sK3)
          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
          | ~ v1_funct_1(X4) )
        & ( ( m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
            & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4),sK5,sK3)
            & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4),u1_struct_0(sK5),u1_struct_0(sK3))
            & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4))
            & m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
            & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4),sK4,sK3)
            & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4),u1_struct_0(sK4),u1_struct_0(sK3))
            & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4)) )
          | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
            & v5_pre_topc(X4,k1_tsep_1(sK2,sK4,sK5),sK3)
            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
            & v1_funct_1(X4) ) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
        & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
        & v1_funct_1(X4) )
   => ( ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3)
        | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6))
        | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
        | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
        | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
        | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
        | ~ v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
        | ~ v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
        | ~ v1_funct_1(sK6) )
      & ( ( m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
          & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3)
          & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
          & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6))
          & m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
          & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
          & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
          & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6)) )
        | ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
          & v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
          & v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
          & v1_funct_1(sK6) ) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
      & v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))
                        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                        | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        | ~ v1_funct_1(X4) )
                      & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
                        | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_tsep_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))
                        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                        | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        | ~ v1_funct_1(X4) )
                      & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
                        | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_tsep_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <~> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_tsep_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <~> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_tsep_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_tsep_1(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(X4) )
                        <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                            & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_tsep_1(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_tsep_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_tmap_1)).

fof(f382,plain,
    ( v2_struct_0(sK2)
    | ~ spl11_2
    | spl11_3
    | ~ spl11_4
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f381,f68])).

fof(f68,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f381,plain,
    ( ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_2
    | spl11_3
    | ~ spl11_4
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f380,f72])).

fof(f72,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f380,plain,
    ( v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_2
    | spl11_3
    | ~ spl11_4
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f379,f74])).

fof(f74,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f379,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_2
    | spl11_3
    | ~ spl11_4
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f378,f75])).

fof(f75,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f53])).

fof(f378,plain,
    ( v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_2
    | spl11_3
    | ~ spl11_4
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f377,f77])).

fof(f77,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f377,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_2
    | spl11_3
    | ~ spl11_4
    | ~ spl11_5 ),
    inference(resolution,[],[f376,f145])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(f376,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ spl11_2
    | spl11_3
    | ~ spl11_4
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f375,f66])).

fof(f375,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | v2_struct_0(sK2)
    | ~ spl11_2
    | spl11_3
    | ~ spl11_4
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f374,f67])).

fof(f67,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f374,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_2
    | spl11_3
    | ~ spl11_4
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f373,f68])).

fof(f373,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_2
    | spl11_3
    | ~ spl11_4
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f372,f69])).

fof(f69,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f53])).

% (13845)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
fof(f372,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_2
    | spl11_3
    | ~ spl11_4
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f371,f70])).

fof(f70,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f371,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_2
    | spl11_3
    | ~ spl11_4
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f370,f71])).

fof(f71,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f370,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_2
    | spl11_3
    | ~ spl11_4
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f369,f77])).

fof(f369,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_2
    | spl11_3
    | ~ spl11_4
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f368,f78])).

fof(f78,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f53])).

fof(f368,plain,
    ( ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_2
    | spl11_3
    | ~ spl11_4
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f367,f79])).

fof(f79,plain,(
    v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f53])).

fof(f367,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_2
    | spl11_3
    | ~ spl11_4
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f366,f80])).

fof(f80,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f53])).

fof(f366,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_2
    | spl11_3
    | ~ spl11_4
    | ~ spl11_5 ),
    inference(resolution,[],[f359,f149])).

fof(f149,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & m1_pre_topc(X2,X0)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).

fof(f359,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ spl11_2
    | spl11_3
    | ~ spl11_4
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f358,f219])).

fof(f219,plain,
    ( v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl11_4
  <=> v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f358,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
    | ~ spl11_2
    | spl11_3
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f357,f348])).

% (13858)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% (13837)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% (13850)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% (13846)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% (13856)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% (13854)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% (13855)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% (13842)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% (13852)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
fof(f348,plain,
    ( v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
    | spl11_3 ),
    inference(subsumption_resolution,[],[f87,f214])).

fof(f214,plain,
    ( ~ v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
    | spl11_3 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl11_3
  <=> v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f87,plain,
    ( v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
    | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f357,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
    | ~ spl11_2
    | spl11_3
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f356,f346])).

fof(f346,plain,
    ( v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
    | spl11_3 ),
    inference(subsumption_resolution,[],[f91,f214])).

fof(f91,plain,
    ( v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
    | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f356,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
    | ~ spl11_2
    | spl11_3
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f355,f345])).

fof(f345,plain,
    ( ~ sP0(sK3,sK5,sK6,sK4,sK2)
    | ~ spl11_2
    | spl11_3 ),
    inference(subsumption_resolution,[],[f344,f195])).

fof(f195,plain,
    ( sP1(sK2,sK4,sK6,sK5,sK3)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl11_2
  <=> sP1(sK2,sK4,sK6,sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f344,plain,
    ( ~ sP0(sK3,sK5,sK6,sK4,sK2)
    | ~ sP1(sK2,sK4,sK6,sK5,sK3)
    | spl11_3 ),
    inference(resolution,[],[f214,f121])).

fof(f121,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
            & v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
            & v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
            & v1_funct_1(X2) )
          | ~ sP0(X4,X3,X2,X1,X0) )
        & ( sP0(X4,X3,X2,X1,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
          | ~ v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
          | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
          | ~ v1_funct_1(X2) ) )
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
    ! [X0,X2,X4,X3,X1] :
      ( ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
            & v1_funct_1(X4) )
          | ~ sP0(X1,X3,X4,X2,X0) )
        & ( sP0(X1,X3,X4,X2,X0)
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          | ~ v1_funct_1(X4) ) )
      | ~ sP1(X0,X2,X4,X3,X1) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X2,X4,X3,X1] :
      ( ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
            & v1_funct_1(X4) )
          | ~ sP0(X1,X3,X4,X2,X0) )
        & ( sP0(X1,X3,X4,X2,X0)
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          | ~ v1_funct_1(X4) ) )
      | ~ sP1(X0,X2,X4,X3,X1) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X2,X4,X3,X1] :
      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          & v1_funct_1(X4) )
      <=> sP0(X1,X3,X4,X2,X0) )
      | ~ sP1(X0,X2,X4,X3,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f355,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | sP0(sK3,sK5,sK6,sK4,sK2)
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
    | spl11_3
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f354,f224])).

fof(f224,plain,
    ( v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6))
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f222])).

fof(f222,plain,
    ( spl11_5
  <=> v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f354,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6))
    | sP0(sK3,sK5,sK6,sK4,sK2)
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
    | spl11_3 ),
    inference(subsumption_resolution,[],[f353,f349])).

fof(f349,plain,
    ( v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
    | spl11_3 ),
    inference(subsumption_resolution,[],[f103,f214])).

fof(f103,plain,
    ( v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
    | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f353,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6))
    | sP0(sK3,sK5,sK6,sK4,sK2)
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
    | spl11_3 ),
    inference(subsumption_resolution,[],[f351,f347])).

fof(f347,plain,
    ( v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3)
    | spl11_3 ),
    inference(subsumption_resolution,[],[f107,f214])).

fof(f107,plain,
    ( v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3)
    | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f351,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6))
    | sP0(sK3,sK5,sK6,sK4,sK2)
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
    | spl11_3 ),
    inference(resolution,[],[f350,f131])).

fof(f131,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
      | sP0(X0,X1,X2,X3,X4)
      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
        | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
        | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
        | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
        | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
        | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
        | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) )
      & ( ( m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
          & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
          & m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
          & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
          & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
          & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( sP0(X1,X3,X4,X2,X0)
        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
      & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
        | ~ sP0(X1,X3,X4,X2,X0) ) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( sP0(X1,X3,X4,X2,X0)
        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
      & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
        | ~ sP0(X1,X3,X4,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( sP0(X1,X3,X4,X2,X0)
    <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
        & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
        & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
        & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f350,plain,
    ( m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | spl11_3 ),
    inference(subsumption_resolution,[],[f95,f214])).

fof(f95,plain,
    ( m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f340,plain,
    ( ~ spl11_2
    | ~ spl11_3
    | spl11_4 ),
    inference(avatar_contradiction_clause,[],[f339])).

fof(f339,plain,
    ( $false
    | ~ spl11_2
    | ~ spl11_3
    | spl11_4 ),
    inference(subsumption_resolution,[],[f334,f227])).

fof(f227,plain,
    ( sP0(sK3,sK5,sK6,sK4,sK2)
    | ~ spl11_2
    | ~ spl11_3 ),
    inference(subsumption_resolution,[],[f226,f195])).

fof(f226,plain,
    ( sP0(sK3,sK5,sK6,sK4,sK2)
    | ~ sP1(sK2,sK4,sK6,sK5,sK3)
    | ~ spl11_3 ),
    inference(subsumption_resolution,[],[f182,f215])).

fof(f215,plain,
    ( v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f213])).

fof(f182,plain,
    ( sP0(sK3,sK5,sK6,sK4,sK2)
    | ~ v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ sP1(sK2,sK4,sK6,sK5,sK3) ),
    inference(subsumption_resolution,[],[f181,f78])).

fof(f181,plain,
    ( sP0(sK3,sK5,sK6,sK4,sK2)
    | ~ v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ v1_funct_1(sK6)
    | ~ sP1(sK2,sK4,sK6,sK5,sK3) ),
    inference(subsumption_resolution,[],[f167,f79])).

fof(f167,plain,
    ( sP0(sK3,sK5,sK6,sK4,sK2)
    | ~ v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ sP1(sK2,sK4,sK6,sK5,sK3) ),
    inference(resolution,[],[f80,f118])).

fof(f118,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
      | sP0(X4,X3,X2,X1,X0)
      | ~ v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
      | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
      | ~ v1_funct_1(X2)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f334,plain,
    ( ~ sP0(sK3,sK5,sK6,sK4,sK2)
    | spl11_4 ),
    inference(resolution,[],[f218,f123])).

fof(f123,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f218,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
    | spl11_4 ),
    inference(avatar_component_clause,[],[f217])).

fof(f317,plain,
    ( ~ spl11_2
    | ~ spl11_3
    | spl11_11 ),
    inference(avatar_contradiction_clause,[],[f316])).

fof(f316,plain,
    ( $false
    | ~ spl11_2
    | ~ spl11_3
    | spl11_11 ),
    inference(subsumption_resolution,[],[f314,f227])).

fof(f314,plain,
    ( ~ sP0(sK3,sK5,sK6,sK4,sK2)
    | spl11_11 ),
    inference(resolution,[],[f256,f130])).

fof(f130,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f256,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | spl11_11 ),
    inference(avatar_component_clause,[],[f254])).

fof(f254,plain,
    ( spl11_11
  <=> m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f313,plain,
    ( ~ spl11_2
    | ~ spl11_3
    | spl11_10 ),
    inference(avatar_contradiction_clause,[],[f312])).

fof(f312,plain,
    ( $false
    | ~ spl11_2
    | ~ spl11_3
    | spl11_10 ),
    inference(subsumption_resolution,[],[f311,f227])).

fof(f311,plain,
    ( ~ sP0(sK3,sK5,sK6,sK4,sK2)
    | spl11_10 ),
    inference(resolution,[],[f252,f129])).

fof(f129,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f252,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3)
    | spl11_10 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl11_10
  <=> v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f300,plain,
    ( ~ spl11_2
    | ~ spl11_3
    | spl11_9 ),
    inference(avatar_contradiction_clause,[],[f299])).

fof(f299,plain,
    ( $false
    | ~ spl11_2
    | ~ spl11_3
    | spl11_9 ),
    inference(subsumption_resolution,[],[f297,f227])).

fof(f297,plain,
    ( ~ sP0(sK3,sK5,sK6,sK4,sK2)
    | spl11_9 ),
    inference(resolution,[],[f248,f128])).

fof(f128,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f248,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
    | spl11_9 ),
    inference(avatar_component_clause,[],[f246])).

fof(f246,plain,
    ( spl11_9
  <=> v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f286,plain,
    ( ~ spl11_2
    | ~ spl11_3
    | spl11_8 ),
    inference(avatar_contradiction_clause,[],[f285])).

fof(f285,plain,
    ( $false
    | ~ spl11_2
    | ~ spl11_3
    | spl11_8 ),
    inference(subsumption_resolution,[],[f283,f227])).

fof(f283,plain,
    ( ~ sP0(sK3,sK5,sK6,sK4,sK2)
    | spl11_8 ),
    inference(resolution,[],[f244,f126])).

fof(f126,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f244,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | spl11_8 ),
    inference(avatar_component_clause,[],[f242])).

fof(f242,plain,
    ( spl11_8
  <=> m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f282,plain,
    ( ~ spl11_2
    | ~ spl11_3
    | spl11_7 ),
    inference(avatar_contradiction_clause,[],[f281])).

fof(f281,plain,
    ( $false
    | ~ spl11_2
    | ~ spl11_3
    | spl11_7 ),
    inference(subsumption_resolution,[],[f280,f227])).

fof(f280,plain,
    ( ~ sP0(sK3,sK5,sK6,sK4,sK2)
    | spl11_7 ),
    inference(resolution,[],[f240,f125])).

fof(f125,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f240,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
    | spl11_7 ),
    inference(avatar_component_clause,[],[f238])).

fof(f238,plain,
    ( spl11_7
  <=> v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f269,plain,
    ( ~ spl11_2
    | ~ spl11_3
    | spl11_6 ),
    inference(avatar_contradiction_clause,[],[f268])).

fof(f268,plain,
    ( $false
    | ~ spl11_2
    | ~ spl11_3
    | spl11_6 ),
    inference(subsumption_resolution,[],[f266,f227])).

fof(f266,plain,
    ( ~ sP0(sK3,sK5,sK6,sK4,sK2)
    | spl11_6 ),
    inference(resolution,[],[f236,f124])).

fof(f124,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f236,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
    | spl11_6 ),
    inference(avatar_component_clause,[],[f234])).

fof(f234,plain,
    ( spl11_6
  <=> v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f265,plain,
    ( ~ spl11_2
    | ~ spl11_3
    | spl11_5 ),
    inference(avatar_contradiction_clause,[],[f264])).

fof(f264,plain,
    ( $false
    | ~ spl11_2
    | ~ spl11_3
    | spl11_5 ),
    inference(subsumption_resolution,[],[f259,f227])).

fof(f259,plain,
    ( ~ sP0(sK3,sK5,sK6,sK4,sK2)
    | spl11_5 ),
    inference(resolution,[],[f223,f127])).

fof(f127,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f223,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6))
    | spl11_5 ),
    inference(avatar_component_clause,[],[f222])).

fof(f257,plain,
    ( ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_5
    | ~ spl11_9
    | ~ spl11_10
    | ~ spl11_11
    | ~ spl11_3
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f232,f217,f213,f254,f250,f246,f222,f242,f238,f234])).

fof(f232,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f231,f78])).

fof(f231,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f230,f79])).

fof(f230,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f229,f215])).

fof(f229,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f228,f80])).

fof(f228,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f113,f219])).

fof(f113,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f53])).

fof(f225,plain,
    ( spl11_3
    | spl11_5 ),
    inference(avatar_split_clause,[],[f99,f222,f213])).

fof(f99,plain,
    ( v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6))
    | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f220,plain,
    ( spl11_3
    | spl11_4 ),
    inference(avatar_split_clause,[],[f83,f217,f213])).

fof(f83,plain,
    ( v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
    | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f205,plain,(
    spl11_1 ),
    inference(avatar_contradiction_clause,[],[f204])).

fof(f204,plain,
    ( $false
    | spl11_1 ),
    inference(subsumption_resolution,[],[f203,f66])).

fof(f203,plain,
    ( v2_struct_0(sK2)
    | spl11_1 ),
    inference(subsumption_resolution,[],[f202,f67])).

fof(f202,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl11_1 ),
    inference(subsumption_resolution,[],[f201,f68])).

fof(f201,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl11_1 ),
    inference(subsumption_resolution,[],[f200,f73])).

fof(f73,plain,(
    v1_tsep_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f200,plain,
    ( ~ v1_tsep_1(sK4,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl11_1 ),
    inference(subsumption_resolution,[],[f199,f74])).

fof(f199,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | ~ v1_tsep_1(sK4,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl11_1 ),
    inference(subsumption_resolution,[],[f198,f76])).

fof(f76,plain,(
    v1_tsep_1(sK5,sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f198,plain,
    ( ~ v1_tsep_1(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ v1_tsep_1(sK4,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl11_1 ),
    inference(subsumption_resolution,[],[f197,f77])).

fof(f197,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | ~ v1_tsep_1(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ v1_tsep_1(sK4,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl11_1 ),
    inference(resolution,[],[f191,f133])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( r4_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_tsep_1(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tsep_1)).

fof(f191,plain,
    ( ~ r4_tsep_1(sK2,sK4,sK5)
    | spl11_1 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl11_1
  <=> r4_tsep_1(sK2,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f196,plain,
    ( ~ spl11_1
    | spl11_2 ),
    inference(avatar_split_clause,[],[f180,f193,f189])).

fof(f180,plain,
    ( sP1(sK2,sK4,sK6,sK5,sK3)
    | ~ r4_tsep_1(sK2,sK4,sK5) ),
    inference(subsumption_resolution,[],[f179,f66])).

fof(f179,plain,
    ( sP1(sK2,sK4,sK6,sK5,sK3)
    | ~ r4_tsep_1(sK2,sK4,sK5)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f178,f67])).

fof(f178,plain,
    ( sP1(sK2,sK4,sK6,sK5,sK3)
    | ~ r4_tsep_1(sK2,sK4,sK5)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f177,f68])).

fof(f177,plain,
    ( sP1(sK2,sK4,sK6,sK5,sK3)
    | ~ r4_tsep_1(sK2,sK4,sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f176,f69])).

fof(f176,plain,
    ( sP1(sK2,sK4,sK6,sK5,sK3)
    | ~ r4_tsep_1(sK2,sK4,sK5)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f175,f70])).

fof(f175,plain,
    ( sP1(sK2,sK4,sK6,sK5,sK3)
    | ~ r4_tsep_1(sK2,sK4,sK5)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f174,f71])).

fof(f174,plain,
    ( sP1(sK2,sK4,sK6,sK5,sK3)
    | ~ r4_tsep_1(sK2,sK4,sK5)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f173,f72])).

fof(f173,plain,
    ( sP1(sK2,sK4,sK6,sK5,sK3)
    | ~ r4_tsep_1(sK2,sK4,sK5)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f172,f74])).

fof(f172,plain,
    ( sP1(sK2,sK4,sK6,sK5,sK3)
    | ~ r4_tsep_1(sK2,sK4,sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f171,f75])).

fof(f171,plain,
    ( sP1(sK2,sK4,sK6,sK5,sK3)
    | ~ r4_tsep_1(sK2,sK4,sK5)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f170,f77])).

fof(f170,plain,
    ( sP1(sK2,sK4,sK6,sK5,sK3)
    | ~ r4_tsep_1(sK2,sK4,sK5)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f169,f78])).

fof(f169,plain,
    ( sP1(sK2,sK4,sK6,sK5,sK3)
    | ~ v1_funct_1(sK6)
    | ~ r4_tsep_1(sK2,sK4,sK5)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f166,f79])).

fof(f166,plain,
    ( sP1(sK2,sK4,sK6,sK5,sK3)
    | ~ v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ r4_tsep_1(sK2,sK4,sK5)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f80,f132])).

fof(f132,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | sP1(X0,X2,X4,X3,X1)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ r4_tsep_1(X0,X2,X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( sP1(X0,X2,X4,X3,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r4_tsep_1(X0,X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f27,f44,f43])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r4_tsep_1(X0,X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r4_tsep_1(X0,X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( r4_tsep_1(X0,X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(X4) )
                        <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                            & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_tmap_1)).

%------------------------------------------------------------------------------
