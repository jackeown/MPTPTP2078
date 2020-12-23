%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  203 (1468 expanded)
%              Number of leaves         :   30 ( 740 expanded)
%              Depth                    :   22
%              Number of atoms          : 1154 (28126 expanded)
%              Number of equality atoms :  115 (1803 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f499,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f128,f156,f197,f203,f215,f225,f229,f391,f449,f465,f481,f486,f498])).

fof(f498,plain,
    ( spl7_30
    | ~ spl7_37 ),
    inference(avatar_contradiction_clause,[],[f497])).

fof(f497,plain,
    ( $false
    | spl7_30
    | ~ spl7_37 ),
    inference(subsumption_resolution,[],[f490,f480])).

fof(f480,plain,
    ( sK5 = k3_tmap_1(sK3,sK1,sK3,sK2,sK4)
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f478])).

fof(f478,plain,
    ( spl7_37
  <=> sK5 = k3_tmap_1(sK3,sK1,sK3,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f490,plain,
    ( sK5 != k3_tmap_1(sK3,sK1,sK3,sK2,sK4)
    | spl7_30 ),
    inference(superposition,[],[f311,f461])).

fof(f461,plain,(
    k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK3,sK1,sK3,sK2,sK4) ),
    inference(subsumption_resolution,[],[f460,f50])).

fof(f50,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    & ! [X6] :
        ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6) = k1_funct_1(sK5,X6)
        | ~ r2_hidden(X6,u1_struct_0(sK2))
        | ~ m1_subset_1(X6,u1_struct_0(sK3)) )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    & v1_funct_1(sK5)
    & m1_pre_topc(sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f14,f35,f34,f33,f32,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                            & ! [X6] :
                                ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                                | ~ r2_hidden(X6,u1_struct_0(X2))
                                | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                        & m1_pre_topc(X2,X3)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
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
                      ( ? [X5] :
                          ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X4),X5)
                          & ! [X6] :
                              ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                              | ~ r2_hidden(X6,u1_struct_0(X2))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X4),X5)
                        & ! [X6] :
                            ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                            | ~ r2_hidden(X6,u1_struct_0(X2))
                            | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X5) )
                    & m1_pre_topc(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X2,X4),X5)
                      & ! [X6] :
                          ( k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(sK1),X4,X6)
                          | ~ r2_hidden(X6,u1_struct_0(X2))
                          | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                      & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK1))
                      & v1_funct_1(X5) )
                  & m1_pre_topc(X2,X3)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X2,X4),X5)
                    & ! [X6] :
                        ( k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(sK1),X4,X6)
                        | ~ r2_hidden(X6,u1_struct_0(X2))
                        | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                    & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK1))
                    & v1_funct_1(X5) )
                & m1_pre_topc(X2,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,sK2,X4),X5)
                  & ! [X6] :
                      ( k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(sK1),X4,X6)
                      | ~ r2_hidden(X6,u1_struct_0(sK2))
                      | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
                  & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1))
                  & v1_funct_1(X5) )
              & m1_pre_topc(sK2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,sK2,X4),X5)
                & ! [X6] :
                    ( k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(sK1),X4,X6)
                    | ~ r2_hidden(X6,u1_struct_0(sK2))
                    | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
                & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1))
                & v1_funct_1(X5) )
            & m1_pre_topc(sK2,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
            & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X4),X5)
              & ! [X6] :
                  ( k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),X4,X6)
                  | ~ r2_hidden(X6,u1_struct_0(sK2))
                  | ~ m1_subset_1(X6,u1_struct_0(sK3)) )
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
              & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1))
              & v1_funct_1(X5) )
          & m1_pre_topc(sK2,sK3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
          & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X4),X5)
            & ! [X6] :
                ( k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),X4,X6)
                | ~ r2_hidden(X6,u1_struct_0(sK2))
                | ~ m1_subset_1(X6,u1_struct_0(sK3)) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
            & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1))
            & v1_funct_1(X5) )
        & m1_pre_topc(sK2,sK3)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X5)
          & ! [X6] :
              ( k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6)
              | ~ r2_hidden(X6,u1_struct_0(sK2))
              | ~ m1_subset_1(X6,u1_struct_0(sK3)) )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
          & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1))
          & v1_funct_1(X5) )
      & m1_pre_topc(sK2,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X5] :
        ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X5)
        & ! [X6] :
            ( k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6)
            | ~ r2_hidden(X6,u1_struct_0(sK2))
            | ~ m1_subset_1(X6,u1_struct_0(sK3)) )
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1))
        & v1_funct_1(X5) )
   => ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
      & ! [X6] :
          ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6) = k1_funct_1(sK5,X6)
          | ~ r2_hidden(X6,u1_struct_0(sK2))
          | ~ m1_subset_1(X6,u1_struct_0(sK3)) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          & ! [X6] :
                              ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                              | ~ r2_hidden(X6,u1_struct_0(X2))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          & ! [X6] :
                              ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                              | ~ r2_hidden(X6,u1_struct_0(X2))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( m1_pre_topc(X2,X3)
                         => ! [X5] :
                              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                                & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                                & v1_funct_1(X5) )
                             => ( ! [X6] :
                                    ( m1_subset_1(X6,u1_struct_0(X3))
                                   => ( r2_hidden(X6,u1_struct_0(X2))
                                     => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) ) )
                               => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ( ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X3))
                                 => ( r2_hidden(X6,u1_struct_0(X2))
                                   => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) ) )
                             => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_tmap_1)).

fof(f460,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK3,sK1,sK3,sK2,sK4)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f459,f95])).

fof(f95,plain,(
    v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f94,f43])).

fof(f43,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f94,plain,
    ( v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f90,f44])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f90,plain,
    ( v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f69,f51])).

fof(f51,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f459,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK3,sK1,sK3,sK2,sK4)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f458,f86])).

fof(f86,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f83,f44])).

fof(f83,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f66,f51])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f458,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK3,sK1,sK3,sK2,sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f452,f55])).

fof(f55,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f452,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK3,sK1,sK3,sK2,sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f435,f164])).

fof(f164,plain,(
    m1_pre_topc(sK3,sK3) ),
    inference(resolution,[],[f86,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f435,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK3,X0)
      | ~ m1_pre_topc(sK2,X0)
      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK3,sK2,sK4)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f434,f45])).

fof(f45,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f434,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK3,sK2,sK4)
      | ~ m1_pre_topc(sK2,X0)
      | ~ m1_pre_topc(sK3,X0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f433,f46])).

fof(f46,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f433,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK3,sK2,sK4)
      | ~ m1_pre_topc(sK2,X0)
      | ~ m1_pre_topc(sK3,X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f432,f47])).

fof(f47,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f432,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK3,sK2,sK4)
      | ~ m1_pre_topc(sK2,X0)
      | ~ m1_pre_topc(sK3,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f431,f52])).

fof(f52,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f431,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK3,sK2,sK4)
      | ~ v1_funct_1(sK4)
      | ~ m1_pre_topc(sK2,X0)
      | ~ m1_pre_topc(sK3,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f430,f53])).

fof(f53,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f36])).

% (18680)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
fof(f430,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK3,sK2,sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(sK4)
      | ~ m1_pre_topc(sK2,X0)
      | ~ m1_pre_topc(sK3,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f161,f54])).

fof(f54,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f36])).

% (18677)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
fof(f161,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X7))))
      | k3_tmap_1(X6,X7,sK3,sK2,X8) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X7),X8,u1_struct_0(sK2))
      | ~ v1_funct_2(X8,u1_struct_0(sK3),u1_struct_0(X7))
      | ~ v1_funct_1(X8)
      | ~ m1_pre_topc(sK2,X6)
      | ~ m1_pre_topc(sK3,X6)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(resolution,[],[f68,f55])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_pre_topc(X3,X2)
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
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
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f311,plain,
    ( sK5 != k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | spl7_30 ),
    inference(avatar_component_clause,[],[f310])).

fof(f310,plain,
    ( spl7_30
  <=> sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f486,plain,
    ( ~ spl7_6
    | spl7_8
    | ~ spl7_16
    | spl7_30
    | ~ spl7_32
    | ~ spl7_36 ),
    inference(avatar_contradiction_clause,[],[f485])).

fof(f485,plain,
    ( $false
    | ~ spl7_6
    | spl7_8
    | ~ spl7_16
    | spl7_30
    | ~ spl7_32
    | ~ spl7_36 ),
    inference(subsumption_resolution,[],[f484,f320])).

fof(f320,plain,
    ( m1_subset_1(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK3))
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f318])).

fof(f318,plain,
    ( spl7_32
  <=> m1_subset_1(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f484,plain,
    ( ~ m1_subset_1(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK3))
    | ~ spl7_6
    | spl7_8
    | ~ spl7_16
    | spl7_30
    | ~ spl7_36 ),
    inference(subsumption_resolution,[],[f483,f467])).

fof(f467,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) != k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | ~ spl7_6
    | spl7_8
    | ~ spl7_16
    | spl7_30 ),
    inference(global_subsumption,[],[f311,f399])).

fof(f399,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) != k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ spl7_6
    | spl7_8
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f398,f393])).

fof(f393,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl7_6 ),
    inference(resolution,[],[f127,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f127,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl7_6
  <=> r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f398,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) != k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | spl7_8
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f397,f53])).

fof(f397,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) != k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | spl7_8
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f396,f52])).

% (18697)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
fof(f396,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) != k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | spl7_8
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f342,f141])).

fof(f141,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3))
    | spl7_8 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl7_8
  <=> v1_xboole_0(u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f342,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) != k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ spl7_16 ),
    inference(resolution,[],[f202,f54])).

fof(f202,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK1))))
        | v1_xboole_0(X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X2,u1_struct_0(sK1))
        | k3_funct_2(X2,u1_struct_0(sK1),X3,sK6(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2),sK5)) != k1_funct_1(sK5,sK6(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2),sK5))
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2))
        | sK5 = k2_partfun1(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2)) )
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl7_16
  <=> ! [X3,X2] :
        ( k3_funct_2(X2,u1_struct_0(sK1),X3,sK6(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2),sK5)) != k1_funct_1(sK5,sK6(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2),sK5))
        | v1_xboole_0(X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X2,u1_struct_0(sK1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK1))))
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2))
        | sK5 = k2_partfun1(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f483,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | ~ m1_subset_1(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK3))
    | ~ spl7_36 ),
    inference(resolution,[],[f476,f59])).

fof(f59,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,u1_struct_0(sK2))
      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6) = k1_funct_1(sK5,X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK3)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f476,plain,
    ( r2_hidden(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK2))
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f474])).

fof(f474,plain,
    ( spl7_36
  <=> r2_hidden(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f481,plain,
    ( spl7_36
    | spl7_37
    | ~ spl7_6
    | spl7_8
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f472,f213,f140,f125,f478,f474])).

fof(f213,plain,
    ( spl7_18
  <=> ! [X3,X2] :
        ( r2_hidden(sK6(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2),sK5),u1_struct_0(sK2))
        | v1_xboole_0(X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X2,u1_struct_0(sK1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK1))))
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2))
        | sK5 = k2_partfun1(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f472,plain,
    ( sK5 = k3_tmap_1(sK3,sK1,sK3,sK2,sK4)
    | r2_hidden(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK2))
    | ~ spl7_6
    | spl7_8
    | ~ spl7_18 ),
    inference(forward_demodulation,[],[f471,f461])).

fof(f471,plain,
    ( r2_hidden(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK2))
    | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ spl7_6
    | spl7_8
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f470,f393])).

fof(f470,plain,
    ( r2_hidden(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | spl7_8
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f469,f53])).

fof(f469,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | r2_hidden(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | spl7_8
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f468,f52])).

fof(f468,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | r2_hidden(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | spl7_8
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f338,f141])).

fof(f338,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | r2_hidden(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ spl7_18 ),
    inference(resolution,[],[f214,f54])).

fof(f214,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK1))))
        | v1_xboole_0(X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X2,u1_struct_0(sK1))
        | r2_hidden(sK6(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2),sK5),u1_struct_0(sK2))
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2))
        | sK5 = k2_partfun1(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2)) )
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f213])).

fof(f465,plain,(
    ~ spl7_30 ),
    inference(avatar_contradiction_clause,[],[f464])).

fof(f464,plain,
    ( $false
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f463,f101])).

fof(f101,plain,(
    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK5) ),
    inference(subsumption_resolution,[],[f100,f56])).

fof(f56,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f100,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK5)
    | ~ v1_funct_1(sK5) ),
    inference(subsumption_resolution,[],[f97,f57])).

fof(f57,plain,(
    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f97,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5) ),
    inference(resolution,[],[f77,f58])).

fof(f58,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f36])).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f76])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f463,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK5)
    | ~ spl7_30 ),
    inference(superposition,[],[f60,f457])).

fof(f457,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5
    | ~ spl7_30 ),
    inference(forward_demodulation,[],[f456,f312])).

fof(f312,plain,
    ( sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f310])).

fof(f456,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f455,f42])).

fof(f42,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f455,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f454,f43])).

fof(f454,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f453,f44])).

fof(f453,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f451,f49])).

fof(f49,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f451,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f435,f51])).

fof(f60,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f449,plain,
    ( ~ spl7_6
    | spl7_8
    | ~ spl7_11
    | ~ spl7_16
    | spl7_32 ),
    inference(avatar_contradiction_clause,[],[f448])).

fof(f448,plain,
    ( $false
    | ~ spl7_6
    | spl7_8
    | ~ spl7_11
    | ~ spl7_16
    | spl7_32 ),
    inference(subsumption_resolution,[],[f447,f101])).

fof(f447,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK5)
    | ~ spl7_6
    | spl7_8
    | ~ spl7_11
    | ~ spl7_16
    | spl7_32 ),
    inference(superposition,[],[f60,f442])).

fof(f442,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5
    | ~ spl7_6
    | spl7_8
    | ~ spl7_11
    | ~ spl7_16
    | spl7_32 ),
    inference(subsumption_resolution,[],[f441,f42])).

fof(f441,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5
    | v2_struct_0(sK0)
    | ~ spl7_6
    | spl7_8
    | ~ spl7_11
    | ~ spl7_16
    | spl7_32 ),
    inference(subsumption_resolution,[],[f440,f43])).

fof(f440,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_6
    | spl7_8
    | ~ spl7_11
    | ~ spl7_16
    | spl7_32 ),
    inference(subsumption_resolution,[],[f439,f44])).

fof(f439,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_6
    | spl7_8
    | ~ spl7_11
    | ~ spl7_16
    | spl7_32 ),
    inference(subsumption_resolution,[],[f437,f49])).

fof(f437,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_6
    | spl7_8
    | ~ spl7_11
    | ~ spl7_16
    | spl7_32 ),
    inference(resolution,[],[f436,f51])).

fof(f436,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ m1_pre_topc(sK2,X0)
        | sK5 = k3_tmap_1(X0,sK1,sK3,sK2,sK4)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl7_6
    | spl7_8
    | ~ spl7_11
    | ~ spl7_16
    | spl7_32 ),
    inference(forward_demodulation,[],[f435,f400])).

% (18679)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
fof(f400,plain,
    ( sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ spl7_6
    | spl7_8
    | ~ spl7_11
    | ~ spl7_16
    | spl7_32 ),
    inference(global_subsumption,[],[f308,f319,f393])).

fof(f319,plain,
    ( ~ m1_subset_1(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK3))
    | spl7_32 ),
    inference(avatar_component_clause,[],[f318])).

fof(f308,plain,
    ( m1_subset_1(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | spl7_8
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f307,f53])).

fof(f307,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | m1_subset_1(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | spl7_8
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f306,f52])).

fof(f306,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | m1_subset_1(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | spl7_8
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f304,f141])).

fof(f304,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | m1_subset_1(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ spl7_11 ),
    inference(resolution,[],[f155,f54])).

fof(f155,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK1))))
        | v1_xboole_0(X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X2,u1_struct_0(sK1))
        | m1_subset_1(sK6(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2),sK5),X2)
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2))
        | sK5 = k2_partfun1(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2)) )
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl7_11
  <=> ! [X3,X2] :
        ( m1_subset_1(sK6(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2),sK5),X2)
        | v1_xboole_0(X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X2,u1_struct_0(sK1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK1))))
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2))
        | sK5 = k2_partfun1(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f391,plain,(
    ~ spl7_5 ),
    inference(avatar_contradiction_clause,[],[f390])).

fof(f390,plain,
    ( $false
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f389,f49])).

fof(f389,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f388,f44])).

fof(f388,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f253,f43])).

fof(f253,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ spl7_5 ),
    inference(resolution,[],[f123,f51])).

fof(f123,plain,
    ( ! [X2] :
        ( ~ m1_pre_topc(sK3,X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(sK2,X2) )
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl7_5
  <=> ! [X2] :
        ( ~ m1_pre_topc(sK3,X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(sK2,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f229,plain,(
    ~ spl7_10 ),
    inference(avatar_contradiction_clause,[],[f228])).

fof(f228,plain,
    ( $false
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f227,f48])).

fof(f48,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f227,plain,
    ( v2_struct_0(sK2)
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f226,f130])).

fof(f130,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f85,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f85,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f82,f44])).

fof(f82,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f66,f49])).

fof(f226,plain,
    ( ~ l1_struct_0(sK2)
    | v2_struct_0(sK2)
    | ~ spl7_10 ),
    inference(resolution,[],[f152,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f152,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl7_10
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f225,plain,(
    ~ spl7_8 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f223,f50])).

fof(f223,plain,
    ( v2_struct_0(sK3)
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f222,f165])).

fof(f165,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f86,f64])).

fof(f222,plain,
    ( ~ l1_struct_0(sK3)
    | v2_struct_0(sK3)
    | ~ spl7_8 ),
    inference(resolution,[],[f142,f67])).

fof(f142,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f140])).

fof(f215,plain,
    ( spl7_7
    | spl7_10
    | spl7_18 ),
    inference(avatar_split_clause,[],[f211,f213,f150,f136])).

fof(f136,plain,
    ( spl7_7
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f211,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK6(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2),sK5),u1_struct_0(sK2))
      | sK5 = k2_partfun1(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2))
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK1))))
      | ~ v1_funct_2(X3,X2,u1_struct_0(sK1))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(u1_struct_0(sK1))
      | v1_xboole_0(X2) ) ),
    inference(subsumption_resolution,[],[f210,f56])).

fof(f210,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK6(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2),sK5),u1_struct_0(sK2))
      | sK5 = k2_partfun1(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2))
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK1))))
      | ~ v1_funct_2(X3,X2,u1_struct_0(sK1))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(u1_struct_0(sK1))
      | v1_xboole_0(X2) ) ),
    inference(subsumption_resolution,[],[f158,f57])).

fof(f158,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK6(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2),sK5),u1_struct_0(sK2))
      | sK5 = k2_partfun1(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2))
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK1))))
      | ~ v1_funct_2(X3,X2,u1_struct_0(sK1))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(u1_struct_0(sK1))
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f62,f58])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | r2_hidden(sK6(X0,X1,X2,X3,X4),X3)
      | k2_partfun1(X0,X1,X2,X3) = X4
      | ~ v1_funct_2(X4,X3,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(X0,X1,X2,X3) = X4
                      | ( k3_funct_2(X0,X1,X2,sK6(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK6(X0,X1,X2,X3,X4))
                        & r2_hidden(sK6(X0,X1,X2,X3,X4),X3)
                        & m1_subset_1(sK6(X0,X1,X2,X3,X4),X0) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      | ~ v1_funct_2(X4,X3,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f16,f37])).

fof(f37,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5)
          & r2_hidden(X5,X3)
          & m1_subset_1(X5,X0) )
     => ( k3_funct_2(X0,X1,X2,sK6(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK6(X0,X1,X2,X3,X4))
        & r2_hidden(sK6(X0,X1,X2,X3,X4),X3)
        & m1_subset_1(sK6(X0,X1,X2,X3,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(X0,X1,X2,X3) = X4
                      | ? [X5] :
                          ( k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5)
                          & r2_hidden(X5,X3)
                          & m1_subset_1(X5,X0) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      | ~ v1_funct_2(X4,X3,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(X0,X1,X2,X3) = X4
                      | ? [X5] :
                          ( k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5)
                          & r2_hidden(X5,X3)
                          & m1_subset_1(X5,X0) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      | ~ v1_funct_2(X4,X3,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                        & v1_funct_2(X4,X3,X1)
                        & v1_funct_1(X4) )
                     => ( ! [X5] :
                            ( m1_subset_1(X5,X0)
                           => ( r2_hidden(X5,X3)
                             => k3_funct_2(X0,X1,X2,X5) = k1_funct_1(X4,X5) ) )
                       => k2_partfun1(X0,X1,X2,X3) = X4 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_funct_2)).

fof(f203,plain,
    ( spl7_7
    | spl7_10
    | spl7_16 ),
    inference(avatar_split_clause,[],[f199,f201,f150,f136])).

fof(f199,plain,(
    ! [X2,X3] :
      ( k3_funct_2(X2,u1_struct_0(sK1),X3,sK6(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2),sK5)) != k1_funct_1(sK5,sK6(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2),sK5))
      | sK5 = k2_partfun1(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2))
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK1))))
      | ~ v1_funct_2(X3,X2,u1_struct_0(sK1))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(u1_struct_0(sK1))
      | v1_xboole_0(X2) ) ),
    inference(subsumption_resolution,[],[f198,f56])).

fof(f198,plain,(
    ! [X2,X3] :
      ( k3_funct_2(X2,u1_struct_0(sK1),X3,sK6(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2),sK5)) != k1_funct_1(sK5,sK6(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2),sK5))
      | sK5 = k2_partfun1(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2))
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK1))))
      | ~ v1_funct_2(X3,X2,u1_struct_0(sK1))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(u1_struct_0(sK1))
      | v1_xboole_0(X2) ) ),
    inference(subsumption_resolution,[],[f163,f57])).

fof(f163,plain,(
    ! [X2,X3] :
      ( k3_funct_2(X2,u1_struct_0(sK1),X3,sK6(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2),sK5)) != k1_funct_1(sK5,sK6(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2),sK5))
      | sK5 = k2_partfun1(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2))
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK1))))
      | ~ v1_funct_2(X3,X2,u1_struct_0(sK1))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(u1_struct_0(sK1))
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f63,f58])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | k3_funct_2(X0,X1,X2,sK6(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK6(X0,X1,X2,X3,X4))
      | k2_partfun1(X0,X1,X2,X3) = X4
      | ~ v1_funct_2(X4,X3,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f197,plain,(
    ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f196])).

fof(f196,plain,
    ( $false
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f195,f45])).

fof(f195,plain,
    ( v2_struct_0(sK1)
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f194,f79])).

fof(f79,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f64,f47])).

fof(f194,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl7_7 ),
    inference(resolution,[],[f138,f67])).

fof(f138,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f136])).

fof(f156,plain,
    ( spl7_7
    | spl7_10
    | spl7_11 ),
    inference(avatar_split_clause,[],[f148,f154,f150,f136])).

fof(f148,plain,(
    ! [X2,X3] :
      ( m1_subset_1(sK6(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2),sK5),X2)
      | sK5 = k2_partfun1(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2))
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK1))))
      | ~ v1_funct_2(X3,X2,u1_struct_0(sK1))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(u1_struct_0(sK1))
      | v1_xboole_0(X2) ) ),
    inference(subsumption_resolution,[],[f147,f56])).

fof(f147,plain,(
    ! [X2,X3] :
      ( m1_subset_1(sK6(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2),sK5),X2)
      | sK5 = k2_partfun1(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2))
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK1))))
      | ~ v1_funct_2(X3,X2,u1_struct_0(sK1))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(u1_struct_0(sK1))
      | v1_xboole_0(X2) ) ),
    inference(subsumption_resolution,[],[f132,f57])).

fof(f132,plain,(
    ! [X2,X3] :
      ( m1_subset_1(sK6(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2),sK5),X2)
      | sK5 = k2_partfun1(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2))
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK1))))
      | ~ v1_funct_2(X3,X2,u1_struct_0(sK1))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(u1_struct_0(sK1))
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f61,f58])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | m1_subset_1(sK6(X0,X1,X2,X3,X4),X0)
      | k2_partfun1(X0,X1,X2,X3) = X4
      | ~ v1_funct_2(X4,X3,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f128,plain,
    ( spl7_5
    | spl7_6 ),
    inference(avatar_split_clause,[],[f104,f125,f122])).

fof(f104,plain,(
    ! [X2] :
      ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ m1_pre_topc(sK3,X2)
      | ~ m1_pre_topc(sK2,X2)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2) ) ),
    inference(resolution,[],[f71,f55])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X2)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:45:17 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (18687)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.48  % (18687)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (18695)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.49  % (18682)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f499,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f128,f156,f197,f203,f215,f225,f229,f391,f449,f465,f481,f486,f498])).
% 0.21/0.50  fof(f498,plain,(
% 0.21/0.50    spl7_30 | ~spl7_37),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f497])).
% 0.21/0.50  fof(f497,plain,(
% 0.21/0.50    $false | (spl7_30 | ~spl7_37)),
% 0.21/0.50    inference(subsumption_resolution,[],[f490,f480])).
% 0.21/0.50  fof(f480,plain,(
% 0.21/0.50    sK5 = k3_tmap_1(sK3,sK1,sK3,sK2,sK4) | ~spl7_37),
% 0.21/0.50    inference(avatar_component_clause,[],[f478])).
% 0.21/0.50  fof(f478,plain,(
% 0.21/0.50    spl7_37 <=> sK5 = k3_tmap_1(sK3,sK1,sK3,sK2,sK4)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).
% 0.21/0.50  fof(f490,plain,(
% 0.21/0.50    sK5 != k3_tmap_1(sK3,sK1,sK3,sK2,sK4) | spl7_30),
% 0.21/0.50    inference(superposition,[],[f311,f461])).
% 0.21/0.50  fof(f461,plain,(
% 0.21/0.50    k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK3,sK1,sK3,sK2,sK4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f460,f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ~v2_struct_0(sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    (((((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) & ! [X6] : (k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6) = k1_funct_1(sK5,X6) | ~r2_hidden(X6,u1_struct_0(sK2)) | ~m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK5)) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f14,f35,f34,f33,f32,f31,f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & ! [X6] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) | ~r2_hidden(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X4),X5) & ! [X6] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) | ~r2_hidden(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X4),X5) & ! [X6] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) | ~r2_hidden(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X2,X4),X5) & ! [X6] : (k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(sK1),X4,X6) | ~r2_hidden(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X2,X4),X5) & ! [X6] : (k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(sK1),X4,X6) | ~r2_hidden(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,sK2,X4),X5) & ! [X6] : (k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(sK1),X4,X6) | ~r2_hidden(X6,u1_struct_0(sK2)) | ~m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,sK2,X4),X5) & ! [X6] : (k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(sK1),X4,X6) | ~r2_hidden(X6,u1_struct_0(sK2)) | ~m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X4),X5) & ! [X6] : (k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),X4,X6) | ~r2_hidden(X6,u1_struct_0(sK2)) | ~m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(sK2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X4),X5) & ! [X6] : (k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),X4,X6) | ~r2_hidden(X6,u1_struct_0(sK2)) | ~m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(sK2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) => (? [X5] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X5) & ! [X6] : (k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6) | ~r2_hidden(X6,u1_struct_0(sK2)) | ~m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ? [X5] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X5) & ! [X6] : (k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6) | ~r2_hidden(X6,u1_struct_0(sK2)) | ~m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X5)) => (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) & ! [X6] : (k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6) = k1_funct_1(sK5,X6) | ~r2_hidden(X6,u1_struct_0(sK2)) | ~m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK5))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & ! [X6] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) | ~r2_hidden(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & ! [X6] : ((k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) | ~r2_hidden(X6,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3)))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => (! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => (r2_hidden(X6,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)))))))))),
% 0.21/0.50    inference(negated_conjecture,[],[f11])).
% 0.21/0.50  fof(f11,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => (! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => (r2_hidden(X6,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)))))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_tmap_1)).
% 0.21/0.50  fof(f460,plain,(
% 0.21/0.50    k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK3,sK1,sK3,sK2,sK4) | v2_struct_0(sK3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f459,f95])).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    v2_pre_topc(sK3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f94,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    v2_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    v2_pre_topc(sK3) | ~v2_pre_topc(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f90,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    l1_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    v2_pre_topc(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.50    inference(resolution,[],[f69,f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    m1_pre_topc(sK3,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.21/0.50  fof(f459,plain,(
% 0.21/0.50    k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK3,sK1,sK3,sK2,sK4) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f458,f86])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    l1_pre_topc(sK3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f83,f44])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    l1_pre_topc(sK3) | ~l1_pre_topc(sK0)),
% 0.21/0.50    inference(resolution,[],[f66,f51])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.50  fof(f458,plain,(
% 0.21/0.50    k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK3,sK1,sK3,sK2,sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f452,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    m1_pre_topc(sK2,sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f452,plain,(
% 0.21/0.50    ~m1_pre_topc(sK2,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK3,sK1,sK3,sK2,sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.50    inference(resolution,[],[f435,f164])).
% 0.21/0.50  fof(f164,plain,(
% 0.21/0.50    m1_pre_topc(sK3,sK3)),
% 0.21/0.50    inference(resolution,[],[f86,f65])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.21/0.50  fof(f435,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~m1_pre_topc(sK2,X0) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK3,sK2,sK4) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f434,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ~v2_struct_0(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f434,plain,(
% 0.21/0.50    ( ! [X0] : (k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK3,sK2,sK4) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(sK3,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f433,f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    v2_pre_topc(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f433,plain,(
% 0.21/0.51    ( ! [X0] : (k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK3,sK2,sK4) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(sK3,X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f432,f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    l1_pre_topc(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f432,plain,(
% 0.21/0.51    ( ! [X0] : (k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK3,sK2,sK4) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f431,f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    v1_funct_1(sK4)),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f431,plain,(
% 0.21/0.51    ( ! [X0] : (k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK3,sK2,sK4) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f430,f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  % (18680)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  fof(f430,plain,(
% 0.21/0.51    ( ! [X0] : (k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK3,sK2,sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(resolution,[],[f161,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  % (18677)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  fof(f161,plain,(
% 0.21/0.51    ( ! [X6,X8,X7] : (~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X7)))) | k3_tmap_1(X6,X7,sK3,sK2,X8) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X7),X8,u1_struct_0(sK2)) | ~v1_funct_2(X8,u1_struct_0(sK3),u1_struct_0(X7)) | ~v1_funct_1(X8) | ~m1_pre_topc(sK2,X6) | ~m1_pre_topc(sK3,X6) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 0.21/0.51    inference(resolution,[],[f68,f55])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).
% 0.21/0.51  fof(f311,plain,(
% 0.21/0.51    sK5 != k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | spl7_30),
% 0.21/0.51    inference(avatar_component_clause,[],[f310])).
% 0.21/0.51  fof(f310,plain,(
% 0.21/0.51    spl7_30 <=> sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 0.21/0.51  fof(f486,plain,(
% 0.21/0.51    ~spl7_6 | spl7_8 | ~spl7_16 | spl7_30 | ~spl7_32 | ~spl7_36),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f485])).
% 0.21/0.51  fof(f485,plain,(
% 0.21/0.51    $false | (~spl7_6 | spl7_8 | ~spl7_16 | spl7_30 | ~spl7_32 | ~spl7_36)),
% 0.21/0.51    inference(subsumption_resolution,[],[f484,f320])).
% 0.21/0.51  fof(f320,plain,(
% 0.21/0.51    m1_subset_1(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK3)) | ~spl7_32),
% 0.21/0.51    inference(avatar_component_clause,[],[f318])).
% 0.21/0.51  fof(f318,plain,(
% 0.21/0.51    spl7_32 <=> m1_subset_1(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).
% 0.21/0.51  fof(f484,plain,(
% 0.21/0.51    ~m1_subset_1(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK3)) | (~spl7_6 | spl7_8 | ~spl7_16 | spl7_30 | ~spl7_36)),
% 0.21/0.51    inference(subsumption_resolution,[],[f483,f467])).
% 0.21/0.51  fof(f467,plain,(
% 0.21/0.51    k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) != k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) | (~spl7_6 | spl7_8 | ~spl7_16 | spl7_30)),
% 0.21/0.51    inference(global_subsumption,[],[f311,f399])).
% 0.21/0.51  fof(f399,plain,(
% 0.21/0.51    k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) != k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | (~spl7_6 | spl7_8 | ~spl7_16)),
% 0.21/0.51    inference(subsumption_resolution,[],[f398,f393])).
% 0.21/0.51  fof(f393,plain,(
% 0.21/0.51    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~spl7_6),
% 0.21/0.51    inference(resolution,[],[f127,f73])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.51    inference(nnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) | ~spl7_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f125])).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    spl7_6 <=> r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.51  fof(f398,plain,(
% 0.21/0.51    k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) != k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | (spl7_8 | ~spl7_16)),
% 0.21/0.51    inference(subsumption_resolution,[],[f397,f53])).
% 0.21/0.51  fof(f397,plain,(
% 0.21/0.51    ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) != k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | (spl7_8 | ~spl7_16)),
% 0.21/0.51    inference(subsumption_resolution,[],[f396,f52])).
% 0.21/0.51  % (18697)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  fof(f396,plain,(
% 0.21/0.51    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) != k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | (spl7_8 | ~spl7_16)),
% 0.21/0.51    inference(subsumption_resolution,[],[f342,f141])).
% 0.21/0.51  fof(f141,plain,(
% 0.21/0.51    ~v1_xboole_0(u1_struct_0(sK3)) | spl7_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f140])).
% 0.21/0.51  fof(f140,plain,(
% 0.21/0.51    spl7_8 <=> v1_xboole_0(u1_struct_0(sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.51  fof(f342,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) != k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | ~spl7_16),
% 0.21/0.51    inference(resolution,[],[f202,f54])).
% 0.21/0.51  fof(f202,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK1)))) | v1_xboole_0(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X2,u1_struct_0(sK1)) | k3_funct_2(X2,u1_struct_0(sK1),X3,sK6(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2),sK5)) != k1_funct_1(sK5,sK6(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2),sK5)) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2)) | sK5 = k2_partfun1(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2))) ) | ~spl7_16),
% 0.21/0.51    inference(avatar_component_clause,[],[f201])).
% 0.21/0.51  fof(f201,plain,(
% 0.21/0.51    spl7_16 <=> ! [X3,X2] : (k3_funct_2(X2,u1_struct_0(sK1),X3,sK6(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2),sK5)) != k1_funct_1(sK5,sK6(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2),sK5)) | v1_xboole_0(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X2,u1_struct_0(sK1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK1)))) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2)) | sK5 = k2_partfun1(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.21/0.51  fof(f483,plain,(
% 0.21/0.51    k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) | ~m1_subset_1(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK3)) | ~spl7_36),
% 0.21/0.51    inference(resolution,[],[f476,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X6] : (~r2_hidden(X6,u1_struct_0(sK2)) | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6) = k1_funct_1(sK5,X6) | ~m1_subset_1(X6,u1_struct_0(sK3))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f476,plain,(
% 0.21/0.51    r2_hidden(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK2)) | ~spl7_36),
% 0.21/0.51    inference(avatar_component_clause,[],[f474])).
% 0.21/0.51  fof(f474,plain,(
% 0.21/0.51    spl7_36 <=> r2_hidden(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).
% 0.21/0.51  fof(f481,plain,(
% 0.21/0.51    spl7_36 | spl7_37 | ~spl7_6 | spl7_8 | ~spl7_18),
% 0.21/0.51    inference(avatar_split_clause,[],[f472,f213,f140,f125,f478,f474])).
% 0.21/0.51  fof(f213,plain,(
% 0.21/0.51    spl7_18 <=> ! [X3,X2] : (r2_hidden(sK6(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2),sK5),u1_struct_0(sK2)) | v1_xboole_0(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X2,u1_struct_0(sK1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK1)))) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2)) | sK5 = k2_partfun1(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.21/0.51  fof(f472,plain,(
% 0.21/0.51    sK5 = k3_tmap_1(sK3,sK1,sK3,sK2,sK4) | r2_hidden(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK2)) | (~spl7_6 | spl7_8 | ~spl7_18)),
% 0.21/0.51    inference(forward_demodulation,[],[f471,f461])).
% 0.21/0.51  fof(f471,plain,(
% 0.21/0.51    r2_hidden(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK2)) | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | (~spl7_6 | spl7_8 | ~spl7_18)),
% 0.21/0.51    inference(subsumption_resolution,[],[f470,f393])).
% 0.21/0.51  fof(f470,plain,(
% 0.21/0.51    r2_hidden(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK2)) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | (spl7_8 | ~spl7_18)),
% 0.21/0.51    inference(subsumption_resolution,[],[f469,f53])).
% 0.21/0.51  fof(f469,plain,(
% 0.21/0.51    ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | r2_hidden(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK2)) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | (spl7_8 | ~spl7_18)),
% 0.21/0.51    inference(subsumption_resolution,[],[f468,f52])).
% 0.21/0.51  fof(f468,plain,(
% 0.21/0.51    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | r2_hidden(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK2)) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | (spl7_8 | ~spl7_18)),
% 0.21/0.51    inference(subsumption_resolution,[],[f338,f141])).
% 0.21/0.51  fof(f338,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | r2_hidden(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK2)) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | ~spl7_18),
% 0.21/0.51    inference(resolution,[],[f214,f54])).
% 0.21/0.51  fof(f214,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK1)))) | v1_xboole_0(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X2,u1_struct_0(sK1)) | r2_hidden(sK6(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2),sK5),u1_struct_0(sK2)) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2)) | sK5 = k2_partfun1(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2))) ) | ~spl7_18),
% 0.21/0.51    inference(avatar_component_clause,[],[f213])).
% 0.21/0.51  fof(f465,plain,(
% 0.21/0.51    ~spl7_30),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f464])).
% 0.21/0.51  fof(f464,plain,(
% 0.21/0.51    $false | ~spl7_30),
% 0.21/0.51    inference(subsumption_resolution,[],[f463,f101])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f100,f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    v1_funct_1(sK5)),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK5) | ~v1_funct_1(sK5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f97,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK5)),
% 0.21/0.51    inference(resolution,[],[f77,f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X3,X3) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f76])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.51    inference(equality_resolution,[],[f75])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.51    inference(nnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 0.21/0.51  fof(f463,plain,(
% 0.21/0.51    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK5) | ~spl7_30),
% 0.21/0.51    inference(superposition,[],[f60,f457])).
% 0.21/0.51  fof(f457,plain,(
% 0.21/0.51    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 | ~spl7_30),
% 0.21/0.51    inference(forward_demodulation,[],[f456,f312])).
% 0.21/0.51  fof(f312,plain,(
% 0.21/0.51    sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | ~spl7_30),
% 0.21/0.51    inference(avatar_component_clause,[],[f310])).
% 0.21/0.51  fof(f456,plain,(
% 0.21/0.51    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))),
% 0.21/0.51    inference(subsumption_resolution,[],[f455,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ~v2_struct_0(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f455,plain,(
% 0.21/0.51    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f454,f43])).
% 0.21/0.51  fof(f454,plain,(
% 0.21/0.51    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f453,f44])).
% 0.21/0.51  fof(f453,plain,(
% 0.21/0.51    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f451,f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    m1_pre_topc(sK2,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f451,plain,(
% 0.21/0.51    ~m1_pre_topc(sK2,sK0) | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.51    inference(resolution,[],[f435,f51])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f449,plain,(
% 0.21/0.51    ~spl7_6 | spl7_8 | ~spl7_11 | ~spl7_16 | spl7_32),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f448])).
% 0.21/0.51  fof(f448,plain,(
% 0.21/0.51    $false | (~spl7_6 | spl7_8 | ~spl7_11 | ~spl7_16 | spl7_32)),
% 0.21/0.51    inference(subsumption_resolution,[],[f447,f101])).
% 0.21/0.51  fof(f447,plain,(
% 0.21/0.51    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK5) | (~spl7_6 | spl7_8 | ~spl7_11 | ~spl7_16 | spl7_32)),
% 0.21/0.51    inference(superposition,[],[f60,f442])).
% 0.21/0.51  fof(f442,plain,(
% 0.21/0.51    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 | (~spl7_6 | spl7_8 | ~spl7_11 | ~spl7_16 | spl7_32)),
% 0.21/0.51    inference(subsumption_resolution,[],[f441,f42])).
% 0.21/0.51  fof(f441,plain,(
% 0.21/0.51    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 | v2_struct_0(sK0) | (~spl7_6 | spl7_8 | ~spl7_11 | ~spl7_16 | spl7_32)),
% 0.21/0.51    inference(subsumption_resolution,[],[f440,f43])).
% 0.21/0.51  fof(f440,plain,(
% 0.21/0.51    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl7_6 | spl7_8 | ~spl7_11 | ~spl7_16 | spl7_32)),
% 0.21/0.51    inference(subsumption_resolution,[],[f439,f44])).
% 0.21/0.51  fof(f439,plain,(
% 0.21/0.51    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl7_6 | spl7_8 | ~spl7_11 | ~spl7_16 | spl7_32)),
% 0.21/0.51    inference(subsumption_resolution,[],[f437,f49])).
% 0.21/0.51  fof(f437,plain,(
% 0.21/0.51    ~m1_pre_topc(sK2,sK0) | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl7_6 | spl7_8 | ~spl7_11 | ~spl7_16 | spl7_32)),
% 0.21/0.51    inference(resolution,[],[f436,f51])).
% 0.21/0.51  fof(f436,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~m1_pre_topc(sK2,X0) | sK5 = k3_tmap_1(X0,sK1,sK3,sK2,sK4) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | (~spl7_6 | spl7_8 | ~spl7_11 | ~spl7_16 | spl7_32)),
% 0.21/0.51    inference(forward_demodulation,[],[f435,f400])).
% 0.21/0.51  % (18679)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  fof(f400,plain,(
% 0.21/0.51    sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | (~spl7_6 | spl7_8 | ~spl7_11 | ~spl7_16 | spl7_32)),
% 0.21/0.51    inference(global_subsumption,[],[f308,f319,f393])).
% 0.21/0.51  fof(f319,plain,(
% 0.21/0.51    ~m1_subset_1(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK3)) | spl7_32),
% 0.21/0.51    inference(avatar_component_clause,[],[f318])).
% 0.21/0.51  fof(f308,plain,(
% 0.21/0.51    m1_subset_1(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK3)) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | (spl7_8 | ~spl7_11)),
% 0.21/0.51    inference(subsumption_resolution,[],[f307,f53])).
% 0.21/0.51  fof(f307,plain,(
% 0.21/0.51    ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | m1_subset_1(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK3)) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | (spl7_8 | ~spl7_11)),
% 0.21/0.51    inference(subsumption_resolution,[],[f306,f52])).
% 0.21/0.51  fof(f306,plain,(
% 0.21/0.51    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | m1_subset_1(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK3)) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | (spl7_8 | ~spl7_11)),
% 0.21/0.51    inference(subsumption_resolution,[],[f304,f141])).
% 0.21/0.51  fof(f304,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | m1_subset_1(sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5),u1_struct_0(sK3)) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | ~spl7_11),
% 0.21/0.51    inference(resolution,[],[f155,f54])).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK1)))) | v1_xboole_0(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X2,u1_struct_0(sK1)) | m1_subset_1(sK6(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2),sK5),X2) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2)) | sK5 = k2_partfun1(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2))) ) | ~spl7_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f154])).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    spl7_11 <=> ! [X3,X2] : (m1_subset_1(sK6(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2),sK5),X2) | v1_xboole_0(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X2,u1_struct_0(sK1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK1)))) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2)) | sK5 = k2_partfun1(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.21/0.51  fof(f391,plain,(
% 0.21/0.51    ~spl7_5),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f390])).
% 0.21/0.51  fof(f390,plain,(
% 0.21/0.51    $false | ~spl7_5),
% 0.21/0.51    inference(subsumption_resolution,[],[f389,f49])).
% 0.21/0.51  fof(f389,plain,(
% 0.21/0.51    ~m1_pre_topc(sK2,sK0) | ~spl7_5),
% 0.21/0.51    inference(subsumption_resolution,[],[f388,f44])).
% 0.21/0.51  fof(f388,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | ~m1_pre_topc(sK2,sK0) | ~spl7_5),
% 0.21/0.51    inference(subsumption_resolution,[],[f253,f43])).
% 0.21/0.51  fof(f253,plain,(
% 0.21/0.51    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK2,sK0) | ~spl7_5),
% 0.21/0.51    inference(resolution,[],[f123,f51])).
% 0.21/0.51  fof(f123,plain,(
% 0.21/0.51    ( ! [X2] : (~m1_pre_topc(sK3,X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_pre_topc(sK2,X2)) ) | ~spl7_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f122])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    spl7_5 <=> ! [X2] : (~m1_pre_topc(sK3,X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_pre_topc(sK2,X2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.51  fof(f229,plain,(
% 0.21/0.51    ~spl7_10),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f228])).
% 0.21/0.51  fof(f228,plain,(
% 0.21/0.51    $false | ~spl7_10),
% 0.21/0.51    inference(subsumption_resolution,[],[f227,f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ~v2_struct_0(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f227,plain,(
% 0.21/0.51    v2_struct_0(sK2) | ~spl7_10),
% 0.21/0.51    inference(subsumption_resolution,[],[f226,f130])).
% 0.21/0.51  fof(f130,plain,(
% 0.21/0.51    l1_struct_0(sK2)),
% 0.21/0.51    inference(resolution,[],[f85,f64])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    l1_pre_topc(sK2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f82,f44])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    l1_pre_topc(sK2) | ~l1_pre_topc(sK0)),
% 0.21/0.51    inference(resolution,[],[f66,f49])).
% 0.21/0.51  fof(f226,plain,(
% 0.21/0.51    ~l1_struct_0(sK2) | v2_struct_0(sK2) | ~spl7_10),
% 0.21/0.51    inference(resolution,[],[f152,f67])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.51  fof(f152,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(sK2)) | ~spl7_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f150])).
% 0.21/0.51  fof(f150,plain,(
% 0.21/0.51    spl7_10 <=> v1_xboole_0(u1_struct_0(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.51  fof(f225,plain,(
% 0.21/0.51    ~spl7_8),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f224])).
% 0.21/0.51  fof(f224,plain,(
% 0.21/0.51    $false | ~spl7_8),
% 0.21/0.51    inference(subsumption_resolution,[],[f223,f50])).
% 0.21/0.51  fof(f223,plain,(
% 0.21/0.51    v2_struct_0(sK3) | ~spl7_8),
% 0.21/0.51    inference(subsumption_resolution,[],[f222,f165])).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    l1_struct_0(sK3)),
% 0.21/0.51    inference(resolution,[],[f86,f64])).
% 0.21/0.51  fof(f222,plain,(
% 0.21/0.51    ~l1_struct_0(sK3) | v2_struct_0(sK3) | ~spl7_8),
% 0.21/0.51    inference(resolution,[],[f142,f67])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(sK3)) | ~spl7_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f140])).
% 0.21/0.51  fof(f215,plain,(
% 0.21/0.51    spl7_7 | spl7_10 | spl7_18),
% 0.21/0.51    inference(avatar_split_clause,[],[f211,f213,f150,f136])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    spl7_7 <=> v1_xboole_0(u1_struct_0(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.51  fof(f211,plain,(
% 0.21/0.51    ( ! [X2,X3] : (r2_hidden(sK6(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2),sK5),u1_struct_0(sK2)) | sK5 = k2_partfun1(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2)) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2)) | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK1)))) | ~v1_funct_2(X3,X2,u1_struct_0(sK1)) | ~v1_funct_1(X3) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(X2)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f210,f56])).
% 0.21/0.51  fof(f210,plain,(
% 0.21/0.51    ( ! [X2,X3] : (r2_hidden(sK6(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2),sK5),u1_struct_0(sK2)) | sK5 = k2_partfun1(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2)) | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK1)))) | ~v1_funct_2(X3,X2,u1_struct_0(sK1)) | ~v1_funct_1(X3) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(X2)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f158,f57])).
% 0.21/0.51  fof(f158,plain,(
% 0.21/0.51    ( ! [X2,X3] : (r2_hidden(sK6(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2),sK5),u1_struct_0(sK2)) | sK5 = k2_partfun1(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2)) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2)) | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK1)))) | ~v1_funct_2(X3,X2,u1_struct_0(sK1)) | ~v1_funct_1(X3) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(X2)) )),
% 0.21/0.51    inference(resolution,[],[f62,f58])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | r2_hidden(sK6(X0,X1,X2,X3,X4),X3) | k2_partfun1(X0,X1,X2,X3) = X4 | ~v1_funct_2(X4,X3,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(X0,X1,X2,X3) = X4 | (k3_funct_2(X0,X1,X2,sK6(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK6(X0,X1,X2,X3,X4)) & r2_hidden(sK6(X0,X1,X2,X3,X4),X3) & m1_subset_1(sK6(X0,X1,X2,X3,X4),X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X4,X3,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f16,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ! [X4,X3,X2,X1,X0] : (? [X5] : (k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,X3) & m1_subset_1(X5,X0)) => (k3_funct_2(X0,X1,X2,sK6(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK6(X0,X1,X2,X3,X4)) & r2_hidden(sK6(X0,X1,X2,X3,X4),X3) & m1_subset_1(sK6(X0,X1,X2,X3,X4),X0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(X0,X1,X2,X3) = X4 | ? [X5] : (k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,X3) & m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X4,X3,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.51    inference(flattening,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(X0,X1,X2,X3) = X4 | ? [X5] : ((k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,X3)) & m1_subset_1(X5,X0))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X4,X3,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X4,X3,X1) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,X0) => (r2_hidden(X5,X3) => k3_funct_2(X0,X1,X2,X5) = k1_funct_1(X4,X5))) => k2_partfun1(X0,X1,X2,X3) = X4))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_funct_2)).
% 0.21/0.51  fof(f203,plain,(
% 0.21/0.51    spl7_7 | spl7_10 | spl7_16),
% 0.21/0.51    inference(avatar_split_clause,[],[f199,f201,f150,f136])).
% 0.21/0.51  fof(f199,plain,(
% 0.21/0.51    ( ! [X2,X3] : (k3_funct_2(X2,u1_struct_0(sK1),X3,sK6(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2),sK5)) != k1_funct_1(sK5,sK6(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2),sK5)) | sK5 = k2_partfun1(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2)) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2)) | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK1)))) | ~v1_funct_2(X3,X2,u1_struct_0(sK1)) | ~v1_funct_1(X3) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(X2)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f198,f56])).
% 0.21/0.51  fof(f198,plain,(
% 0.21/0.51    ( ! [X2,X3] : (k3_funct_2(X2,u1_struct_0(sK1),X3,sK6(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2),sK5)) != k1_funct_1(sK5,sK6(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2),sK5)) | sK5 = k2_partfun1(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2)) | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK1)))) | ~v1_funct_2(X3,X2,u1_struct_0(sK1)) | ~v1_funct_1(X3) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(X2)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f163,f57])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    ( ! [X2,X3] : (k3_funct_2(X2,u1_struct_0(sK1),X3,sK6(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2),sK5)) != k1_funct_1(sK5,sK6(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2),sK5)) | sK5 = k2_partfun1(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2)) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2)) | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK1)))) | ~v1_funct_2(X3,X2,u1_struct_0(sK1)) | ~v1_funct_1(X3) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(X2)) )),
% 0.21/0.51    inference(resolution,[],[f63,f58])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k3_funct_2(X0,X1,X2,sK6(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK6(X0,X1,X2,X3,X4)) | k2_partfun1(X0,X1,X2,X3) = X4 | ~v1_funct_2(X4,X3,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f197,plain,(
% 0.21/0.51    ~spl7_7),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f196])).
% 0.21/0.51  fof(f196,plain,(
% 0.21/0.51    $false | ~spl7_7),
% 0.21/0.51    inference(subsumption_resolution,[],[f195,f45])).
% 0.21/0.51  fof(f195,plain,(
% 0.21/0.51    v2_struct_0(sK1) | ~spl7_7),
% 0.21/0.51    inference(subsumption_resolution,[],[f194,f79])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    l1_struct_0(sK1)),
% 0.21/0.51    inference(resolution,[],[f64,f47])).
% 0.21/0.51  fof(f194,plain,(
% 0.21/0.51    ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl7_7),
% 0.21/0.51    inference(resolution,[],[f138,f67])).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(sK1)) | ~spl7_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f136])).
% 0.21/0.51  fof(f156,plain,(
% 0.21/0.51    spl7_7 | spl7_10 | spl7_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f148,f154,f150,f136])).
% 0.21/0.51  fof(f148,plain,(
% 0.21/0.51    ( ! [X2,X3] : (m1_subset_1(sK6(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2),sK5),X2) | sK5 = k2_partfun1(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2)) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2)) | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK1)))) | ~v1_funct_2(X3,X2,u1_struct_0(sK1)) | ~v1_funct_1(X3) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(X2)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f147,f56])).
% 0.21/0.51  fof(f147,plain,(
% 0.21/0.51    ( ! [X2,X3] : (m1_subset_1(sK6(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2),sK5),X2) | sK5 = k2_partfun1(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2)) | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK1)))) | ~v1_funct_2(X3,X2,u1_struct_0(sK1)) | ~v1_funct_1(X3) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(X2)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f132,f57])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    ( ! [X2,X3] : (m1_subset_1(sK6(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2),sK5),X2) | sK5 = k2_partfun1(X2,u1_struct_0(sK1),X3,u1_struct_0(sK2)) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X2)) | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK1)))) | ~v1_funct_2(X3,X2,u1_struct_0(sK1)) | ~v1_funct_1(X3) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(X2)) )),
% 0.21/0.51    inference(resolution,[],[f61,f58])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | m1_subset_1(sK6(X0,X1,X2,X3,X4),X0) | k2_partfun1(X0,X1,X2,X3) = X4 | ~v1_funct_2(X4,X3,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    spl7_5 | spl7_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f104,f125,f122])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    ( ! [X2] : (r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) | ~m1_pre_topc(sK3,X2) | ~m1_pre_topc(sK2,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) )),
% 0.21/0.51    inference(resolution,[],[f71,f55])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X2) | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (18687)------------------------------
% 0.21/0.51  % (18687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (18687)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (18687)Memory used [KB]: 11001
% 0.21/0.51  % (18687)Time elapsed: 0.075 s
% 0.21/0.51  % (18687)------------------------------
% 0.21/0.51  % (18687)------------------------------
% 0.21/0.51  % (18696)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (18676)Success in time 0.154 s
%------------------------------------------------------------------------------
