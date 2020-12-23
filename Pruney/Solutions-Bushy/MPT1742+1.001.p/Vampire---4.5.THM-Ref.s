%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1742+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:28 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  191 (1568 expanded)
%              Number of leaves         :   25 ( 816 expanded)
%              Depth                    :   24
%              Number of atoms          : 1017 (29236 expanded)
%              Number of equality atoms :   49 (2782 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f674,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f128,f377,f565,f601,f645,f673])).

fof(f673,plain,
    ( ~ spl12_5
    | ~ spl12_13 ),
    inference(avatar_contradiction_clause,[],[f672])).

fof(f672,plain,
    ( $false
    | ~ spl12_5
    | ~ spl12_13 ),
    inference(subsumption_resolution,[],[f671,f603])).

fof(f603,plain,
    ( r1_tmap_1(sK4,sK5,sK6,sK8)
    | ~ spl12_13 ),
    inference(forward_demodulation,[],[f96,f576])).

fof(f576,plain,
    ( sK6 = sK7
    | ~ spl12_13 ),
    inference(avatar_component_clause,[],[f574])).

fof(f574,plain,
    ( spl12_13
  <=> sK6 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_13])])).

fof(f96,plain,(
    r1_tmap_1(sK4,sK5,sK7,sK8) ),
    inference(forward_demodulation,[],[f68,f67])).

fof(f67,plain,(
    sK8 = sK9 ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ~ r1_tmap_1(sK3,sK5,sK6,sK8)
    & r1_tmap_1(sK4,sK5,sK7,sK9)
    & sK8 = sK9
    & m1_subset_1(sK9,u1_struct_0(sK4))
    & m1_subset_1(sK8,u1_struct_0(sK3))
    & r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK5),u1_struct_0(sK4),u1_struct_0(sK5),sK6,sK7)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
    & v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK5))
    & v1_funct_1(sK7)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK5))))
    & v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK5))
    & v1_funct_1(sK6)
    & r1_tarski(u1_pre_topc(sK4),u1_pre_topc(sK3))
    & u1_struct_0(sK3) = u1_struct_0(sK4)
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & ~ v2_struct_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8,sK9])],[f11,f32,f31,f30,f29,f28,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ~ r1_tmap_1(X0,X2,X3,X5)
                                & r1_tmap_1(X1,X2,X4,X6)
                                & X5 = X6
                                & m1_subset_1(X6,u1_struct_0(X1)) )
                            & m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_funct_2(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X2),X3,X4)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                        & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                        & v1_funct_1(X4) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                    & v1_funct_1(X3) )
                & r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
                & u1_struct_0(X0) = u1_struct_0(X1)
                & l1_pre_topc(X2)
                & v2_pre_topc(X2)
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
                          ( ? [X6] :
                              ( ~ r1_tmap_1(sK3,X2,X3,X5)
                              & r1_tmap_1(X1,X2,X4,X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X1)) )
                          & m1_subset_1(X5,u1_struct_0(sK3)) )
                      & r1_funct_2(u1_struct_0(sK3),u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X2),X3,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                      & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X2))))
                  & v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X2))
                  & v1_funct_1(X3) )
              & r1_tarski(u1_pre_topc(X1),u1_pre_topc(sK3))
              & u1_struct_0(X1) = u1_struct_0(sK3)
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ~ r1_tmap_1(sK3,X2,X3,X5)
                            & r1_tmap_1(X1,X2,X4,X6)
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X1)) )
                        & m1_subset_1(X5,u1_struct_0(sK3)) )
                    & r1_funct_2(u1_struct_0(sK3),u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X2),X3,X4)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                    & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X2))))
                & v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X2))
                & v1_funct_1(X3) )
            & r1_tarski(u1_pre_topc(X1),u1_pre_topc(sK3))
            & u1_struct_0(X1) = u1_struct_0(sK3)
            & l1_pre_topc(X2)
            & v2_pre_topc(X2)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ r1_tmap_1(sK3,X2,X3,X5)
                          & r1_tmap_1(sK4,X2,X4,X6)
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(sK4)) )
                      & m1_subset_1(X5,u1_struct_0(sK3)) )
                  & r1_funct_2(u1_struct_0(sK3),u1_struct_0(X2),u1_struct_0(sK4),u1_struct_0(X2),X3,X4)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X2))))
                  & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X2))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X2))))
              & v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X2))
              & v1_funct_1(X3) )
          & r1_tarski(u1_pre_topc(sK4),u1_pre_topc(sK3))
          & u1_struct_0(sK3) = u1_struct_0(sK4)
          & l1_pre_topc(X2)
          & v2_pre_topc(X2)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ~ r1_tmap_1(sK3,X2,X3,X5)
                        & r1_tmap_1(sK4,X2,X4,X6)
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(sK4)) )
                    & m1_subset_1(X5,u1_struct_0(sK3)) )
                & r1_funct_2(u1_struct_0(sK3),u1_struct_0(X2),u1_struct_0(sK4),u1_struct_0(X2),X3,X4)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X2))))
                & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X2))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X2))))
            & v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X2))
            & v1_funct_1(X3) )
        & r1_tarski(u1_pre_topc(sK4),u1_pre_topc(sK3))
        & u1_struct_0(sK3) = u1_struct_0(sK4)
        & l1_pre_topc(X2)
        & v2_pre_topc(X2)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ~ r1_tmap_1(sK3,sK5,X3,X5)
                      & r1_tmap_1(sK4,sK5,X4,X6)
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(sK4)) )
                  & m1_subset_1(X5,u1_struct_0(sK3)) )
              & r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK5),u1_struct_0(sK4),u1_struct_0(sK5),X3,X4)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
              & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(sK5))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK5))))
          & v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(sK5))
          & v1_funct_1(X3) )
      & r1_tarski(u1_pre_topc(sK4),u1_pre_topc(sK3))
      & u1_struct_0(sK3) = u1_struct_0(sK4)
      & l1_pre_topc(sK5)
      & v2_pre_topc(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ r1_tmap_1(sK3,sK5,X3,X5)
                    & r1_tmap_1(sK4,sK5,X4,X6)
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(sK4)) )
                & m1_subset_1(X5,u1_struct_0(sK3)) )
            & r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK5),u1_struct_0(sK4),u1_struct_0(sK5),X3,X4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
            & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(sK5))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK5))))
        & v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(sK5))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ r1_tmap_1(sK3,sK5,sK6,X5)
                  & r1_tmap_1(sK4,sK5,X4,X6)
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(sK4)) )
              & m1_subset_1(X5,u1_struct_0(sK3)) )
          & r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK5),u1_struct_0(sK4),u1_struct_0(sK5),sK6,X4)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
          & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(sK5))
          & v1_funct_1(X4) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK5))))
      & v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK5))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ~ r1_tmap_1(sK3,sK5,sK6,X5)
                & r1_tmap_1(sK4,sK5,X4,X6)
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(sK4)) )
            & m1_subset_1(X5,u1_struct_0(sK3)) )
        & r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK5),u1_struct_0(sK4),u1_struct_0(sK5),sK6,X4)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
        & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(sK5))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ~ r1_tmap_1(sK3,sK5,sK6,X5)
              & r1_tmap_1(sK4,sK5,sK7,X6)
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(sK4)) )
          & m1_subset_1(X5,u1_struct_0(sK3)) )
      & r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK5),u1_struct_0(sK4),u1_struct_0(sK5),sK6,sK7)
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
      & v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK5))
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ~ r1_tmap_1(sK3,sK5,sK6,X5)
            & r1_tmap_1(sK4,sK5,sK7,X6)
            & X5 = X6
            & m1_subset_1(X6,u1_struct_0(sK4)) )
        & m1_subset_1(X5,u1_struct_0(sK3)) )
   => ( ? [X6] :
          ( ~ r1_tmap_1(sK3,sK5,sK6,sK8)
          & r1_tmap_1(sK4,sK5,sK7,X6)
          & sK8 = X6
          & m1_subset_1(X6,u1_struct_0(sK4)) )
      & m1_subset_1(sK8,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X6] :
        ( ~ r1_tmap_1(sK3,sK5,sK6,sK8)
        & r1_tmap_1(sK4,sK5,sK7,X6)
        & sK8 = X6
        & m1_subset_1(X6,u1_struct_0(sK4)) )
   => ( ~ r1_tmap_1(sK3,sK5,sK6,sK8)
      & r1_tmap_1(sK4,sK5,sK7,sK9)
      & sK8 = sK9
      & m1_subset_1(sK9,u1_struct_0(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X0,X2,X3,X5)
                              & r1_tmap_1(X1,X2,X4,X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X1)) )
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & r1_funct_2(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X2),X3,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                      & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                  & v1_funct_1(X3) )
              & r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
              & u1_struct_0(X0) = u1_struct_0(X1)
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X0,X2,X3,X5)
                              & r1_tmap_1(X1,X2,X4,X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X1)) )
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & r1_funct_2(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X2),X3,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                      & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                  & v1_funct_1(X3) )
              & r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
              & u1_struct_0(X0) = u1_struct_0(X1)
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( l1_pre_topc(X2)
                  & v2_pre_topc(X2)
                  & ~ v2_struct_0(X2) )
               => ( ( r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
                    & u1_struct_0(X0) = u1_struct_0(X1) )
                 => ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                        & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                        & v1_funct_1(X3) )
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                            & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                            & v1_funct_1(X4) )
                         => ( r1_funct_2(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X2),X3,X4)
                           => ! [X5] :
                                ( m1_subset_1(X5,u1_struct_0(X0))
                               => ! [X6] :
                                    ( m1_subset_1(X6,u1_struct_0(X1))
                                   => ( ( r1_tmap_1(X1,X2,X4,X6)
                                        & X5 = X6 )
                                     => r1_tmap_1(X0,X2,X3,X5) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ( ( r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
                  & u1_struct_0(X0) = u1_struct_0(X1) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                      & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                      & v1_funct_1(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                          & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                          & v1_funct_1(X4) )
                       => ( r1_funct_2(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X2),X3,X4)
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X0))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X1))
                                 => ( ( r1_tmap_1(X1,X2,X4,X6)
                                      & X5 = X6 )
                                   => r1_tmap_1(X0,X2,X3,X5) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_tmap_1)).

fof(f68,plain,(
    r1_tmap_1(sK4,sK5,sK7,sK9) ),
    inference(cnf_transformation,[],[f33])).

fof(f671,plain,
    ( ~ r1_tmap_1(sK4,sK5,sK6,sK8)
    | ~ spl12_5 ),
    inference(subsumption_resolution,[],[f670,f65])).

fof(f65,plain,(
    m1_subset_1(sK8,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f33])).

fof(f670,plain,
    ( ~ m1_subset_1(sK8,u1_struct_0(sK3))
    | ~ r1_tmap_1(sK4,sK5,sK6,sK8)
    | ~ spl12_5 ),
    inference(resolution,[],[f669,f69])).

fof(f69,plain,(
    ~ r1_tmap_1(sK3,sK5,sK6,sK8) ),
    inference(cnf_transformation,[],[f33])).

fof(f669,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK3,sK5,sK6,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK4,sK5,sK6,X0) )
    | ~ spl12_5 ),
    inference(duplicate_literal_removal,[],[f666])).

fof(f666,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | r1_tmap_1(sK3,sK5,sK6,X0)
        | ~ r1_tmap_1(sK4,sK5,sK6,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3)) )
    | ~ spl12_5 ),
    inference(resolution,[],[f665,f498])).

fof(f498,plain,(
    ! [X1] :
      ( sP1(X1,sK4,sK5,sK6)
      | ~ r1_tmap_1(sK4,sK5,sK6,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK3)) ) ),
    inference(resolution,[],[f493,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP2(X0,X1,X2,X3)
      | ~ r1_tmap_1(X2,X1,X0,X3)
      | sP1(X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r1_tmap_1(X2,X1,X0,X3)
          | ~ sP1(X3,X2,X1,X0) )
        & ( sP1(X3,X2,X1,X0)
          | ~ r1_tmap_1(X2,X1,X0,X3) ) )
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X2,X1,X0,X3] :
      ( ( ( r1_tmap_1(X0,X1,X2,X3)
          | ~ sP1(X3,X0,X1,X2) )
        & ( sP1(X3,X0,X1,X2)
          | ~ r1_tmap_1(X0,X1,X2,X3) ) )
      | ~ sP2(X2,X1,X0,X3) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X2,X1,X0,X3] :
      ( ( r1_tmap_1(X0,X1,X2,X3)
      <=> sP1(X3,X0,X1,X2) )
      | ~ sP2(X2,X1,X0,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f493,plain,(
    ! [X0] :
      ( sP2(sK6,sK5,sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f492,f53])).

fof(f53,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f33])).

fof(f492,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | sP2(sK6,sK5,sK4,X0)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f491,f54])).

fof(f54,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f33])).

fof(f491,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | sP2(sK6,sK5,sK4,X0)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f490,f55])).

fof(f55,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f33])).

fof(f490,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | sP2(sK6,sK5,sK4,X0)
      | ~ l1_pre_topc(sK5)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f489,f58])).

fof(f58,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f33])).

fof(f489,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | sP2(sK6,sK5,sK4,X0)
      | ~ v1_funct_1(sK6)
      | ~ l1_pre_topc(sK5)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f486,f59])).

fof(f59,plain,(
    v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f33])).

fof(f486,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | sP2(sK6,sK5,sK4,X0)
      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK5))
      | ~ v1_funct_1(sK6)
      | ~ l1_pre_topc(sK5)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5) ) ),
    inference(resolution,[],[f361,f60])).

fof(f60,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f33])).

fof(f361,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | sP2(X0,X1,sK4,X2)
      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f360,f50])).

fof(f50,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f360,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | sP2(X0,X1,sK4,X2)
      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | v2_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f359,f51])).

fof(f51,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f359,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | sP2(X0,X1,sK4,X2)
      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(sK4)
      | v2_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f341,f52])).

fof(f52,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f341,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | sP2(X0,X1,sK4,X2)
      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK4)
      | ~ v2_pre_topc(sK4)
      | v2_struct_0(sK4) ) ),
    inference(superposition,[],[f84,f56])).

fof(f56,plain,(
    u1_struct_0(sK3) = u1_struct_0(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP2(X2,X1,X0,X3)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( sP2(X2,X1,X0,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f14,f24,f23,f22])).

fof(f22,plain,(
    ! [X4,X2,X1,X0,X3] :
      ( sP0(X4,X2,X1,X0,X3)
    <=> ? [X5] :
          ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
          & r2_hidden(X3,X5)
          & v3_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f23,plain,(
    ! [X3,X0,X1,X2] :
      ( sP1(X3,X0,X1,X2)
    <=> ! [X4] :
          ( sP0(X4,X2,X1,X0,X3)
          | ~ r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X4)
          | ~ v3_pre_topc(X4,X1)
          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r1_tmap_1(X0,X1,X2,X3)
                  <=> ! [X4] :
                        ( ? [X5] :
                            ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                            & r2_hidden(X3,X5)
                            & v3_pre_topc(X5,X0)
                            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X4)
                        | ~ v3_pre_topc(X4,X1)
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r1_tmap_1(X0,X1,X2,X3)
                  <=> ! [X4] :
                        ( ? [X5] :
                            ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                            & r2_hidden(X3,X5)
                            & v3_pre_topc(X5,X0)
                            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X4)
                        | ~ v3_pre_topc(X4,X1)
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_tmap_1(X0,X1,X2,X3)
                  <=> ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ~ ( ! [X5] :
                                ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
                               => ~ ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                                    & r2_hidden(X3,X5)
                                    & v3_pre_topc(X5,X0) ) )
                            & r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X4)
                            & v3_pre_topc(X4,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tmap_1)).

fof(f665,plain,
    ( ! [X0] :
        ( ~ sP1(X0,sK4,sK5,sK6)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | r1_tmap_1(sK3,sK5,sK6,X0) )
    | ~ spl12_5 ),
    inference(resolution,[],[f664,f365])).

fof(f365,plain,(
    ! [X0] :
      ( ~ sP1(X0,sK3,sK5,sK6)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | r1_tmap_1(sK3,sK5,sK6,X0) ) ),
    inference(resolution,[],[f350,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP2(X0,X1,X2,X3)
      | ~ sP1(X3,X2,X1,X0)
      | r1_tmap_1(X2,X1,X0,X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f350,plain,(
    ! [X0] :
      ( sP2(sK6,sK5,sK3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f349,f47])).

fof(f47,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f349,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | sP2(sK6,sK5,sK3,X0)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f348,f48])).

fof(f48,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f348,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | sP2(sK6,sK5,sK3,X0)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f347,f49])).

fof(f49,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f347,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | sP2(sK6,sK5,sK3,X0)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f346,f53])).

fof(f346,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | sP2(sK6,sK5,sK3,X0)
      | v2_struct_0(sK5)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f345,f54])).

fof(f345,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | sP2(sK6,sK5,sK3,X0)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f344,f55])).

fof(f344,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | sP2(sK6,sK5,sK3,X0)
      | ~ l1_pre_topc(sK5)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f343,f58])).

fof(f343,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | sP2(sK6,sK5,sK3,X0)
      | ~ v1_funct_1(sK6)
      | ~ l1_pre_topc(sK5)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f338,f59])).

fof(f338,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | sP2(sK6,sK5,sK3,X0)
      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK5))
      | ~ v1_funct_1(sK6)
      | ~ l1_pre_topc(sK5)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f84,f60])).

fof(f664,plain,
    ( ! [X6,X7,X5] :
        ( sP1(X5,sK3,X6,X7)
        | ~ sP1(X5,sK4,X6,X7) )
    | ~ spl12_5 ),
    inference(subsumption_resolution,[],[f663,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK10(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ( ~ sP0(sK10(X0,X1,X2,X3),X3,X2,X1,X0)
          & r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X0),sK10(X0,X1,X2,X3))
          & v3_pre_topc(sK10(X0,X1,X2,X3),X2)
          & m1_subset_1(sK10(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ! [X5] :
            ( sP0(X5,X3,X2,X1,X0)
            | ~ r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X0),X5)
            | ~ v3_pre_topc(X5,X2)
            | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f38,f39])).

% (19739)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% (19742)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% (19741)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% (19734)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% (19740)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% (19731)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% (19731)Refutation not found, incomplete strategy% (19731)------------------------------
% (19731)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19731)Termination reason: Refutation not found, incomplete strategy

% (19731)Memory used [KB]: 6268
% (19731)Time elapsed: 0.142 s
% (19731)------------------------------
% (19731)------------------------------
fof(f39,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ sP0(X4,X3,X2,X1,X0)
          & r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X0),X4)
          & v3_pre_topc(X4,X2)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( ~ sP0(sK10(X0,X1,X2,X3),X3,X2,X1,X0)
        & r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X0),sK10(X0,X1,X2,X3))
        & v3_pre_topc(sK10(X0,X1,X2,X3),X2)
        & m1_subset_1(sK10(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ? [X4] :
            ( ~ sP0(X4,X3,X2,X1,X0)
            & r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X0),X4)
            & v3_pre_topc(X4,X2)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ! [X5] :
            ( sP0(X5,X3,X2,X1,X0)
            | ~ r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X0),X5)
            | ~ v3_pre_topc(X5,X2)
            | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X3,X0,X1,X2] :
      ( ( sP1(X3,X0,X1,X2)
        | ? [X4] :
            ( ~ sP0(X4,X2,X1,X0,X3)
            & r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X4)
            & v3_pre_topc(X4,X1)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X4] :
            ( sP0(X4,X2,X1,X0,X3)
            | ~ r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X4)
            | ~ v3_pre_topc(X4,X1)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP1(X3,X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f663,plain,
    ( ! [X6,X7,X5] :
        ( ~ m1_subset_1(sK10(X5,sK3,X6,X7),k1_zfmisc_1(u1_struct_0(X6)))
        | ~ sP1(X5,sK4,X6,X7)
        | sP1(X5,sK3,X6,X7) )
    | ~ spl12_5 ),
    inference(subsumption_resolution,[],[f658,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(sK10(X0,X1,X2,X3),X2)
      | sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f658,plain,
    ( ! [X6,X7,X5] :
        ( ~ v3_pre_topc(sK10(X5,sK3,X6,X7),X6)
        | ~ m1_subset_1(sK10(X5,sK3,X6,X7),k1_zfmisc_1(u1_struct_0(X6)))
        | ~ sP1(X5,sK4,X6,X7)
        | sP1(X5,sK3,X6,X7) )
    | ~ spl12_5 ),
    inference(resolution,[],[f620,f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X0),sK10(X0,X1,X2,X3))
      | sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f620,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(k3_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,X2),X3)
        | ~ v3_pre_topc(X3,X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ sP1(X2,sK4,X0,X1) )
    | ~ spl12_5 ),
    inference(subsumption_resolution,[],[f319,f608])).

fof(f608,plain,
    ( ! [X6,X4,X7,X5] : ~ sP0(X4,X5,X6,sK4,X7)
    | ~ spl12_5 ),
    inference(subsumption_resolution,[],[f226,f127])).

fof(f127,plain,
    ( ! [X0] : ~ r2_hidden(X0,u1_pre_topc(sK4))
    | ~ spl12_5 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl12_5
  <=> ! [X0] : ~ r2_hidden(X0,u1_pre_topc(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).

fof(f226,plain,(
    ! [X6,X4,X7,X5] :
      ( r2_hidden(sK11(X4,X5,X6,sK4,X7),u1_pre_topc(sK4))
      | ~ sP0(X4,X5,X6,sK4,X7) ) ),
    inference(subsumption_resolution,[],[f220,f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v3_pre_topc(sK11(X0,X1,X2,X3,X4),X3)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ! [X5] :
            ( ~ r1_tarski(k7_relset_1(u1_struct_0(X3),u1_struct_0(X2),X1,X5),X0)
            | ~ r2_hidden(X4,X5)
            | ~ v3_pre_topc(X5,X3)
            | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) ) )
      & ( ( r1_tarski(k7_relset_1(u1_struct_0(X3),u1_struct_0(X2),X1,sK11(X0,X1,X2,X3,X4)),X0)
          & r2_hidden(X4,sK11(X0,X1,X2,X3,X4))
          & v3_pre_topc(sK11(X0,X1,X2,X3,X4),X3)
          & m1_subset_1(sK11(X0,X1,X2,X3,X4),k1_zfmisc_1(u1_struct_0(X3))) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f42,f43])).

fof(f43,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r1_tarski(k7_relset_1(u1_struct_0(X3),u1_struct_0(X2),X1,X6),X0)
          & r2_hidden(X4,X6)
          & v3_pre_topc(X6,X3)
          & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X3))) )
     => ( r1_tarski(k7_relset_1(u1_struct_0(X3),u1_struct_0(X2),X1,sK11(X0,X1,X2,X3,X4)),X0)
        & r2_hidden(X4,sK11(X0,X1,X2,X3,X4))
        & v3_pre_topc(sK11(X0,X1,X2,X3,X4),X3)
        & m1_subset_1(sK11(X0,X1,X2,X3,X4),k1_zfmisc_1(u1_struct_0(X3))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ! [X5] :
            ( ~ r1_tarski(k7_relset_1(u1_struct_0(X3),u1_struct_0(X2),X1,X5),X0)
            | ~ r2_hidden(X4,X5)
            | ~ v3_pre_topc(X5,X3)
            | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) ) )
      & ( ? [X6] :
            ( r1_tarski(k7_relset_1(u1_struct_0(X3),u1_struct_0(X2),X1,X6),X0)
            & r2_hidden(X4,X6)
            & v3_pre_topc(X6,X3)
            & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X3))) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X4,X2,X1,X0,X3] :
      ( ( sP0(X4,X2,X1,X0,X3)
        | ! [X5] :
            ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
            | ~ r2_hidden(X3,X5)
            | ~ v3_pre_topc(X5,X0)
            | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ? [X5] :
            ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
            & r2_hidden(X3,X5)
            & v3_pre_topc(X5,X0)
            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X4,X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f220,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ sP0(X4,X5,X6,sK4,X7)
      | ~ v3_pre_topc(sK11(X4,X5,X6,sK4,X7),sK4)
      | r2_hidden(sK11(X4,X5,X6,sK4,X7),u1_pre_topc(sK4)) ) ),
    inference(resolution,[],[f217,f146])).

fof(f146,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v3_pre_topc(X0,sK4)
      | r2_hidden(X0,u1_pre_topc(sK4)) ) ),
    inference(subsumption_resolution,[],[f145,f52])).

fof(f145,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v3_pre_topc(X0,sK4)
      | r2_hidden(X0,u1_pre_topc(sK4))
      | ~ l1_pre_topc(sK4) ) ),
    inference(superposition,[],[f70,f56])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f217,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK11(X0,X1,X2,sK4,X3),k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ sP0(X0,X1,X2,sK4,X3) ) ),
    inference(superposition,[],[f79,f56])).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK11(X0,X1,X2,X3,X4),k1_zfmisc_1(u1_struct_0(X3)))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f319,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k3_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X1,X2),X3)
      | sP0(X3,X1,X0,sK4,X2)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP1(X2,sK4,X0,X1) ) ),
    inference(superposition,[],[f74,f56])).

fof(f74,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X0),X5)
      | sP0(X5,X3,X2,X1,X0)
      | ~ v3_pre_topc(X5,X2)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f645,plain,(
    ~ spl12_11 ),
    inference(avatar_contradiction_clause,[],[f644])).

fof(f644,plain,
    ( $false
    | ~ spl12_11 ),
    inference(subsumption_resolution,[],[f643,f65])).

fof(f643,plain,
    ( ~ m1_subset_1(sK8,u1_struct_0(sK3))
    | ~ spl12_11 ),
    inference(resolution,[],[f376,f69])).

fof(f376,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK3,sK5,sK6,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3)) )
    | ~ spl12_11 ),
    inference(avatar_component_clause,[],[f375])).

fof(f375,plain,
    ( spl12_11
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | r1_tmap_1(sK3,sK5,sK6,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).

fof(f601,plain,
    ( spl12_13
    | spl12_10 ),
    inference(avatar_split_clause,[],[f391,f371,f574])).

fof(f371,plain,
    ( spl12_10
  <=> v1_xboole_0(u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f391,plain,
    ( sK6 = sK7
    | spl12_10 ),
    inference(subsumption_resolution,[],[f390,f373])).

fof(f373,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK5))
    | spl12_10 ),
    inference(avatar_component_clause,[],[f371])).

fof(f390,plain,
    ( sK6 = sK7
    | v1_xboole_0(u1_struct_0(sK5)) ),
    inference(subsumption_resolution,[],[f389,f58])).

fof(f389,plain,
    ( sK6 = sK7
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(u1_struct_0(sK5)) ),
    inference(subsumption_resolution,[],[f388,f59])).

fof(f388,plain,
    ( sK6 = sK7
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK5))
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(u1_struct_0(sK5)) ),
    inference(subsumption_resolution,[],[f387,f60])).

fof(f387,plain,
    ( sK6 = sK7
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK5))
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(u1_struct_0(sK5)) ),
    inference(subsumption_resolution,[],[f386,f61])).

fof(f61,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f33])).

fof(f386,plain,
    ( sK6 = sK7
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK5))
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(u1_struct_0(sK5)) ),
    inference(subsumption_resolution,[],[f385,f97])).

fof(f97,plain,(
    v1_funct_2(sK7,u1_struct_0(sK3),u1_struct_0(sK5)) ),
    inference(forward_demodulation,[],[f62,f56])).

fof(f62,plain,(
    v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f33])).

fof(f385,plain,
    ( sK6 = sK7
    | ~ v1_funct_2(sK7,u1_struct_0(sK3),u1_struct_0(sK5))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK5))
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(u1_struct_0(sK5)) ),
    inference(subsumption_resolution,[],[f384,f98])).

fof(f98,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK5)))) ),
    inference(forward_demodulation,[],[f63,f56])).

fof(f63,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f33])).

fof(f384,plain,
    ( sK6 = sK7
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK3),u1_struct_0(sK5))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK5))
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(u1_struct_0(sK5)) ),
    inference(duplicate_literal_removal,[],[f381])).

fof(f381,plain,
    ( sK6 = sK7
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK3),u1_struct_0(sK5))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK5))
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(u1_struct_0(sK5))
    | v1_xboole_0(u1_struct_0(sK5)) ),
    inference(resolution,[],[f90,f99])).

fof(f99,plain,(
    r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK5),u1_struct_0(sK3),u1_struct_0(sK5),sK6,sK7) ),
    inference(forward_demodulation,[],[f64,f56])).

fof(f64,plain,(
    r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK5),u1_struct_0(sK4),u1_struct_0(sK5),sK6,sK7) ),
    inference(cnf_transformation,[],[f33])).

fof(f90,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
      | X4 = X5
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
          | X4 != X5 )
        & ( X4 = X5
          | ~ r1_funct_2(X0,X1,X2,X3,X4,X5) ) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

fof(f565,plain,
    ( spl12_4
    | spl12_10 ),
    inference(avatar_contradiction_clause,[],[f564])).

fof(f564,plain,
    ( $false
    | spl12_4
    | spl12_10 ),
    inference(subsumption_resolution,[],[f563,f393])).

fof(f393,plain,
    ( r1_tmap_1(sK4,sK5,sK6,sK8)
    | spl12_10 ),
    inference(backward_demodulation,[],[f96,f391])).

fof(f563,plain,
    ( ~ r1_tmap_1(sK4,sK5,sK6,sK8)
    | spl12_4 ),
    inference(subsumption_resolution,[],[f562,f65])).

fof(f562,plain,
    ( ~ m1_subset_1(sK8,u1_struct_0(sK3))
    | ~ r1_tmap_1(sK4,sK5,sK6,sK8)
    | spl12_4 ),
    inference(resolution,[],[f561,f69])).

fof(f561,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK3,sK5,sK6,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK4,sK5,sK6,X0) )
    | spl12_4 ),
    inference(duplicate_literal_removal,[],[f558])).

fof(f558,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | r1_tmap_1(sK3,sK5,sK6,X0)
        | ~ r1_tmap_1(sK4,sK5,sK6,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3)) )
    | spl12_4 ),
    inference(resolution,[],[f557,f498])).

fof(f557,plain,
    ( ! [X0] :
        ( ~ sP1(X0,sK4,sK5,sK6)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | r1_tmap_1(sK3,sK5,sK6,X0) )
    | spl12_4 ),
    inference(resolution,[],[f551,f365])).

fof(f551,plain,
    ( ! [X6,X7,X5] :
        ( sP1(X5,sK3,X6,X7)
        | ~ sP1(X5,sK4,X6,X7) )
    | spl12_4 ),
    inference(subsumption_resolution,[],[f460,f548])).

fof(f548,plain,
    ( ! [X2,X0,X1] :
        ( ~ sP0(sK10(X0,sK3,X1,X2),X2,X1,sK4,X0)
        | sP1(X0,sK3,X1,X2) )
    | spl12_4 ),
    inference(resolution,[],[f547,f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(sK10(X0,X1,X2,X3),X3,X2,X1,X0)
      | sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f547,plain,
    ( ! [X2,X0,X3,X1] :
        ( sP0(X0,X1,X2,sK3,X3)
        | ~ sP0(X0,X1,X2,sK4,X3) )
    | spl12_4 ),
    inference(duplicate_literal_removal,[],[f545])).

fof(f545,plain,
    ( ! [X2,X0,X3,X1] :
        ( sP0(X0,X1,X2,sK3,X3)
        | ~ sP0(X0,X1,X2,sK4,X3)
        | ~ sP0(X0,X1,X2,sK4,X3) )
    | spl12_4 ),
    inference(resolution,[],[f544,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X4,sK11(X0,X1,X2,X3,X4))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f544,plain,
    ( ! [X6,X10,X8,X7,X9] :
        ( ~ r2_hidden(X9,sK11(X6,X7,X8,sK4,X10))
        | sP0(X6,X7,X8,sK3,X9)
        | ~ sP0(X6,X7,X8,sK4,X10) )
    | spl12_4 ),
    inference(subsumption_resolution,[],[f302,f337])).

fof(f337,plain,
    ( ! [X2,X0,X3,X1] :
        ( v3_pre_topc(sK11(X0,X1,X2,sK4,X3),sK3)
        | ~ sP0(X0,X1,X2,sK4,X3) )
    | spl12_4 ),
    inference(subsumption_resolution,[],[f336,f238])).

fof(f238,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK11(X0,X1,X2,sK4,X3),u1_pre_topc(sK3))
      | ~ sP0(X0,X1,X2,sK4,X3) ) ),
    inference(resolution,[],[f226,f132])).

fof(f132,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_pre_topc(sK4))
      | m1_subset_1(X0,u1_pre_topc(sK3)) ) ),
    inference(resolution,[],[f131,f57])).

fof(f57,plain,(
    r1_tarski(u1_pre_topc(sK4),u1_pre_topc(sK3)) ),
    inference(cnf_transformation,[],[f33])).

fof(f131,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X4,X3)
      | ~ r2_hidden(X2,X4)
      | m1_subset_1(X2,X3) ) ),
    inference(resolution,[],[f88,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f336,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ sP0(X0,X1,X2,sK4,X3)
        | v3_pre_topc(sK11(X0,X1,X2,sK4,X3),sK3)
        | ~ m1_subset_1(sK11(X0,X1,X2,sK4,X3),u1_pre_topc(sK3)) )
    | spl12_4 ),
    inference(subsumption_resolution,[],[f335,f124])).

fof(f124,plain,
    ( ~ v1_xboole_0(u1_pre_topc(sK3))
    | spl12_4 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl12_4
  <=> v1_xboole_0(u1_pre_topc(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f335,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,sK4,X3)
      | v3_pre_topc(sK11(X0,X1,X2,sK4,X3),sK3)
      | v1_xboole_0(u1_pre_topc(sK3))
      | ~ m1_subset_1(sK11(X0,X1,X2,sK4,X3),u1_pre_topc(sK3)) ) ),
    inference(resolution,[],[f227,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f227,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r2_hidden(sK11(X8,X9,X10,sK4,X11),u1_pre_topc(sK3))
      | ~ sP0(X8,X9,X10,sK4,X11)
      | v3_pre_topc(sK11(X8,X9,X10,sK4,X11),sK3) ) ),
    inference(subsumption_resolution,[],[f221,f49])).

fof(f221,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ sP0(X8,X9,X10,sK4,X11)
      | ~ r2_hidden(sK11(X8,X9,X10,sK4,X11),u1_pre_topc(sK3))
      | v3_pre_topc(sK11(X8,X9,X10,sK4,X11),sK3)
      | ~ l1_pre_topc(sK3) ) ),
    inference(resolution,[],[f217,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f302,plain,(
    ! [X6,X10,X8,X7,X9] :
      ( sP0(X6,X7,X8,sK3,X9)
      | ~ r2_hidden(X9,sK11(X6,X7,X8,sK4,X10))
      | ~ v3_pre_topc(sK11(X6,X7,X8,sK4,X10),sK3)
      | ~ sP0(X6,X7,X8,sK4,X10) ) ),
    inference(subsumption_resolution,[],[f295,f217])).

fof(f295,plain,(
    ! [X6,X10,X8,X7,X9] :
      ( sP0(X6,X7,X8,sK3,X9)
      | ~ r2_hidden(X9,sK11(X6,X7,X8,sK4,X10))
      | ~ v3_pre_topc(sK11(X6,X7,X8,sK4,X10),sK3)
      | ~ m1_subset_1(sK11(X6,X7,X8,sK4,X10),k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ sP0(X6,X7,X8,sK4,X10) ) ),
    inference(resolution,[],[f83,f268])).

fof(f268,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k7_relset_1(u1_struct_0(sK3),u1_struct_0(X0),X1,sK11(X2,X1,X0,sK4,X3)),X2)
      | ~ sP0(X2,X1,X0,sK4,X3) ) ),
    inference(superposition,[],[f82,f56])).

fof(f82,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_tarski(k7_relset_1(u1_struct_0(X3),u1_struct_0(X2),X1,sK11(X0,X1,X2,X3,X4)),X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_tarski(k7_relset_1(u1_struct_0(X3),u1_struct_0(X2),X1,X5),X0)
      | sP0(X0,X1,X2,X3,X4)
      | ~ r2_hidden(X4,X5)
      | ~ v3_pre_topc(X5,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f460,plain,(
    ! [X6,X7,X5] :
      ( sP0(sK10(X5,sK3,X6,X7),X7,X6,sK4,X5)
      | ~ sP1(X5,sK4,X6,X7)
      | sP1(X5,sK3,X6,X7) ) ),
    inference(subsumption_resolution,[],[f459,f75])).

fof(f459,plain,(
    ! [X6,X7,X5] :
      ( sP0(sK10(X5,sK3,X6,X7),X7,X6,sK4,X5)
      | ~ m1_subset_1(sK10(X5,sK3,X6,X7),k1_zfmisc_1(u1_struct_0(X6)))
      | ~ sP1(X5,sK4,X6,X7)
      | sP1(X5,sK3,X6,X7) ) ),
    inference(subsumption_resolution,[],[f454,f76])).

fof(f454,plain,(
    ! [X6,X7,X5] :
      ( sP0(sK10(X5,sK3,X6,X7),X7,X6,sK4,X5)
      | ~ v3_pre_topc(sK10(X5,sK3,X6,X7),X6)
      | ~ m1_subset_1(sK10(X5,sK3,X6,X7),k1_zfmisc_1(u1_struct_0(X6)))
      | ~ sP1(X5,sK4,X6,X7)
      | sP1(X5,sK3,X6,X7) ) ),
    inference(resolution,[],[f319,f77])).

fof(f377,plain,
    ( ~ spl12_10
    | spl12_11 ),
    inference(avatar_split_clause,[],[f369,f375,f371])).

fof(f369,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | r1_tmap_1(sK3,sK5,sK6,X0)
      | ~ v1_xboole_0(u1_struct_0(sK5)) ) ),
    inference(resolution,[],[f365,f246])).

fof(f246,plain,(
    ! [X6,X4,X5,X3] :
      ( sP1(X3,X4,X5,X6)
      | ~ v1_xboole_0(u1_struct_0(X5)) ) ),
    inference(duplicate_literal_removal,[],[f243])).

fof(f243,plain,(
    ! [X6,X4,X5,X3] :
      ( sP1(X3,X4,X5,X6)
      | ~ v1_xboole_0(u1_struct_0(X5))
      | sP1(X3,X4,X5,X6) ) ),
    inference(resolution,[],[f77,f158])).

fof(f158,plain,(
    ! [X23,X21,X19,X22,X20] :
      ( ~ r2_hidden(X23,sK10(X19,X20,X21,X22))
      | ~ v1_xboole_0(u1_struct_0(X21))
      | sP1(X19,X20,X21,X22) ) ),
    inference(resolution,[],[f75,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f128,plain,
    ( ~ spl12_4
    | spl12_5 ),
    inference(avatar_split_clause,[],[f118,f126,f122])).

fof(f118,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_pre_topc(sK4))
      | ~ v1_xboole_0(u1_pre_topc(sK3)) ) ),
    inference(resolution,[],[f105,f57])).

fof(f105,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X4,X2)
      | ~ r2_hidden(X3,X4)
      | ~ v1_xboole_0(X2) ) ),
    inference(resolution,[],[f89,f87])).

%------------------------------------------------------------------------------
