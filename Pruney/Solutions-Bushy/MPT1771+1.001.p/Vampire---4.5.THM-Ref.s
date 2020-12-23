%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1771+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:30 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 539 expanded)
%              Number of leaves         :   24 ( 269 expanded)
%              Depth                    :   32
%              Number of atoms          : 1154 (8287 expanded)
%              Number of equality atoms :   37 ( 570 expanded)
%              Maximal formula depth    :   41 (   9 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f345,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f102,f103,f140,f148,f151,f316,f324,f344])).

fof(f344,plain,
    ( ~ spl9_1
    | ~ spl9_5
    | ~ spl9_7 ),
    inference(avatar_contradiction_clause,[],[f343])).

fof(f343,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_5
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f342,f95])).

fof(f95,plain,
    ( l1_pre_topc(sK5)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl9_1
  <=> l1_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f342,plain,
    ( ~ l1_pre_topc(sK5)
    | ~ spl9_5
    | ~ spl9_7 ),
    inference(resolution,[],[f341,f66])).

fof(f66,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f341,plain,
    ( ~ l1_struct_0(sK5)
    | ~ spl9_5
    | ~ spl9_7 ),
    inference(resolution,[],[f331,f139])).

fof(f139,plain,
    ( ! [X0] :
        ( sP0(sK3,X0,sK6,sK2)
        | ~ l1_struct_0(X0) )
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl9_5
  <=> ! [X0] :
        ( ~ l1_struct_0(X0)
        | sP0(sK3,X0,sK6,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f331,plain,
    ( ~ sP0(sK3,sK5,sK6,sK2)
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f330,f61])).

fof(f61,plain,(
    m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ~ r1_tmap_1(sK4,sK3,k2_tmap_1(sK2,sK3,sK6,sK4),sK8)
    & r1_tmap_1(sK5,sK3,k2_tmap_1(sK2,sK3,sK6,sK5),sK7)
    & sK7 = sK8
    & m1_subset_1(sK8,u1_struct_0(sK4))
    & m1_subset_1(sK7,u1_struct_0(sK5))
    & m1_pre_topc(sK4,sK5)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK6)
    & m1_pre_topc(sK5,sK2)
    & ~ v2_struct_0(sK5)
    & m1_pre_topc(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f13,f40,f39,f38,f37,f36,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6)
                                & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
                                & X5 = X6
                                & m1_subset_1(X6,u1_struct_0(X2)) )
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & m1_pre_topc(X2,X3)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X2,X1,k2_tmap_1(sK2,X1,X4,X2),X6)
                              & r1_tmap_1(X3,X1,k2_tmap_1(sK2,X1,X4,X3),X5)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK2)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ~ r1_tmap_1(X2,X1,k2_tmap_1(sK2,X1,X4,X2),X6)
                            & r1_tmap_1(X3,X1,k2_tmap_1(sK2,X1,X4,X3),X5)
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_pre_topc(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                    & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK2)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK2)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ r1_tmap_1(X2,sK3,k2_tmap_1(sK2,sK3,X4,X2),X6)
                          & r1_tmap_1(X3,sK3,k2_tmap_1(sK2,sK3,X4,X3),X5)
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & m1_pre_topc(X2,X3)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                  & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK2)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK2)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ~ r1_tmap_1(X2,sK3,k2_tmap_1(sK2,sK3,X4,X2),X6)
                        & r1_tmap_1(X3,sK3,k2_tmap_1(sK2,sK3,X4,X3),X5)
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(X2)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_pre_topc(X2,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK2)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK2)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ~ r1_tmap_1(sK4,sK3,k2_tmap_1(sK2,sK3,X4,sK4),X6)
                      & r1_tmap_1(X3,sK3,k2_tmap_1(sK2,sK3,X4,X3),X5)
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(sK4)) )
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & m1_pre_topc(sK4,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
              & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK2)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK4,sK2)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ r1_tmap_1(sK4,sK3,k2_tmap_1(sK2,sK3,X4,sK4),X6)
                    & r1_tmap_1(X3,sK3,k2_tmap_1(sK2,sK3,X4,X3),X5)
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(sK4)) )
                & m1_subset_1(X5,u1_struct_0(X3)) )
            & m1_pre_topc(sK4,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
            & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK2)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ r1_tmap_1(sK4,sK3,k2_tmap_1(sK2,sK3,X4,sK4),X6)
                  & r1_tmap_1(sK5,sK3,k2_tmap_1(sK2,sK3,X4,sK5),X5)
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(sK4)) )
              & m1_subset_1(X5,u1_struct_0(sK5)) )
          & m1_pre_topc(sK4,sK5)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
          & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK5,sK2)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ~ r1_tmap_1(sK4,sK3,k2_tmap_1(sK2,sK3,X4,sK4),X6)
                & r1_tmap_1(sK5,sK3,k2_tmap_1(sK2,sK3,X4,sK5),X5)
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(sK4)) )
            & m1_subset_1(X5,u1_struct_0(sK5)) )
        & m1_pre_topc(sK4,sK5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ~ r1_tmap_1(sK4,sK3,k2_tmap_1(sK2,sK3,sK6,sK4),X6)
              & r1_tmap_1(sK5,sK3,k2_tmap_1(sK2,sK3,sK6,sK5),X5)
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(sK4)) )
          & m1_subset_1(X5,u1_struct_0(sK5)) )
      & m1_pre_topc(sK4,sK5)
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      & v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ~ r1_tmap_1(sK4,sK3,k2_tmap_1(sK2,sK3,sK6,sK4),X6)
            & r1_tmap_1(sK5,sK3,k2_tmap_1(sK2,sK3,sK6,sK5),X5)
            & X5 = X6
            & m1_subset_1(X6,u1_struct_0(sK4)) )
        & m1_subset_1(X5,u1_struct_0(sK5)) )
   => ( ? [X6] :
          ( ~ r1_tmap_1(sK4,sK3,k2_tmap_1(sK2,sK3,sK6,sK4),X6)
          & r1_tmap_1(sK5,sK3,k2_tmap_1(sK2,sK3,sK6,sK5),sK7)
          & sK7 = X6
          & m1_subset_1(X6,u1_struct_0(sK4)) )
      & m1_subset_1(sK7,u1_struct_0(sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X6] :
        ( ~ r1_tmap_1(sK4,sK3,k2_tmap_1(sK2,sK3,sK6,sK4),X6)
        & r1_tmap_1(sK5,sK3,k2_tmap_1(sK2,sK3,sK6,sK5),sK7)
        & sK7 = X6
        & m1_subset_1(X6,u1_struct_0(sK4)) )
   => ( ~ r1_tmap_1(sK4,sK3,k2_tmap_1(sK2,sK3,sK6,sK4),sK8)
      & r1_tmap_1(sK5,sK3,k2_tmap_1(sK2,sK3,sK6,sK5),sK7)
      & sK7 = sK8
      & m1_subset_1(sK8,u1_struct_0(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6)
                              & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6)
                              & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( m1_pre_topc(X2,X3)
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( ( r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
                                      & X5 = X6 )
                                   => r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( ( r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
                                    & X5 = X6 )
                                 => r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_tmap_1)).

fof(f330,plain,
    ( ~ sP0(sK3,sK5,sK6,sK2)
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f329,f60])).

fof(f60,plain,(
    m1_pre_topc(sK4,sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f329,plain,
    ( ~ sP0(sK3,sK5,sK6,sK2)
    | ~ m1_pre_topc(sK4,sK5)
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f328,f56])).

fof(f56,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f328,plain,
    ( ~ sP0(sK3,sK5,sK6,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK5)
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f325,f55])).

fof(f55,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f325,plain,
    ( ~ sP0(sK3,sK5,sK6,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK5)
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ spl9_7 ),
    inference(resolution,[],[f315,f64])).

fof(f64,plain,(
    r1_tmap_1(sK5,sK3,k2_tmap_1(sK2,sK3,sK6,sK5),sK7) ),
    inference(cnf_transformation,[],[f41])).

fof(f315,plain,
    ( ! [X0] :
        ( ~ r1_tmap_1(X0,sK3,k2_tmap_1(sK2,sK3,sK6,X0),sK7)
        | ~ sP0(sK3,X0,sK6,sK2)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK2)
        | ~ m1_pre_topc(sK4,X0)
        | ~ m1_subset_1(sK7,u1_struct_0(X0)) )
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f314])).

fof(f314,plain,
    ( spl9_7
  <=> ! [X0] :
        ( ~ m1_pre_topc(sK4,X0)
        | ~ sP0(sK3,X0,sK6,sK2)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK2)
        | ~ r1_tmap_1(X0,sK3,k2_tmap_1(sK2,sK3,sK6,X0),sK7)
        | ~ m1_subset_1(sK7,u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f324,plain,
    ( ~ spl9_2
    | ~ spl9_5
    | spl9_6 ),
    inference(avatar_contradiction_clause,[],[f323])).

fof(f323,plain,
    ( $false
    | ~ spl9_2
    | ~ spl9_5
    | spl9_6 ),
    inference(subsumption_resolution,[],[f322,f100])).

fof(f100,plain,
    ( l1_pre_topc(sK4)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl9_2
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f322,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ spl9_5
    | spl9_6 ),
    inference(resolution,[],[f321,f66])).

fof(f321,plain,
    ( ~ l1_struct_0(sK4)
    | ~ spl9_5
    | spl9_6 ),
    inference(resolution,[],[f312,f139])).

fof(f312,plain,
    ( ~ sP0(sK3,sK4,sK6,sK2)
    | spl9_6 ),
    inference(avatar_component_clause,[],[f310])).

fof(f310,plain,
    ( spl9_6
  <=> sP0(sK3,sK4,sK6,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f316,plain,
    ( ~ spl9_6
    | spl9_7 ),
    inference(avatar_split_clause,[],[f308,f314,f310])).

fof(f308,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK4,X0)
      | ~ m1_subset_1(sK7,u1_struct_0(X0))
      | ~ r1_tmap_1(X0,sK3,k2_tmap_1(sK2,sK3,sK6,X0),sK7)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ sP0(sK3,sK4,sK6,sK2)
      | ~ sP0(sK3,X0,sK6,sK2) ) ),
    inference(subsumption_resolution,[],[f307,f59])).

fof(f59,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f41])).

fof(f307,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK4,X0)
      | ~ m1_subset_1(sK7,u1_struct_0(X0))
      | ~ r1_tmap_1(X0,sK3,k2_tmap_1(sK2,sK3,sK6,X0),sK7)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      | ~ sP0(sK3,sK4,sK6,sK2)
      | ~ sP0(sK3,X0,sK6,sK2) ) ),
    inference(subsumption_resolution,[],[f306,f57])).

fof(f57,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f41])).

fof(f306,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK4,X0)
      | ~ m1_subset_1(sK7,u1_struct_0(X0))
      | ~ r1_tmap_1(X0,sK3,k2_tmap_1(sK2,sK3,sK6,X0),sK7)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ v1_funct_1(sK6)
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      | ~ sP0(sK3,sK4,sK6,sK2)
      | ~ sP0(sK3,X0,sK6,sK2) ) ),
    inference(subsumption_resolution,[],[f305,f58])).

fof(f58,plain,(
    v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f41])).

fof(f305,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK4,X0)
      | ~ m1_subset_1(sK7,u1_struct_0(X0))
      | ~ r1_tmap_1(X0,sK3,k2_tmap_1(sK2,sK3,sK6,X0),sK7)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK6)
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      | ~ sP0(sK3,sK4,sK6,sK2)
      | ~ sP0(sK3,X0,sK6,sK2) ) ),
    inference(subsumption_resolution,[],[f304,f47])).

fof(f47,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f304,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK4,X0)
      | ~ m1_subset_1(sK7,u1_struct_0(X0))
      | ~ r1_tmap_1(X0,sK3,k2_tmap_1(sK2,sK3,sK6,X0),sK7)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | v2_struct_0(sK2)
      | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK6)
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      | ~ sP0(sK3,sK4,sK6,sK2)
      | ~ sP0(sK3,X0,sK6,sK2) ) ),
    inference(subsumption_resolution,[],[f303,f48])).

fof(f48,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f303,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK4,X0)
      | ~ m1_subset_1(sK7,u1_struct_0(X0))
      | ~ r1_tmap_1(X0,sK3,k2_tmap_1(sK2,sK3,sK6,X0),sK7)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK6)
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      | ~ sP0(sK3,sK4,sK6,sK2)
      | ~ sP0(sK3,X0,sK6,sK2) ) ),
    inference(subsumption_resolution,[],[f302,f49])).

fof(f49,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f302,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK4,X0)
      | ~ m1_subset_1(sK7,u1_struct_0(X0))
      | ~ r1_tmap_1(X0,sK3,k2_tmap_1(sK2,sK3,sK6,X0),sK7)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK6)
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      | ~ sP0(sK3,sK4,sK6,sK2)
      | ~ sP0(sK3,X0,sK6,sK2) ) ),
    inference(subsumption_resolution,[],[f301,f50])).

fof(f50,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f301,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK4,X0)
      | ~ m1_subset_1(sK7,u1_struct_0(X0))
      | ~ r1_tmap_1(X0,sK3,k2_tmap_1(sK2,sK3,sK6,X0),sK7)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK6)
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      | ~ sP0(sK3,sK4,sK6,sK2)
      | ~ sP0(sK3,X0,sK6,sK2) ) ),
    inference(subsumption_resolution,[],[f300,f51])).

fof(f51,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f300,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK4,X0)
      | ~ m1_subset_1(sK7,u1_struct_0(X0))
      | ~ r1_tmap_1(X0,sK3,k2_tmap_1(sK2,sK3,sK6,X0),sK7)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK6)
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      | ~ sP0(sK3,sK4,sK6,sK2)
      | ~ sP0(sK3,X0,sK6,sK2) ) ),
    inference(subsumption_resolution,[],[f299,f52])).

fof(f52,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f299,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK4,X0)
      | ~ m1_subset_1(sK7,u1_struct_0(X0))
      | ~ r1_tmap_1(X0,sK3,k2_tmap_1(sK2,sK3,sK6,X0),sK7)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK6)
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      | ~ sP0(sK3,sK4,sK6,sK2)
      | ~ sP0(sK3,X0,sK6,sK2) ) ),
    inference(subsumption_resolution,[],[f298,f53])).

fof(f53,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f298,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK4,X0)
      | ~ m1_subset_1(sK7,u1_struct_0(X0))
      | ~ r1_tmap_1(X0,sK3,k2_tmap_1(sK2,sK3,sK6,X0),sK7)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK6)
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      | ~ sP0(sK3,sK4,sK6,sK2)
      | ~ sP0(sK3,X0,sK6,sK2) ) ),
    inference(subsumption_resolution,[],[f297,f54])).

fof(f54,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f41])).

% (30030)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
fof(f297,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK4,X0)
      | ~ m1_subset_1(sK7,u1_struct_0(X0))
      | ~ r1_tmap_1(X0,sK3,k2_tmap_1(sK2,sK3,sK6,X0),sK7)
      | ~ m1_pre_topc(sK4,sK2)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK6)
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      | ~ sP0(sK3,sK4,sK6,sK2)
      | ~ sP0(sK3,X0,sK6,sK2) ) ),
    inference(subsumption_resolution,[],[f296,f86])).

fof(f86,plain,(
    m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(forward_demodulation,[],[f62,f63])).

fof(f63,plain,(
    sK7 = sK8 ),
    inference(cnf_transformation,[],[f41])).

fof(f62,plain,(
    m1_subset_1(sK8,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f41])).

fof(f296,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK4,X0)
      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
      | ~ m1_subset_1(sK7,u1_struct_0(X0))
      | ~ r1_tmap_1(X0,sK3,k2_tmap_1(sK2,sK3,sK6,X0),sK7)
      | ~ m1_pre_topc(sK4,sK2)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK6)
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      | ~ sP0(sK3,sK4,sK6,sK2)
      | ~ sP0(sK3,X0,sK6,sK2) ) ),
    inference(resolution,[],[f295,f87])).

fof(f87,plain,(
    ~ r1_tmap_1(sK4,sK3,k2_tmap_1(sK2,sK3,sK6,sK4),sK7) ),
    inference(forward_demodulation,[],[f65,f63])).

fof(f65,plain,(
    ~ r1_tmap_1(sK4,sK3,k2_tmap_1(sK2,sK3,sK6,sK4),sK8) ),
    inference(cnf_transformation,[],[f41])).

fof(f295,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X5,X1,k2_tmap_1(X2,X1,X3,X5),X4)
      | ~ m1_pre_topc(X5,X0)
      | ~ m1_subset_1(X4,u1_struct_0(X5))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
      | ~ m1_pre_topc(X5,X2)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X0,X2)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ sP0(X1,X5,X3,X2)
      | ~ sP0(X1,X0,X3,X2) ) ),
    inference(subsumption_resolution,[],[f294,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) )
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X1,X3,X2,X0] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ sP0(X1,X3,X2,X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X1,X3,X2,X0] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ sP0(X1,X3,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f294,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
      | ~ m1_pre_topc(X5,X0)
      | ~ m1_subset_1(X4,u1_struct_0(X5))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_tmap_1(X5,X1,k2_tmap_1(X2,X1,X3,X5),X4)
      | ~ v1_funct_1(k2_tmap_1(X2,X1,X3,X0))
      | ~ m1_pre_topc(X5,X2)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X0,X2)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ sP0(X1,X5,X3,X2)
      | ~ sP0(X1,X0,X3,X2) ) ),
    inference(subsumption_resolution,[],[f291,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f291,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
      | ~ m1_pre_topc(X5,X0)
      | ~ m1_subset_1(X4,u1_struct_0(X5))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_tmap_1(X5,X1,k2_tmap_1(X2,X1,X3,X5),X4)
      | ~ v1_funct_2(k2_tmap_1(X2,X1,X3,X0),u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(k2_tmap_1(X2,X1,X3,X0))
      | ~ m1_pre_topc(X5,X2)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X0,X2)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ sP0(X1,X5,X3,X2)
      | ~ sP0(X1,X0,X3,X2) ) ),
    inference(resolution,[],[f290,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f290,plain,(
    ! [X30,X28,X26,X29,X27,X25] :
      ( ~ m1_subset_1(k2_tmap_1(X25,X26,X29,X27),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X26))))
      | ~ r1_tmap_1(X27,X26,k2_tmap_1(X25,X26,X29,X27),X30)
      | ~ m1_pre_topc(X28,X27)
      | ~ m1_subset_1(X30,u1_struct_0(X28))
      | ~ m1_subset_1(X30,u1_struct_0(X27))
      | r1_tmap_1(X28,X26,k2_tmap_1(X25,X26,X29,X28),X30)
      | ~ v1_funct_2(k2_tmap_1(X25,X26,X29,X27),u1_struct_0(X27),u1_struct_0(X26))
      | ~ v1_funct_1(k2_tmap_1(X25,X26,X29,X27))
      | ~ m1_pre_topc(X28,X25)
      | v2_struct_0(X28)
      | ~ m1_pre_topc(X27,X25)
      | v2_struct_0(X27)
      | ~ l1_pre_topc(X26)
      | ~ v2_pre_topc(X26)
      | v2_struct_0(X26)
      | ~ l1_pre_topc(X25)
      | ~ v2_pre_topc(X25)
      | v2_struct_0(X25)
      | ~ v1_funct_2(X29,u1_struct_0(X25),u1_struct_0(X26))
      | ~ v1_funct_1(X29)
      | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(X26))))
      | ~ sP0(X26,X28,X29,X25) ) ),
    inference(subsumption_resolution,[],[f285,f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | sP1(X1,X3,X4,X2,X0)
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
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( sP1(X1,X3,X4,X2,X0)
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
    inference(definition_folding,[],[f29,f32])).

fof(f32,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ sP1(X1,X3,X4,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).

fof(f285,plain,(
    ! [X30,X28,X26,X29,X27,X25] :
      ( r1_tmap_1(X28,X26,k2_tmap_1(X25,X26,X29,X28),X30)
      | ~ r1_tmap_1(X27,X26,k2_tmap_1(X25,X26,X29,X27),X30)
      | ~ m1_pre_topc(X28,X27)
      | ~ m1_subset_1(X30,u1_struct_0(X28))
      | ~ m1_subset_1(X30,u1_struct_0(X27))
      | ~ m1_subset_1(k2_tmap_1(X25,X26,X29,X27),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X26))))
      | ~ v1_funct_2(k2_tmap_1(X25,X26,X29,X27),u1_struct_0(X27),u1_struct_0(X26))
      | ~ v1_funct_1(k2_tmap_1(X25,X26,X29,X27))
      | ~ m1_pre_topc(X28,X25)
      | v2_struct_0(X28)
      | ~ m1_pre_topc(X27,X25)
      | v2_struct_0(X27)
      | ~ l1_pre_topc(X26)
      | ~ v2_pre_topc(X26)
      | v2_struct_0(X26)
      | ~ l1_pre_topc(X25)
      | ~ v2_pre_topc(X25)
      | v2_struct_0(X25)
      | ~ v1_funct_2(X29,u1_struct_0(X25),u1_struct_0(X26))
      | ~ v1_funct_1(X29)
      | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(X26))))
      | ~ sP0(X26,X28,X29,X25)
      | ~ sP1(X26,X28,k2_tmap_1(X25,X26,X29,X27),X27,X25) ) ),
    inference(duplicate_literal_removal,[],[f270])).

fof(f270,plain,(
    ! [X30,X28,X26,X29,X27,X25] :
      ( r1_tmap_1(X28,X26,k2_tmap_1(X25,X26,X29,X28),X30)
      | ~ r1_tmap_1(X27,X26,k2_tmap_1(X25,X26,X29,X27),X30)
      | ~ m1_pre_topc(X28,X27)
      | ~ m1_subset_1(X30,u1_struct_0(X28))
      | ~ m1_subset_1(X30,u1_struct_0(X27))
      | ~ m1_subset_1(k2_tmap_1(X25,X26,X29,X27),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X26))))
      | ~ v1_funct_2(k2_tmap_1(X25,X26,X29,X27),u1_struct_0(X27),u1_struct_0(X26))
      | ~ v1_funct_1(k2_tmap_1(X25,X26,X29,X27))
      | ~ m1_pre_topc(X28,X25)
      | v2_struct_0(X28)
      | ~ m1_pre_topc(X27,X25)
      | v2_struct_0(X27)
      | ~ l1_pre_topc(X26)
      | ~ v2_pre_topc(X26)
      | v2_struct_0(X26)
      | ~ l1_pre_topc(X25)
      | ~ v2_pre_topc(X25)
      | v2_struct_0(X25)
      | ~ v1_funct_2(X29,u1_struct_0(X25),u1_struct_0(X26))
      | ~ v1_funct_1(X29)
      | ~ m1_pre_topc(X27,X25)
      | v2_struct_0(X27)
      | ~ m1_pre_topc(X28,X25)
      | v2_struct_0(X28)
      | ~ l1_pre_topc(X26)
      | ~ v2_pre_topc(X26)
      | v2_struct_0(X26)
      | ~ l1_pre_topc(X25)
      | ~ v2_pre_topc(X25)
      | v2_struct_0(X25)
      | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(X26))))
      | ~ m1_pre_topc(X28,X27)
      | ~ sP0(X26,X28,X29,X25)
      | ~ sP1(X26,X28,k2_tmap_1(X25,X26,X29,X27),X27,X25) ) ),
    inference(superposition,[],[f83,f264])).

fof(f264,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_tmap_1(X1,X2,X0,X4) = k3_tmap_1(X1,X2,X3,X4,k2_tmap_1(X1,X2,X0,X3))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X4,X1)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ m1_pre_topc(X4,X3)
      | ~ sP0(X2,X4,X0,X1)
      | ~ sP1(X2,X4,k2_tmap_1(X1,X2,X0,X3),X3,X1) ) ),
    inference(subsumption_resolution,[],[f263,f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k3_tmap_1(X4,X0,X3,X1,X2))
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k3_tmap_1(X4,X0,X3,X1,X2)) )
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ sP1(X1,X3,X4,X2,X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f263,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X4,X1)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | k2_tmap_1(X1,X2,X0,X4) = k3_tmap_1(X1,X2,X3,X4,k2_tmap_1(X1,X2,X0,X3))
      | ~ m1_pre_topc(X4,X3)
      | ~ v1_funct_1(k3_tmap_1(X1,X2,X3,X4,k2_tmap_1(X1,X2,X0,X3)))
      | ~ sP0(X2,X4,X0,X1)
      | ~ sP1(X2,X4,k2_tmap_1(X1,X2,X0,X3),X3,X1) ) ),
    inference(subsumption_resolution,[],[f262,f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0))
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f262,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X4,X1)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | k2_tmap_1(X1,X2,X0,X4) = k3_tmap_1(X1,X2,X3,X4,k2_tmap_1(X1,X2,X0,X3))
      | ~ m1_pre_topc(X4,X3)
      | ~ v1_funct_2(k3_tmap_1(X1,X2,X3,X4,k2_tmap_1(X1,X2,X0,X3)),u1_struct_0(X4),u1_struct_0(X2))
      | ~ v1_funct_1(k3_tmap_1(X1,X2,X3,X4,k2_tmap_1(X1,X2,X0,X3)))
      | ~ sP0(X2,X4,X0,X1)
      | ~ sP1(X2,X4,k2_tmap_1(X1,X2,X0,X3),X3,X1) ) ),
    inference(resolution,[],[f242,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f242,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k3_tmap_1(X3,X4,X1,X0,k2_tmap_1(X3,X4,X2,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X4))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4))))
      | ~ v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(X4))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X3)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,X3)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | k2_tmap_1(X3,X4,X2,X0) = k3_tmap_1(X3,X4,X1,X0,k2_tmap_1(X3,X4,X2,X1))
      | ~ m1_pre_topc(X0,X1)
      | ~ v1_funct_2(k3_tmap_1(X3,X4,X1,X0,k2_tmap_1(X3,X4,X2,X1)),u1_struct_0(X0),u1_struct_0(X4))
      | ~ v1_funct_1(k3_tmap_1(X3,X4,X1,X0,k2_tmap_1(X3,X4,X2,X1)))
      | ~ sP0(X4,X0,X2,X3) ) ),
    inference(resolution,[],[f68,f159])).

fof(f159,plain,(
    ! [X4,X2,X5,X3,X1] :
      ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,k2_tmap_1(X4,X2,X5,X1))
      | k2_tmap_1(X4,X2,X5,X1) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X3)
      | ~ sP0(X2,X1,X5,X4) ) ),
    inference(subsumption_resolution,[],[f158,f71])).

fof(f158,plain,(
    ! [X4,X2,X5,X3,X1] :
      ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,k2_tmap_1(X4,X2,X5,X1))
      | k2_tmap_1(X4,X2,X5,X1) = X3
      | ~ v1_funct_1(k2_tmap_1(X4,X2,X5,X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X3)
      | ~ sP0(X2,X1,X5,X4) ) ),
    inference(subsumption_resolution,[],[f153,f72])).

fof(f153,plain,(
    ! [X4,X2,X5,X3,X1] :
      ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,k2_tmap_1(X4,X2,X5,X1))
      | k2_tmap_1(X4,X2,X5,X1) = X3
      | ~ v1_funct_2(k2_tmap_1(X4,X2,X5,X1),u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(k2_tmap_1(X4,X2,X5,X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X3)
      | ~ sP0(X2,X1,X5,X4) ) ),
    inference(resolution,[],[f75,f73])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
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
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tmap_1)).

fof(f83,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ r1_tmap_1(X2,X1,X4,X6)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
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
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ r1_tmap_1(X2,X1,X4,X5)
      | ~ m1_pre_topc(X3,X2)
      | X5 != X6
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
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
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( r1_tmap_1(X2,X1,X4,X5)
                                  & m1_pre_topc(X3,X2)
                                  & X5 = X6 )
                               => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tmap_1)).

fof(f151,plain,(
    spl9_4 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | spl9_4 ),
    inference(subsumption_resolution,[],[f149,f52])).

fof(f149,plain,
    ( ~ l1_pre_topc(sK3)
    | spl9_4 ),
    inference(resolution,[],[f136,f66])).

fof(f136,plain,
    ( ~ l1_struct_0(sK3)
    | spl9_4 ),
    inference(avatar_component_clause,[],[f134])).

% (30043)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
fof(f134,plain,
    ( spl9_4
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f148,plain,(
    spl9_3 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | spl9_3 ),
    inference(subsumption_resolution,[],[f146,f49])).

fof(f146,plain,
    ( ~ l1_pre_topc(sK2)
    | spl9_3 ),
    inference(resolution,[],[f132,f66])).

fof(f132,plain,
    ( ~ l1_struct_0(sK2)
    | spl9_3 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl9_3
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f140,plain,
    ( ~ spl9_3
    | ~ spl9_4
    | spl9_5 ),
    inference(avatar_split_clause,[],[f128,f138,f134,f130])).

fof(f128,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | sP0(sK3,X0,sK6,sK2)
      | ~ l1_struct_0(sK3)
      | ~ l1_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f127,f57])).

fof(f127,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | sP0(sK3,X0,sK6,sK2)
      | ~ v1_funct_1(sK6)
      | ~ l1_struct_0(sK3)
      | ~ l1_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f123,f58])).

fof(f123,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | sP0(sK3,X0,sK6,sK2)
      | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK6)
      | ~ l1_struct_0(sK3)
      | ~ l1_struct_0(sK2) ) ),
    inference(resolution,[],[f74,f59])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | sP0(X1,X3,X2,X0)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( sP0(X1,X3,X2,X0)
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(definition_folding,[],[f23,f30])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( l1_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).

fof(f103,plain,(
    spl9_1 ),
    inference(avatar_split_clause,[],[f92,f94])).

fof(f92,plain,(
    l1_pre_topc(sK5) ),
    inference(subsumption_resolution,[],[f89,f49])).

fof(f89,plain,
    ( l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f67,f56])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f102,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f91,f98])).

fof(f91,plain,(
    l1_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f88,f49])).

fof(f88,plain,
    ( l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f67,f54])).

%------------------------------------------------------------------------------
