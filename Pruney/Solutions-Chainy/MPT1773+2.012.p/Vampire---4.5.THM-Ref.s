%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:50 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 450 expanded)
%              Number of leaves         :    9 (  82 expanded)
%              Depth                    :   45
%              Number of atoms          : 1013 (6805 expanded)
%              Number of equality atoms :   13 ( 260 expanded)
%              Maximal formula depth    :   31 (   9 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f211,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f76,f170,f193])).

fof(f193,plain,
    ( ~ spl10_1
    | spl10_2 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | ~ spl10_1
    | spl10_2 ),
    inference(subsumption_resolution,[],[f191,f45])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X3)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X3)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
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
                              ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X3))
                                 => ! [X7] :
                                      ( m1_subset_1(X7,u1_struct_0(X2))
                                     => ( ( X6 = X7
                                          & r1_tarski(X5,u1_struct_0(X2))
                                          & r2_hidden(X6,X5)
                                          & v3_pre_topc(X5,X3) )
                                       => ( r1_tmap_1(X3,X1,X4,X6)
                                        <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
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
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X2))
                                   => ( ( X6 = X7
                                        & r1_tarski(X5,u1_struct_0(X2))
                                        & r2_hidden(X6,X5)
                                        & v3_pre_topc(X5,X3) )
                                     => ( r1_tmap_1(X3,X1,X4,X6)
                                      <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tmap_1)).

fof(f191,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_1
    | spl10_2 ),
    inference(subsumption_resolution,[],[f190,f68])).

fof(f68,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl10_1
  <=> r1_tmap_1(sK3,sK1,sK4,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f190,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK6)
    | v2_struct_0(sK0)
    | spl10_2 ),
    inference(subsumption_resolution,[],[f189,f37])).

fof(f37,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f189,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK6)
    | v2_struct_0(sK0)
    | spl10_2 ),
    inference(subsumption_resolution,[],[f188,f64])).

fof(f64,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f27,f31])).

fof(f31,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f11])).

fof(f27,plain,(
    m1_subset_1(sK7,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f188,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK6)
    | v2_struct_0(sK0)
    | spl10_2 ),
    inference(subsumption_resolution,[],[f187,f32])).

fof(f32,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f187,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK6)
    | v2_struct_0(sK0)
    | spl10_2 ),
    inference(subsumption_resolution,[],[f186,f36])).

fof(f36,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f11])).

fof(f186,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK6)
    | v2_struct_0(sK0)
    | spl10_2 ),
    inference(subsumption_resolution,[],[f185,f35])).

fof(f35,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f185,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK6)
    | v2_struct_0(sK0)
    | spl10_2 ),
    inference(subsumption_resolution,[],[f184,f34])).

fof(f34,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f11])).

fof(f184,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK6)
    | v2_struct_0(sK0)
    | spl10_2 ),
    inference(subsumption_resolution,[],[f183,f41])).

fof(f41,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f183,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK6)
    | v2_struct_0(sK0)
    | spl10_2 ),
    inference(subsumption_resolution,[],[f182,f40])).

fof(f40,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f182,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK6)
    | v2_struct_0(sK0)
    | spl10_2 ),
    inference(subsumption_resolution,[],[f181,f39])).

fof(f39,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f181,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK6)
    | v2_struct_0(sK0)
    | spl10_2 ),
    inference(subsumption_resolution,[],[f180,f38])).

fof(f38,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f180,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK6)
    | v2_struct_0(sK0)
    | spl10_2 ),
    inference(subsumption_resolution,[],[f179,f44])).

fof(f44,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f179,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK6)
    | v2_struct_0(sK0)
    | spl10_2 ),
    inference(subsumption_resolution,[],[f178,f43])).

fof(f43,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f178,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK6)
    | v2_struct_0(sK0)
    | spl10_2 ),
    inference(subsumption_resolution,[],[f177,f42])).

fof(f42,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f177,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK6)
    | v2_struct_0(sK0)
    | spl10_2 ),
    inference(subsumption_resolution,[],[f176,f47])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f176,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK6)
    | v2_struct_0(sK0)
    | spl10_2 ),
    inference(subsumption_resolution,[],[f174,f46])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f174,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK6)
    | v2_struct_0(sK0)
    | spl10_2 ),
    inference(resolution,[],[f73,f63])).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X2)
      | ~ r1_tmap_1(X2,X1,X4,X6)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | X5 != X6
      | ~ m1_pre_topc(X3,X2)
      | ~ r1_tmap_1(X2,X1,X4,X5)
      | r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) ) ),
    inference(cnf_transformation,[],[f18])).

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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f73,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl10_2
  <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f170,plain,
    ( spl10_1
    | ~ spl10_2 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f168,f29])).

fof(f29,plain,(
    r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f11])).

fof(f168,plain,
    ( ~ r2_hidden(sK6,sK5)
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f167,f30])).

fof(f30,plain,(
    r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f167,plain,
    ( ~ r1_tarski(sK5,u1_struct_0(sK2))
    | ~ r2_hidden(sK6,sK5)
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f165,f28])).

fof(f28,plain,(
    v3_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f165,plain,
    ( ~ v3_pre_topc(sK5,sK3)
    | ~ r1_tarski(sK5,u1_struct_0(sK2))
    | ~ r2_hidden(sK6,sK5)
    | spl10_1
    | ~ spl10_2 ),
    inference(resolution,[],[f164,f33])).

fof(f33,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f11])).

fof(f164,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v3_pre_topc(X0,sK3)
        | ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ r2_hidden(sK6,X0) )
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f163,f38])).

fof(f163,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK6,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | v2_struct_0(sK3) )
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f162,f32])).

fof(f162,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK6,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | v2_struct_0(sK3) )
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f161,f103])).

fof(f103,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f98,f47])).

fof(f98,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[],[f39,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f161,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK6,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ l1_pre_topc(sK3)
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | v2_struct_0(sK3) )
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f160,f100])).

fof(f100,plain,(
    v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f99,f46])).

fof(f99,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f97,f47])).

fof(f97,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3) ),
    inference(resolution,[],[f39,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f160,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK6,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | v2_struct_0(sK3) )
    | spl10_1
    | ~ spl10_2 ),
    inference(duplicate_literal_removal,[],[f158])).

fof(f158,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK6,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ r2_hidden(sK6,X0)
        | v2_struct_0(sK3)
        | ~ v3_pre_topc(X0,sK3) )
    | spl10_1
    | ~ spl10_2 ),
    inference(resolution,[],[f139,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK9(X0,X1,X2),X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | v2_struct_0(X0)
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( r1_tarski(X3,X1)
                            & m1_connsp_2(X3,X0,X2) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_connsp_2)).

fof(f139,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK9(sK3,X0,sK6),X1)
        | ~ r2_hidden(sK6,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ r1_tarski(X1,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) )
    | spl10_1
    | ~ spl10_2 ),
    inference(resolution,[],[f137,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f137,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK9(sK3,X0,sK6),u1_struct_0(sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ r2_hidden(sK6,X0)
        | ~ v3_pre_topc(X0,sK3) )
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f136,f38])).

fof(f136,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK9(sK3,X0,sK6),u1_struct_0(sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ r2_hidden(sK6,X0)
        | ~ v3_pre_topc(X0,sK3)
        | v2_struct_0(sK3) )
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f135,f103])).

fof(f135,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK9(sK3,X0,sK6),u1_struct_0(sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ r2_hidden(sK6,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f134,f100])).

fof(f134,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK9(sK3,X0,sK6),u1_struct_0(sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ r2_hidden(sK6,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f133,f32])).

fof(f133,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK9(sK3,X0,sK6),u1_struct_0(sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ r2_hidden(sK6,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | spl10_1
    | ~ spl10_2 ),
    inference(duplicate_literal_removal,[],[f132])).

fof(f132,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK9(sK3,X0,sK6),u1_struct_0(sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ r2_hidden(sK6,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ r2_hidden(sK6,X0)
        | v2_struct_0(sK3)
        | ~ v3_pre_topc(X0,sK3) )
    | spl10_1
    | ~ spl10_2 ),
    inference(resolution,[],[f131,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(sK9(X0,X1,X2),X0,X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | v2_struct_0(X0)
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f131,plain,
    ( ! [X0,X1] :
        ( ~ m1_connsp_2(sK9(sK3,X0,X1),sK3,sK6)
        | ~ r1_tarski(sK9(sK3,X0,X1),u1_struct_0(sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ r2_hidden(X1,X0)
        | ~ v3_pre_topc(X0,sK3) )
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f130,f38])).

fof(f130,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK9(sK3,X0,X1),u1_struct_0(sK2))
        | ~ m1_connsp_2(sK9(sK3,X0,X1),sK3,sK6)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ r2_hidden(X1,X0)
        | v2_struct_0(sK3)
        | ~ v3_pre_topc(X0,sK3) )
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f129,f103])).

fof(f129,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK9(sK3,X0,X1),u1_struct_0(sK2))
        | ~ m1_connsp_2(sK9(sK3,X0,X1),sK3,sK6)
        | ~ l1_pre_topc(sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ r2_hidden(X1,X0)
        | v2_struct_0(sK3)
        | ~ v3_pre_topc(X0,sK3) )
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f127,f100])).

fof(f127,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK9(sK3,X0,X1),u1_struct_0(sK2))
        | ~ m1_connsp_2(sK9(sK3,X0,X1),sK3,sK6)
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ r2_hidden(X1,X0)
        | v2_struct_0(sK3)
        | ~ v3_pre_topc(X0,sK3) )
    | spl10_1
    | ~ spl10_2 ),
    inference(resolution,[],[f125,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK9(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | v2_struct_0(X0)
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f125,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ m1_connsp_2(X0,sK3,sK6) )
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f124,f69])).

fof(f69,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK6)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f124,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ m1_connsp_2(X0,sK3,sK6)
        | r1_tmap_1(sK3,sK1,sK4,sK6) )
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f123,f45])).

fof(f123,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ m1_connsp_2(X0,sK3,sK6)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK3,sK1,sK4,sK6) )
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f122,f64])).

fof(f122,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK6,u1_struct_0(sK2))
        | ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ m1_connsp_2(X0,sK3,sK6)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK3,sK1,sK4,sK6) )
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f121,f32])).

fof(f121,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ m1_subset_1(sK6,u1_struct_0(sK2))
        | ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ m1_connsp_2(X0,sK3,sK6)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK3,sK1,sK4,sK6) )
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f120,f37])).

fof(f120,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ m1_subset_1(sK6,u1_struct_0(sK2))
        | ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ m1_connsp_2(X0,sK3,sK6)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK3,sK1,sK4,sK6) )
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f119,f36])).

fof(f119,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ m1_subset_1(sK6,u1_struct_0(sK2))
        | ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ m1_connsp_2(X0,sK3,sK6)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK3,sK1,sK4,sK6) )
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f118,f35])).

fof(f118,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ m1_subset_1(sK6,u1_struct_0(sK2))
        | ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ m1_connsp_2(X0,sK3,sK6)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK3,sK1,sK4,sK6) )
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f117,f34])).

fof(f117,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ m1_subset_1(sK6,u1_struct_0(sK2))
        | ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ m1_connsp_2(X0,sK3,sK6)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK3,sK1,sK4,sK6) )
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f116,f39])).

fof(f116,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ m1_subset_1(sK6,u1_struct_0(sK2))
        | ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ m1_connsp_2(X0,sK3,sK6)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK3,sK1,sK4,sK6) )
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f115,f38])).

fof(f115,plain,
    ( ! [X0] :
        ( v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ m1_subset_1(sK6,u1_struct_0(sK2))
        | ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ m1_connsp_2(X0,sK3,sK6)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK3,sK1,sK4,sK6) )
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f114,f41])).

fof(f114,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ m1_subset_1(sK6,u1_struct_0(sK2))
        | ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ m1_connsp_2(X0,sK3,sK6)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK3,sK1,sK4,sK6) )
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f113,f40])).

fof(f113,plain,
    ( ! [X0] :
        ( v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ m1_subset_1(sK6,u1_struct_0(sK2))
        | ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ m1_connsp_2(X0,sK3,sK6)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK3,sK1,sK4,sK6) )
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f112,f44])).

fof(f112,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK1)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ m1_subset_1(sK6,u1_struct_0(sK2))
        | ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ m1_connsp_2(X0,sK3,sK6)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK3,sK1,sK4,sK6) )
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f111,f43])).

fof(f111,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ m1_subset_1(sK6,u1_struct_0(sK2))
        | ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ m1_connsp_2(X0,sK3,sK6)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK3,sK1,sK4,sK6) )
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f110,f42])).

fof(f110,plain,
    ( ! [X0] :
        ( v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ m1_subset_1(sK6,u1_struct_0(sK2))
        | ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ m1_connsp_2(X0,sK3,sK6)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK3,sK1,sK4,sK6) )
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f109,f47])).

fof(f109,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ m1_subset_1(sK6,u1_struct_0(sK2))
        | ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ m1_connsp_2(X0,sK3,sK6)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK3,sK1,sK4,sK6) )
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f108,f46])).

fof(f108,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ m1_subset_1(sK6,u1_struct_0(sK2))
        | ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ m1_connsp_2(X0,sK3,sK6)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK3,sK1,sK4,sK6) )
    | ~ spl10_2 ),
    inference(resolution,[],[f72,f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_connsp_2(X5,X3,X7)
      | v2_struct_0(X0)
      | r1_tmap_1(X3,X1,X4,X7) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_connsp_2(X5,X3,X6)
      | X6 != X7
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | r1_tmap_1(X3,X1,X4,X6) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X2))
                                   => ( ( X6 = X7
                                        & m1_connsp_2(X5,X3,X6)
                                        & r1_tarski(X5,u1_struct_0(X2)) )
                                     => ( r1_tmap_1(X3,X1,X4,X6)
                                      <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_tmap_1)).

fof(f72,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f76,plain,
    ( spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f75,f71,f67])).

fof(f75,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | r1_tmap_1(sK3,sK1,sK4,sK6) ),
    inference(forward_demodulation,[],[f25,f31])).

fof(f25,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
    | r1_tmap_1(sK3,sK1,sK4,sK6) ),
    inference(cnf_transformation,[],[f11])).

fof(f74,plain,
    ( ~ spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f65,f71,f67])).

fof(f65,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK6) ),
    inference(forward_demodulation,[],[f26,f31])).

fof(f26,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK6) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:21:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (31059)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (31059)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.48  % (31075)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f211,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f74,f76,f170,f193])).
% 0.20/0.48  fof(f193,plain,(
% 0.20/0.48    ~spl10_1 | spl10_2),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f192])).
% 0.20/0.48  fof(f192,plain,(
% 0.20/0.48    $false | (~spl10_1 | spl10_2)),
% 0.20/0.48    inference(subsumption_resolution,[],[f191,f45])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ~v2_struct_0(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X3,X1,X4,X6) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X3,X1,X4,X6) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3))) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,negated_conjecture,(
% 0.20/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 0.20/0.48    inference(negated_conjecture,[],[f8])).
% 0.20/0.48  fof(f8,conjecture,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tmap_1)).
% 0.20/0.48  fof(f191,plain,(
% 0.20/0.48    v2_struct_0(sK0) | (~spl10_1 | spl10_2)),
% 0.20/0.48    inference(subsumption_resolution,[],[f190,f68])).
% 0.20/0.48  fof(f68,plain,(
% 0.20/0.48    r1_tmap_1(sK3,sK1,sK4,sK6) | ~spl10_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f67])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    spl10_1 <=> r1_tmap_1(sK3,sK1,sK4,sK6)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.20/0.48  fof(f190,plain,(
% 0.20/0.48    ~r1_tmap_1(sK3,sK1,sK4,sK6) | v2_struct_0(sK0) | spl10_2),
% 0.20/0.48    inference(subsumption_resolution,[],[f189,f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    m1_pre_topc(sK2,sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f189,plain,(
% 0.20/0.48    ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK1,sK4,sK6) | v2_struct_0(sK0) | spl10_2),
% 0.20/0.48    inference(subsumption_resolution,[],[f188,f64])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.20/0.48    inference(forward_demodulation,[],[f27,f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    sK6 = sK7),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    m1_subset_1(sK7,u1_struct_0(sK2))),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f188,plain,(
% 0.20/0.48    ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK1,sK4,sK6) | v2_struct_0(sK0) | spl10_2),
% 0.20/0.48    inference(subsumption_resolution,[],[f187,f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f187,plain,(
% 0.20/0.48    ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK1,sK4,sK6) | v2_struct_0(sK0) | spl10_2),
% 0.20/0.48    inference(subsumption_resolution,[],[f186,f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f186,plain,(
% 0.20/0.48    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK1,sK4,sK6) | v2_struct_0(sK0) | spl10_2),
% 0.20/0.48    inference(subsumption_resolution,[],[f185,f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f185,plain,(
% 0.20/0.48    ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK1,sK4,sK6) | v2_struct_0(sK0) | spl10_2),
% 0.20/0.48    inference(subsumption_resolution,[],[f184,f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    v1_funct_1(sK4)),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f184,plain,(
% 0.20/0.48    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK1,sK4,sK6) | v2_struct_0(sK0) | spl10_2),
% 0.20/0.48    inference(subsumption_resolution,[],[f183,f41])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    m1_pre_topc(sK2,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f183,plain,(
% 0.20/0.48    ~m1_pre_topc(sK2,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK1,sK4,sK6) | v2_struct_0(sK0) | spl10_2),
% 0.20/0.48    inference(subsumption_resolution,[],[f182,f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ~v2_struct_0(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f182,plain,(
% 0.20/0.48    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK1,sK4,sK6) | v2_struct_0(sK0) | spl10_2),
% 0.20/0.48    inference(subsumption_resolution,[],[f181,f39])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    m1_pre_topc(sK3,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f181,plain,(
% 0.20/0.48    ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK1,sK4,sK6) | v2_struct_0(sK0) | spl10_2),
% 0.20/0.48    inference(subsumption_resolution,[],[f180,f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ~v2_struct_0(sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f180,plain,(
% 0.20/0.48    v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK1,sK4,sK6) | v2_struct_0(sK0) | spl10_2),
% 0.20/0.48    inference(subsumption_resolution,[],[f179,f44])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    l1_pre_topc(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f179,plain,(
% 0.20/0.48    ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK1,sK4,sK6) | v2_struct_0(sK0) | spl10_2),
% 0.20/0.48    inference(subsumption_resolution,[],[f178,f43])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    v2_pre_topc(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f178,plain,(
% 0.20/0.48    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK1,sK4,sK6) | v2_struct_0(sK0) | spl10_2),
% 0.20/0.48    inference(subsumption_resolution,[],[f177,f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ~v2_struct_0(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f177,plain,(
% 0.20/0.48    v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK1,sK4,sK6) | v2_struct_0(sK0) | spl10_2),
% 0.20/0.48    inference(subsumption_resolution,[],[f176,f47])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    l1_pre_topc(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f176,plain,(
% 0.20/0.48    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK1,sK4,sK6) | v2_struct_0(sK0) | spl10_2),
% 0.20/0.48    inference(subsumption_resolution,[],[f174,f46])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    v2_pre_topc(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f174,plain,(
% 0.20/0.48    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK1,sK4,sK6) | v2_struct_0(sK0) | spl10_2),
% 0.20/0.48    inference(resolution,[],[f73,f63])).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~r1_tmap_1(X2,X1,X4,X6) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(equality_resolution,[],[f57])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | X5 != X6 | ~m1_pre_topc(X3,X2) | ~r1_tmap_1(X2,X1,X4,X5) | r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | (~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((r1_tmap_1(X2,X1,X4,X5) & m1_pre_topc(X3,X2) & X5 = X6) => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)))))))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tmap_1)).
% 0.20/0.48  fof(f73,plain,(
% 0.20/0.48    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | spl10_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f71])).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    spl10_2 <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.20/0.48  fof(f170,plain,(
% 0.20/0.48    spl10_1 | ~spl10_2),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f169])).
% 0.20/0.48  fof(f169,plain,(
% 0.20/0.48    $false | (spl10_1 | ~spl10_2)),
% 0.20/0.48    inference(subsumption_resolution,[],[f168,f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    r2_hidden(sK6,sK5)),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f168,plain,(
% 0.20/0.48    ~r2_hidden(sK6,sK5) | (spl10_1 | ~spl10_2)),
% 0.20/0.48    inference(subsumption_resolution,[],[f167,f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    r1_tarski(sK5,u1_struct_0(sK2))),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f167,plain,(
% 0.20/0.48    ~r1_tarski(sK5,u1_struct_0(sK2)) | ~r2_hidden(sK6,sK5) | (spl10_1 | ~spl10_2)),
% 0.20/0.48    inference(subsumption_resolution,[],[f165,f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    v3_pre_topc(sK5,sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f165,plain,(
% 0.20/0.48    ~v3_pre_topc(sK5,sK3) | ~r1_tarski(sK5,u1_struct_0(sK2)) | ~r2_hidden(sK6,sK5) | (spl10_1 | ~spl10_2)),
% 0.20/0.48    inference(resolution,[],[f164,f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f164,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~v3_pre_topc(X0,sK3) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~r2_hidden(sK6,X0)) ) | (spl10_1 | ~spl10_2)),
% 0.20/0.48    inference(subsumption_resolution,[],[f163,f38])).
% 0.20/0.48  fof(f163,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(sK6,X0) | ~v3_pre_topc(X0,sK3) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | v2_struct_0(sK3)) ) | (spl10_1 | ~spl10_2)),
% 0.20/0.48    inference(subsumption_resolution,[],[f162,f32])).
% 0.20/0.48  fof(f162,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(sK6,X0) | ~v3_pre_topc(X0,sK3) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | v2_struct_0(sK3)) ) | (spl10_1 | ~spl10_2)),
% 0.20/0.48    inference(subsumption_resolution,[],[f161,f103])).
% 0.20/0.48  fof(f103,plain,(
% 0.20/0.48    l1_pre_topc(sK3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f98,f47])).
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    ~l1_pre_topc(sK0) | l1_pre_topc(sK3)),
% 0.20/0.48    inference(resolution,[],[f39,f48])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.49  fof(f161,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(sK6,X0) | ~v3_pre_topc(X0,sK3) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | v2_struct_0(sK3)) ) | (spl10_1 | ~spl10_2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f160,f100])).
% 0.20/0.49  fof(f100,plain,(
% 0.20/0.49    v2_pre_topc(sK3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f99,f46])).
% 0.20/0.49  fof(f99,plain,(
% 0.20/0.49    ~v2_pre_topc(sK0) | v2_pre_topc(sK3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f97,f47])).
% 0.20/0.49  fof(f97,plain,(
% 0.20/0.49    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_pre_topc(sK3)),
% 0.20/0.49    inference(resolution,[],[f39,f58])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_pre_topc(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.20/0.49  fof(f160,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(sK6,X0) | ~v3_pre_topc(X0,sK3) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | v2_struct_0(sK3)) ) | (spl10_1 | ~spl10_2)),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f158])).
% 0.20/0.49  fof(f158,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(sK6,X0) | ~v3_pre_topc(X0,sK3) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~r2_hidden(sK6,X0) | v2_struct_0(sK3) | ~v3_pre_topc(X0,sK3)) ) | (spl10_1 | ~spl10_2)),
% 0.20/0.49    inference(resolution,[],[f139,f52])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_tarski(sK9(X0,X1,X2),X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | v2_struct_0(X0) | ~v3_pre_topc(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : ((? [X3] : ((r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_connsp_2)).
% 0.20/0.49  fof(f139,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(sK9(sK3,X0,sK6),X1) | ~r2_hidden(sK6,X0) | ~v3_pre_topc(X0,sK3) | ~r1_tarski(X1,u1_struct_0(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))) ) | (spl10_1 | ~spl10_2)),
% 0.20/0.49    inference(resolution,[],[f137,f60])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.49    inference(flattening,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.49  fof(f137,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(sK9(sK3,X0,sK6),u1_struct_0(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~r2_hidden(sK6,X0) | ~v3_pre_topc(X0,sK3)) ) | (spl10_1 | ~spl10_2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f136,f38])).
% 0.20/0.49  fof(f136,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(sK9(sK3,X0,sK6),u1_struct_0(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~r2_hidden(sK6,X0) | ~v3_pre_topc(X0,sK3) | v2_struct_0(sK3)) ) | (spl10_1 | ~spl10_2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f135,f103])).
% 0.20/0.49  fof(f135,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(sK9(sK3,X0,sK6),u1_struct_0(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~r2_hidden(sK6,X0) | ~v3_pre_topc(X0,sK3) | ~l1_pre_topc(sK3) | v2_struct_0(sK3)) ) | (spl10_1 | ~spl10_2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f134,f100])).
% 0.20/0.49  fof(f134,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(sK9(sK3,X0,sK6),u1_struct_0(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~r2_hidden(sK6,X0) | ~v3_pre_topc(X0,sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | v2_struct_0(sK3)) ) | (spl10_1 | ~spl10_2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f133,f32])).
% 0.20/0.49  fof(f133,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(sK9(sK3,X0,sK6),u1_struct_0(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~r2_hidden(sK6,X0) | ~v3_pre_topc(X0,sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | v2_struct_0(sK3)) ) | (spl10_1 | ~spl10_2)),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f132])).
% 0.20/0.49  fof(f132,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(sK9(sK3,X0,sK6),u1_struct_0(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~r2_hidden(sK6,X0) | ~v3_pre_topc(X0,sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~r2_hidden(sK6,X0) | v2_struct_0(sK3) | ~v3_pre_topc(X0,sK3)) ) | (spl10_1 | ~spl10_2)),
% 0.20/0.49    inference(resolution,[],[f131,f51])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (m1_connsp_2(sK9(X0,X1,X2),X0,X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | v2_struct_0(X0) | ~v3_pre_topc(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f131,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_connsp_2(sK9(sK3,X0,X1),sK3,sK6) | ~r1_tarski(sK9(sK3,X0,X1),u1_struct_0(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~r2_hidden(X1,X0) | ~v3_pre_topc(X0,sK3)) ) | (spl10_1 | ~spl10_2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f130,f38])).
% 0.20/0.49  fof(f130,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(sK9(sK3,X0,X1),u1_struct_0(sK2)) | ~m1_connsp_2(sK9(sK3,X0,X1),sK3,sK6) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~r2_hidden(X1,X0) | v2_struct_0(sK3) | ~v3_pre_topc(X0,sK3)) ) | (spl10_1 | ~spl10_2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f129,f103])).
% 0.20/0.49  fof(f129,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(sK9(sK3,X0,X1),u1_struct_0(sK2)) | ~m1_connsp_2(sK9(sK3,X0,X1),sK3,sK6) | ~l1_pre_topc(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~r2_hidden(X1,X0) | v2_struct_0(sK3) | ~v3_pre_topc(X0,sK3)) ) | (spl10_1 | ~spl10_2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f127,f100])).
% 0.20/0.49  fof(f127,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(sK9(sK3,X0,X1),u1_struct_0(sK2)) | ~m1_connsp_2(sK9(sK3,X0,X1),sK3,sK6) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~r2_hidden(X1,X0) | v2_struct_0(sK3) | ~v3_pre_topc(X0,sK3)) ) | (spl10_1 | ~spl10_2)),
% 0.20/0.49    inference(resolution,[],[f125,f50])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (m1_subset_1(sK9(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | v2_struct_0(X0) | ~v3_pre_topc(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f125,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6)) ) | (spl10_1 | ~spl10_2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f124,f69])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    ~r1_tmap_1(sK3,sK1,sK4,sK6) | spl10_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f67])).
% 0.20/0.49  fof(f124,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6) | r1_tmap_1(sK3,sK1,sK4,sK6)) ) | ~spl10_2),
% 0.20/0.49    inference(subsumption_resolution,[],[f123,f45])).
% 0.20/0.49  fof(f123,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK6)) ) | ~spl10_2),
% 0.20/0.49    inference(subsumption_resolution,[],[f122,f64])).
% 0.20/0.49  fof(f122,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK6)) ) | ~spl10_2),
% 0.20/0.49    inference(subsumption_resolution,[],[f121,f32])).
% 0.20/0.49  fof(f121,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK6)) ) | ~spl10_2),
% 0.20/0.49    inference(subsumption_resolution,[],[f120,f37])).
% 0.20/0.49  fof(f120,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK6)) ) | ~spl10_2),
% 0.20/0.49    inference(subsumption_resolution,[],[f119,f36])).
% 0.20/0.49  fof(f119,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK6)) ) | ~spl10_2),
% 0.20/0.49    inference(subsumption_resolution,[],[f118,f35])).
% 0.20/0.49  fof(f118,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK6)) ) | ~spl10_2),
% 0.20/0.49    inference(subsumption_resolution,[],[f117,f34])).
% 0.20/0.49  fof(f117,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK6)) ) | ~spl10_2),
% 0.20/0.49    inference(subsumption_resolution,[],[f116,f39])).
% 0.20/0.49  fof(f116,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK6)) ) | ~spl10_2),
% 0.20/0.49    inference(subsumption_resolution,[],[f115,f38])).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    ( ! [X0] : (v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK6)) ) | ~spl10_2),
% 0.20/0.49    inference(subsumption_resolution,[],[f114,f41])).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK6)) ) | ~spl10_2),
% 0.20/0.49    inference(subsumption_resolution,[],[f113,f40])).
% 0.20/0.49  fof(f113,plain,(
% 0.20/0.49    ( ! [X0] : (v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK6)) ) | ~spl10_2),
% 0.20/0.49    inference(subsumption_resolution,[],[f112,f44])).
% 0.20/0.49  fof(f112,plain,(
% 0.20/0.49    ( ! [X0] : (~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK6)) ) | ~spl10_2),
% 0.20/0.49    inference(subsumption_resolution,[],[f111,f43])).
% 0.20/0.49  fof(f111,plain,(
% 0.20/0.49    ( ! [X0] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK6)) ) | ~spl10_2),
% 0.20/0.49    inference(subsumption_resolution,[],[f110,f42])).
% 0.20/0.49  fof(f110,plain,(
% 0.20/0.49    ( ! [X0] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK6)) ) | ~spl10_2),
% 0.20/0.49    inference(subsumption_resolution,[],[f109,f47])).
% 0.20/0.49  fof(f109,plain,(
% 0.20/0.49    ( ! [X0] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK6)) ) | ~spl10_2),
% 0.20/0.49    inference(subsumption_resolution,[],[f108,f46])).
% 0.20/0.49  fof(f108,plain,(
% 0.20/0.49    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK6)) ) | ~spl10_2),
% 0.20/0.49    inference(resolution,[],[f72,f62])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X7,X5,X3,X1] : (~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_connsp_2(X5,X3,X7) | v2_struct_0(X0) | r1_tmap_1(X3,X1,X4,X7)) )),
% 0.20/0.49    inference(equality_resolution,[],[f55])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_connsp_2(X5,X3,X6) | X6 != X7 | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2))) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_tmap_1)).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | ~spl10_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f71])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    spl10_1 | spl10_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f75,f71,f67])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK1,sK4,sK6)),
% 0.20/0.49    inference(forward_demodulation,[],[f25,f31])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK1,sK4,sK6)),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    ~spl10_1 | ~spl10_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f65,f71,f67])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK1,sK4,sK6)),
% 0.20/0.49    inference(forward_demodulation,[],[f26,f31])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,sK4,sK6)),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (31059)------------------------------
% 0.20/0.49  % (31059)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (31059)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (31059)Memory used [KB]: 10746
% 0.20/0.49  % (31059)Time elapsed: 0.060 s
% 0.20/0.49  % (31059)------------------------------
% 0.20/0.49  % (31059)------------------------------
% 0.20/0.49  % (31051)Success in time 0.136 s
%------------------------------------------------------------------------------
