%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1780+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 264 expanded)
%              Number of leaves         :   24 (  96 expanded)
%              Depth                    :   12
%              Number of atoms          :  412 (1389 expanded)
%              Number of equality atoms :   70 ( 212 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f142,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f92,f94,f96,f106,f108,f121,f135,f141])).

fof(f141,plain,
    ( ~ spl3_2
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(trivial_inequality_removal,[],[f139])).

fof(f139,plain,
    ( sK2 != sK2
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(superposition,[],[f44,f138])).

fof(f138,plain,
    ( sK2 = k1_funct_1(k4_tmap_1(sK0,sK1),sK2)
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(backward_demodulation,[],[f111,f137])).

fof(f137,plain,
    ( k4_tmap_1(sK0,sK1) = k7_relat_1(k3_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f136,f97])).

fof(f97,plain,
    ( k4_tmap_1(sK0,sK1) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1)
    | ~ spl3_5 ),
    inference(resolution,[],[f91,f41])).

fof(f41,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( sK2 != k1_funct_1(k4_tmap_1(sK0,sK1),sK2)
    & r2_hidden(sK2,u1_struct_0(sK1))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f35,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_funct_1(k4_tmap_1(X0,X1),X2) != X2
                & r2_hidden(X2,u1_struct_0(X1))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_funct_1(k4_tmap_1(sK0,X1),X2) != X2
              & r2_hidden(X2,u1_struct_0(X1))
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k1_funct_1(k4_tmap_1(sK0,X1),X2) != X2
            & r2_hidden(X2,u1_struct_0(X1))
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( k1_funct_1(k4_tmap_1(sK0,sK1),X2) != X2
          & r2_hidden(X2,u1_struct_0(sK1))
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X2] :
        ( k1_funct_1(k4_tmap_1(sK0,sK1),X2) != X2
        & r2_hidden(X2,u1_struct_0(sK1))
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( sK2 != k1_funct_1(k4_tmap_1(sK0,sK1),sK2)
      & r2_hidden(sK2,u1_struct_0(sK1))
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_funct_1(k4_tmap_1(X0,X1),X2) != X2
              & r2_hidden(X2,u1_struct_0(X1))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_funct_1(k4_tmap_1(X0,X1),X2) != X2
              & r2_hidden(X2,u1_struct_0(X1))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

% (29542)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,u1_struct_0(X1))
                 => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,u1_struct_0(X1))
               => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_tmap_1)).

fof(f91,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k4_tmap_1(sK0,X0) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X0) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl3_5
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k4_tmap_1(sK0,X0) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f136,plain,
    ( k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1) = k7_relat_1(k3_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_9 ),
    inference(resolution,[],[f134,f41])).

fof(f134,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X0) = k7_relat_1(k3_struct_0(sK0),u1_struct_0(X0)) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl3_9
  <=> ! [X0] :
        ( k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X0) = k7_relat_1(k3_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f111,plain,
    ( sK2 = k1_funct_1(k7_relat_1(k3_struct_0(sK0),u1_struct_0(sK1)),sK2)
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f109,f76])).

fof(f76,plain,
    ( sK2 = k1_funct_1(k3_struct_0(sK0),sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl3_2
  <=> sK2 = k1_funct_1(k3_struct_0(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f109,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),u1_struct_0(sK1)),sK2)
    | ~ spl3_7 ),
    inference(resolution,[],[f105,f43])).

fof(f43,plain,(
    r2_hidden(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f105,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | k1_funct_1(k7_relat_1(k3_struct_0(sK0),X0),X1) = k1_funct_1(k3_struct_0(sK0),X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( k1_funct_1(k7_relat_1(k3_struct_0(sK0),X0),X1) = k1_funct_1(k3_struct_0(sK0),X1)
        | ~ r2_hidden(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f44,plain,(
    sK2 != k1_funct_1(k4_tmap_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f135,plain,
    ( ~ spl3_6
    | spl3_3
    | ~ spl3_4
    | spl3_9 ),
    inference(avatar_split_clause,[],[f131,f133,f86,f82,f100])).

fof(f100,plain,
    ( spl3_6
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f82,plain,
    ( spl3_3
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f86,plain,
    ( spl3_4
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f131,plain,(
    ! [X0] :
      ( k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X0) = k7_relat_1(k3_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_struct_0(sK0) ) ),
    inference(forward_demodulation,[],[f130,f124])).

fof(f124,plain,(
    ! [X0] : k7_relat_1(k3_struct_0(sK0),X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),X0) ),
    inference(resolution,[],[f123,f61])).

fof(f61,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f51,f39])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f51,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | k7_relat_1(k3_struct_0(X0),X1) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X0),k3_struct_0(X0),X1) ) ),
    inference(duplicate_literal_removal,[],[f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( k7_relat_1(k3_struct_0(X0),X1) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X0),k3_struct_0(X0),X1)
      | ~ l1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(resolution,[],[f79,f50])).

fof(f50,plain,(
    ! [X0] :
      ( m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k3_struct_0(X0)) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ( m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k3_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_struct_0)).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k2_partfun1(X1,X2,k3_struct_0(X0),X3) = k7_relat_1(k3_struct_0(X0),X3)
      | ~ l1_struct_0(X0) ) ),
    inference(resolution,[],[f58,f48])).

fof(f48,plain,(
    ! [X0] :
      ( v1_funct_1(k3_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f130,plain,(
    ! [X0] :
      ( k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_struct_0(sK0) ) ),
    inference(resolution,[],[f129,f39])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | k2_tmap_1(X1,X1,k3_struct_0(X1),X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X1),k3_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X0,X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | k2_tmap_1(X1,X1,k3_struct_0(X1),X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X1),k3_struct_0(X1),u1_struct_0(X0))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X1) ) ),
    inference(resolution,[],[f127,f49])).

fof(f49,plain,(
    ! [X0] :
      ( v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(k3_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1))
      | ~ m1_pre_topc(X0,X1)
      | k2_tmap_1(X1,X1,k3_struct_0(X1),X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X1),k3_struct_0(X1),u1_struct_0(X0))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | ~ v1_funct_2(k3_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1))
      | k2_tmap_1(X1,X1,k3_struct_0(X1),X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X1),k3_struct_0(X1),u1_struct_0(X0))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X1) ) ),
    inference(resolution,[],[f125,f50])).

fof(f125,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(k3_struct_0(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
      | ~ m1_pre_topc(X0,X1)
      | ~ v1_funct_2(k3_struct_0(X2),u1_struct_0(X1),u1_struct_0(X3))
      | k2_tmap_1(X1,X3,k3_struct_0(X2),X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),k3_struct_0(X2),u1_struct_0(X0))
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X2) ) ),
    inference(resolution,[],[f53,f48])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
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
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
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
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f121,plain,
    ( spl3_3
    | ~ spl3_6
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f120,f70,f100,f82])).

fof(f70,plain,
    ( spl3_1
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f120,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_1 ),
    inference(resolution,[],[f72,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f72,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f108,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f107])).

fof(f107,plain,
    ( $false
    | spl3_6 ),
    inference(resolution,[],[f102,f61])).

fof(f102,plain,
    ( ~ l1_struct_0(sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f100])).

fof(f106,plain,
    ( ~ spl3_6
    | spl3_7 ),
    inference(avatar_split_clause,[],[f98,f104,f100])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k7_relat_1(k3_struct_0(sK0),X0),X1) = k1_funct_1(k3_struct_0(sK0),X1)
      | ~ r2_hidden(X1,X0)
      | ~ l1_struct_0(sK0) ) ),
    inference(resolution,[],[f78,f63])).

fof(f63,plain,(
    v1_relat_1(k3_struct_0(sK0)) ),
    inference(superposition,[],[f59,f62])).

fof(f62,plain,(
    k3_struct_0(sK0) = k6_partfun1(u1_struct_0(sK0)) ),
    inference(resolution,[],[f47,f61])).

fof(f47,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k3_struct_0(X0) = k6_partfun1(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k3_struct_0(X0) = k6_partfun1(u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k3_struct_0(X0) = k6_partfun1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_struct_0)).

fof(f59,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f45,f46])).

% (29540)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
fof(f46,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f45,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(k3_struct_0(X2))
      | k1_funct_1(k7_relat_1(k3_struct_0(X2),X1),X0) = k1_funct_1(k3_struct_0(X2),X0)
      | ~ r2_hidden(X0,X1)
      | ~ l1_struct_0(X2) ) ),
    inference(resolution,[],[f57,f48])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,X1)
      | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,X1)
       => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_funct_1)).

fof(f96,plain,(
    ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f95])).

fof(f95,plain,
    ( $false
    | ~ spl3_3 ),
    inference(resolution,[],[f84,f37])).

fof(f37,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f84,plain,
    ( v2_struct_0(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f94,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f88,f38])).

fof(f38,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

% (29553)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
fof(f88,plain,
    ( ~ v2_pre_topc(sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f92,plain,
    ( spl3_3
    | ~ spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f80,f90,f86,f82])).

fof(f80,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | k4_tmap_1(sK0,X0) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f52,f39])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | k4_tmap_1(X0,X1) = k2_tmap_1(X0,X0,k3_struct_0(X0),X1)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_tmap_1(X0,X1) = k2_tmap_1(X0,X0,k3_struct_0(X0),X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_tmap_1(X0,X1) = k2_tmap_1(X0,X0,k3_struct_0(X0),X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => k4_tmap_1(X0,X1) = k2_tmap_1(X0,X0,k3_struct_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tmap_1)).

fof(f77,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f68,f74,f70])).

fof(f68,plain,
    ( sK2 = k1_funct_1(k3_struct_0(sK0),sK2)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f66,f62])).

fof(f66,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | sK2 = k1_funct_1(k6_partfun1(u1_struct_0(sK0)),sK2) ),
    inference(resolution,[],[f65,f42])).

fof(f42,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k1_funct_1(k6_partfun1(X0),X1) = X1 ) ),
    inference(resolution,[],[f60,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_funct_1(k6_partfun1(X1),X0) = X0 ) ),
    inference(definition_unfolding,[],[f55,f46])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_funct_1(k6_relat_1(X1),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_1)).

%------------------------------------------------------------------------------
