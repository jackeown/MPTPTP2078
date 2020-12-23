%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1968+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:58 EST 2020

% Result     : Theorem 0.11s
% Output     : Refutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :  257 (3370 expanded)
%              Number of leaves         :   24 ( 598 expanded)
%              Depth                    :   34
%              Number of atoms          : 1416 (40693 expanded)
%              Number of equality atoms :  104 (3118 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f549,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f111,f114,f123,f141,f144,f525,f532,f533,f544,f546,f548])).

fof(f548,plain,
    ( spl7_4
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f547])).

fof(f547,plain,
    ( $false
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f99,f356])).

fof(f356,plain,
    ( v1_waybel_0(sK2,sK1)
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f355,f42])).

fof(f42,plain,(
    v1_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                | ~ v1_waybel_7(X2,X1)
                | ~ v12_waybel_0(X2,X1)
                | ~ v1_waybel_0(X2,X1)
                | v1_xboole_0(X2) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_7(X2,X0)
              & v12_waybel_0(X2,X0)
              & v1_waybel_0(X2,X0)
              & ~ v1_xboole_0(X2) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1)
          & v2_lattice3(X1)
          & v5_orders_2(X1)
          & v4_orders_2(X1)
          & v3_orders_2(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

% (18264)Termination reason: Refutation not found, incomplete strategy

% (18264)Memory used [KB]: 10618
% (18264)Time elapsed: 0.084 s
% (18264)------------------------------
% (18264)------------------------------
fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                | ~ v1_waybel_7(X2,X1)
                | ~ v12_waybel_0(X2,X1)
                | ~ v1_waybel_0(X2,X1)
                | v1_xboole_0(X2) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_7(X2,X0)
              & v12_waybel_0(X2,X0)
              & v1_waybel_0(X2,X0)
              & ~ v1_xboole_0(X2) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1)
          & v2_lattice3(X1)
          & v5_orders_2(X1)
          & v4_orders_2(X1)
          & v3_orders_2(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ( l1_orders_2(X1)
              & v2_lattice3(X1)
              & v5_orders_2(X1)
              & v4_orders_2(X1)
              & v3_orders_2(X1) )
           => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
             => ! [X2] :
                  ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                    & v1_waybel_7(X2,X0)
                    & v12_waybel_0(X2,X0)
                    & v1_waybel_0(X2,X0)
                    & ~ v1_xboole_0(X2) )
                 => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                    & v1_waybel_7(X2,X1)
                    & v12_waybel_0(X2,X1)
                    & v1_waybel_0(X2,X1)
                    & ~ v1_xboole_0(X2) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ( l1_orders_2(X1)
              & v2_lattice3(X1)
              & v1_lattice3(X1)
              & v5_orders_2(X1)
              & v4_orders_2(X1)
              & v3_orders_2(X1) )
           => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
             => ! [X2] :
                  ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                    & v1_waybel_7(X2,X0)
                    & v12_waybel_0(X2,X0)
                    & v1_waybel_0(X2,X0)
                    & ~ v1_xboole_0(X2) )
                 => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                    & v1_waybel_7(X2,X1)
                    & v12_waybel_0(X2,X1)
                    & v1_waybel_0(X2,X1)
                    & ~ v1_xboole_0(X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( l1_orders_2(X1)
            & v2_lattice3(X1)
            & v1_lattice3(X1)
            & v5_orders_2(X1)
            & v4_orders_2(X1)
            & v3_orders_2(X1) )
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & v1_waybel_7(X2,X0)
                  & v12_waybel_0(X2,X0)
                  & v1_waybel_0(X2,X0)
                  & ~ v1_xboole_0(X2) )
               => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                  & v1_waybel_7(X2,X1)
                  & v12_waybel_0(X2,X1)
                  & v1_waybel_0(X2,X1)
                  & ~ v1_xboole_0(X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_waybel_7)).

fof(f355,plain,
    ( ~ v1_waybel_0(sK2,sK0)
    | v1_waybel_0(sK2,sK1)
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(resolution,[],[f354,f45])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f354,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(X0,sK0)
        | v1_waybel_0(X0,sK1) )
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f352,f56])).

fof(f56,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f352,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(X0,sK0)
        | v1_waybel_0(X0,sK1) )
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(duplicate_literal_removal,[],[f351])).

% (18254)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
fof(f351,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(X0,sK0)
        | v1_waybel_0(X0,sK1) )
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(equality_resolution,[],[f338])).

fof(f338,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(X1,X0)
        | v1_waybel_0(X1,sK1) )
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f337,f154])).

fof(f154,plain,
    ( u1_orders_2(sK0) = u1_orders_2(sK1)
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(equality_resolution,[],[f152])).

fof(f152,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_orders_2(sK1) = X1 )
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f149,f117])).

fof(f117,plain,
    ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f106,f116])).

fof(f116,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK0)
    | ~ spl7_6 ),
    inference(equality_resolution,[],[f110])).

fof(f110,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_struct_0(sK1) = X0 )
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl7_6
  <=> ! [X1,X0] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_struct_0(sK1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f106,plain,
    ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl7_5
  <=> m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f149,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | u1_orders_2(sK1) = X1 )
    | ~ spl7_6 ),
    inference(superposition,[],[f78,f121])).

fof(f121,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1))
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f51,f116])).

fof(f51,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f337,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1))
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(X1,X0)
        | v1_waybel_0(X1,sK1) )
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f328,f50])).

fof(f50,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f328,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1))
        | ~ l1_orders_2(sK1)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(X1,X0)
        | v1_waybel_0(X1,sK1) )
    | ~ spl7_6 ),
    inference(superposition,[],[f82,f116])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v1_waybel_0(X3,X0)
      | v1_waybel_0(X3,X1) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ l1_orders_2(X1)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | X2 != X3
      | ~ v1_waybel_0(X2,X0)
      | v1_waybel_0(X3,X1) ) ),
    inference(cnf_transformation,[],[f28])).

% (18267)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (18278)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v1_waybel_0(X3,X1)
                  | ~ v1_waybel_0(X2,X0)
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v1_waybel_0(X3,X1)
                  | ~ v1_waybel_0(X2,X0)
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v1_waybel_0(X2,X0)
                        & X2 = X3 )
                     => v1_waybel_0(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_waybel_0)).

fof(f99,plain,
    ( ~ v1_waybel_0(sK2,sK1)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f97])).

% (18253)Refutation not found, incomplete strategy% (18253)------------------------------
% (18253)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (18253)Termination reason: Refutation not found, incomplete strategy

% (18253)Memory used [KB]: 10618
% (18253)Time elapsed: 0.090 s
% (18253)------------------------------
% (18253)------------------------------
fof(f97,plain,
    ( spl7_4
  <=> v1_waybel_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f546,plain,
    ( spl7_3
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f545])).

fof(f545,plain,
    ( $false
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f95,f311])).

fof(f311,plain,
    ( v12_waybel_0(sK2,sK1)
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f310,f43])).

fof(f43,plain,(
    v12_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f310,plain,
    ( ~ v12_waybel_0(sK2,sK0)
    | v12_waybel_0(sK2,sK1)
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(resolution,[],[f309,f45])).

fof(f309,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v12_waybel_0(X0,sK0)
        | v12_waybel_0(X0,sK1) )
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f307,f56])).

fof(f307,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v12_waybel_0(X0,sK0)
        | v12_waybel_0(X0,sK1) )
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(duplicate_literal_removal,[],[f306])).

fof(f306,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v12_waybel_0(X0,sK0)
        | v12_waybel_0(X0,sK1) )
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(equality_resolution,[],[f277])).

fof(f277,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v12_waybel_0(X1,X0)
        | v12_waybel_0(X1,sK1) )
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f276,f154])).

fof(f276,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1))
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v12_waybel_0(X1,X0)
        | v12_waybel_0(X1,sK1) )
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f267,f50])).

fof(f267,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1))
        | ~ l1_orders_2(sK1)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v12_waybel_0(X1,X0)
        | v12_waybel_0(X1,sK1) )
    | ~ spl7_6 ),
    inference(superposition,[],[f80,f116])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v12_waybel_0(X3,X0)
      | v12_waybel_0(X3,X1) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ l1_orders_2(X1)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | X2 != X3
      | ~ v12_waybel_0(X2,X0)
      | v12_waybel_0(X3,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v13_waybel_0(X3,X1)
                      | ~ v13_waybel_0(X2,X0) )
                    & ( v12_waybel_0(X3,X1)
                      | ~ v12_waybel_0(X2,X0) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v13_waybel_0(X3,X1)
                      | ~ v13_waybel_0(X2,X0) )
                    & ( v12_waybel_0(X3,X1)
                      | ~ v12_waybel_0(X2,X0) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( X2 = X3
                     => ( ( v13_waybel_0(X2,X0)
                         => v13_waybel_0(X3,X1) )
                        & ( v12_waybel_0(X2,X0)
                         => v12_waybel_0(X3,X1) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_waybel_0)).

fof(f95,plain,
    ( ~ v12_waybel_0(sK2,sK1)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl7_3
  <=> v12_waybel_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f544,plain,
    ( spl7_2
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_15 ),
    inference(avatar_contradiction_clause,[],[f543])).

fof(f543,plain,
    ( $false
    | spl7_2
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f542,f91])).

fof(f91,plain,
    ( ~ v1_waybel_7(sK2,sK1)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl7_2
  <=> v1_waybel_7(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f542,plain,
    ( v1_waybel_7(sK2,sK1)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f541,f45])).

fof(f541,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_waybel_7(sK2,sK1)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f540,f311])).

fof(f540,plain,
    ( ~ v12_waybel_0(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_waybel_7(sK2,sK1)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f539,f356])).

fof(f539,plain,
    ( ~ v1_waybel_0(sK2,sK1)
    | ~ v12_waybel_0(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_waybel_7(sK2,sK1)
    | ~ spl7_6
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f538,f41])).

fof(f41,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f538,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_waybel_0(sK2,sK1)
    | ~ v12_waybel_0(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_waybel_7(sK2,sK1)
    | ~ spl7_6
    | ~ spl7_15 ),
    inference(resolution,[],[f512,f249])).

fof(f249,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(sK1,X0),X0)
        | v1_xboole_0(X0)
        | ~ v1_waybel_0(X0,sK1)
        | ~ v12_waybel_0(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_waybel_7(X0,sK1) )
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f248,f116])).

fof(f248,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ v1_waybel_0(X0,sK1)
      | ~ v12_waybel_0(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r2_hidden(sK3(sK1,X0),X0)
      | v1_waybel_7(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f247,f50])).

fof(f247,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK1)
      | v1_xboole_0(X0)
      | ~ v1_waybel_0(X0,sK1)
      | ~ v12_waybel_0(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r2_hidden(sK3(sK1,X0),X0)
      | v1_waybel_7(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f246,f49])).

fof(f49,plain,(
    v2_lattice3(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f246,plain,(
    ! [X0] :
      ( ~ v2_lattice3(sK1)
      | ~ l1_orders_2(sK1)
      | v1_xboole_0(X0)
      | ~ v1_waybel_0(X0,sK1)
      | ~ v12_waybel_0(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r2_hidden(sK3(sK1,X0),X0)
      | v1_waybel_7(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f245,f46])).

fof(f46,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f245,plain,(
    ! [X0] :
      ( ~ v3_orders_2(sK1)
      | ~ v2_lattice3(sK1)
      | ~ l1_orders_2(sK1)
      | v1_xboole_0(X0)
      | ~ v1_waybel_0(X0,sK1)
      | ~ v12_waybel_0(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r2_hidden(sK3(sK1,X0),X0)
      | v1_waybel_7(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f243,f47])).

% (18274)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% (18260)Refutation not found, incomplete strategy% (18260)------------------------------
% (18260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (18260)Termination reason: Refutation not found, incomplete strategy

% (18260)Memory used [KB]: 1791
% (18260)Time elapsed: 0.080 s
% (18260)------------------------------
% (18260)------------------------------
% (18270)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
fof(f47,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f243,plain,(
    ! [X0] :
      ( ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1)
      | ~ v2_lattice3(sK1)
      | ~ l1_orders_2(sK1)
      | v1_xboole_0(X0)
      | ~ v1_waybel_0(X0,sK1)
      | ~ v12_waybel_0(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r2_hidden(sK3(sK1,X0),X0)
      | v1_waybel_7(X0,sK1) ) ),
    inference(resolution,[],[f68,f48])).

fof(f48,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v1_waybel_0(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(sK3(X0,X1),X1)
      | v1_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | r2_hidden(X2,X1)
                    | ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | r2_hidden(X2,X1)
                    | ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_waybel_7(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ~ ( ~ r2_hidden(X3,X1)
                        & ~ r2_hidden(X2,X1)
                        & r2_hidden(k12_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_waybel_7)).

fof(f512,plain,
    ( r2_hidden(sK3(sK1,sK2),sK2)
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f510])).

fof(f510,plain,
    ( spl7_15
  <=> r2_hidden(sK3(sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f533,plain,
    ( spl7_14
    | spl7_15
    | spl7_2
    | ~ spl7_5
    | ~ spl7_6
    | spl7_9 ),
    inference(avatar_split_clause,[],[f504,f138,f109,f105,f89,f510,f506])).

fof(f506,plain,
    ( spl7_14
  <=> r2_hidden(sK4(sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f138,plain,
    ( spl7_9
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f504,plain,
    ( r2_hidden(sK3(sK1,sK2),sK2)
    | r2_hidden(sK4(sK1,sK2),sK2)
    | spl7_2
    | ~ spl7_5
    | ~ spl7_6
    | spl7_9 ),
    inference(subsumption_resolution,[],[f503,f411])).

fof(f411,plain,
    ( m1_subset_1(sK3(sK1,sK2),u1_struct_0(sK0))
    | spl7_2
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f410,f311])).

fof(f410,plain,
    ( ~ v12_waybel_0(sK2,sK1)
    | m1_subset_1(sK3(sK1,sK2),u1_struct_0(sK0))
    | spl7_2
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f409,f356])).

fof(f409,plain,
    ( ~ v1_waybel_0(sK2,sK1)
    | ~ v12_waybel_0(sK2,sK1)
    | m1_subset_1(sK3(sK1,sK2),u1_struct_0(sK0))
    | spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f408,f41])).

fof(f408,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_waybel_0(sK2,sK1)
    | ~ v12_waybel_0(sK2,sK1)
    | m1_subset_1(sK3(sK1,sK2),u1_struct_0(sK0))
    | spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f407,f45])).

fof(f407,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK2)
    | ~ v1_waybel_0(sK2,sK1)
    | ~ v12_waybel_0(sK2,sK1)
    | m1_subset_1(sK3(sK1,sK2),u1_struct_0(sK0))
    | spl7_2
    | ~ spl7_6 ),
    inference(resolution,[],[f402,f91])).

fof(f402,plain,
    ( ! [X0] :
        ( v1_waybel_7(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | ~ v1_waybel_0(X0,sK1)
        | ~ v12_waybel_0(X0,sK1)
        | m1_subset_1(sK3(sK1,X0),u1_struct_0(sK0)) )
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f401,f116])).

fof(f401,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | ~ v1_waybel_0(X0,sK1)
        | ~ v12_waybel_0(X0,sK1)
        | m1_subset_1(sK3(sK1,X0),u1_struct_0(sK1))
        | v1_waybel_7(X0,sK1) )
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f400,f116])).

fof(f400,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ v1_waybel_0(X0,sK1)
      | ~ v12_waybel_0(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | m1_subset_1(sK3(sK1,X0),u1_struct_0(sK1))
      | v1_waybel_7(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f399,f50])).

fof(f399,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK1)
      | v1_xboole_0(X0)
      | ~ v1_waybel_0(X0,sK1)
      | ~ v12_waybel_0(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | m1_subset_1(sK3(sK1,X0),u1_struct_0(sK1))
      | v1_waybel_7(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f398,f49])).

fof(f398,plain,(
    ! [X0] :
      ( ~ v2_lattice3(sK1)
      | ~ l1_orders_2(sK1)
      | v1_xboole_0(X0)
      | ~ v1_waybel_0(X0,sK1)
      | ~ v12_waybel_0(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | m1_subset_1(sK3(sK1,X0),u1_struct_0(sK1))
      | v1_waybel_7(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f397,f46])).

fof(f397,plain,(
    ! [X0] :
      ( ~ v3_orders_2(sK1)
      | ~ v2_lattice3(sK1)
      | ~ l1_orders_2(sK1)
      | v1_xboole_0(X0)
      | ~ v1_waybel_0(X0,sK1)
      | ~ v12_waybel_0(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | m1_subset_1(sK3(sK1,X0),u1_struct_0(sK1))
      | v1_waybel_7(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f395,f47])).

fof(f395,plain,(
    ! [X0] :
      ( ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1)
      | ~ v2_lattice3(sK1)
      | ~ l1_orders_2(sK1)
      | v1_xboole_0(X0)
      | ~ v1_waybel_0(X0,sK1)
      | ~ v12_waybel_0(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | m1_subset_1(sK3(sK1,X0),u1_struct_0(sK1))
      | v1_waybel_7(X0,sK1) ) ),
    inference(resolution,[],[f71,f48])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v1_waybel_0(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | v1_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f503,plain,
    ( ~ m1_subset_1(sK3(sK1,sK2),u1_struct_0(sK0))
    | r2_hidden(sK3(sK1,sK2),sK2)
    | r2_hidden(sK4(sK1,sK2),sK2)
    | spl7_2
    | ~ spl7_5
    | ~ spl7_6
    | spl7_9 ),
    inference(subsumption_resolution,[],[f500,f373])).

fof(f373,plain,
    ( m1_subset_1(sK4(sK1,sK2),u1_struct_0(sK0))
    | spl7_2
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f372,f311])).

fof(f372,plain,
    ( ~ v12_waybel_0(sK2,sK1)
    | m1_subset_1(sK4(sK1,sK2),u1_struct_0(sK0))
    | spl7_2
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f371,f356])).

fof(f371,plain,
    ( ~ v1_waybel_0(sK2,sK1)
    | ~ v12_waybel_0(sK2,sK1)
    | m1_subset_1(sK4(sK1,sK2),u1_struct_0(sK0))
    | spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f370,f41])).

fof(f370,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_waybel_0(sK2,sK1)
    | ~ v12_waybel_0(sK2,sK1)
    | m1_subset_1(sK4(sK1,sK2),u1_struct_0(sK0))
    | spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f369,f45])).

fof(f369,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK2)
    | ~ v1_waybel_0(sK2,sK1)
    | ~ v12_waybel_0(sK2,sK1)
    | m1_subset_1(sK4(sK1,sK2),u1_struct_0(sK0))
    | spl7_2
    | ~ spl7_6 ),
    inference(resolution,[],[f364,f91])).

fof(f364,plain,
    ( ! [X0] :
        ( v1_waybel_7(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | ~ v1_waybel_0(X0,sK1)
        | ~ v12_waybel_0(X0,sK1)
        | m1_subset_1(sK4(sK1,X0),u1_struct_0(sK0)) )
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f363,f116])).

fof(f363,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | ~ v1_waybel_0(X0,sK1)
        | ~ v12_waybel_0(X0,sK1)
        | m1_subset_1(sK4(sK1,X0),u1_struct_0(sK1))
        | v1_waybel_7(X0,sK1) )
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f362,f116])).

fof(f362,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ v1_waybel_0(X0,sK1)
      | ~ v12_waybel_0(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | m1_subset_1(sK4(sK1,X0),u1_struct_0(sK1))
      | v1_waybel_7(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f361,f50])).

fof(f361,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK1)
      | v1_xboole_0(X0)
      | ~ v1_waybel_0(X0,sK1)
      | ~ v12_waybel_0(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | m1_subset_1(sK4(sK1,X0),u1_struct_0(sK1))
      | v1_waybel_7(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f360,f49])).

fof(f360,plain,(
    ! [X0] :
      ( ~ v2_lattice3(sK1)
      | ~ l1_orders_2(sK1)
      | v1_xboole_0(X0)
      | ~ v1_waybel_0(X0,sK1)
      | ~ v12_waybel_0(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | m1_subset_1(sK4(sK1,X0),u1_struct_0(sK1))
      | v1_waybel_7(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f359,f46])).

fof(f359,plain,(
    ! [X0] :
      ( ~ v3_orders_2(sK1)
      | ~ v2_lattice3(sK1)
      | ~ l1_orders_2(sK1)
      | v1_xboole_0(X0)
      | ~ v1_waybel_0(X0,sK1)
      | ~ v12_waybel_0(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | m1_subset_1(sK4(sK1,X0),u1_struct_0(sK1))
      | v1_waybel_7(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f357,f47])).

fof(f357,plain,(
    ! [X0] :
      ( ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1)
      | ~ v2_lattice3(sK1)
      | ~ l1_orders_2(sK1)
      | v1_xboole_0(X0)
      | ~ v1_waybel_0(X0,sK1)
      | ~ v12_waybel_0(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | m1_subset_1(sK4(sK1,X0),u1_struct_0(sK1))
      | v1_waybel_7(X0,sK1) ) ),
    inference(resolution,[],[f66,f48])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v1_waybel_0(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | v1_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f500,plain,
    ( ~ m1_subset_1(sK4(sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK1,sK2),u1_struct_0(sK0))
    | r2_hidden(sK3(sK1,sK2),sK2)
    | r2_hidden(sK4(sK1,sK2),sK2)
    | spl7_2
    | ~ spl7_5
    | ~ spl7_6
    | spl7_9 ),
    inference(resolution,[],[f499,f473])).

fof(f473,plain,
    ( r2_hidden(k12_lattice3(sK0,sK3(sK1,sK2),sK4(sK1,sK2)),sK2)
    | spl7_2
    | ~ spl7_5
    | ~ spl7_6
    | spl7_9 ),
    inference(subsumption_resolution,[],[f472,f91])).

fof(f472,plain,
    ( r2_hidden(k12_lattice3(sK0,sK3(sK1,sK2),sK4(sK1,sK2)),sK2)
    | v1_waybel_7(sK2,sK1)
    | spl7_2
    | ~ spl7_5
    | ~ spl7_6
    | spl7_9 ),
    inference(subsumption_resolution,[],[f471,f45])).

fof(f471,plain,
    ( r2_hidden(k12_lattice3(sK0,sK3(sK1,sK2),sK4(sK1,sK2)),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_waybel_7(sK2,sK1)
    | spl7_2
    | ~ spl7_5
    | ~ spl7_6
    | spl7_9 ),
    inference(subsumption_resolution,[],[f470,f311])).

fof(f470,plain,
    ( r2_hidden(k12_lattice3(sK0,sK3(sK1,sK2),sK4(sK1,sK2)),sK2)
    | ~ v12_waybel_0(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_waybel_7(sK2,sK1)
    | spl7_2
    | ~ spl7_5
    | ~ spl7_6
    | spl7_9 ),
    inference(subsumption_resolution,[],[f469,f356])).

fof(f469,plain,
    ( r2_hidden(k12_lattice3(sK0,sK3(sK1,sK2),sK4(sK1,sK2)),sK2)
    | ~ v1_waybel_0(sK2,sK1)
    | ~ v12_waybel_0(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_waybel_7(sK2,sK1)
    | spl7_2
    | ~ spl7_5
    | ~ spl7_6
    | spl7_9 ),
    inference(subsumption_resolution,[],[f468,f41])).

fof(f468,plain,
    ( r2_hidden(k12_lattice3(sK0,sK3(sK1,sK2),sK4(sK1,sK2)),sK2)
    | v1_xboole_0(sK2)
    | ~ v1_waybel_0(sK2,sK1)
    | ~ v12_waybel_0(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_waybel_7(sK2,sK1)
    | spl7_2
    | ~ spl7_5
    | ~ spl7_6
    | spl7_9 ),
    inference(superposition,[],[f463,f423])).

fof(f423,plain,
    ( k12_lattice3(sK0,sK3(sK1,sK2),sK4(sK1,sK2)) = k12_lattice3(sK1,sK3(sK1,sK2),sK4(sK1,sK2))
    | spl7_2
    | ~ spl7_5
    | ~ spl7_6
    | spl7_9 ),
    inference(backward_demodulation,[],[f422,f421])).

fof(f421,plain,
    ( k12_lattice3(sK0,sK3(sK1,sK2),sK4(sK1,sK2)) = k2_yellow_0(sK0,k2_tarski(sK3(sK1,sK2),sK4(sK1,sK2)))
    | spl7_2
    | ~ spl7_5
    | ~ spl7_6
    | spl7_9 ),
    inference(backward_demodulation,[],[f415,f418])).

fof(f418,plain,
    ( k7_domain_1(u1_struct_0(sK0),sK3(sK1,sK2),sK4(sK1,sK2)) = k2_tarski(sK3(sK1,sK2),sK4(sK1,sK2))
    | spl7_2
    | ~ spl7_5
    | ~ spl7_6
    | spl7_9 ),
    inference(resolution,[],[f411,f378])).

fof(f378,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k7_domain_1(u1_struct_0(sK0),X3,sK4(sK1,sK2)) = k2_tarski(X3,sK4(sK1,sK2)) )
    | spl7_2
    | ~ spl7_5
    | ~ spl7_6
    | spl7_9 ),
    inference(subsumption_resolution,[],[f377,f140])).

fof(f140,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl7_9 ),
    inference(avatar_component_clause,[],[f138])).

fof(f377,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0))
        | k7_domain_1(u1_struct_0(sK0),X3,sK4(sK1,sK2)) = k2_tarski(X3,sK4(sK1,sK2)) )
    | spl7_2
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(resolution,[],[f373,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_domain_1)).

% (18269)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
fof(f415,plain,
    ( k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),sK3(sK1,sK2),sK4(sK1,sK2))) = k12_lattice3(sK0,sK3(sK1,sK2),sK4(sK1,sK2))
    | spl7_2
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(resolution,[],[f411,f374])).

fof(f374,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X0,sK4(sK1,sK2))) = k12_lattice3(sK0,X0,sK4(sK1,sK2)) )
    | spl7_2
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(resolution,[],[f373,f238])).

fof(f238,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X2,X3)) = k12_lattice3(sK0,X2,X3) ) ),
    inference(subsumption_resolution,[],[f237,f56])).

fof(f237,plain,(
    ! [X2,X3] :
      ( ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X2,X3)) = k12_lattice3(sK0,X2,X3) ) ),
    inference(subsumption_resolution,[],[f236,f55])).

fof(f55,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f236,plain,(
    ! [X2,X3] :
      ( ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X2,X3)) = k12_lattice3(sK0,X2,X3) ) ),
    inference(subsumption_resolution,[],[f235,f52])).

fof(f52,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f235,plain,(
    ! [X2,X3] :
      ( ~ v3_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X2,X3)) = k12_lattice3(sK0,X2,X3) ) ),
    inference(subsumption_resolution,[],[f227,f53])).

fof(f53,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f227,plain,(
    ! [X2,X3] :
      ( ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X2,X3)) = k12_lattice3(sK0,X2,X3) ) ),
    inference(resolution,[],[f65,f54])).

fof(f54,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) = k12_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) = k12_lattice3(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) = k12_lattice3(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) = k12_lattice3(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_yellow_0)).

fof(f422,plain,
    ( k12_lattice3(sK1,sK3(sK1,sK2),sK4(sK1,sK2)) = k2_yellow_0(sK0,k2_tarski(sK3(sK1,sK2),sK4(sK1,sK2)))
    | spl7_2
    | ~ spl7_5
    | ~ spl7_6
    | spl7_9 ),
    inference(backward_demodulation,[],[f417,f420])).

fof(f420,plain,
    ( k12_lattice3(sK1,sK3(sK1,sK2),sK4(sK1,sK2)) = k2_yellow_0(sK1,k2_tarski(sK3(sK1,sK2),sK4(sK1,sK2)))
    | spl7_2
    | ~ spl7_5
    | ~ spl7_6
    | spl7_9 ),
    inference(backward_demodulation,[],[f416,f418])).

fof(f416,plain,
    ( k12_lattice3(sK1,sK3(sK1,sK2),sK4(sK1,sK2)) = k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK0),sK3(sK1,sK2),sK4(sK1,sK2)))
    | spl7_2
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(resolution,[],[f411,f375])).

fof(f375,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k12_lattice3(sK1,X1,sK4(sK1,sK2)) = k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK0),X1,sK4(sK1,sK2))) )
    | spl7_2
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(resolution,[],[f373,f234])).

fof(f234,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k12_lattice3(sK1,X0,X1) = k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK0),X0,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f233,f116])).

fof(f233,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),X0,X1)) = k12_lattice3(sK1,X0,X1) )
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f232,f116])).

fof(f232,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),X0,X1)) = k12_lattice3(sK1,X0,X1) )
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f231,f116])).

fof(f231,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),X0,X1)) = k12_lattice3(sK1,X0,X1) ) ),
    inference(subsumption_resolution,[],[f230,f50])).

fof(f230,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),X0,X1)) = k12_lattice3(sK1,X0,X1) ) ),
    inference(subsumption_resolution,[],[f229,f49])).

fof(f229,plain,(
    ! [X0,X1] :
      ( ~ v2_lattice3(sK1)
      | ~ l1_orders_2(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),X0,X1)) = k12_lattice3(sK1,X0,X1) ) ),
    inference(subsumption_resolution,[],[f228,f46])).

fof(f228,plain,(
    ! [X0,X1] :
      ( ~ v3_orders_2(sK1)
      | ~ v2_lattice3(sK1)
      | ~ l1_orders_2(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),X0,X1)) = k12_lattice3(sK1,X0,X1) ) ),
    inference(subsumption_resolution,[],[f226,f47])).

fof(f226,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1)
      | ~ v2_lattice3(sK1)
      | ~ l1_orders_2(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),X0,X1)) = k12_lattice3(sK1,X0,X1) ) ),
    inference(resolution,[],[f65,f48])).

fof(f417,plain,
    ( k2_yellow_0(sK1,k2_tarski(sK3(sK1,sK2),sK4(sK1,sK2))) = k2_yellow_0(sK0,k2_tarski(sK3(sK1,sK2),sK4(sK1,sK2)))
    | spl7_2
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(resolution,[],[f411,f376])).

fof(f376,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k2_yellow_0(sK1,k2_tarski(X2,sK4(sK1,sK2))) = k2_yellow_0(sK0,k2_tarski(X2,sK4(sK1,sK2))) )
    | spl7_2
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(resolution,[],[f373,f218])).

fof(f218,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_yellow_0(sK1,k2_tarski(X0,X1)) = k2_yellow_0(sK0,k2_tarski(X0,X1)) )
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(resolution,[],[f217,f187])).

fof(f187,plain,
    ( ! [X0,X1] :
        ( r2_yellow_0(sK1,k2_tarski(X0,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f186,f116])).

fof(f186,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_yellow_0(sK1,k2_tarski(X0,X1)) )
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f185,f116])).

fof(f185,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | r2_yellow_0(sK1,k2_tarski(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f184,f49])).

fof(f184,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | r2_yellow_0(sK1,k2_tarski(X0,X1))
      | ~ v2_lattice3(sK1) ) ),
    inference(subsumption_resolution,[],[f182,f50])).

fof(f182,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | r2_yellow_0(sK1,k2_tarski(X0,X1))
      | ~ v2_lattice3(sK1) ) ),
    inference(resolution,[],[f74,f48])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ v2_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( r2_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( r2_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ( v2_lattice3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => r2_yellow_0(X0,k2_tarski(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_yellow_0)).

fof(f217,plain,
    ( ! [X0] :
        ( ~ r2_yellow_0(sK1,X0)
        | k2_yellow_0(sK1,X0) = k2_yellow_0(sK0,X0) )
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f216,f56])).

fof(f216,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(sK0)
        | ~ r2_yellow_0(sK1,X0)
        | k2_yellow_0(sK1,X0) = k2_yellow_0(sK0,X0) )
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(equality_resolution,[],[f207])).

fof(f207,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ l1_orders_2(X0)
        | ~ r2_yellow_0(sK1,X1)
        | k2_yellow_0(X0,X1) = k2_yellow_0(sK1,X1) )
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f206,f154])).

fof(f206,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1))
        | ~ l1_orders_2(X0)
        | ~ r2_yellow_0(sK1,X1)
        | k2_yellow_0(X0,X1) = k2_yellow_0(sK1,X1) )
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f200,f50])).

fof(f200,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1))
        | ~ l1_orders_2(X0)
        | ~ l1_orders_2(sK1)
        | ~ r2_yellow_0(sK1,X1)
        | k2_yellow_0(X0,X1) = k2_yellow_0(sK1,X1) )
    | ~ spl7_6 ),
    inference(superposition,[],[f60,f116])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,X2)
      | k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
              | ~ r2_yellow_0(X0,X2) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
              | ~ r2_yellow_0(X0,X2) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( r2_yellow_0(X0,X2)
               => k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_0)).

fof(f463,plain,
    ( ! [X0] :
        ( r2_hidden(k12_lattice3(sK1,sK3(sK1,X0),sK4(sK1,X0)),X0)
        | v1_xboole_0(X0)
        | ~ v1_waybel_0(X0,sK1)
        | ~ v12_waybel_0(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_waybel_7(X0,sK1) )
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f462,f116])).

fof(f462,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ v1_waybel_0(X0,sK1)
      | ~ v12_waybel_0(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | r2_hidden(k12_lattice3(sK1,sK3(sK1,X0),sK4(sK1,X0)),X0)
      | v1_waybel_7(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f461,f50])).

fof(f461,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK1)
      | v1_xboole_0(X0)
      | ~ v1_waybel_0(X0,sK1)
      | ~ v12_waybel_0(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | r2_hidden(k12_lattice3(sK1,sK3(sK1,X0),sK4(sK1,X0)),X0)
      | v1_waybel_7(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f460,f49])).

fof(f460,plain,(
    ! [X0] :
      ( ~ v2_lattice3(sK1)
      | ~ l1_orders_2(sK1)
      | v1_xboole_0(X0)
      | ~ v1_waybel_0(X0,sK1)
      | ~ v12_waybel_0(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | r2_hidden(k12_lattice3(sK1,sK3(sK1,X0),sK4(sK1,X0)),X0)
      | v1_waybel_7(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f459,f46])).

fof(f459,plain,(
    ! [X0] :
      ( ~ v3_orders_2(sK1)
      | ~ v2_lattice3(sK1)
      | ~ l1_orders_2(sK1)
      | v1_xboole_0(X0)
      | ~ v1_waybel_0(X0,sK1)
      | ~ v12_waybel_0(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | r2_hidden(k12_lattice3(sK1,sK3(sK1,X0),sK4(sK1,X0)),X0)
      | v1_waybel_7(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f457,f47])).

fof(f457,plain,(
    ! [X0] :
      ( ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1)
      | ~ v2_lattice3(sK1)
      | ~ l1_orders_2(sK1)
      | v1_xboole_0(X0)
      | ~ v1_waybel_0(X0,sK1)
      | ~ v12_waybel_0(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | r2_hidden(k12_lattice3(sK1,sK3(sK1,X0),sK4(sK1,X0)),X0)
      | v1_waybel_7(X0,sK1) ) ),
    inference(resolution,[],[f67,f48])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v1_waybel_0(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(k12_lattice3(X0,sK3(X0,X1),sK4(X0,X1)),X1)
      | v1_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f499,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k12_lattice3(sK0,X0,X1),sK2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,sK2)
      | r2_hidden(X1,sK2) ) ),
    inference(subsumption_resolution,[],[f498,f41])).

fof(f498,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(k12_lattice3(sK0,X0,X1),sK2)
      | r2_hidden(X0,sK2)
      | r2_hidden(X1,sK2)
      | v1_xboole_0(sK2) ) ),
    inference(subsumption_resolution,[],[f497,f45])).

fof(f497,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(k12_lattice3(sK0,X0,X1),sK2)
      | r2_hidden(X0,sK2)
      | r2_hidden(X1,sK2)
      | v1_xboole_0(sK2) ) ),
    inference(subsumption_resolution,[],[f496,f43])).

fof(f496,plain,(
    ! [X0,X1] :
      ( ~ v12_waybel_0(sK2,sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(k12_lattice3(sK0,X0,X1),sK2)
      | r2_hidden(X0,sK2)
      | r2_hidden(X1,sK2)
      | v1_xboole_0(sK2) ) ),
    inference(subsumption_resolution,[],[f491,f42])).

fof(f491,plain,(
    ! [X0,X1] :
      ( ~ v1_waybel_0(sK2,sK0)
      | ~ v12_waybel_0(sK2,sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(k12_lattice3(sK0,X0,X1),sK2)
      | r2_hidden(X0,sK2)
      | r2_hidden(X1,sK2)
      | v1_xboole_0(sK2) ) ),
    inference(resolution,[],[f486,f44])).

fof(f44,plain,(
    v1_waybel_7(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f486,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_waybel_7(X3,sK0)
      | ~ v1_waybel_0(X3,sK0)
      | ~ v12_waybel_0(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ r2_hidden(k12_lattice3(sK0,X4,X5),X3)
      | r2_hidden(X4,X3)
      | r2_hidden(X5,X3)
      | v1_xboole_0(X3) ) ),
    inference(subsumption_resolution,[],[f485,f56])).

fof(f485,plain,(
    ! [X4,X5,X3] :
      ( ~ l1_orders_2(sK0)
      | v1_xboole_0(X3)
      | ~ v1_waybel_0(X3,sK0)
      | ~ v12_waybel_0(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ r2_hidden(k12_lattice3(sK0,X4,X5),X3)
      | r2_hidden(X4,X3)
      | r2_hidden(X5,X3)
      | ~ v1_waybel_7(X3,sK0) ) ),
    inference(subsumption_resolution,[],[f484,f55])).

fof(f484,plain,(
    ! [X4,X5,X3] :
      ( ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(X3)
      | ~ v1_waybel_0(X3,sK0)
      | ~ v12_waybel_0(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ r2_hidden(k12_lattice3(sK0,X4,X5),X3)
      | r2_hidden(X4,X3)
      | r2_hidden(X5,X3)
      | ~ v1_waybel_7(X3,sK0) ) ),
    inference(subsumption_resolution,[],[f483,f52])).

fof(f483,plain,(
    ! [X4,X5,X3] :
      ( ~ v3_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(X3)
      | ~ v1_waybel_0(X3,sK0)
      | ~ v12_waybel_0(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ r2_hidden(k12_lattice3(sK0,X4,X5),X3)
      | r2_hidden(X4,X3)
      | r2_hidden(X5,X3)
      | ~ v1_waybel_7(X3,sK0) ) ),
    inference(subsumption_resolution,[],[f475,f53])).

fof(f475,plain,(
    ! [X4,X5,X3] :
      ( ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(X3)
      | ~ v1_waybel_0(X3,sK0)
      | ~ v12_waybel_0(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ r2_hidden(k12_lattice3(sK0,X4,X5),X3)
      | r2_hidden(X4,X3)
      | r2_hidden(X5,X3)
      | ~ v1_waybel_7(X3,sK0) ) ),
    inference(resolution,[],[f70,f54])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v1_waybel_0(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X3,X1)
      | ~ v1_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f532,plain,
    ( spl7_2
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_14 ),
    inference(avatar_contradiction_clause,[],[f531])).

fof(f531,plain,
    ( $false
    | spl7_2
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f530,f91])).

fof(f530,plain,
    ( v1_waybel_7(sK2,sK1)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f529,f45])).

fof(f529,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_waybel_7(sK2,sK1)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f528,f311])).

fof(f528,plain,
    ( ~ v12_waybel_0(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_waybel_7(sK2,sK1)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f527,f356])).

fof(f527,plain,
    ( ~ v1_waybel_0(sK2,sK1)
    | ~ v12_waybel_0(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_waybel_7(sK2,sK1)
    | ~ spl7_6
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f526,f41])).

fof(f526,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_waybel_0(sK2,sK1)
    | ~ v12_waybel_0(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_waybel_7(sK2,sK1)
    | ~ spl7_6
    | ~ spl7_14 ),
    inference(resolution,[],[f508,f260])).

fof(f260,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK1,X0),X0)
        | v1_xboole_0(X0)
        | ~ v1_waybel_0(X0,sK1)
        | ~ v12_waybel_0(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_waybel_7(X0,sK1) )
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f259,f116])).

fof(f259,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ v1_waybel_0(X0,sK1)
      | ~ v12_waybel_0(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r2_hidden(sK4(sK1,X0),X0)
      | v1_waybel_7(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f258,f50])).

fof(f258,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK1)
      | v1_xboole_0(X0)
      | ~ v1_waybel_0(X0,sK1)
      | ~ v12_waybel_0(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r2_hidden(sK4(sK1,X0),X0)
      | v1_waybel_7(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f257,f49])).

fof(f257,plain,(
    ! [X0] :
      ( ~ v2_lattice3(sK1)
      | ~ l1_orders_2(sK1)
      | v1_xboole_0(X0)
      | ~ v1_waybel_0(X0,sK1)
      | ~ v12_waybel_0(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r2_hidden(sK4(sK1,X0),X0)
      | v1_waybel_7(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f256,f46])).

fof(f256,plain,(
    ! [X0] :
      ( ~ v3_orders_2(sK1)
      | ~ v2_lattice3(sK1)
      | ~ l1_orders_2(sK1)
      | v1_xboole_0(X0)
      | ~ v1_waybel_0(X0,sK1)
      | ~ v12_waybel_0(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r2_hidden(sK4(sK1,X0),X0)
      | v1_waybel_7(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f254,f47])).

fof(f254,plain,(
    ! [X0] :
      ( ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1)
      | ~ v2_lattice3(sK1)
      | ~ l1_orders_2(sK1)
      | v1_xboole_0(X0)
      | ~ v1_waybel_0(X0,sK1)
      | ~ v12_waybel_0(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r2_hidden(sK4(sK1,X0),X0)
      | v1_waybel_7(X0,sK1) ) ),
    inference(resolution,[],[f69,f48])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v1_waybel_0(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(sK4(X0,X1),X1)
      | v1_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f508,plain,
    ( r2_hidden(sK4(sK1,sK2),sK2)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f506])).

fof(f525,plain,(
    ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f524])).

fof(f524,plain,
    ( $false
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f523,f50])).

fof(f523,plain,
    ( ~ l1_orders_2(sK1)
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f522,f49])).

fof(f522,plain,
    ( ~ v2_lattice3(sK1)
    | ~ l1_orders_2(sK1)
    | ~ spl7_7 ),
    inference(resolution,[],[f132,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

fof(f132,plain,
    ( v2_struct_0(sK1)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl7_7
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f144,plain,(
    spl7_8 ),
    inference(avatar_contradiction_clause,[],[f143])).

fof(f143,plain,
    ( $false
    | spl7_8 ),
    inference(subsumption_resolution,[],[f142,f50])).

fof(f142,plain,
    ( ~ l1_orders_2(sK1)
    | spl7_8 ),
    inference(resolution,[],[f136,f57])).

fof(f57,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f136,plain,
    ( ~ l1_struct_0(sK1)
    | spl7_8 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl7_8
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f141,plain,
    ( spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f128,f109,f138,f134,f130])).

fof(f128,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl7_6 ),
    inference(superposition,[],[f64,f116])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f123,plain,
    ( spl7_1
    | ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | spl7_1
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f120,f45])).

fof(f120,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_1
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f87,f116])).

fof(f87,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl7_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f114,plain,(
    spl7_5 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | spl7_5 ),
    inference(subsumption_resolution,[],[f112,f50])).

fof(f112,plain,
    ( ~ l1_orders_2(sK1)
    | spl7_5 ),
    inference(resolution,[],[f107,f58])).

fof(f58,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f107,plain,
    ( ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | spl7_5 ),
    inference(avatar_component_clause,[],[f105])).

fof(f111,plain,
    ( ~ spl7_5
    | spl7_6 ),
    inference(avatar_split_clause,[],[f101,f109,f105])).

fof(f101,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
      | u1_struct_0(sK1) = X0 ) ),
    inference(superposition,[],[f77,f51])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f100,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f83,f97,f93,f89,f85])).

fof(f83,plain,
    ( ~ v1_waybel_0(sK2,sK1)
    | ~ v12_waybel_0(sK2,sK1)
    | ~ v1_waybel_7(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f40,f41])).

fof(f40,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_waybel_0(sK2,sK1)
    | ~ v12_waybel_0(sK2,sK1)
    | ~ v1_waybel_7(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f18])).

%------------------------------------------------------------------------------
