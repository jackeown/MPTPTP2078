%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:52 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 379 expanded)
%              Number of leaves         :   39 ( 163 expanded)
%              Depth                    :   16
%              Number of atoms          :  780 (1697 expanded)
%              Number of equality atoms :   86 ( 171 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f506,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f73,f78,f83,f88,f93,f99,f104,f111,f116,f139,f179,f212,f224,f240,f251,f255,f273,f286,f295,f327,f337,f420,f428,f459,f505])).

fof(f505,plain,
    ( ~ spl4_3
    | ~ spl4_5
    | spl4_6
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_52 ),
    inference(avatar_contradiction_clause,[],[f504])).

fof(f504,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_5
    | spl4_6
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_52 ),
    inference(subsumption_resolution,[],[f503,f115])).

fof(f115,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl4_10
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f503,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl4_3
    | ~ spl4_5
    | spl4_6
    | ~ spl4_9
    | ~ spl4_52 ),
    inference(forward_demodulation,[],[f502,f110])).

fof(f110,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl4_9
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f502,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_3
    | ~ spl4_5
    | spl4_6
    | ~ spl4_52 ),
    inference(subsumption_resolution,[],[f501,f77])).

fof(f77,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl4_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f501,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_5
    | spl4_6
    | ~ spl4_52 ),
    inference(subsumption_resolution,[],[f500,f87])).

fof(f87,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl4_5
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f500,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl4_6
    | ~ spl4_52 ),
    inference(subsumption_resolution,[],[f493,f92])).

fof(f92,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl4_6
  <=> v3_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f493,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_52 ),
    inference(trivial_inequality_removal,[],[f491])).

fof(f491,plain,
    ( sK1 != sK1
    | v3_tex_2(sK1,sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_52 ),
    inference(superposition,[],[f53,f458])).

fof(f458,plain,
    ( sK1 = sK2(sK0,sK1)
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f456])).

fof(f456,plain,
    ( spl4_52
  <=> sK1 = sK2(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f53,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK2(X0,X1) != X1
                & r1_tarski(X1,sK2(X0,X1))
                & v2_tex_2(sK2(X0,X1),X0)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK2(X0,X1) != X1
        & r1_tarski(X1,sK2(X0,X1))
        & v2_tex_2(sK2(X0,X1),X0)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

% (17032)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

fof(f459,plain,
    ( spl4_52
    | ~ spl4_17
    | ~ spl4_36
    | ~ spl4_49 ),
    inference(avatar_split_clause,[],[f437,f425,f324,f177,f456])).

fof(f177,plain,
    ( spl4_17
  <=> ! [X0] : k9_subset_1(k2_struct_0(sK0),X0,k2_struct_0(sK0)) = k3_xboole_0(X0,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f324,plain,
    ( spl4_36
  <=> sK2(sK0,sK1) = k3_xboole_0(sK2(sK0,sK1),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f425,plain,
    ( spl4_49
  <=> sK1 = k9_subset_1(k2_struct_0(sK0),sK2(sK0,sK1),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f437,plain,
    ( sK1 = sK2(sK0,sK1)
    | ~ spl4_17
    | ~ spl4_36
    | ~ spl4_49 ),
    inference(backward_demodulation,[],[f326,f433])).

fof(f433,plain,
    ( sK1 = k3_xboole_0(sK2(sK0,sK1),k2_struct_0(sK0))
    | ~ spl4_17
    | ~ spl4_49 ),
    inference(superposition,[],[f427,f178])).

fof(f178,plain,
    ( ! [X0] : k9_subset_1(k2_struct_0(sK0),X0,k2_struct_0(sK0)) = k3_xboole_0(X0,k2_struct_0(sK0))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f177])).

fof(f427,plain,
    ( sK1 = k9_subset_1(k2_struct_0(sK0),sK2(sK0,sK1),k2_struct_0(sK0))
    | ~ spl4_49 ),
    inference(avatar_component_clause,[],[f425])).

fof(f326,plain,
    ( sK2(sK0,sK1) = k3_xboole_0(sK2(sK0,sK1),k2_struct_0(sK0))
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f324])).

fof(f428,plain,
    ( spl4_49
    | ~ spl4_10
    | ~ spl4_23
    | ~ spl4_26
    | ~ spl4_48 ),
    inference(avatar_split_clause,[],[f423,f418,f248,f221,f113,f425])).

fof(f221,plain,
    ( spl4_23
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f248,plain,
    ( spl4_26
  <=> r1_tarski(sK1,sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f418,plain,
    ( spl4_48
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(X0,sK2(sK0,sK1))
        | k9_subset_1(k2_struct_0(sK0),sK2(sK0,sK1),k2_pre_topc(sK0,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f423,plain,
    ( sK1 = k9_subset_1(k2_struct_0(sK0),sK2(sK0,sK1),k2_struct_0(sK0))
    | ~ spl4_10
    | ~ spl4_23
    | ~ spl4_26
    | ~ spl4_48 ),
    inference(forward_demodulation,[],[f422,f223])).

fof(f223,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f221])).

fof(f422,plain,
    ( sK1 = k9_subset_1(k2_struct_0(sK0),sK2(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ spl4_10
    | ~ spl4_26
    | ~ spl4_48 ),
    inference(subsumption_resolution,[],[f421,f115])).

fof(f421,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | sK1 = k9_subset_1(k2_struct_0(sK0),sK2(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ spl4_26
    | ~ spl4_48 ),
    inference(resolution,[],[f419,f250])).

fof(f250,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f248])).

fof(f419,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2(sK0,sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k9_subset_1(k2_struct_0(sK0),sK2(sK0,sK1),k2_pre_topc(sK0,X0)) = X0 )
    | ~ spl4_48 ),
    inference(avatar_component_clause,[],[f418])).

fof(f420,plain,
    ( spl4_48
    | ~ spl4_5
    | spl4_6
    | ~ spl4_10
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f346,f335,f113,f90,f85,f418])).

fof(f335,plain,
    ( spl4_38
  <=> ! [X1,X2] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(X2,sK2(sK0,X1))
        | k9_subset_1(k2_struct_0(sK0),sK2(sK0,X1),k2_pre_topc(sK0,X2)) = X2
        | v3_tex_2(X1,sK0)
        | ~ v2_tex_2(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f346,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(X0,sK2(sK0,sK1))
        | k9_subset_1(k2_struct_0(sK0),sK2(sK0,sK1),k2_pre_topc(sK0,X0)) = X0 )
    | ~ spl4_5
    | spl4_6
    | ~ spl4_10
    | ~ spl4_38 ),
    inference(subsumption_resolution,[],[f345,f115])).

fof(f345,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(X0,sK2(sK0,sK1))
        | k9_subset_1(k2_struct_0(sK0),sK2(sK0,sK1),k2_pre_topc(sK0,X0)) = X0
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl4_5
    | spl4_6
    | ~ spl4_38 ),
    inference(subsumption_resolution,[],[f343,f92])).

fof(f343,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(X0,sK2(sK0,sK1))
        | k9_subset_1(k2_struct_0(sK0),sK2(sK0,sK1),k2_pre_topc(sK0,X0)) = X0
        | v3_tex_2(sK1,sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl4_5
    | ~ spl4_38 ),
    inference(resolution,[],[f336,f87])).

fof(f336,plain,
    ( ! [X2,X1] :
        ( ~ v2_tex_2(X1,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(X2,sK2(sK0,X1))
        | k9_subset_1(k2_struct_0(sK0),sK2(sK0,X1),k2_pre_topc(sK0,X2)) = X2
        | v3_tex_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f335])).

fof(f337,plain,
    ( spl4_38
    | ~ spl4_3
    | ~ spl4_9
    | ~ spl4_27
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f281,f271,f253,f108,f75,f335])).

fof(f253,plain,
    ( spl4_27
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK0)
        | v3_tex_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f271,plain,
    ( spl4_29
  <=> ! [X1,X0] :
        ( k9_subset_1(k2_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(X0,X1)
        | ~ v2_tex_2(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f281,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(X2,sK2(sK0,X1))
        | k9_subset_1(k2_struct_0(sK0),sK2(sK0,X1),k2_pre_topc(sK0,X2)) = X2
        | v3_tex_2(X1,sK0)
        | ~ v2_tex_2(X1,sK0) )
    | ~ spl4_3
    | ~ spl4_9
    | ~ spl4_27
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f280,f254])).

fof(f254,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v3_tex_2(X0,sK0) )
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f253])).

fof(f280,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(sK2(sK0,X1),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(X2,sK2(sK0,X1))
        | k9_subset_1(k2_struct_0(sK0),sK2(sK0,X1),k2_pre_topc(sK0,X2)) = X2
        | v3_tex_2(X1,sK0)
        | ~ v2_tex_2(X1,sK0) )
    | ~ spl4_3
    | ~ spl4_9
    | ~ spl4_29 ),
    inference(forward_demodulation,[],[f279,f110])).

fof(f279,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(sK2(sK0,X1),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(X2,sK2(sK0,X1))
        | k9_subset_1(k2_struct_0(sK0),sK2(sK0,X1),k2_pre_topc(sK0,X2)) = X2
        | v3_tex_2(X1,sK0)
        | ~ v2_tex_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_3
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f277,f77])).

fof(f277,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(sK2(sK0,X1),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(X2,sK2(sK0,X1))
        | k9_subset_1(k2_struct_0(sK0),sK2(sK0,X1),k2_pre_topc(sK0,X2)) = X2
        | v3_tex_2(X1,sK0)
        | ~ v2_tex_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl4_29 ),
    inference(resolution,[],[f272,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v2_tex_2(sK2(X0,X1),X0)
      | v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f272,plain,
    ( ! [X0,X1] :
        ( ~ v2_tex_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(X0,X1)
        | k9_subset_1(k2_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0 )
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f271])).

fof(f327,plain,
    ( spl4_36
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f300,f292,f324])).

fof(f292,plain,
    ( spl4_31
  <=> r1_tarski(sK2(sK0,sK1),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f300,plain,
    ( sK2(sK0,sK1) = k3_xboole_0(sK2(sK0,sK1),k2_struct_0(sK0))
    | ~ spl4_31 ),
    inference(resolution,[],[f294,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f294,plain,
    ( r1_tarski(sK2(sK0,sK1),k2_struct_0(sK0))
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f292])).

% (17018)Refutation not found, incomplete strategy% (17018)------------------------------
% (17018)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f295,plain,
    ( spl4_31
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f290,f283,f292])).

fof(f283,plain,
    ( spl4_30
  <=> m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f290,plain,
    ( r1_tarski(sK2(sK0,sK1),k2_struct_0(sK0))
    | ~ spl4_30 ),
    inference(resolution,[],[f285,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f285,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f283])).

fof(f286,plain,
    ( spl4_30
    | ~ spl4_5
    | spl4_6
    | ~ spl4_10
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f261,f253,f113,f90,f85,f283])).

fof(f261,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl4_5
    | spl4_6
    | ~ spl4_10
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f260,f92])).

fof(f260,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | v3_tex_2(sK1,sK0)
    | ~ spl4_5
    | ~ spl4_10
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f258,f115])).

fof(f258,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v3_tex_2(sK1,sK0)
    | ~ spl4_5
    | ~ spl4_27 ),
    inference(resolution,[],[f254,f87])).

fof(f273,plain,
    ( spl4_29
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f189,f108,f75,f70,f65,f271])).

fof(f65,plain,
    ( spl4_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

% (17026)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f70,plain,
    ( spl4_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f189,plain,
    ( ! [X0,X1] :
        ( k9_subset_1(k2_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(X0,X1)
        | ~ v2_tex_2(X1,sK0) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f188,f110])).

fof(f188,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(X0,X1)
        | ~ v2_tex_2(X1,sK0)
        | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0 )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f187,f110])).

fof(f187,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(X0,X1)
        | ~ v2_tex_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0 )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f186,f110])).

fof(f186,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0 )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f185,f67])).

fof(f67,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f185,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0
        | v2_struct_0(sK0) )
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f184,f77])).

fof(f184,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0
        | v2_struct_0(sK0) )
    | ~ spl4_2 ),
    inference(resolution,[],[f56,f72])).

fof(f72,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r1_tarski(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1)))
                & r1_tarski(sK3(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1)))
        & r1_tarski(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r1_tarski(X2,X1)
                 => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tex_2)).

fof(f255,plain,
    ( spl4_27
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f166,f108,f75,f253])).

fof(f166,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK0)
        | v3_tex_2(X0,sK0) )
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f165,f110])).

fof(f165,plain,
    ( ! [X0] :
        ( m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_tex_2(X0,sK0) )
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f164,f110])).

fof(f164,plain,
    ( ! [X0] :
        ( m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_tex_2(X0,sK0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f50,f77])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f251,plain,
    ( spl4_26
    | ~ spl4_5
    | spl4_6
    | ~ spl4_10
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f244,f238,f113,f90,f85,f248])).

fof(f238,plain,
    ( spl4_25
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | r1_tarski(X0,sK2(sK0,X0))
        | ~ v2_tex_2(X0,sK0)
        | v3_tex_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f244,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | ~ spl4_5
    | spl4_6
    | ~ spl4_10
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f243,f92])).

fof(f243,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | v3_tex_2(sK1,sK0)
    | ~ spl4_5
    | ~ spl4_10
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f241,f115])).

fof(f241,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v3_tex_2(sK1,sK0)
    | ~ spl4_5
    | ~ spl4_25 ),
    inference(resolution,[],[f239,f87])).

fof(f239,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | r1_tarski(X0,sK2(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v3_tex_2(X0,sK0) )
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f238])).

fof(f240,plain,
    ( spl4_25
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f152,f108,f75,f238])).

fof(f152,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | r1_tarski(X0,sK2(sK0,X0))
        | ~ v2_tex_2(X0,sK0)
        | v3_tex_2(X0,sK0) )
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f151,f110])).

fof(f151,plain,
    ( ! [X0] :
        ( r1_tarski(X0,sK2(sK0,X0))
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_tex_2(X0,sK0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f52,f77])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | r1_tarski(X1,sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f224,plain,
    ( spl4_23
    | ~ spl4_4
    | ~ spl4_10
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f219,f210,f113,f80,f221])).

fof(f80,plain,
    ( spl4_4
  <=> v1_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f210,plain,
    ( spl4_21
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v1_tops_1(X0,sK0)
        | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f219,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ spl4_4
    | ~ spl4_10
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f218,f115])).

fof(f218,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ spl4_4
    | ~ spl4_21 ),
    inference(resolution,[],[f211,f82])).

fof(f82,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f80])).

fof(f211,plain,
    ( ! [X0] :
        ( ~ v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) )
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f210])).

fof(f212,plain,
    ( spl4_21
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f141,f108,f75,f210])).

fof(f141,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v1_tops_1(X0,sK0)
        | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) )
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f140,f110])).

fof(f140,plain,
    ( ! [X0] :
        ( ~ v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f54,f77])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(f179,plain,
    ( spl4_17
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f142,f136,f177])).

% (17012)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
fof(f136,plain,
    ( spl4_13
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f142,plain,
    ( ! [X0] : k9_subset_1(k2_struct_0(sK0),X0,k2_struct_0(sK0)) = k3_xboole_0(X0,k2_struct_0(sK0))
    | ~ spl4_13 ),
    inference(resolution,[],[f138,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f138,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f136])).

fof(f139,plain,
    ( spl4_13
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f126,f108,f101,f136])).

fof(f101,plain,
    ( spl4_8
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f126,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f125,f103])).

fof(f103,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f101])).

fof(f125,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | ~ spl4_9 ),
    inference(superposition,[],[f46,f110])).

fof(f46,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f116,plain,
    ( spl4_10
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f106,f101,f96,f113])).

fof(f96,plain,
    ( spl4_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f106,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(backward_demodulation,[],[f98,f105])).

fof(f105,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl4_8 ),
    inference(resolution,[],[f45,f103])).

fof(f45,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f98,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f96])).

fof(f111,plain,
    ( spl4_9
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f105,f101,f108])).

fof(f104,plain,
    ( spl4_8
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f94,f75,f101])).

fof(f94,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f47,f77])).

fof(f47,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f99,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f41,f96])).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ v3_tex_2(sK1,sK0)
    & v2_tex_2(sK1,sK0)
    & v1_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v3_tex_2(X1,X0)
            & v2_tex_2(X1,X0)
            & v1_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v3_tex_2(X1,sK0)
          & v2_tex_2(X1,sK0)
          & v1_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ~ v3_tex_2(X1,sK0)
        & v2_tex_2(X1,sK0)
        & v1_tops_1(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v3_tex_2(sK1,sK0)
      & v2_tex_2(sK1,sK0)
      & v1_tops_1(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tex_2(X1,X0)
          & v2_tex_2(X1,X0)
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tex_2(X1,X0)
          & v2_tex_2(X1,X0)
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v2_tex_2(X1,X0)
                & v1_tops_1(X1,X0) )
             => v3_tex_2(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_tex_2(X1,X0)
              & v1_tops_1(X1,X0) )
           => v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).

fof(f93,plain,(
    ~ spl4_6 ),
    inference(avatar_split_clause,[],[f44,f90])).

fof(f44,plain,(
    ~ v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f88,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f43,f85])).

fof(f43,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f83,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f42,f80])).

fof(f42,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f78,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f40,f75])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f73,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f39,f70])).

fof(f39,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f68,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f38,f65])).

fof(f38,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:50:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (17031)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.48  % (17023)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.49  % (17019)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.49  % (17019)Refutation not found, incomplete strategy% (17019)------------------------------
% 0.22/0.49  % (17019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (17019)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (17019)Memory used [KB]: 1663
% 0.22/0.49  % (17019)Time elapsed: 0.069 s
% 0.22/0.49  % (17019)------------------------------
% 0.22/0.49  % (17019)------------------------------
% 0.22/0.49  % (17018)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.49  % (17014)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.49  % (17029)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.50  % (17027)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.50  % (17035)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.50  % (17034)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.50  % (17037)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.51  % (17014)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f506,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f68,f73,f78,f83,f88,f93,f99,f104,f111,f116,f139,f179,f212,f224,f240,f251,f255,f273,f286,f295,f327,f337,f420,f428,f459,f505])).
% 0.22/0.51  fof(f505,plain,(
% 0.22/0.51    ~spl4_3 | ~spl4_5 | spl4_6 | ~spl4_9 | ~spl4_10 | ~spl4_52),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f504])).
% 0.22/0.51  fof(f504,plain,(
% 0.22/0.51    $false | (~spl4_3 | ~spl4_5 | spl4_6 | ~spl4_9 | ~spl4_10 | ~spl4_52)),
% 0.22/0.51    inference(subsumption_resolution,[],[f503,f115])).
% 0.22/0.51  fof(f115,plain,(
% 0.22/0.51    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl4_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f113])).
% 0.22/0.51  fof(f113,plain,(
% 0.22/0.51    spl4_10 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.51  fof(f503,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl4_3 | ~spl4_5 | spl4_6 | ~spl4_9 | ~spl4_52)),
% 0.22/0.51    inference(forward_demodulation,[],[f502,f110])).
% 0.22/0.51  fof(f110,plain,(
% 0.22/0.51    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl4_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f108])).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    spl4_9 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.51  fof(f502,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_3 | ~spl4_5 | spl4_6 | ~spl4_52)),
% 0.22/0.51    inference(subsumption_resolution,[],[f501,f77])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    l1_pre_topc(sK0) | ~spl4_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f75])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    spl4_3 <=> l1_pre_topc(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.51  fof(f501,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl4_5 | spl4_6 | ~spl4_52)),
% 0.22/0.51    inference(subsumption_resolution,[],[f500,f87])).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    v2_tex_2(sK1,sK0) | ~spl4_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f85])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    spl4_5 <=> v2_tex_2(sK1,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.51  fof(f500,plain,(
% 0.22/0.51    ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl4_6 | ~spl4_52)),
% 0.22/0.51    inference(subsumption_resolution,[],[f493,f92])).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    ~v3_tex_2(sK1,sK0) | spl4_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f90])).
% 0.22/0.51  fof(f90,plain,(
% 0.22/0.51    spl4_6 <=> v3_tex_2(sK1,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.51  fof(f493,plain,(
% 0.22/0.51    v3_tex_2(sK1,sK0) | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl4_52),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f491])).
% 0.22/0.51  fof(f491,plain,(
% 0.22/0.51    sK1 != sK1 | v3_tex_2(sK1,sK0) | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl4_52),
% 0.22/0.51    inference(superposition,[],[f53,f458])).
% 0.22/0.51  fof(f458,plain,(
% 0.22/0.51    sK1 = sK2(sK0,sK1) | ~spl4_52),
% 0.22/0.51    inference(avatar_component_clause,[],[f456])).
% 0.22/0.51  fof(f456,plain,(
% 0.22/0.51    spl4_52 <=> sK1 = sK2(sK0,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ( ! [X0,X1] : (sK2(X0,X1) != X1 | v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(rectify,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f18])).
% 0.22/0.51  % (17032)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).
% 0.22/0.51  fof(f459,plain,(
% 0.22/0.51    spl4_52 | ~spl4_17 | ~spl4_36 | ~spl4_49),
% 0.22/0.51    inference(avatar_split_clause,[],[f437,f425,f324,f177,f456])).
% 0.22/0.51  fof(f177,plain,(
% 0.22/0.51    spl4_17 <=> ! [X0] : k9_subset_1(k2_struct_0(sK0),X0,k2_struct_0(sK0)) = k3_xboole_0(X0,k2_struct_0(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.22/0.51  fof(f324,plain,(
% 0.22/0.51    spl4_36 <=> sK2(sK0,sK1) = k3_xboole_0(sK2(sK0,sK1),k2_struct_0(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.22/0.51  fof(f425,plain,(
% 0.22/0.51    spl4_49 <=> sK1 = k9_subset_1(k2_struct_0(sK0),sK2(sK0,sK1),k2_struct_0(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 0.22/0.51  fof(f437,plain,(
% 0.22/0.51    sK1 = sK2(sK0,sK1) | (~spl4_17 | ~spl4_36 | ~spl4_49)),
% 0.22/0.51    inference(backward_demodulation,[],[f326,f433])).
% 0.22/0.51  fof(f433,plain,(
% 0.22/0.51    sK1 = k3_xboole_0(sK2(sK0,sK1),k2_struct_0(sK0)) | (~spl4_17 | ~spl4_49)),
% 0.22/0.51    inference(superposition,[],[f427,f178])).
% 0.22/0.51  fof(f178,plain,(
% 0.22/0.51    ( ! [X0] : (k9_subset_1(k2_struct_0(sK0),X0,k2_struct_0(sK0)) = k3_xboole_0(X0,k2_struct_0(sK0))) ) | ~spl4_17),
% 0.22/0.51    inference(avatar_component_clause,[],[f177])).
% 0.22/0.51  fof(f427,plain,(
% 0.22/0.51    sK1 = k9_subset_1(k2_struct_0(sK0),sK2(sK0,sK1),k2_struct_0(sK0)) | ~spl4_49),
% 0.22/0.51    inference(avatar_component_clause,[],[f425])).
% 0.22/0.51  fof(f326,plain,(
% 0.22/0.51    sK2(sK0,sK1) = k3_xboole_0(sK2(sK0,sK1),k2_struct_0(sK0)) | ~spl4_36),
% 0.22/0.51    inference(avatar_component_clause,[],[f324])).
% 0.22/0.51  fof(f428,plain,(
% 0.22/0.51    spl4_49 | ~spl4_10 | ~spl4_23 | ~spl4_26 | ~spl4_48),
% 0.22/0.51    inference(avatar_split_clause,[],[f423,f418,f248,f221,f113,f425])).
% 0.22/0.51  fof(f221,plain,(
% 0.22/0.51    spl4_23 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.22/0.51  fof(f248,plain,(
% 0.22/0.51    spl4_26 <=> r1_tarski(sK1,sK2(sK0,sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.22/0.51  fof(f418,plain,(
% 0.22/0.51    spl4_48 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,sK2(sK0,sK1)) | k9_subset_1(k2_struct_0(sK0),sK2(sK0,sK1),k2_pre_topc(sK0,X0)) = X0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 0.22/0.51  fof(f423,plain,(
% 0.22/0.51    sK1 = k9_subset_1(k2_struct_0(sK0),sK2(sK0,sK1),k2_struct_0(sK0)) | (~spl4_10 | ~spl4_23 | ~spl4_26 | ~spl4_48)),
% 0.22/0.51    inference(forward_demodulation,[],[f422,f223])).
% 0.22/0.51  fof(f223,plain,(
% 0.22/0.51    k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~spl4_23),
% 0.22/0.51    inference(avatar_component_clause,[],[f221])).
% 0.22/0.51  fof(f422,plain,(
% 0.22/0.51    sK1 = k9_subset_1(k2_struct_0(sK0),sK2(sK0,sK1),k2_pre_topc(sK0,sK1)) | (~spl4_10 | ~spl4_26 | ~spl4_48)),
% 0.22/0.51    inference(subsumption_resolution,[],[f421,f115])).
% 0.22/0.51  fof(f421,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | sK1 = k9_subset_1(k2_struct_0(sK0),sK2(sK0,sK1),k2_pre_topc(sK0,sK1)) | (~spl4_26 | ~spl4_48)),
% 0.22/0.51    inference(resolution,[],[f419,f250])).
% 0.22/0.51  fof(f250,plain,(
% 0.22/0.51    r1_tarski(sK1,sK2(sK0,sK1)) | ~spl4_26),
% 0.22/0.51    inference(avatar_component_clause,[],[f248])).
% 0.22/0.51  fof(f419,plain,(
% 0.22/0.51    ( ! [X0] : (~r1_tarski(X0,sK2(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k9_subset_1(k2_struct_0(sK0),sK2(sK0,sK1),k2_pre_topc(sK0,X0)) = X0) ) | ~spl4_48),
% 0.22/0.51    inference(avatar_component_clause,[],[f418])).
% 0.22/0.51  fof(f420,plain,(
% 0.22/0.51    spl4_48 | ~spl4_5 | spl4_6 | ~spl4_10 | ~spl4_38),
% 0.22/0.51    inference(avatar_split_clause,[],[f346,f335,f113,f90,f85,f418])).
% 0.22/0.51  fof(f335,plain,(
% 0.22/0.51    spl4_38 <=> ! [X1,X2] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X2,sK2(sK0,X1)) | k9_subset_1(k2_struct_0(sK0),sK2(sK0,X1),k2_pre_topc(sK0,X2)) = X2 | v3_tex_2(X1,sK0) | ~v2_tex_2(X1,sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.22/0.51  fof(f346,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,sK2(sK0,sK1)) | k9_subset_1(k2_struct_0(sK0),sK2(sK0,sK1),k2_pre_topc(sK0,X0)) = X0) ) | (~spl4_5 | spl4_6 | ~spl4_10 | ~spl4_38)),
% 0.22/0.51    inference(subsumption_resolution,[],[f345,f115])).
% 0.22/0.51  fof(f345,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,sK2(sK0,sK1)) | k9_subset_1(k2_struct_0(sK0),sK2(sK0,sK1),k2_pre_topc(sK0,X0)) = X0 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))) ) | (~spl4_5 | spl4_6 | ~spl4_38)),
% 0.22/0.51    inference(subsumption_resolution,[],[f343,f92])).
% 0.22/0.51  fof(f343,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,sK2(sK0,sK1)) | k9_subset_1(k2_struct_0(sK0),sK2(sK0,sK1),k2_pre_topc(sK0,X0)) = X0 | v3_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))) ) | (~spl4_5 | ~spl4_38)),
% 0.22/0.51    inference(resolution,[],[f336,f87])).
% 0.22/0.51  fof(f336,plain,(
% 0.22/0.51    ( ! [X2,X1] : (~v2_tex_2(X1,sK0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X2,sK2(sK0,X1)) | k9_subset_1(k2_struct_0(sK0),sK2(sK0,X1),k2_pre_topc(sK0,X2)) = X2 | v3_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl4_38),
% 0.22/0.51    inference(avatar_component_clause,[],[f335])).
% 0.22/0.51  fof(f337,plain,(
% 0.22/0.51    spl4_38 | ~spl4_3 | ~spl4_9 | ~spl4_27 | ~spl4_29),
% 0.22/0.51    inference(avatar_split_clause,[],[f281,f271,f253,f108,f75,f335])).
% 0.22/0.51  fof(f253,plain,(
% 0.22/0.51    spl4_27 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | v3_tex_2(X0,sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.22/0.51  fof(f271,plain,(
% 0.22/0.51    spl4_29 <=> ! [X1,X0] : (k9_subset_1(k2_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,X1) | ~v2_tex_2(X1,sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.22/0.51  fof(f281,plain,(
% 0.22/0.51    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X2,sK2(sK0,X1)) | k9_subset_1(k2_struct_0(sK0),sK2(sK0,X1),k2_pre_topc(sK0,X2)) = X2 | v3_tex_2(X1,sK0) | ~v2_tex_2(X1,sK0)) ) | (~spl4_3 | ~spl4_9 | ~spl4_27 | ~spl4_29)),
% 0.22/0.51    inference(subsumption_resolution,[],[f280,f254])).
% 0.22/0.51  fof(f254,plain,(
% 0.22/0.51    ( ! [X0] : (~v2_tex_2(X0,sK0) | m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v3_tex_2(X0,sK0)) ) | ~spl4_27),
% 0.22/0.51    inference(avatar_component_clause,[],[f253])).
% 0.22/0.51  fof(f280,plain,(
% 0.22/0.51    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK2(sK0,X1),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X2,sK2(sK0,X1)) | k9_subset_1(k2_struct_0(sK0),sK2(sK0,X1),k2_pre_topc(sK0,X2)) = X2 | v3_tex_2(X1,sK0) | ~v2_tex_2(X1,sK0)) ) | (~spl4_3 | ~spl4_9 | ~spl4_29)),
% 0.22/0.51    inference(forward_demodulation,[],[f279,f110])).
% 0.22/0.51  fof(f279,plain,(
% 0.22/0.51    ( ! [X2,X1] : (~m1_subset_1(sK2(sK0,X1),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X2,sK2(sK0,X1)) | k9_subset_1(k2_struct_0(sK0),sK2(sK0,X1),k2_pre_topc(sK0,X2)) = X2 | v3_tex_2(X1,sK0) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl4_3 | ~spl4_29)),
% 0.22/0.51    inference(subsumption_resolution,[],[f277,f77])).
% 0.22/0.51  fof(f277,plain,(
% 0.22/0.51    ( ! [X2,X1] : (~m1_subset_1(sK2(sK0,X1),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X2,sK2(sK0,X1)) | k9_subset_1(k2_struct_0(sK0),sK2(sK0,X1),k2_pre_topc(sK0,X2)) = X2 | v3_tex_2(X1,sK0) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl4_29),
% 0.22/0.51    inference(resolution,[],[f272,f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v2_tex_2(sK2(X0,X1),X0) | v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f31])).
% 0.22/0.51  fof(f272,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,X1) | k9_subset_1(k2_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0) ) | ~spl4_29),
% 0.22/0.51    inference(avatar_component_clause,[],[f271])).
% 0.22/0.51  fof(f327,plain,(
% 0.22/0.51    spl4_36 | ~spl4_31),
% 0.22/0.51    inference(avatar_split_clause,[],[f300,f292,f324])).
% 0.22/0.51  fof(f292,plain,(
% 0.22/0.51    spl4_31 <=> r1_tarski(sK2(sK0,sK1),k2_struct_0(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.22/0.51  fof(f300,plain,(
% 0.22/0.51    sK2(sK0,sK1) = k3_xboole_0(sK2(sK0,sK1),k2_struct_0(sK0)) | ~spl4_31),
% 0.22/0.51    inference(resolution,[],[f294,f60])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.51  fof(f294,plain,(
% 0.22/0.51    r1_tarski(sK2(sK0,sK1),k2_struct_0(sK0)) | ~spl4_31),
% 0.22/0.51    inference(avatar_component_clause,[],[f292])).
% 0.22/0.51  % (17018)Refutation not found, incomplete strategy% (17018)------------------------------
% 0.22/0.51  % (17018)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  fof(f295,plain,(
% 0.22/0.51    spl4_31 | ~spl4_30),
% 0.22/0.51    inference(avatar_split_clause,[],[f290,f283,f292])).
% 0.22/0.51  fof(f283,plain,(
% 0.22/0.51    spl4_30 <=> m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.22/0.51  fof(f290,plain,(
% 0.22/0.51    r1_tarski(sK2(sK0,sK1),k2_struct_0(sK0)) | ~spl4_30),
% 0.22/0.51    inference(resolution,[],[f285,f61])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.51    inference(nnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.51  fof(f285,plain,(
% 0.22/0.51    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl4_30),
% 0.22/0.51    inference(avatar_component_clause,[],[f283])).
% 0.22/0.51  fof(f286,plain,(
% 0.22/0.51    spl4_30 | ~spl4_5 | spl4_6 | ~spl4_10 | ~spl4_27),
% 0.22/0.51    inference(avatar_split_clause,[],[f261,f253,f113,f90,f85,f283])).
% 0.22/0.51  fof(f261,plain,(
% 0.22/0.51    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0))) | (~spl4_5 | spl4_6 | ~spl4_10 | ~spl4_27)),
% 0.22/0.51    inference(subsumption_resolution,[],[f260,f92])).
% 0.22/0.51  fof(f260,plain,(
% 0.22/0.51    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0))) | v3_tex_2(sK1,sK0) | (~spl4_5 | ~spl4_10 | ~spl4_27)),
% 0.22/0.51    inference(subsumption_resolution,[],[f258,f115])).
% 0.22/0.51  fof(f258,plain,(
% 0.22/0.51    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v3_tex_2(sK1,sK0) | (~spl4_5 | ~spl4_27)),
% 0.22/0.51    inference(resolution,[],[f254,f87])).
% 0.22/0.51  fof(f273,plain,(
% 0.22/0.51    spl4_29 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f189,f108,f75,f70,f65,f271])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    spl4_1 <=> v2_struct_0(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.51  % (17026)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    spl4_2 <=> v2_pre_topc(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.51  fof(f189,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k9_subset_1(k2_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,X1) | ~v2_tex_2(X1,sK0)) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_9)),
% 0.22/0.51    inference(forward_demodulation,[],[f188,f110])).
% 0.22/0.51  fof(f188,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,X1) | ~v2_tex_2(X1,sK0) | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_9)),
% 0.22/0.51    inference(forward_demodulation,[],[f187,f110])).
% 0.22/0.51  fof(f187,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,X1) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_9)),
% 0.22/0.51    inference(forward_demodulation,[],[f186,f110])).
% 0.22/0.51  fof(f186,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0) ) | (spl4_1 | ~spl4_2 | ~spl4_3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f185,f67])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    ~v2_struct_0(sK0) | spl4_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f65])).
% 0.22/0.51  fof(f185,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0 | v2_struct_0(sK0)) ) | (~spl4_2 | ~spl4_3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f184,f77])).
% 0.22/0.51  fof(f184,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0 | v2_struct_0(sK0)) ) | ~spl4_2),
% 0.22/0.51    inference(resolution,[],[f56,f72])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    v2_pre_topc(sK0) | ~spl4_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f70])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1))) & r1_tarski(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ! [X1,X0] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1))) & r1_tarski(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(rectify,[],[f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tex_2)).
% 0.22/0.51  fof(f255,plain,(
% 0.22/0.51    spl4_27 | ~spl4_3 | ~spl4_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f166,f108,f75,f253])).
% 0.22/0.51  fof(f166,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | v3_tex_2(X0,sK0)) ) | (~spl4_3 | ~spl4_9)),
% 0.22/0.51    inference(forward_demodulation,[],[f165,f110])).
% 0.22/0.51  fof(f165,plain,(
% 0.22/0.51    ( ! [X0] : (m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(X0,sK0)) ) | (~spl4_3 | ~spl4_9)),
% 0.22/0.51    inference(forward_demodulation,[],[f164,f110])).
% 0.22/0.51  fof(f164,plain,(
% 0.22/0.51    ( ! [X0] : (m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(X0,sK0)) ) | ~spl4_3),
% 0.22/0.51    inference(resolution,[],[f50,f77])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_tex_2(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f31])).
% 0.22/0.51  fof(f251,plain,(
% 0.22/0.51    spl4_26 | ~spl4_5 | spl4_6 | ~spl4_10 | ~spl4_25),
% 0.22/0.51    inference(avatar_split_clause,[],[f244,f238,f113,f90,f85,f248])).
% 0.22/0.51  fof(f238,plain,(
% 0.22/0.51    spl4_25 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | r1_tarski(X0,sK2(sK0,X0)) | ~v2_tex_2(X0,sK0) | v3_tex_2(X0,sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.22/0.51  fof(f244,plain,(
% 0.22/0.51    r1_tarski(sK1,sK2(sK0,sK1)) | (~spl4_5 | spl4_6 | ~spl4_10 | ~spl4_25)),
% 0.22/0.51    inference(subsumption_resolution,[],[f243,f92])).
% 0.22/0.51  fof(f243,plain,(
% 0.22/0.51    r1_tarski(sK1,sK2(sK0,sK1)) | v3_tex_2(sK1,sK0) | (~spl4_5 | ~spl4_10 | ~spl4_25)),
% 0.22/0.51    inference(subsumption_resolution,[],[f241,f115])).
% 0.22/0.51  fof(f241,plain,(
% 0.22/0.51    r1_tarski(sK1,sK2(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v3_tex_2(sK1,sK0) | (~spl4_5 | ~spl4_25)),
% 0.22/0.51    inference(resolution,[],[f239,f87])).
% 0.22/0.51  fof(f239,plain,(
% 0.22/0.51    ( ! [X0] : (~v2_tex_2(X0,sK0) | r1_tarski(X0,sK2(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v3_tex_2(X0,sK0)) ) | ~spl4_25),
% 0.22/0.51    inference(avatar_component_clause,[],[f238])).
% 0.22/0.51  fof(f240,plain,(
% 0.22/0.51    spl4_25 | ~spl4_3 | ~spl4_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f152,f108,f75,f238])).
% 0.22/0.51  fof(f152,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | r1_tarski(X0,sK2(sK0,X0)) | ~v2_tex_2(X0,sK0) | v3_tex_2(X0,sK0)) ) | (~spl4_3 | ~spl4_9)),
% 0.22/0.51    inference(forward_demodulation,[],[f151,f110])).
% 0.22/0.51  fof(f151,plain,(
% 0.22/0.51    ( ! [X0] : (r1_tarski(X0,sK2(sK0,X0)) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(X0,sK0)) ) | ~spl4_3),
% 0.22/0.51    inference(resolution,[],[f52,f77])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | r1_tarski(X1,sK2(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_tex_2(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f31])).
% 0.22/0.51  fof(f224,plain,(
% 0.22/0.51    spl4_23 | ~spl4_4 | ~spl4_10 | ~spl4_21),
% 0.22/0.51    inference(avatar_split_clause,[],[f219,f210,f113,f80,f221])).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    spl4_4 <=> v1_tops_1(sK1,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.51  fof(f210,plain,(
% 0.22/0.51    spl4_21 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tops_1(X0,sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.22/0.51  fof(f219,plain,(
% 0.22/0.51    k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | (~spl4_4 | ~spl4_10 | ~spl4_21)),
% 0.22/0.51    inference(subsumption_resolution,[],[f218,f115])).
% 0.22/0.51  fof(f218,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | (~spl4_4 | ~spl4_21)),
% 0.22/0.51    inference(resolution,[],[f211,f82])).
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    v1_tops_1(sK1,sK0) | ~spl4_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f80])).
% 0.22/0.51  fof(f211,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)) ) | ~spl4_21),
% 0.22/0.51    inference(avatar_component_clause,[],[f210])).
% 0.22/0.51  fof(f212,plain,(
% 0.22/0.51    spl4_21 | ~spl4_3 | ~spl4_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f141,f108,f75,f210])).
% 0.22/0.51  fof(f141,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tops_1(X0,sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)) ) | (~spl4_3 | ~spl4_9)),
% 0.22/0.51    inference(forward_demodulation,[],[f140,f110])).
% 0.22/0.51  fof(f140,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)) ) | ~spl4_3),
% 0.22/0.51    inference(resolution,[],[f54,f77])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_struct_0(X0) = k2_pre_topc(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
% 0.22/0.51  fof(f179,plain,(
% 0.22/0.51    spl4_17 | ~spl4_13),
% 0.22/0.51    inference(avatar_split_clause,[],[f142,f136,f177])).
% 0.22/0.51  % (17012)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  fof(f136,plain,(
% 0.22/0.51    spl4_13 <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.51  fof(f142,plain,(
% 0.22/0.51    ( ! [X0] : (k9_subset_1(k2_struct_0(sK0),X0,k2_struct_0(sK0)) = k3_xboole_0(X0,k2_struct_0(sK0))) ) | ~spl4_13),
% 0.22/0.51    inference(resolution,[],[f138,f63])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.22/0.51  fof(f138,plain,(
% 0.22/0.51    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl4_13),
% 0.22/0.51    inference(avatar_component_clause,[],[f136])).
% 0.22/0.51  fof(f139,plain,(
% 0.22/0.51    spl4_13 | ~spl4_8 | ~spl4_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f126,f108,f101,f136])).
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    spl4_8 <=> l1_struct_0(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.51  fof(f126,plain,(
% 0.22/0.51    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | (~spl4_8 | ~spl4_9)),
% 0.22/0.51    inference(subsumption_resolution,[],[f125,f103])).
% 0.22/0.51  fof(f103,plain,(
% 0.22/0.51    l1_struct_0(sK0) | ~spl4_8),
% 0.22/0.51    inference(avatar_component_clause,[],[f101])).
% 0.22/0.51  fof(f125,plain,(
% 0.22/0.51    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_struct_0(sK0) | ~spl4_9),
% 0.22/0.51    inference(superposition,[],[f46,f110])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).
% 0.22/0.51  fof(f116,plain,(
% 0.22/0.51    spl4_10 | ~spl4_7 | ~spl4_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f106,f101,f96,f113])).
% 0.22/0.51  fof(f96,plain,(
% 0.22/0.51    spl4_7 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.51  fof(f106,plain,(
% 0.22/0.51    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl4_7 | ~spl4_8)),
% 0.22/0.51    inference(backward_demodulation,[],[f98,f105])).
% 0.22/0.51  fof(f105,plain,(
% 0.22/0.51    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl4_8),
% 0.22/0.51    inference(resolution,[],[f45,f103])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.51  fof(f98,plain,(
% 0.22/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f96])).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    spl4_9 | ~spl4_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f105,f101,f108])).
% 0.22/0.51  fof(f104,plain,(
% 0.22/0.51    spl4_8 | ~spl4_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f94,f75,f101])).
% 0.22/0.51  fof(f94,plain,(
% 0.22/0.51    l1_struct_0(sK0) | ~spl4_3),
% 0.22/0.51    inference(resolution,[],[f47,f77])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.51  fof(f99,plain,(
% 0.22/0.51    spl4_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f41,f96])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    (~v3_tex_2(sK1,sK0) & v2_tex_2(sK1,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f25,f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (~v3_tex_2(X1,X0) & v2_tex_2(X1,X0) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v3_tex_2(X1,sK0) & v2_tex_2(X1,sK0) & v1_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ? [X1] : (~v3_tex_2(X1,sK0) & v2_tex_2(X1,sK0) & v1_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v3_tex_2(sK1,sK0) & v2_tex_2(sK1,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (~v3_tex_2(X1,X0) & v2_tex_2(X1,X0) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : ((~v3_tex_2(X1,X0) & (v2_tex_2(X1,X0) & v1_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,negated_conjecture,(
% 0.22/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 0.22/0.52    inference(negated_conjecture,[],[f10])).
% 0.22/0.52  fof(f10,conjecture,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).
% 0.22/0.52  fof(f93,plain,(
% 0.22/0.52    ~spl4_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f44,f90])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ~v3_tex_2(sK1,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f88,plain,(
% 0.22/0.52    spl4_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f43,f85])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    v2_tex_2(sK1,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    spl4_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f42,f80])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    v1_tops_1(sK1,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    spl4_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f40,f75])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    l1_pre_topc(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    spl4_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f39,f70])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    v2_pre_topc(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    ~spl4_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f38,f65])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ~v2_struct_0(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (17014)------------------------------
% 0.22/0.52  % (17014)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (17014)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (17014)Memory used [KB]: 6524
% 0.22/0.52  % (17014)Time elapsed: 0.072 s
% 0.22/0.52  % (17014)------------------------------
% 0.22/0.52  % (17014)------------------------------
% 0.22/0.52  % (17011)Success in time 0.148 s
%------------------------------------------------------------------------------
