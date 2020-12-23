%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 488 expanded)
%              Number of leaves         :   20 ( 145 expanded)
%              Depth                    :   15
%              Number of atoms          :  590 (3757 expanded)
%              Number of equality atoms :   34 (  93 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f343,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f94,f118,f125,f132,f150,f156,f162,f187,f231,f255,f342])).

fof(f342,plain,
    ( ~ spl5_7
    | ~ spl5_8
    | spl5_10 ),
    inference(avatar_contradiction_clause,[],[f341])).

fof(f341,plain,
    ( $false
    | ~ spl5_7
    | ~ spl5_8
    | spl5_10 ),
    inference(subsumption_resolution,[],[f298,f289])).

fof(f289,plain,
    ( k1_xboole_0 != sK1
    | ~ spl5_8
    | spl5_10 ),
    inference(backward_demodulation,[],[f185,f281])).

fof(f281,plain,
    ( k1_xboole_0 = sK2(sK0,sK1)
    | ~ spl5_8 ),
    inference(resolution,[],[f256,f60])).

fof(f60,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f256,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK2(sK0,sK1) = X0 )
    | ~ spl5_8 ),
    inference(resolution,[],[f178,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f178,plain,
    ( v1_xboole_0(sK2(sK0,sK1))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl5_8
  <=> v1_xboole_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f185,plain,
    ( sK1 != sK2(sK0,sK1)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl5_10
  <=> sK1 = sK2(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f298,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(resolution,[],[f285,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f285,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(backward_demodulation,[],[f131,f281])).

fof(f131,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl5_7
  <=> r1_tarski(sK1,sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f255,plain,
    ( spl5_1
    | ~ spl5_3
    | ~ spl5_10 ),
    inference(avatar_contradiction_clause,[],[f254])).

fof(f254,plain,
    ( $false
    | spl5_1
    | ~ spl5_3
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f253,f55])).

fof(f55,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( ~ v1_zfmisc_1(sK1)
      | ~ v3_tex_2(sK1,sK0) )
    & ( v1_zfmisc_1(sK1)
      | v3_tex_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & ~ v1_xboole_0(sK1)
    & l1_pre_topc(sK0)
    & v2_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_zfmisc_1(X1)
              | ~ v3_tex_2(X1,X0) )
            & ( v1_zfmisc_1(X1)
              | v3_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,sK0) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK0)
      & v2_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ( ~ v1_zfmisc_1(X1)
          | ~ v3_tex_2(X1,sK0) )
        & ( v1_zfmisc_1(X1)
          | v3_tex_2(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & ~ v1_xboole_0(X1) )
   => ( ( ~ v1_zfmisc_1(sK1)
        | ~ v3_tex_2(sK1,sK0) )
      & ( v1_zfmisc_1(sK1)
        | v3_tex_2(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ( v3_tex_2(X1,X0)
            <=> v1_zfmisc_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v3_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tex_2)).

fof(f253,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_1
    | ~ spl5_3
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f252,f57])).

fof(f57,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f252,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl5_1
    | ~ spl5_3
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f251,f106])).

fof(f106,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl5_3
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f251,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl5_1
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f250,f88])).

fof(f88,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl5_1
  <=> v3_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f250,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_10 ),
    inference(trivial_inequality_removal,[],[f249])).

fof(f249,plain,
    ( sK1 != sK1
    | v3_tex_2(sK1,sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_10 ),
    inference(superposition,[],[f68,f186])).

fof(f186,plain,
    ( sK1 = sK2(sK0,sK1)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f184])).

fof(f68,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).

fof(f44,plain,(
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

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

fof(f231,plain,
    ( ~ spl5_5
    | ~ spl5_6
    | spl5_9 ),
    inference(avatar_contradiction_clause,[],[f230])).

fof(f230,plain,
    ( $false
    | ~ spl5_5
    | ~ spl5_6
    | spl5_9 ),
    inference(subsumption_resolution,[],[f229,f182])).

fof(f182,plain,
    ( ~ v1_zfmisc_1(sK2(sK0,sK1))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl5_9
  <=> v1_zfmisc_1(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f229,plain,
    ( v1_zfmisc_1(sK2(sK0,sK1))
    | ~ spl5_5
    | ~ spl5_6
    | spl5_9 ),
    inference(resolution,[],[f227,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_zfmisc_1)).

fof(f227,plain,
    ( v1_xboole_0(sK2(sK0,sK1))
    | ~ spl5_5
    | ~ spl5_6
    | spl5_9 ),
    inference(subsumption_resolution,[],[f226,f52])).

fof(f52,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f226,plain,
    ( v1_xboole_0(sK2(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl5_5
    | ~ spl5_6
    | spl5_9 ),
    inference(subsumption_resolution,[],[f225,f53])).

fof(f53,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f225,plain,
    ( v1_xboole_0(sK2(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_5
    | ~ spl5_6
    | spl5_9 ),
    inference(subsumption_resolution,[],[f224,f54])).

fof(f54,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f224,plain,
    ( v1_xboole_0(sK2(sK0,sK1))
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_5
    | ~ spl5_6
    | spl5_9 ),
    inference(subsumption_resolution,[],[f223,f55])).

fof(f223,plain,
    ( v1_xboole_0(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_5
    | ~ spl5_6
    | spl5_9 ),
    inference(subsumption_resolution,[],[f222,f182])).

fof(f222,plain,
    ( v1_zfmisc_1(sK2(sK0,sK1))
    | v1_xboole_0(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f193,f124])).

fof(f124,plain,
    ( v2_tex_2(sK2(sK0,sK1),sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl5_6
  <=> v2_tex_2(sK2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f193,plain,
    ( ~ v2_tex_2(sK2(sK0,sK1),sK0)
    | v1_zfmisc_1(sK2(sK0,sK1))
    | v1_xboole_0(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_5 ),
    inference(resolution,[],[f117,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ~ v1_zfmisc_1(X1) )
            & ( v1_zfmisc_1(X1)
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).

fof(f117,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl5_5
  <=> m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f187,plain,
    ( spl5_8
    | ~ spl5_9
    | spl5_10
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f174,f129,f184,f180,f176])).

fof(f174,plain,
    ( sK1 = sK2(sK0,sK1)
    | ~ v1_zfmisc_1(sK2(sK0,sK1))
    | v1_xboole_0(sK2(sK0,sK1))
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f172,f56])).

fof(f56,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f172,plain,
    ( sK1 = sK2(sK0,sK1)
    | ~ v1_zfmisc_1(sK2(sK0,sK1))
    | v1_xboole_0(sK2(sK0,sK1))
    | v1_xboole_0(sK1)
    | ~ spl5_7 ),
    inference(resolution,[],[f131,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f162,plain,
    ( spl5_3
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f161,f90,f105])).

fof(f90,plain,
    ( spl5_2
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f161,plain,
    ( ~ v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f160,f52])).

fof(f160,plain,
    ( ~ v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f159,f53])).

fof(f159,plain,
    ( ~ v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f158,f54])).

fof(f158,plain,
    ( ~ v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f157,f55])).

fof(f157,plain,
    ( ~ v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f102,f56])).

fof(f102,plain,
    ( ~ v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f57,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_zfmisc_1(X1)
      | v2_tex_2(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f156,plain,
    ( spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f155,f105,f90])).

fof(f155,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_zfmisc_1(sK1) ),
    inference(subsumption_resolution,[],[f154,f52])).

fof(f154,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_zfmisc_1(sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f153,f53])).

fof(f153,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_zfmisc_1(sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f152,f54])).

fof(f152,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_zfmisc_1(sK1)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f151,f55])).

fof(f151,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_zfmisc_1(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f101,f56])).

fof(f101,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_zfmisc_1(sK1)
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f57,f71])).

fof(f150,plain,
    ( ~ spl5_1
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | ~ spl5_1
    | spl5_3 ),
    inference(subsumption_resolution,[],[f142,f87])).

fof(f87,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f142,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f141,f55])).

fof(f141,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f96,f107])).

fof(f107,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f105])).

fof(f96,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f57,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f132,plain,
    ( ~ spl5_3
    | spl5_7
    | spl5_1 ),
    inference(avatar_split_clause,[],[f127,f86,f129,f105])).

fof(f127,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f126,f55])).

fof(f126,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f100,f88])).

fof(f100,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0)
    | v3_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f57,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | v3_tex_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f125,plain,
    ( ~ spl5_3
    | spl5_6
    | spl5_1 ),
    inference(avatar_split_clause,[],[f120,f86,f122,f105])).

% (22871)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
fof(f120,plain,
    ( v2_tex_2(sK2(sK0,sK1),sK0)
    | ~ v2_tex_2(sK1,sK0)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f119,f55])).

fof(f119,plain,
    ( v2_tex_2(sK2(sK0,sK1),sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f99,f88])).

fof(f99,plain,
    ( v2_tex_2(sK2(sK0,sK1),sK0)
    | ~ v2_tex_2(sK1,sK0)
    | v3_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f57,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(sK2(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | v3_tex_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f118,plain,
    ( ~ spl5_3
    | spl5_5
    | spl5_1 ),
    inference(avatar_split_clause,[],[f113,f86,f115,f105])).

fof(f113,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f112,f55])).

fof(f112,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f98,f88])).

fof(f98,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | v3_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f57,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | v3_tex_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f94,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f58,f90,f86])).

fof(f58,plain,
    ( v1_zfmisc_1(sK1)
    | v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f93,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f59,f90,f86])).

fof(f59,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:12:40 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (22874)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (22882)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.50  % (22862)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (22866)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (22861)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (22861)Refutation not found, incomplete strategy% (22861)------------------------------
% 0.21/0.50  % (22861)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (22864)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (22865)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (22868)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (22879)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (22884)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.51  % (22869)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (22875)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (22862)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (22861)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (22861)Memory used [KB]: 10618
% 0.21/0.51  % (22861)Time elapsed: 0.090 s
% 0.21/0.51  % (22861)------------------------------
% 0.21/0.51  % (22861)------------------------------
% 0.21/0.51  % (22863)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (22873)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f343,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f93,f94,f118,f125,f132,f150,f156,f162,f187,f231,f255,f342])).
% 0.21/0.51  fof(f342,plain,(
% 0.21/0.51    ~spl5_7 | ~spl5_8 | spl5_10),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f341])).
% 0.21/0.51  fof(f341,plain,(
% 0.21/0.51    $false | (~spl5_7 | ~spl5_8 | spl5_10)),
% 0.21/0.51    inference(subsumption_resolution,[],[f298,f289])).
% 0.21/0.51  fof(f289,plain,(
% 0.21/0.51    k1_xboole_0 != sK1 | (~spl5_8 | spl5_10)),
% 0.21/0.51    inference(backward_demodulation,[],[f185,f281])).
% 0.21/0.51  fof(f281,plain,(
% 0.21/0.51    k1_xboole_0 = sK2(sK0,sK1) | ~spl5_8),
% 0.21/0.51    inference(resolution,[],[f256,f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.51  fof(f256,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_xboole_0(X0) | sK2(sK0,sK1) = X0) ) | ~spl5_8),
% 0.21/0.51    inference(resolution,[],[f178,f84])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 0.21/0.51  fof(f178,plain,(
% 0.21/0.51    v1_xboole_0(sK2(sK0,sK1)) | ~spl5_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f176])).
% 0.21/0.51  fof(f176,plain,(
% 0.21/0.51    spl5_8 <=> v1_xboole_0(sK2(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.51  fof(f185,plain,(
% 0.21/0.51    sK1 != sK2(sK0,sK1) | spl5_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f184])).
% 0.21/0.51  fof(f184,plain,(
% 0.21/0.51    spl5_10 <=> sK1 = sK2(sK0,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.51  fof(f298,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | (~spl5_7 | ~spl5_8)),
% 0.21/0.51    inference(resolution,[],[f285,f70])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.52  fof(f285,plain,(
% 0.21/0.52    r1_tarski(sK1,k1_xboole_0) | (~spl5_7 | ~spl5_8)),
% 0.21/0.52    inference(backward_demodulation,[],[f131,f281])).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    r1_tarski(sK1,sK2(sK0,sK1)) | ~spl5_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f129])).
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    spl5_7 <=> r1_tarski(sK1,sK2(sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.52  fof(f255,plain,(
% 0.21/0.52    spl5_1 | ~spl5_3 | ~spl5_10),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f254])).
% 0.21/0.52  fof(f254,plain,(
% 0.21/0.52    $false | (spl5_1 | ~spl5_3 | ~spl5_10)),
% 0.21/0.52    inference(subsumption_resolution,[],[f253,f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    l1_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ((~v1_zfmisc_1(sK1) | ~v3_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f39,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK1) | ~v3_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,negated_conjecture,(
% 0.21/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.52    inference(negated_conjecture,[],[f16])).
% 0.21/0.52  fof(f16,conjecture,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tex_2)).
% 0.21/0.52  fof(f253,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | (spl5_1 | ~spl5_3 | ~spl5_10)),
% 0.21/0.52    inference(subsumption_resolution,[],[f252,f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f252,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl5_1 | ~spl5_3 | ~spl5_10)),
% 0.21/0.52    inference(subsumption_resolution,[],[f251,f106])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    v2_tex_2(sK1,sK0) | ~spl5_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f105])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    spl5_3 <=> v2_tex_2(sK1,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.52  fof(f251,plain,(
% 0.21/0.52    ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl5_1 | ~spl5_10)),
% 0.21/0.52    inference(subsumption_resolution,[],[f250,f88])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    ~v3_tex_2(sK1,sK0) | spl5_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f86])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    spl5_1 <=> v3_tex_2(sK1,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.52  fof(f250,plain,(
% 0.21/0.52    v3_tex_2(sK1,sK0) | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl5_10),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f249])).
% 0.21/0.52  fof(f249,plain,(
% 0.21/0.52    sK1 != sK1 | v3_tex_2(sK1,sK0) | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl5_10),
% 0.21/0.52    inference(superposition,[],[f68,f186])).
% 0.21/0.52  fof(f186,plain,(
% 0.21/0.52    sK1 = sK2(sK0,sK1) | ~spl5_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f184])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sK2(X0,X1) != X1 | v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(rectify,[],[f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).
% 0.21/0.52  fof(f231,plain,(
% 0.21/0.52    ~spl5_5 | ~spl5_6 | spl5_9),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f230])).
% 0.21/0.52  fof(f230,plain,(
% 0.21/0.52    $false | (~spl5_5 | ~spl5_6 | spl5_9)),
% 0.21/0.52    inference(subsumption_resolution,[],[f229,f182])).
% 0.21/0.52  fof(f182,plain,(
% 0.21/0.52    ~v1_zfmisc_1(sK2(sK0,sK1)) | spl5_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f180])).
% 0.21/0.52  fof(f180,plain,(
% 0.21/0.52    spl5_9 <=> v1_zfmisc_1(sK2(sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.52  fof(f229,plain,(
% 0.21/0.52    v1_zfmisc_1(sK2(sK0,sK1)) | (~spl5_5 | ~spl5_6 | spl5_9)),
% 0.21/0.52    inference(resolution,[],[f227,f69])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_xboole_0(X0) | v1_zfmisc_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_zfmisc_1)).
% 0.21/0.52  fof(f227,plain,(
% 0.21/0.52    v1_xboole_0(sK2(sK0,sK1)) | (~spl5_5 | ~spl5_6 | spl5_9)),
% 0.21/0.52    inference(subsumption_resolution,[],[f226,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ~v2_struct_0(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f226,plain,(
% 0.21/0.52    v1_xboole_0(sK2(sK0,sK1)) | v2_struct_0(sK0) | (~spl5_5 | ~spl5_6 | spl5_9)),
% 0.21/0.52    inference(subsumption_resolution,[],[f225,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    v2_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f225,plain,(
% 0.21/0.52    v1_xboole_0(sK2(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_5 | ~spl5_6 | spl5_9)),
% 0.21/0.52    inference(subsumption_resolution,[],[f224,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    v2_tdlat_3(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f224,plain,(
% 0.21/0.52    v1_xboole_0(sK2(sK0,sK1)) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_5 | ~spl5_6 | spl5_9)),
% 0.21/0.52    inference(subsumption_resolution,[],[f223,f55])).
% 0.21/0.52  fof(f223,plain,(
% 0.21/0.52    v1_xboole_0(sK2(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_5 | ~spl5_6 | spl5_9)),
% 0.21/0.52    inference(subsumption_resolution,[],[f222,f182])).
% 0.21/0.52  fof(f222,plain,(
% 0.21/0.52    v1_zfmisc_1(sK2(sK0,sK1)) | v1_xboole_0(sK2(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_5 | ~spl5_6)),
% 0.21/0.52    inference(subsumption_resolution,[],[f193,f124])).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    v2_tex_2(sK2(sK0,sK1),sK0) | ~spl5_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f122])).
% 0.21/0.52  fof(f122,plain,(
% 0.21/0.52    spl5_6 <=> v2_tex_2(sK2(sK0,sK1),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.52  fof(f193,plain,(
% 0.21/0.52    ~v2_tex_2(sK2(sK0,sK1),sK0) | v1_zfmisc_1(sK2(sK0,sK1)) | v1_xboole_0(sK2(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_5),
% 0.21/0.52    inference(resolution,[],[f117,f71])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | v1_zfmisc_1(X1) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1)) & (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f115])).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    spl5_5 <=> m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.52  fof(f187,plain,(
% 0.21/0.52    spl5_8 | ~spl5_9 | spl5_10 | ~spl5_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f174,f129,f184,f180,f176])).
% 0.21/0.52  fof(f174,plain,(
% 0.21/0.52    sK1 = sK2(sK0,sK1) | ~v1_zfmisc_1(sK2(sK0,sK1)) | v1_xboole_0(sK2(sK0,sK1)) | ~spl5_7),
% 0.21/0.52    inference(subsumption_resolution,[],[f172,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ~v1_xboole_0(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f172,plain,(
% 0.21/0.52    sK1 = sK2(sK0,sK1) | ~v1_zfmisc_1(sK2(sK0,sK1)) | v1_xboole_0(sK2(sK0,sK1)) | v1_xboole_0(sK1) | ~spl5_7),
% 0.21/0.52    inference(resolution,[],[f131,f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.52    inference(flattening,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,axiom,(
% 0.21/0.52    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 0.21/0.52  fof(f162,plain,(
% 0.21/0.52    spl5_3 | ~spl5_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f161,f90,f105])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    spl5_2 <=> v1_zfmisc_1(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.52  fof(f161,plain,(
% 0.21/0.52    ~v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f160,f52])).
% 0.21/0.52  fof(f160,plain,(
% 0.21/0.52    ~v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0) | v2_struct_0(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f159,f53])).
% 0.21/0.52  fof(f159,plain,(
% 0.21/0.52    ~v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f158,f54])).
% 0.21/0.52  fof(f158,plain,(
% 0.21/0.52    ~v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f157,f55])).
% 0.21/0.52  fof(f157,plain,(
% 0.21/0.52    ~v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f102,f56])).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    ~v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.52    inference(resolution,[],[f57,f72])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_zfmisc_1(X1) | v2_tex_2(X1,X0) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f46])).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    spl5_2 | ~spl5_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f155,f105,f90])).
% 0.21/0.52  fof(f155,plain,(
% 0.21/0.52    ~v2_tex_2(sK1,sK0) | v1_zfmisc_1(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f154,f52])).
% 0.21/0.52  fof(f154,plain,(
% 0.21/0.52    ~v2_tex_2(sK1,sK0) | v1_zfmisc_1(sK1) | v2_struct_0(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f153,f53])).
% 0.21/0.52  fof(f153,plain,(
% 0.21/0.52    ~v2_tex_2(sK1,sK0) | v1_zfmisc_1(sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f152,f54])).
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    ~v2_tex_2(sK1,sK0) | v1_zfmisc_1(sK1) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f151,f55])).
% 0.21/0.52  fof(f151,plain,(
% 0.21/0.52    ~v2_tex_2(sK1,sK0) | v1_zfmisc_1(sK1) | ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f101,f56])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    ~v2_tex_2(sK1,sK0) | v1_zfmisc_1(sK1) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.52    inference(resolution,[],[f57,f71])).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    ~spl5_1 | spl5_3),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f149])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    $false | (~spl5_1 | spl5_3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f142,f87])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    v3_tex_2(sK1,sK0) | ~spl5_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f86])).
% 0.21/0.52  fof(f142,plain,(
% 0.21/0.52    ~v3_tex_2(sK1,sK0) | spl5_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f141,f55])).
% 0.21/0.52  fof(f141,plain,(
% 0.21/0.52    ~v3_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | spl5_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f96,f107])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    ~v2_tex_2(sK1,sK0) | spl5_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f105])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    ~v3_tex_2(sK1,sK0) | v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.52    inference(resolution,[],[f57,f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | v2_tex_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f45])).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    ~spl5_3 | spl5_7 | spl5_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f127,f86,f129,f105])).
% 0.21/0.52  fof(f127,plain,(
% 0.21/0.52    r1_tarski(sK1,sK2(sK0,sK1)) | ~v2_tex_2(sK1,sK0) | spl5_1),
% 0.21/0.52    inference(subsumption_resolution,[],[f126,f55])).
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    r1_tarski(sK1,sK2(sK0,sK1)) | ~v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | spl5_1),
% 0.21/0.52    inference(subsumption_resolution,[],[f100,f88])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    r1_tarski(sK1,sK2(sK0,sK1)) | ~v2_tex_2(sK1,sK0) | v3_tex_2(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.52    inference(resolution,[],[f57,f67])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,sK2(X0,X1)) | ~v2_tex_2(X1,X0) | v3_tex_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f45])).
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    ~spl5_3 | spl5_6 | spl5_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f120,f86,f122,f105])).
% 0.21/0.52  % (22871)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    v2_tex_2(sK2(sK0,sK1),sK0) | ~v2_tex_2(sK1,sK0) | spl5_1),
% 0.21/0.52    inference(subsumption_resolution,[],[f119,f55])).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    v2_tex_2(sK2(sK0,sK1),sK0) | ~v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | spl5_1),
% 0.21/0.52    inference(subsumption_resolution,[],[f99,f88])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    v2_tex_2(sK2(sK0,sK1),sK0) | ~v2_tex_2(sK1,sK0) | v3_tex_2(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.52    inference(resolution,[],[f57,f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(sK2(X0,X1),X0) | ~v2_tex_2(X1,X0) | v3_tex_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f45])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    ~spl5_3 | spl5_5 | spl5_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f113,f86,f115,f105])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | spl5_1),
% 0.21/0.52    inference(subsumption_resolution,[],[f112,f55])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | spl5_1),
% 0.21/0.52    inference(subsumption_resolution,[],[f98,f88])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | v3_tex_2(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.52    inference(resolution,[],[f57,f65])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | v3_tex_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f45])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    spl5_1 | spl5_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f58,f90,f86])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    v1_zfmisc_1(sK1) | v3_tex_2(sK1,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    ~spl5_1 | ~spl5_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f59,f90,f86])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ~v1_zfmisc_1(sK1) | ~v3_tex_2(sK1,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (22862)------------------------------
% 0.21/0.52  % (22862)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22862)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (22862)Memory used [KB]: 10746
% 0.21/0.52  % (22862)Time elapsed: 0.112 s
% 0.21/0.52  % (22862)------------------------------
% 0.21/0.52  % (22862)------------------------------
% 0.21/0.52  % (22860)Success in time 0.162 s
%------------------------------------------------------------------------------
