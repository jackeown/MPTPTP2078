%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:07 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 147 expanded)
%              Number of leaves         :   21 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :  256 ( 439 expanded)
%              Number of equality atoms :   26 (  36 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f197,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f61,f66,f76,f82,f90,f95,f119,f125,f132,f141,f196])).

fof(f196,plain,
    ( spl7_7
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f195,f138,f122,f53,f87])).

fof(f87,plain,
    ( spl7_7
  <=> v2_tex_2(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

% (26369)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f53,plain,
    ( spl7_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f122,plain,
    ( spl7_10
  <=> v3_pre_topc(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f138,plain,
    ( spl7_12
  <=> k1_xboole_0 = sK2(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f195,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_tex_2(k1_xboole_0,sK0)
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(trivial_inequality_removal,[],[f194])).

fof(f194,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ l1_pre_topc(sK0)
    | v2_tex_2(k1_xboole_0,sK0)
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f193,f140])).

fof(f140,plain,
    ( k1_xboole_0 = sK2(sK0,k1_xboole_0)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f138])).

fof(f193,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_xboole_0 != sK2(sK0,k1_xboole_0)
    | v2_tex_2(k1_xboole_0,sK0)
    | ~ spl7_10 ),
    inference(resolution,[],[f192,f124])).

fof(f124,plain,
    ( v3_pre_topc(k1_xboole_0,sK0)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f122])).

fof(f192,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(k1_xboole_0,X0)
      | ~ l1_pre_topc(X0)
      | k1_xboole_0 != sK2(X0,k1_xboole_0)
      | v2_tex_2(k1_xboole_0,X0) ) ),
    inference(forward_demodulation,[],[f191,f103])).

fof(f103,plain,(
    ! [X0,X1] : k9_subset_1(X0,X1,X1) = X1 ),
    inference(global_subsumption,[],[f98,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ sP6(X0) ) ),
    inference(general_splitting,[],[f46,f50_D])).

fof(f50,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | sP6(X0) ) ),
    inference(cnf_transformation,[],[f50_D])).

fof(f50_D,plain,(
    ! [X0] :
      ( ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    <=> ~ sP6(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X1) = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(f98,plain,(
    ! [X0] : sP6(X0) ),
    inference(resolution,[],[f50,f29])).

fof(f29,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f191,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(k1_xboole_0,X0)
      | sK2(X0,k1_xboole_0) != k9_subset_1(u1_struct_0(X0),k1_xboole_0,k1_xboole_0)
      | v2_tex_2(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f171,f29])).

fof(f171,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | sK2(X0,k1_xboole_0) != k9_subset_1(u1_struct_0(X0),k1_xboole_0,X1)
      | v2_tex_2(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f30,f29])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v3_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).

fof(f141,plain,
    ( spl7_12
    | ~ spl7_8
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f134,f129,f92,f138])).

fof(f92,plain,
    ( spl7_8
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f129,plain,
    ( spl7_11
  <=> r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f134,plain,
    ( k1_xboole_0 = sK2(sK0,k1_xboole_0)
    | ~ spl7_8
    | ~ spl7_11 ),
    inference(resolution,[],[f131,f105])).

fof(f105,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k1_xboole_0)
        | k1_xboole_0 = X1 )
    | ~ spl7_8 ),
    inference(resolution,[],[f42,f100])).

fof(f100,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl7_8 ),
    inference(resolution,[],[f99,f94])).

fof(f94,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f92])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f44,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f131,plain,
    ( r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f129])).

fof(f132,plain,
    ( spl7_7
    | spl7_11
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f127,f53,f129,f87])).

fof(f127,plain,
    ( r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0)
    | v2_tex_2(k1_xboole_0,sK0)
    | ~ spl7_1 ),
    inference(resolution,[],[f126,f55])).

fof(f55,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f126,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | r1_tarski(sK2(X0,k1_xboole_0),k1_xboole_0)
      | v2_tex_2(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f35,f29])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(sK2(X0,X1),X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f125,plain,
    ( ~ spl7_2
    | spl7_10
    | ~ spl7_1
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f120,f117,f53,f122,f58])).

fof(f58,plain,
    ( spl7_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f117,plain,
    ( spl7_9
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | v3_pre_topc(k1_xboole_0,X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f120,plain,
    ( v3_pre_topc(k1_xboole_0,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_1
    | ~ spl7_9 ),
    inference(resolution,[],[f118,f55])).

fof(f118,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | v3_pre_topc(k1_xboole_0,X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f117])).

fof(f119,plain,
    ( ~ spl7_8
    | spl7_9 ),
    inference(avatar_split_clause,[],[f115,f117,f92])).

fof(f115,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_xboole_0(k1_xboole_0)
      | v3_pre_topc(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f37,f29])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_xboole_0(X1)
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tops_1)).

fof(f95,plain,
    ( spl7_8
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f85,f79,f73,f92])).

fof(f73,plain,
    ( spl7_5
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f79,plain,
    ( spl7_6
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f85,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f75,f81])).

fof(f81,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f79])).

fof(f75,plain,
    ( v1_xboole_0(sK1)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f73])).

fof(f90,plain,
    ( ~ spl7_7
    | spl7_3
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f84,f79,f63,f87])).

fof(f63,plain,
    ( spl7_3
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f84,plain,
    ( ~ v2_tex_2(k1_xboole_0,sK0)
    | spl7_3
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f65,f81])).

fof(f65,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f82,plain,
    ( spl7_6
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f77,f73,f79])).

fof(f77,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_5 ),
    inference(resolution,[],[f36,f75])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f76,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f24,f73])).

fof(f24,plain,(
    v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

fof(f66,plain,(
    ~ spl7_3 ),
    inference(avatar_split_clause,[],[f26,f63])).

fof(f26,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f61,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f27,f58])).

fof(f27,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f56,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f28,f53])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:27:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (26371)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.51  % (26371)Refutation not found, incomplete strategy% (26371)------------------------------
% 0.22/0.51  % (26371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (26371)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (26371)Memory used [KB]: 10618
% 0.22/0.51  % (26371)Time elapsed: 0.093 s
% 0.22/0.51  % (26371)------------------------------
% 0.22/0.51  % (26371)------------------------------
% 0.22/0.51  % (26379)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.51  % (26387)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.51  % (26370)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.51  % (26377)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (26366)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (26391)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.52  % (26379)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f197,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f56,f61,f66,f76,f82,f90,f95,f119,f125,f132,f141,f196])).
% 0.22/0.52  fof(f196,plain,(
% 0.22/0.52    spl7_7 | ~spl7_1 | ~spl7_10 | ~spl7_12),
% 0.22/0.52    inference(avatar_split_clause,[],[f195,f138,f122,f53,f87])).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    spl7_7 <=> v2_tex_2(k1_xboole_0,sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.22/0.52  % (26369)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    spl7_1 <=> l1_pre_topc(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.52  fof(f122,plain,(
% 0.22/0.52    spl7_10 <=> v3_pre_topc(k1_xboole_0,sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.22/0.52  fof(f138,plain,(
% 0.22/0.52    spl7_12 <=> k1_xboole_0 = sK2(sK0,k1_xboole_0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.22/0.52  fof(f195,plain,(
% 0.22/0.52    ~l1_pre_topc(sK0) | v2_tex_2(k1_xboole_0,sK0) | (~spl7_10 | ~spl7_12)),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f194])).
% 0.22/0.52  fof(f194,plain,(
% 0.22/0.52    k1_xboole_0 != k1_xboole_0 | ~l1_pre_topc(sK0) | v2_tex_2(k1_xboole_0,sK0) | (~spl7_10 | ~spl7_12)),
% 0.22/0.52    inference(forward_demodulation,[],[f193,f140])).
% 0.22/0.52  fof(f140,plain,(
% 0.22/0.52    k1_xboole_0 = sK2(sK0,k1_xboole_0) | ~spl7_12),
% 0.22/0.52    inference(avatar_component_clause,[],[f138])).
% 0.22/0.52  fof(f193,plain,(
% 0.22/0.52    ~l1_pre_topc(sK0) | k1_xboole_0 != sK2(sK0,k1_xboole_0) | v2_tex_2(k1_xboole_0,sK0) | ~spl7_10),
% 0.22/0.52    inference(resolution,[],[f192,f124])).
% 0.22/0.52  fof(f124,plain,(
% 0.22/0.52    v3_pre_topc(k1_xboole_0,sK0) | ~spl7_10),
% 0.22/0.52    inference(avatar_component_clause,[],[f122])).
% 0.22/0.52  fof(f192,plain,(
% 0.22/0.52    ( ! [X0] : (~v3_pre_topc(k1_xboole_0,X0) | ~l1_pre_topc(X0) | k1_xboole_0 != sK2(X0,k1_xboole_0) | v2_tex_2(k1_xboole_0,X0)) )),
% 0.22/0.52    inference(forward_demodulation,[],[f191,f103])).
% 0.22/0.52  fof(f103,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k9_subset_1(X0,X1,X1) = X1) )),
% 0.22/0.52    inference(global_subsumption,[],[f98,f51])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~sP6(X0)) )),
% 0.22/0.52    inference(general_splitting,[],[f46,f50_D])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | sP6(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f50_D])).
% 0.22/0.52  fof(f50_D,plain,(
% 0.22/0.52    ( ! [X0] : (( ! [X2] : ~m1_subset_1(X2,k1_zfmisc_1(X0)) ) <=> ~sP6(X0)) )),
% 0.22/0.52    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X1) = X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).
% 0.22/0.52  fof(f98,plain,(
% 0.22/0.52    ( ! [X0] : (sP6(X0)) )),
% 0.22/0.52    inference(resolution,[],[f50,f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.52  fof(f191,plain,(
% 0.22/0.52    ( ! [X0] : (~l1_pre_topc(X0) | ~v3_pre_topc(k1_xboole_0,X0) | sK2(X0,k1_xboole_0) != k9_subset_1(u1_struct_0(X0),k1_xboole_0,k1_xboole_0) | v2_tex_2(k1_xboole_0,X0)) )),
% 0.22/0.52    inference(resolution,[],[f171,f29])).
% 0.22/0.52  fof(f171,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | sK2(X0,k1_xboole_0) != k9_subset_1(u1_struct_0(X0),k1_xboole_0,X1) | v2_tex_2(k1_xboole_0,X0)) )),
% 0.22/0.52    inference(resolution,[],[f30,f29])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ( ! [X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X3,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | v2_tex_2(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(flattening,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).
% 0.22/0.52  fof(f141,plain,(
% 0.22/0.52    spl7_12 | ~spl7_8 | ~spl7_11),
% 0.22/0.52    inference(avatar_split_clause,[],[f134,f129,f92,f138])).
% 0.22/0.52  fof(f92,plain,(
% 0.22/0.52    spl7_8 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.22/0.52  fof(f129,plain,(
% 0.22/0.52    spl7_11 <=> r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.22/0.52  fof(f134,plain,(
% 0.22/0.52    k1_xboole_0 = sK2(sK0,k1_xboole_0) | (~spl7_8 | ~spl7_11)),
% 0.22/0.52    inference(resolution,[],[f131,f105])).
% 0.22/0.52  fof(f105,plain,(
% 0.22/0.52    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) ) | ~spl7_8),
% 0.22/0.52    inference(resolution,[],[f42,f100])).
% 0.22/0.52  fof(f100,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl7_8),
% 0.22/0.52    inference(resolution,[],[f99,f94])).
% 0.22/0.52  fof(f94,plain,(
% 0.22/0.52    v1_xboole_0(k1_xboole_0) | ~spl7_8),
% 0.22/0.52    inference(avatar_component_clause,[],[f92])).
% 0.22/0.52  fof(f99,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_xboole_0(X0) | r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(resolution,[],[f44,f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.52  fof(f131,plain,(
% 0.22/0.52    r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0) | ~spl7_11),
% 0.22/0.52    inference(avatar_component_clause,[],[f129])).
% 0.22/0.52  fof(f132,plain,(
% 0.22/0.52    spl7_7 | spl7_11 | ~spl7_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f127,f53,f129,f87])).
% 0.22/0.52  fof(f127,plain,(
% 0.22/0.52    r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0) | v2_tex_2(k1_xboole_0,sK0) | ~spl7_1),
% 0.22/0.52    inference(resolution,[],[f126,f55])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    l1_pre_topc(sK0) | ~spl7_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f53])).
% 0.22/0.52  fof(f126,plain,(
% 0.22/0.52    ( ! [X0] : (~l1_pre_topc(X0) | r1_tarski(sK2(X0,k1_xboole_0),k1_xboole_0) | v2_tex_2(k1_xboole_0,X0)) )),
% 0.22/0.52    inference(resolution,[],[f35,f29])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(sK2(X0,X1),X1) | v2_tex_2(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f125,plain,(
% 0.22/0.52    ~spl7_2 | spl7_10 | ~spl7_1 | ~spl7_9),
% 0.22/0.52    inference(avatar_split_clause,[],[f120,f117,f53,f122,f58])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    spl7_2 <=> v2_pre_topc(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.52  fof(f117,plain,(
% 0.22/0.52    spl7_9 <=> ! [X0] : (~l1_pre_topc(X0) | v3_pre_topc(k1_xboole_0,X0) | ~v2_pre_topc(X0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.22/0.52  fof(f120,plain,(
% 0.22/0.52    v3_pre_topc(k1_xboole_0,sK0) | ~v2_pre_topc(sK0) | (~spl7_1 | ~spl7_9)),
% 0.22/0.52    inference(resolution,[],[f118,f55])).
% 0.22/0.52  fof(f118,plain,(
% 0.22/0.52    ( ! [X0] : (~l1_pre_topc(X0) | v3_pre_topc(k1_xboole_0,X0) | ~v2_pre_topc(X0)) ) | ~spl7_9),
% 0.22/0.52    inference(avatar_component_clause,[],[f117])).
% 0.22/0.52  fof(f119,plain,(
% 0.22/0.52    ~spl7_8 | spl7_9),
% 0.22/0.52    inference(avatar_split_clause,[],[f115,f117,f92])).
% 0.22/0.52  fof(f115,plain,(
% 0.22/0.52    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v1_xboole_0(k1_xboole_0) | v3_pre_topc(k1_xboole_0,X0)) )),
% 0.22/0.52    inference(resolution,[],[f37,f29])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v1_xboole_0(X1) | v3_pre_topc(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (v3_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.52    inference(flattening,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v3_pre_topc(X1,X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tops_1)).
% 0.22/0.52  fof(f95,plain,(
% 0.22/0.52    spl7_8 | ~spl7_5 | ~spl7_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f85,f79,f73,f92])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    spl7_5 <=> v1_xboole_0(sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    spl7_6 <=> k1_xboole_0 = sK1),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.22/0.52  fof(f85,plain,(
% 0.22/0.52    v1_xboole_0(k1_xboole_0) | (~spl7_5 | ~spl7_6)),
% 0.22/0.52    inference(backward_demodulation,[],[f75,f81])).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    k1_xboole_0 = sK1 | ~spl7_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f79])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    v1_xboole_0(sK1) | ~spl7_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f73])).
% 0.22/0.52  fof(f90,plain,(
% 0.22/0.52    ~spl7_7 | spl7_3 | ~spl7_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f84,f79,f63,f87])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    spl7_3 <=> v2_tex_2(sK1,sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.52  fof(f84,plain,(
% 0.22/0.52    ~v2_tex_2(k1_xboole_0,sK0) | (spl7_3 | ~spl7_6)),
% 0.22/0.52    inference(backward_demodulation,[],[f65,f81])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    ~v2_tex_2(sK1,sK0) | spl7_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f63])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    spl7_6 | ~spl7_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f77,f73,f79])).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    k1_xboole_0 = sK1 | ~spl7_5),
% 0.22/0.52    inference(resolution,[],[f36,f75])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    spl7_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f24,f73])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    v1_xboole_0(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.52    inference(flattening,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.22/0.52    inference(pure_predicate_removal,[],[f11])).
% 0.22/0.52  fof(f11,negated_conjecture,(
% 0.22/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.22/0.52    inference(negated_conjecture,[],[f10])).
% 0.22/0.52  fof(f10,conjecture,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    ~spl7_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f26,f63])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ~v2_tex_2(sK1,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    spl7_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f27,f58])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    v2_pre_topc(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    spl7_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f28,f53])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    l1_pre_topc(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (26379)------------------------------
% 0.22/0.52  % (26379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (26379)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (26379)Memory used [KB]: 10746
% 0.22/0.52  % (26379)Time elapsed: 0.104 s
% 0.22/0.52  % (26379)------------------------------
% 0.22/0.52  % (26379)------------------------------
% 1.19/0.52  % (26362)Success in time 0.155 s
%------------------------------------------------------------------------------
