%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1840+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   43 (  68 expanded)
%              Number of leaves         :    9 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :  108 ( 206 expanded)
%              Number of equality atoms :    7 (  25 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f55,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f22,f27,f32,f37,f42,f50,f54])).

fof(f54,plain,
    ( ~ spl2_1
    | ~ spl2_3
    | spl2_6 ),
    inference(avatar_contradiction_clause,[],[f53])).

fof(f53,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_3
    | spl2_6 ),
    inference(subsumption_resolution,[],[f52,f49])).

fof(f49,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl2_6
  <=> v1_zfmisc_1(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f52,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f51,f21])).

fof(f21,plain,
    ( l1_struct_0(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f19])).

fof(f19,plain,
    ( spl2_1
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f51,plain,
    ( ~ l1_struct_0(sK0)
    | v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl2_3 ),
    inference(resolution,[],[f17,f31])).

fof(f31,plain,
    ( v7_struct_0(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl2_3
  <=> v7_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_zfmisc_1(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f50,plain,
    ( ~ spl2_6
    | spl2_2
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f45,f39,f34,f24,f47])).

fof(f24,plain,
    ( spl2_2
  <=> v7_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f34,plain,
    ( spl2_4
  <=> u1_struct_0(sK0) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f39,plain,
    ( spl2_5
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f45,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | spl2_2
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f44,f26])).

fof(f26,plain,
    ( ~ v7_struct_0(sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f24])).

fof(f44,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | v7_struct_0(sK1)
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f43,f41])).

fof(f41,plain,
    ( l1_struct_0(sK1)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f39])).

fof(f43,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ l1_struct_0(sK1)
    | v7_struct_0(sK1)
    | ~ spl2_4 ),
    inference(superposition,[],[f16,f36])).

fof(f36,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f34])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).

fof(f42,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f11,f39])).

fof(f11,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v7_struct_0(X1)
          & v7_struct_0(X0)
          & u1_struct_0(X0) = u1_struct_0(X1)
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v7_struct_0(X1)
          & v7_struct_0(X0)
          & u1_struct_0(X0) = u1_struct_0(X1)
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ( ( v7_struct_0(X0)
                & u1_struct_0(X0) = u1_struct_0(X1) )
             => v7_struct_0(X1) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( ( v7_struct_0(X0)
              & u1_struct_0(X0) = u1_struct_0(X1) )
           => v7_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tex_2)).

fof(f37,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f12,f34])).

fof(f12,plain,(
    u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f32,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f13,f29])).

fof(f13,plain,(
    v7_struct_0(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f27,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f14,f24])).

fof(f14,plain,(
    ~ v7_struct_0(sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f22,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f15,f19])).

fof(f15,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f6])).

%------------------------------------------------------------------------------
