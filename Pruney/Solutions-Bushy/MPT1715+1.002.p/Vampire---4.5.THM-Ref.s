%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1715+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:24 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 251 expanded)
%              Number of leaves         :   11 (  57 expanded)
%              Depth                    :   16
%              Number of atoms          :  246 (1658 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f198,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f57,f72,f191,f197])).

fof(f197,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f196])).

fof(f196,plain,
    ( $false
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f195,f43])).

fof(f43,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl4_1
  <=> r1_tsep_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f195,plain,
    ( r1_tsep_1(sK3,sK1)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f194,f67])).

fof(f67,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f64,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f64,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f61,f31])).

fof(f31,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( m1_pre_topc(X1,X2)
                     => ( ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) )
                        | ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( m1_pre_topc(X1,X2)
                   => ( ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) )
                      | ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tmap_1)).

fof(f61,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK1) ),
    inference(resolution,[],[f35,f28])).

fof(f28,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f194,plain,
    ( ~ l1_struct_0(sK1)
    | r1_tsep_1(sK3,sK1)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f193,f66])).

fof(f66,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f63,f34])).

fof(f63,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f59,f31])).

fof(f59,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[],[f35,f23])).

fof(f23,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f193,plain,
    ( ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1)
    | r1_tsep_1(sK3,sK1)
    | ~ spl4_2 ),
    inference(resolution,[],[f46,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f46,plain,
    ( r1_tsep_1(sK1,sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl4_2
  <=> r1_tsep_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f191,plain,
    ( spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f190,f54,f45])).

fof(f54,plain,
    ( spl4_4
  <=> r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f190,plain,
    ( r1_tsep_1(sK1,sK3)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f189,f67])).

fof(f189,plain,
    ( ~ l1_struct_0(sK1)
    | r1_tsep_1(sK1,sK3)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f188,f66])).

fof(f188,plain,
    ( ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1)
    | r1_tsep_1(sK1,sK3)
    | ~ spl4_4 ),
    inference(resolution,[],[f187,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | r1_tsep_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

% (21017)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
fof(f187,plain,
    ( r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ spl4_4 ),
    inference(resolution,[],[f138,f79])).

fof(f79,plain,
    ( r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f78,f68])).

fof(f68,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f65,f34])).

fof(f65,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f62,f31])).

fof(f62,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[],[f35,f26])).

fof(f26,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f78,plain,
    ( r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ l1_struct_0(sK2)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f75,f66])).

fof(f75,plain,
    ( ~ l1_struct_0(sK3)
    | r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ l1_struct_0(sK2)
    | ~ spl4_4 ),
    inference(resolution,[],[f33,f56])).

fof(f56,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f138,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(u1_struct_0(sK2),X0)
      | r1_xboole_0(u1_struct_0(sK1),X0) ) ),
    inference(resolution,[],[f137,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f137,plain,(
    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f136,f24])).

fof(f24,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f136,plain,
    ( ~ m1_pre_topc(sK1,sK2)
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(resolution,[],[f90,f26])).

fof(f90,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK0)
      | ~ m1_pre_topc(sK1,X2)
      | r1_tarski(u1_struct_0(sK1),u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f89,f30])).

fof(f30,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f89,plain,(
    ! [X2] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X2,sK0)
      | ~ m1_pre_topc(sK1,X2)
      | r1_tarski(u1_struct_0(sK1),u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f84,f31])).

fof(f84,plain,(
    ! [X2] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X2,sK0)
      | ~ m1_pre_topc(sK1,X2)
      | r1_tarski(u1_struct_0(sK1),u1_struct_0(X2)) ) ),
    inference(resolution,[],[f36,f28])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X2)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f72,plain,
    ( spl4_4
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f71,f50,f54])).

fof(f50,plain,
    ( spl4_3
  <=> r1_tsep_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f71,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f70,f66])).

fof(f70,plain,
    ( ~ l1_struct_0(sK3)
    | r1_tsep_1(sK2,sK3)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f69,f68])).

fof(f69,plain,
    ( ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK3)
    | r1_tsep_1(sK2,sK3)
    | ~ spl4_3 ),
    inference(resolution,[],[f38,f52])).

fof(f52,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f57,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f21,f54,f50])).

fof(f21,plain,
    ( r1_tsep_1(sK2,sK3)
    | r1_tsep_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f48,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f20,f45,f41])).

fof(f20,plain,
    ( ~ r1_tsep_1(sK1,sK3)
    | ~ r1_tsep_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f10])).

%------------------------------------------------------------------------------
