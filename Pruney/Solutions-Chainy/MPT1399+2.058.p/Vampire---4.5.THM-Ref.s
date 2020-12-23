%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 192 expanded)
%              Number of leaves         :   26 (  64 expanded)
%              Depth                    :    9
%              Number of atoms          :  285 ( 734 expanded)
%              Number of equality atoms :   21 (  67 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f498,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f147,f161,f175,f210,f214,f218,f223,f335,f375,f490,f491,f497])).

fof(f497,plain,(
    ~ spl4_26 ),
    inference(avatar_contradiction_clause,[],[f496])).

fof(f496,plain,
    ( $false
    | ~ spl4_26 ),
    inference(resolution,[],[f277,f40])).

fof(f40,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ~ ( k1_xboole_0 = X2
                    & ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( r2_hidden(X3,X2)
                        <=> ( r2_hidden(X1,X3)
                            & v4_pre_topc(X3,X0)
                            & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ~ ( k1_xboole_0 = X2
                  & ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( r2_hidden(X3,X2)
                      <=> ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).

fof(f277,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f276])).

fof(f276,plain,
    ( spl4_26
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f491,plain,
    ( spl4_26
    | ~ spl4_21
    | ~ spl4_20
    | ~ spl4_27
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f436,f159,f279,f205,f208,f276])).

fof(f208,plain,
    ( spl4_21
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f205,plain,
    ( spl4_20
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

% (5071)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
fof(f279,plain,
    ( spl4_27
  <=> v2_tops_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f159,plain,
    ( spl4_16
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f436,plain,
    ( ~ v2_tops_1(k1_xboole_0,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_16 ),
    inference(superposition,[],[f52,f411])).

fof(f411,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f176,f338])).

fof(f338,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl4_16 ),
    inference(resolution,[],[f160,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f160,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f159])).

fof(f176,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f79,f42])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f79,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f47,f48])).

fof(f48,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f47,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f52,plain,(
    ! [X0] :
      ( ~ v2_tops_1(k2_struct_0(X0),X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v2_tops_1(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v2_tops_1(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ~ v2_tops_1(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_tops_1)).

fof(f490,plain,
    ( ~ spl4_21
    | spl4_27
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f487,f373,f279,f208])).

fof(f373,plain,
    ( spl4_33
  <=> r1_tarski(sK3(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f487,plain,
    ( v2_tops_1(k1_xboole_0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_33 ),
    inference(superposition,[],[f50,f477])).

fof(f477,plain,
    ( k1_xboole_0 = sK3(sK0)
    | ~ spl4_33 ),
    inference(resolution,[],[f374,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f374,plain,
    ( r1_tarski(sK3(sK0),k1_xboole_0)
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f373])).

fof(f50,plain,(
    ! [X0] :
      ( v2_tops_1(sK3(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v2_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ? [X1] :
          ( v2_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc5_tops_1)).

fof(f375,plain,
    ( ~ spl4_21
    | spl4_33
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f370,f159,f373,f208])).

fof(f370,plain,
    ( r1_tarski(sK3(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_16 ),
    inference(superposition,[],[f90,f338])).

fof(f90,plain,(
    ! [X0] :
      ( r1_tarski(sK3(X0),u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f49,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f49,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f335,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f334])).

fof(f334,plain,
    ( $false
    | ~ spl4_2 ),
    inference(resolution,[],[f306,f43])).

fof(f43,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f306,plain,
    ( ~ r1_tarski(k1_xboole_0,u1_struct_0(sK0))
    | ~ spl4_2 ),
    inference(resolution,[],[f146,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f146,plain,
    ( r2_hidden(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl4_2
  <=> r2_hidden(u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f223,plain,
    ( ~ spl4_20
    | ~ spl4_21
    | spl4_1 ),
    inference(avatar_split_clause,[],[f222,f66,f208,f205])).

fof(f66,plain,
    ( spl4_1
  <=> v3_pre_topc(u1_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f222,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl4_1 ),
    inference(resolution,[],[f192,f54])).

fof(f54,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f192,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK0),sK0)
    | spl4_1 ),
    inference(backward_demodulation,[],[f145,f176])).

fof(f145,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK0),sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f218,plain,(
    spl4_21 ),
    inference(avatar_contradiction_clause,[],[f217])).

fof(f217,plain,
    ( $false
    | spl4_21 ),
    inference(resolution,[],[f209,f42])).

fof(f209,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_21 ),
    inference(avatar_component_clause,[],[f208])).

fof(f214,plain,(
    spl4_20 ),
    inference(avatar_contradiction_clause,[],[f213])).

fof(f213,plain,
    ( $false
    | spl4_20 ),
    inference(resolution,[],[f206,f41])).

fof(f41,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f206,plain,
    ( ~ v2_pre_topc(sK0)
    | spl4_20 ),
    inference(avatar_component_clause,[],[f205])).

fof(f210,plain,
    ( ~ spl4_20
    | ~ spl4_21
    | spl4_3 ),
    inference(avatar_split_clause,[],[f203,f74,f208,f205])).

fof(f74,plain,
    ( spl4_3
  <=> v4_pre_topc(u1_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f203,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl4_3 ),
    inference(resolution,[],[f191,f53])).

fof(f53,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

fof(f191,plain,
    ( ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | spl4_3 ),
    inference(backward_demodulation,[],[f144,f176])).

fof(f144,plain,
    ( ~ v4_pre_topc(u1_struct_0(sK0),sK0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f175,plain,(
    spl4_15 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | spl4_15 ),
    inference(resolution,[],[f157,f39])).

fof(f39,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f157,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl4_15 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl4_15
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f161,plain,
    ( ~ spl4_15
    | spl4_16
    | spl4_14 ),
    inference(avatar_split_clause,[],[f154,f142,f159,f156])).

fof(f142,plain,
    ( spl4_14
  <=> r2_hidden(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f154,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl4_14 ),
    inference(resolution,[],[f143,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f143,plain,
    ( ~ r2_hidden(sK1,u1_struct_0(sK0))
    | spl4_14 ),
    inference(avatar_component_clause,[],[f142])).

fof(f147,plain,
    ( ~ spl4_14
    | ~ spl4_3
    | ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f138,f69,f66,f74,f142])).

fof(f138,plain,
    ( r2_hidden(u1_struct_0(sK0),k1_xboole_0)
    | ~ v3_pre_topc(u1_struct_0(sK0),sK0)
    | ~ v4_pre_topc(u1_struct_0(sK0),sK0)
    | ~ r2_hidden(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f137,f60])).

fof(f60,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f45,f44])).

fof(f44,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f45,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f137,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X3,k1_xboole_0)
      | ~ v3_pre_topc(X3,sK0)
      | ~ v4_pre_topc(X3,sK0)
      | ~ r2_hidden(sK1,X3) ) ),
    inference(forward_demodulation,[],[f36,f38])).

fof(f38,plain,(
    k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f18])).

fof(f36,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X3,sK0)
      | ~ v4_pre_topc(X3,sK0)
      | ~ r2_hidden(sK1,X3)
      | r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:37:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (5069)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.48  % (5077)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.49  % (5077)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.50  % (5070)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f498,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f147,f161,f175,f210,f214,f218,f223,f335,f375,f490,f491,f497])).
% 0.22/0.50  fof(f497,plain,(
% 0.22/0.50    ~spl4_26),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f496])).
% 0.22/0.50  fof(f496,plain,(
% 0.22/0.50    $false | ~spl4_26),
% 0.22/0.50    inference(resolution,[],[f277,f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ~v2_struct_0(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : ((k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,negated_conjecture,(
% 0.22/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.22/0.50    inference(negated_conjecture,[],[f15])).
% 0.22/0.50  fof(f15,conjecture,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).
% 0.22/0.50  fof(f277,plain,(
% 0.22/0.50    v2_struct_0(sK0) | ~spl4_26),
% 0.22/0.50    inference(avatar_component_clause,[],[f276])).
% 0.22/0.50  fof(f276,plain,(
% 0.22/0.50    spl4_26 <=> v2_struct_0(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.22/0.50  fof(f491,plain,(
% 0.22/0.50    spl4_26 | ~spl4_21 | ~spl4_20 | ~spl4_27 | ~spl4_16),
% 0.22/0.50    inference(avatar_split_clause,[],[f436,f159,f279,f205,f208,f276])).
% 0.22/0.50  fof(f208,plain,(
% 0.22/0.50    spl4_21 <=> l1_pre_topc(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.22/0.50  fof(f205,plain,(
% 0.22/0.50    spl4_20 <=> v2_pre_topc(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.22/0.50  % (5071)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.50  fof(f279,plain,(
% 0.22/0.50    spl4_27 <=> v2_tops_1(k1_xboole_0,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.22/0.50  fof(f159,plain,(
% 0.22/0.50    spl4_16 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.22/0.50  fof(f436,plain,(
% 0.22/0.50    ~v2_tops_1(k1_xboole_0,sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_16),
% 0.22/0.50    inference(superposition,[],[f52,f411])).
% 0.22/0.50  fof(f411,plain,(
% 0.22/0.50    k1_xboole_0 = k2_struct_0(sK0) | ~spl4_16),
% 0.22/0.50    inference(forward_demodulation,[],[f176,f338])).
% 0.22/0.50  fof(f338,plain,(
% 0.22/0.50    k1_xboole_0 = u1_struct_0(sK0) | ~spl4_16),
% 0.22/0.50    inference(resolution,[],[f160,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.50  fof(f160,plain,(
% 0.22/0.50    v1_xboole_0(u1_struct_0(sK0)) | ~spl4_16),
% 0.22/0.50    inference(avatar_component_clause,[],[f159])).
% 0.22/0.50  fof(f176,plain,(
% 0.22/0.50    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.22/0.50    inference(resolution,[],[f79,f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    l1_pre_topc(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.50    inference(resolution,[],[f47,f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X0] : (~v2_tops_1(k2_struct_0(X0),X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0] : (~v2_tops_1(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0] : (~v2_tops_1(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,axiom,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ~v2_tops_1(k2_struct_0(X0),X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_tops_1)).
% 0.22/0.50  fof(f490,plain,(
% 0.22/0.50    ~spl4_21 | spl4_27 | ~spl4_33),
% 0.22/0.50    inference(avatar_split_clause,[],[f487,f373,f279,f208])).
% 0.22/0.50  fof(f373,plain,(
% 0.22/0.50    spl4_33 <=> r1_tarski(sK3(sK0),k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.22/0.50  fof(f487,plain,(
% 0.22/0.50    v2_tops_1(k1_xboole_0,sK0) | ~l1_pre_topc(sK0) | ~spl4_33),
% 0.22/0.50    inference(superposition,[],[f50,f477])).
% 0.22/0.50  fof(f477,plain,(
% 0.22/0.50    k1_xboole_0 = sK3(sK0) | ~spl4_33),
% 0.22/0.50    inference(resolution,[],[f374,f51])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.22/0.50  fof(f374,plain,(
% 0.22/0.50    r1_tarski(sK3(sK0),k1_xboole_0) | ~spl4_33),
% 0.22/0.50    inference(avatar_component_clause,[],[f373])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X0] : (v2_tops_1(sK3(X0),X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0] : (? [X1] : (v2_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ? [X1] : (v2_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc5_tops_1)).
% 0.22/0.50  fof(f375,plain,(
% 0.22/0.50    ~spl4_21 | spl4_33 | ~spl4_16),
% 0.22/0.50    inference(avatar_split_clause,[],[f370,f159,f373,f208])).
% 0.22/0.50  fof(f370,plain,(
% 0.22/0.50    r1_tarski(sK3(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~spl4_16),
% 0.22/0.50    inference(superposition,[],[f90,f338])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    ( ! [X0] : (r1_tarski(sK3(X0),u1_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(resolution,[],[f49,f57])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f335,plain,(
% 0.22/0.50    ~spl4_2),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f334])).
% 0.22/0.50  fof(f334,plain,(
% 0.22/0.50    $false | ~spl4_2),
% 0.22/0.50    inference(resolution,[],[f306,f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.50  fof(f306,plain,(
% 0.22/0.50    ~r1_tarski(k1_xboole_0,u1_struct_0(sK0)) | ~spl4_2),
% 0.22/0.50    inference(resolution,[],[f146,f58])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.50  fof(f146,plain,(
% 0.22/0.50    r2_hidden(u1_struct_0(sK0),k1_xboole_0) | ~spl4_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f69])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    spl4_2 <=> r2_hidden(u1_struct_0(sK0),k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.50  fof(f223,plain,(
% 0.22/0.50    ~spl4_20 | ~spl4_21 | spl4_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f222,f66,f208,f205])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    spl4_1 <=> v3_pre_topc(u1_struct_0(sK0),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.50  fof(f222,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl4_1),
% 0.22/0.50    inference(resolution,[],[f192,f54])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,axiom,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).
% 0.22/0.50  fof(f192,plain,(
% 0.22/0.50    ~v3_pre_topc(k2_struct_0(sK0),sK0) | spl4_1),
% 0.22/0.50    inference(backward_demodulation,[],[f145,f176])).
% 0.22/0.50  fof(f145,plain,(
% 0.22/0.50    ~v3_pre_topc(u1_struct_0(sK0),sK0) | spl4_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f66])).
% 0.22/0.50  fof(f218,plain,(
% 0.22/0.50    spl4_21),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f217])).
% 0.22/0.50  fof(f217,plain,(
% 0.22/0.50    $false | spl4_21),
% 0.22/0.50    inference(resolution,[],[f209,f42])).
% 0.22/0.50  fof(f209,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | spl4_21),
% 0.22/0.50    inference(avatar_component_clause,[],[f208])).
% 0.22/0.50  fof(f214,plain,(
% 0.22/0.50    spl4_20),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f213])).
% 0.22/0.50  fof(f213,plain,(
% 0.22/0.50    $false | spl4_20),
% 0.22/0.50    inference(resolution,[],[f206,f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    v2_pre_topc(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f206,plain,(
% 0.22/0.50    ~v2_pre_topc(sK0) | spl4_20),
% 0.22/0.50    inference(avatar_component_clause,[],[f205])).
% 0.22/0.50  fof(f210,plain,(
% 0.22/0.50    ~spl4_20 | ~spl4_21 | spl4_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f203,f74,f208,f205])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    spl4_3 <=> v4_pre_topc(u1_struct_0(sK0),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.50  fof(f203,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl4_3),
% 0.22/0.50    inference(resolution,[],[f191,f53])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,axiom,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).
% 0.22/0.50  fof(f191,plain,(
% 0.22/0.50    ~v4_pre_topc(k2_struct_0(sK0),sK0) | spl4_3),
% 0.22/0.50    inference(backward_demodulation,[],[f144,f176])).
% 0.22/0.50  fof(f144,plain,(
% 0.22/0.50    ~v4_pre_topc(u1_struct_0(sK0),sK0) | spl4_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f74])).
% 0.22/0.50  fof(f175,plain,(
% 0.22/0.50    spl4_15),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f174])).
% 0.22/0.50  fof(f174,plain,(
% 0.22/0.50    $false | spl4_15),
% 0.22/0.50    inference(resolution,[],[f157,f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f157,plain,(
% 0.22/0.50    ~m1_subset_1(sK1,u1_struct_0(sK0)) | spl4_15),
% 0.22/0.50    inference(avatar_component_clause,[],[f156])).
% 0.22/0.50  fof(f156,plain,(
% 0.22/0.50    spl4_15 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.22/0.50  fof(f161,plain,(
% 0.22/0.50    ~spl4_15 | spl4_16 | spl4_14),
% 0.22/0.50    inference(avatar_split_clause,[],[f154,f142,f159,f156])).
% 0.22/0.50  fof(f142,plain,(
% 0.22/0.50    spl4_14 <=> r2_hidden(sK1,u1_struct_0(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.22/0.50  fof(f154,plain,(
% 0.22/0.50    v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | spl4_14),
% 0.22/0.50    inference(resolution,[],[f143,f55])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.50    inference(flattening,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.50  fof(f143,plain,(
% 0.22/0.50    ~r2_hidden(sK1,u1_struct_0(sK0)) | spl4_14),
% 0.22/0.50    inference(avatar_component_clause,[],[f142])).
% 0.22/0.50  fof(f147,plain,(
% 0.22/0.50    ~spl4_14 | ~spl4_3 | ~spl4_1 | spl4_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f138,f69,f66,f74,f142])).
% 0.22/0.50  fof(f138,plain,(
% 0.22/0.50    r2_hidden(u1_struct_0(sK0),k1_xboole_0) | ~v3_pre_topc(u1_struct_0(sK0),sK0) | ~v4_pre_topc(u1_struct_0(sK0),sK0) | ~r2_hidden(sK1,u1_struct_0(sK0))),
% 0.22/0.50    inference(resolution,[],[f137,f60])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.22/0.50    inference(forward_demodulation,[],[f45,f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.22/0.50  fof(f137,plain,(
% 0.22/0.50    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X3,k1_xboole_0) | ~v3_pre_topc(X3,sK0) | ~v4_pre_topc(X3,sK0) | ~r2_hidden(sK1,X3)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f36,f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    k1_xboole_0 = sK2),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | ~v4_pre_topc(X3,sK0) | ~r2_hidden(sK1,X3) | r2_hidden(X3,sK2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (5077)------------------------------
% 0.22/0.50  % (5077)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (5077)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (5077)Memory used [KB]: 10746
% 0.22/0.50  % (5077)Time elapsed: 0.079 s
% 0.22/0.50  % (5077)------------------------------
% 0.22/0.50  % (5077)------------------------------
% 0.22/0.51  % (5062)Success in time 0.147 s
%------------------------------------------------------------------------------
