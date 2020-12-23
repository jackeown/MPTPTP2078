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
% DateTime   : Thu Dec  3 13:17:58 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 577 expanded)
%              Number of leaves         :   10 ( 102 expanded)
%              Depth                    :   29
%              Number of atoms          :  313 (3760 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f179,plain,(
    $false ),
    inference(subsumption_resolution,[],[f178,f55])).

fof(f55,plain,(
    l1_pre_topc(sK3) ),
    inference(resolution,[],[f54,f29])).

fof(f29,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0) )
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0) )
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ! [X3] :
                    ( m1_pre_topc(X3,X0)
                   => ( m1_pre_topc(X1,X2)
                     => ( ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) )
                        | ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

% (32507)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f54,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f38,f34])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f178,plain,(
    ~ l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f177,f56])).

fof(f56,plain,(
    l1_pre_topc(sK1) ),
    inference(resolution,[],[f54,f32])).

fof(f32,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f177,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f176,f175])).

fof(f175,plain,(
    ~ r1_tsep_1(sK1,sK3) ),
    inference(resolution,[],[f174,f27])).

fof(f27,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | ~ r1_tsep_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f174,plain,(
    r1_tsep_1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f173,f56])).

fof(f173,plain,
    ( r1_tsep_1(sK3,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f172,f37])).

fof(f37,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f172,plain,
    ( ~ l1_struct_0(sK1)
    | r1_tsep_1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f171,f55])).

% (32515)Refutation not found, incomplete strategy% (32515)------------------------------
% (32515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f171,plain,
    ( ~ l1_struct_0(sK1)
    | r1_tsep_1(sK3,sK1)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f169,f37])).

fof(f169,plain,
    ( ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1)
    | r1_tsep_1(sK3,sK1) ),
    inference(resolution,[],[f168,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | r1_tsep_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

% (32501)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f168,plain,(
    r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(duplicate_literal_removal,[],[f167])).

fof(f167,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1))
    | r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(resolution,[],[f164,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f164,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(u1_struct_0(sK3),X0),u1_struct_0(sK1))
      | r1_xboole_0(u1_struct_0(sK3),X0) ) ),
    inference(resolution,[],[f163,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f163,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_struct_0(sK3))
      | ~ r2_hidden(X0,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f162,f55])).

fof(f162,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK3)
      | ~ r2_hidden(X0,u1_struct_0(sK3))
      | ~ r2_hidden(X0,u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f151,f83])).

fof(f83,plain,(
    r1_tsep_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f82,f55])).

fof(f82,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f81,f57])).

fof(f57,plain,(
    l1_pre_topc(sK2) ),
    inference(resolution,[],[f54,f31])).

fof(f31,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f81,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3) ),
    inference(duplicate_literal_removal,[],[f80])).

fof(f80,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | r1_tsep_1(sK2,sK3) ),
    inference(resolution,[],[f79,f28])).

fof(f28,plain,
    ( r1_tsep_1(sK3,sK2)
    | r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | r1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f78,f37])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ r1_tsep_1(X0,X1)
      | r1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f45,f37])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | ~ r1_tsep_1(X0,X1)
      | r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f151,plain,(
    ! [X2,X1] :
      ( ~ r1_tsep_1(sK2,X2)
      | ~ l1_pre_topc(X2)
      | ~ r2_hidden(X1,u1_struct_0(X2))
      | ~ r2_hidden(X1,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f150,f57])).

% (32511)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f150,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,u1_struct_0(sK1))
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(sK2)
      | ~ r2_hidden(X1,u1_struct_0(X2))
      | ~ r1_tsep_1(sK2,X2) ) ),
    inference(resolution,[],[f147,f91])).

fof(f91,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X4,u1_struct_0(X2))
      | ~ l1_pre_topc(X3)
      | ~ l1_pre_topc(X2)
      | ~ r2_hidden(X4,u1_struct_0(X3))
      | ~ r1_tsep_1(X2,X3) ) ),
    inference(resolution,[],[f89,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f88,f37])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f36,f37])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f147,plain,(
    ! [X1] :
      ( r2_hidden(X1,u1_struct_0(sK2))
      | ~ r2_hidden(X1,u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f144,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f144,plain,(
    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(resolution,[],[f137,f30])).

fof(f30,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f137,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) ) ),
    inference(duplicate_literal_removal,[],[f134])).

fof(f134,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | ~ m1_pre_topc(X0,sK2)
      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f123,f101])).

fof(f101,plain,(
    ! [X4,X5] :
      ( ~ m1_pre_topc(X5,sK2)
      | ~ m1_pre_topc(X4,sK2)
      | ~ m1_pre_topc(X4,X5)
      | r1_tarski(u1_struct_0(X4),u1_struct_0(X5)) ) ),
    inference(subsumption_resolution,[],[f97,f68])).

fof(f68,plain,(
    v2_pre_topc(sK2) ),
    inference(resolution,[],[f65,f31])).

fof(f65,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f64,f34])).

fof(f64,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_pre_topc(X0) ) ),
    inference(resolution,[],[f39,f33])).

fof(f33,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f97,plain,(
    ! [X4,X5] :
      ( ~ v2_pre_topc(sK2)
      | ~ m1_pre_topc(X4,sK2)
      | ~ m1_pre_topc(X5,sK2)
      | ~ m1_pre_topc(X4,X5)
      | r1_tarski(u1_struct_0(X4),u1_struct_0(X5)) ) ),
    inference(resolution,[],[f40,f57])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X2)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f123,plain,(
    m1_pre_topc(sK2,sK2) ),
    inference(resolution,[],[f117,f31])).

fof(f117,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | m1_pre_topc(X0,X0) ) ),
    inference(subsumption_resolution,[],[f113,f33])).

fof(f113,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | m1_pre_topc(X0,X0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f112,f34])).

fof(f112,plain,(
    ! [X4,X3] :
      ( ~ l1_pre_topc(X3)
      | ~ m1_pre_topc(X4,X3)
      | m1_pre_topc(X4,X4)
      | ~ v2_pre_topc(X3) ) ),
    inference(duplicate_literal_removal,[],[f111])).

fof(f111,plain,(
    ! [X4,X3] :
      ( ~ l1_pre_topc(X3)
      | ~ m1_pre_topc(X4,X3)
      | ~ m1_pre_topc(X4,X3)
      | m1_pre_topc(X4,X4)
      | ~ v2_pre_topc(X3) ) ),
    inference(resolution,[],[f41,f52])).

fof(f52,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(X1,X2)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f176,plain,
    ( r1_tsep_1(sK1,sK3)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f174,f79])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:14:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.47  % (32496)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.53  % (32516)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.53  % (32508)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.53  % (32520)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.19/0.54  % (32495)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.54  % (32500)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.54  % (32512)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.54  % (32499)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.55  % (32515)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.55  % (32504)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.55  % (32499)Refutation found. Thanks to Tanya!
% 0.19/0.55  % SZS status Theorem for theBenchmark
% 0.19/0.55  % SZS output start Proof for theBenchmark
% 0.19/0.55  fof(f179,plain,(
% 0.19/0.55    $false),
% 0.19/0.55    inference(subsumption_resolution,[],[f178,f55])).
% 0.19/0.55  fof(f55,plain,(
% 0.19/0.55    l1_pre_topc(sK3)),
% 0.19/0.55    inference(resolution,[],[f54,f29])).
% 0.19/0.55  fof(f29,plain,(
% 0.19/0.55    m1_pre_topc(sK3,sK0)),
% 0.19/0.55    inference(cnf_transformation,[],[f15])).
% 0.19/0.55  fof(f15,plain,(
% 0.19/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.19/0.55    inference(flattening,[],[f14])).
% 0.19/0.55  fof(f14,plain,(
% 0.19/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3))) & m1_pre_topc(X1,X2)) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.19/0.55    inference(ennf_transformation,[],[f13])).
% 0.19/0.55  fof(f13,plain,(
% 0.19/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => (m1_pre_topc(X1,X2) => ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 0.19/0.55    inference(pure_predicate_removal,[],[f11])).
% 0.19/0.55  fof(f11,negated_conjecture,(
% 0.19/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 0.19/0.55    inference(negated_conjecture,[],[f10])).
% 0.19/0.55  fof(f10,conjecture,(
% 0.19/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 0.19/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tmap_1)).
% 1.51/0.56  % (32507)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.51/0.56  fof(f54,plain,(
% 1.51/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) )),
% 1.51/0.56    inference(resolution,[],[f38,f34])).
% 1.51/0.56  fof(f34,plain,(
% 1.51/0.56    l1_pre_topc(sK0)),
% 1.51/0.56    inference(cnf_transformation,[],[f15])).
% 1.51/0.56  fof(f38,plain,(
% 1.51/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f18])).
% 1.51/0.56  fof(f18,plain,(
% 1.51/0.56    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.51/0.56    inference(ennf_transformation,[],[f6])).
% 1.51/0.56  fof(f6,axiom,(
% 1.51/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.51/0.56  fof(f178,plain,(
% 1.51/0.56    ~l1_pre_topc(sK3)),
% 1.51/0.56    inference(subsumption_resolution,[],[f177,f56])).
% 1.51/0.56  fof(f56,plain,(
% 1.51/0.56    l1_pre_topc(sK1)),
% 1.51/0.56    inference(resolution,[],[f54,f32])).
% 1.51/0.56  fof(f32,plain,(
% 1.51/0.56    m1_pre_topc(sK1,sK0)),
% 1.51/0.56    inference(cnf_transformation,[],[f15])).
% 1.51/0.56  fof(f177,plain,(
% 1.51/0.56    ~l1_pre_topc(sK1) | ~l1_pre_topc(sK3)),
% 1.51/0.56    inference(subsumption_resolution,[],[f176,f175])).
% 1.51/0.56  fof(f175,plain,(
% 1.51/0.56    ~r1_tsep_1(sK1,sK3)),
% 1.51/0.56    inference(resolution,[],[f174,f27])).
% 1.51/0.56  fof(f27,plain,(
% 1.51/0.56    ~r1_tsep_1(sK3,sK1) | ~r1_tsep_1(sK1,sK3)),
% 1.51/0.56    inference(cnf_transformation,[],[f15])).
% 1.51/0.56  fof(f174,plain,(
% 1.51/0.56    r1_tsep_1(sK3,sK1)),
% 1.51/0.56    inference(subsumption_resolution,[],[f173,f56])).
% 1.51/0.56  fof(f173,plain,(
% 1.51/0.56    r1_tsep_1(sK3,sK1) | ~l1_pre_topc(sK1)),
% 1.51/0.56    inference(resolution,[],[f172,f37])).
% 1.51/0.56  fof(f37,plain,(
% 1.51/0.56    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f17])).
% 1.51/0.56  fof(f17,plain,(
% 1.51/0.56    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.51/0.56    inference(ennf_transformation,[],[f5])).
% 1.51/0.56  fof(f5,axiom,(
% 1.51/0.56    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.51/0.56  fof(f172,plain,(
% 1.51/0.56    ~l1_struct_0(sK1) | r1_tsep_1(sK3,sK1)),
% 1.51/0.56    inference(subsumption_resolution,[],[f171,f55])).
% 1.51/0.56  % (32515)Refutation not found, incomplete strategy% (32515)------------------------------
% 1.51/0.56  % (32515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.56  fof(f171,plain,(
% 1.51/0.56    ~l1_struct_0(sK1) | r1_tsep_1(sK3,sK1) | ~l1_pre_topc(sK3)),
% 1.51/0.56    inference(resolution,[],[f169,f37])).
% 1.51/0.56  fof(f169,plain,(
% 1.51/0.56    ~l1_struct_0(sK3) | ~l1_struct_0(sK1) | r1_tsep_1(sK3,sK1)),
% 1.51/0.56    inference(resolution,[],[f168,f35])).
% 1.51/0.56  fof(f35,plain,(
% 1.51/0.56    ( ! [X0,X1] : (~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~l1_struct_0(X0) | r1_tsep_1(X0,X1)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f16])).
% 1.51/0.56  % (32501)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.51/0.56  fof(f16,plain,(
% 1.51/0.56    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 1.51/0.56    inference(ennf_transformation,[],[f7])).
% 1.51/0.56  fof(f7,axiom,(
% 1.51/0.56    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).
% 1.51/0.56  fof(f168,plain,(
% 1.51/0.56    r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.51/0.56    inference(duplicate_literal_removal,[],[f167])).
% 1.51/0.56  fof(f167,plain,(
% 1.51/0.56    r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)) | r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.51/0.56    inference(resolution,[],[f164,f44])).
% 1.51/0.56  fof(f44,plain,(
% 1.51/0.56    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f23])).
% 1.51/0.56  fof(f23,plain,(
% 1.51/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.51/0.56    inference(ennf_transformation,[],[f12])).
% 1.51/0.56  fof(f12,plain,(
% 1.51/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.51/0.56    inference(rectify,[],[f2])).
% 1.51/0.56  fof(f2,axiom,(
% 1.51/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.51/0.56  fof(f164,plain,(
% 1.51/0.56    ( ! [X0] : (~r2_hidden(sK4(u1_struct_0(sK3),X0),u1_struct_0(sK1)) | r1_xboole_0(u1_struct_0(sK3),X0)) )),
% 1.51/0.56    inference(resolution,[],[f163,f43])).
% 1.51/0.56  fof(f43,plain,(
% 1.51/0.56    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f23])).
% 1.51/0.56  fof(f163,plain,(
% 1.51/0.56    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK3)) | ~r2_hidden(X0,u1_struct_0(sK1))) )),
% 1.51/0.56    inference(subsumption_resolution,[],[f162,f55])).
% 1.51/0.56  fof(f162,plain,(
% 1.51/0.56    ( ! [X0] : (~l1_pre_topc(sK3) | ~r2_hidden(X0,u1_struct_0(sK3)) | ~r2_hidden(X0,u1_struct_0(sK1))) )),
% 1.51/0.56    inference(resolution,[],[f151,f83])).
% 1.51/0.56  fof(f83,plain,(
% 1.51/0.56    r1_tsep_1(sK2,sK3)),
% 1.51/0.56    inference(subsumption_resolution,[],[f82,f55])).
% 1.51/0.56  fof(f82,plain,(
% 1.51/0.56    r1_tsep_1(sK2,sK3) | ~l1_pre_topc(sK3)),
% 1.51/0.56    inference(subsumption_resolution,[],[f81,f57])).
% 1.51/0.56  fof(f57,plain,(
% 1.51/0.56    l1_pre_topc(sK2)),
% 1.51/0.56    inference(resolution,[],[f54,f31])).
% 1.51/0.56  fof(f31,plain,(
% 1.51/0.56    m1_pre_topc(sK2,sK0)),
% 1.51/0.56    inference(cnf_transformation,[],[f15])).
% 1.51/0.56  fof(f81,plain,(
% 1.51/0.56    r1_tsep_1(sK2,sK3) | ~l1_pre_topc(sK2) | ~l1_pre_topc(sK3)),
% 1.51/0.56    inference(duplicate_literal_removal,[],[f80])).
% 1.51/0.56  fof(f80,plain,(
% 1.51/0.56    r1_tsep_1(sK2,sK3) | ~l1_pre_topc(sK2) | ~l1_pre_topc(sK3) | r1_tsep_1(sK2,sK3)),
% 1.51/0.56    inference(resolution,[],[f79,f28])).
% 1.51/0.56  fof(f28,plain,(
% 1.51/0.56    r1_tsep_1(sK3,sK2) | r1_tsep_1(sK2,sK3)),
% 1.51/0.56    inference(cnf_transformation,[],[f15])).
% 1.51/0.56  fof(f79,plain,(
% 1.51/0.56    ( ! [X0,X1] : (~r1_tsep_1(X0,X1) | r1_tsep_1(X1,X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.51/0.56    inference(resolution,[],[f78,f37])).
% 1.51/0.56  fof(f78,plain,(
% 1.51/0.56    ( ! [X0,X1] : (~l1_struct_0(X0) | ~r1_tsep_1(X0,X1) | r1_tsep_1(X1,X0) | ~l1_pre_topc(X1)) )),
% 1.51/0.56    inference(resolution,[],[f45,f37])).
% 1.51/0.56  fof(f45,plain,(
% 1.51/0.56    ( ! [X0,X1] : (~l1_struct_0(X1) | ~l1_struct_0(X0) | ~r1_tsep_1(X0,X1) | r1_tsep_1(X1,X0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f25])).
% 1.51/0.56  fof(f25,plain,(
% 1.51/0.56    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 1.51/0.56    inference(flattening,[],[f24])).
% 1.51/0.56  fof(f24,plain,(
% 1.51/0.56    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 1.51/0.56    inference(ennf_transformation,[],[f8])).
% 1.51/0.56  fof(f8,axiom,(
% 1.51/0.56    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).
% 1.51/0.56  fof(f151,plain,(
% 1.51/0.56    ( ! [X2,X1] : (~r1_tsep_1(sK2,X2) | ~l1_pre_topc(X2) | ~r2_hidden(X1,u1_struct_0(X2)) | ~r2_hidden(X1,u1_struct_0(sK1))) )),
% 1.51/0.56    inference(subsumption_resolution,[],[f150,f57])).
% 1.51/0.56  % (32511)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.51/0.56  fof(f150,plain,(
% 1.51/0.56    ( ! [X2,X1] : (~r2_hidden(X1,u1_struct_0(sK1)) | ~l1_pre_topc(X2) | ~l1_pre_topc(sK2) | ~r2_hidden(X1,u1_struct_0(X2)) | ~r1_tsep_1(sK2,X2)) )),
% 1.51/0.56    inference(resolution,[],[f147,f91])).
% 1.51/0.56  fof(f91,plain,(
% 1.51/0.56    ( ! [X4,X2,X3] : (~r2_hidden(X4,u1_struct_0(X2)) | ~l1_pre_topc(X3) | ~l1_pre_topc(X2) | ~r2_hidden(X4,u1_struct_0(X3)) | ~r1_tsep_1(X2,X3)) )),
% 1.51/0.56    inference(resolution,[],[f89,f42])).
% 1.51/0.56  fof(f42,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f23])).
% 1.51/0.56  fof(f89,plain,(
% 1.51/0.56    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.51/0.56    inference(resolution,[],[f88,f37])).
% 1.51/0.56  fof(f88,plain,(
% 1.51/0.56    ( ! [X0,X1] : (~l1_struct_0(X0) | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_pre_topc(X1)) )),
% 1.51/0.56    inference(resolution,[],[f36,f37])).
% 1.51/0.56  fof(f36,plain,(
% 1.51/0.56    ( ! [X0,X1] : (~l1_struct_0(X1) | ~l1_struct_0(X0) | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f16])).
% 1.51/0.56  fof(f147,plain,(
% 1.51/0.56    ( ! [X1] : (r2_hidden(X1,u1_struct_0(sK2)) | ~r2_hidden(X1,u1_struct_0(sK1))) )),
% 1.51/0.56    inference(resolution,[],[f144,f49])).
% 1.51/0.56  fof(f49,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f26])).
% 1.51/0.56  fof(f26,plain,(
% 1.51/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.51/0.56    inference(ennf_transformation,[],[f1])).
% 1.51/0.56  fof(f1,axiom,(
% 1.51/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.51/0.56  fof(f144,plain,(
% 1.51/0.56    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))),
% 1.51/0.56    inference(resolution,[],[f137,f30])).
% 1.51/0.56  fof(f30,plain,(
% 1.51/0.56    m1_pre_topc(sK1,sK2)),
% 1.51/0.56    inference(cnf_transformation,[],[f15])).
% 1.51/0.56  fof(f137,plain,(
% 1.51/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK2) | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2))) )),
% 1.51/0.56    inference(duplicate_literal_removal,[],[f134])).
% 1.51/0.56  fof(f134,plain,(
% 1.51/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X0,sK2) | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2))) )),
% 1.51/0.56    inference(resolution,[],[f123,f101])).
% 1.51/0.56  fof(f101,plain,(
% 1.51/0.56    ( ! [X4,X5] : (~m1_pre_topc(X5,sK2) | ~m1_pre_topc(X4,sK2) | ~m1_pre_topc(X4,X5) | r1_tarski(u1_struct_0(X4),u1_struct_0(X5))) )),
% 1.51/0.56    inference(subsumption_resolution,[],[f97,f68])).
% 1.51/0.56  fof(f68,plain,(
% 1.51/0.56    v2_pre_topc(sK2)),
% 1.51/0.56    inference(resolution,[],[f65,f31])).
% 1.51/0.56  fof(f65,plain,(
% 1.51/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_pre_topc(X0)) )),
% 1.51/0.56    inference(subsumption_resolution,[],[f64,f34])).
% 1.51/0.56  fof(f64,plain,(
% 1.51/0.56    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_pre_topc(X0)) )),
% 1.51/0.56    inference(resolution,[],[f39,f33])).
% 1.51/0.56  fof(f33,plain,(
% 1.51/0.56    v2_pre_topc(sK0)),
% 1.51/0.56    inference(cnf_transformation,[],[f15])).
% 1.51/0.56  fof(f39,plain,(
% 1.51/0.56    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_pre_topc(X1)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f20])).
% 1.51/0.56  fof(f20,plain,(
% 1.51/0.56    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.51/0.56    inference(flattening,[],[f19])).
% 1.51/0.56  fof(f19,plain,(
% 1.51/0.56    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.51/0.56    inference(ennf_transformation,[],[f4])).
% 1.51/0.56  fof(f4,axiom,(
% 1.51/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 1.51/0.56  fof(f97,plain,(
% 1.51/0.56    ( ! [X4,X5] : (~v2_pre_topc(sK2) | ~m1_pre_topc(X4,sK2) | ~m1_pre_topc(X5,sK2) | ~m1_pre_topc(X4,X5) | r1_tarski(u1_struct_0(X4),u1_struct_0(X5))) )),
% 1.51/0.56    inference(resolution,[],[f40,f57])).
% 1.51/0.56  fof(f40,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X2) | r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) )),
% 1.51/0.56    inference(cnf_transformation,[],[f22])).
% 1.51/0.56  fof(f22,plain,(
% 1.51/0.56    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.51/0.56    inference(flattening,[],[f21])).
% 1.51/0.56  fof(f21,plain,(
% 1.51/0.56    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.51/0.56    inference(ennf_transformation,[],[f9])).
% 1.51/0.56  fof(f9,axiom,(
% 1.51/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).
% 1.51/0.56  fof(f123,plain,(
% 1.51/0.56    m1_pre_topc(sK2,sK2)),
% 1.51/0.56    inference(resolution,[],[f117,f31])).
% 1.51/0.56  fof(f117,plain,(
% 1.51/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_pre_topc(X0,X0)) )),
% 1.51/0.56    inference(subsumption_resolution,[],[f113,f33])).
% 1.51/0.56  fof(f113,plain,(
% 1.51/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_pre_topc(X0,X0) | ~v2_pre_topc(sK0)) )),
% 1.51/0.56    inference(resolution,[],[f112,f34])).
% 1.51/0.56  fof(f112,plain,(
% 1.51/0.56    ( ! [X4,X3] : (~l1_pre_topc(X3) | ~m1_pre_topc(X4,X3) | m1_pre_topc(X4,X4) | ~v2_pre_topc(X3)) )),
% 1.51/0.56    inference(duplicate_literal_removal,[],[f111])).
% 1.51/0.56  fof(f111,plain,(
% 1.51/0.56    ( ! [X4,X3] : (~l1_pre_topc(X3) | ~m1_pre_topc(X4,X3) | ~m1_pre_topc(X4,X3) | m1_pre_topc(X4,X4) | ~v2_pre_topc(X3)) )),
% 1.51/0.56    inference(resolution,[],[f41,f52])).
% 1.51/0.56  fof(f52,plain,(
% 1.51/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.51/0.56    inference(equality_resolution,[],[f47])).
% 1.51/0.56  fof(f47,plain,(
% 1.51/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.51/0.56    inference(cnf_transformation,[],[f3])).
% 1.51/0.56  fof(f3,axiom,(
% 1.51/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.51/0.56  fof(f41,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | m1_pre_topc(X1,X2) | ~v2_pre_topc(X0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f22])).
% 1.51/0.56  fof(f176,plain,(
% 1.51/0.56    r1_tsep_1(sK1,sK3) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK3)),
% 1.51/0.56    inference(resolution,[],[f174,f79])).
% 1.51/0.56  % SZS output end Proof for theBenchmark
% 1.51/0.56  % (32499)------------------------------
% 1.51/0.56  % (32499)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.56  % (32499)Termination reason: Refutation
% 1.51/0.56  
% 1.51/0.56  % (32499)Memory used [KB]: 6268
% 1.51/0.56  % (32499)Time elapsed: 0.139 s
% 1.51/0.56  % (32499)------------------------------
% 1.51/0.56  % (32499)------------------------------
% 1.51/0.56  % (32492)Success in time 0.209 s
%------------------------------------------------------------------------------
