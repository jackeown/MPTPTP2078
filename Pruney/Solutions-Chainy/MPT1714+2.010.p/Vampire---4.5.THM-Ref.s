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
% DateTime   : Thu Dec  3 13:17:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 710 expanded)
%              Number of leaves         :   11 ( 146 expanded)
%              Depth                    :   19
%              Number of atoms          :  257 (4454 expanded)
%              Number of equality atoms :   18 (  58 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f433,plain,(
    $false ),
    inference(subsumption_resolution,[],[f432,f425])).

fof(f425,plain,(
    ~ r1_tsep_1(sK1,sK3) ),
    inference(subsumption_resolution,[],[f32,f423])).

fof(f423,plain,(
    r1_tsep_1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f223,f422])).

fof(f422,plain,(
    r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1)) ),
    inference(resolution,[],[f412,f273])).

fof(f273,plain,(
    r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f272,f105])).

fof(f105,plain,(
    r1_tsep_1(sK3,sK2) ),
    inference(subsumption_resolution,[],[f104,f90])).

fof(f90,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f84,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f84,plain,(
    l1_pre_topc(sK2) ),
    inference(resolution,[],[f81,f37])).

fof(f37,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
                     => ( ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) )
                        | ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( m1_pre_topc(X1,X2)
                   => ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) )
                      | ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tmap_1)).

fof(f81,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f57,f42])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f104,plain,
    ( ~ l1_struct_0(sK2)
    | r1_tsep_1(sK3,sK2) ),
    inference(resolution,[],[f100,f103])).

fof(f103,plain,(
    r1_tsep_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f102,f86])).

fof(f86,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f82,f46])).

fof(f82,plain,(
    l1_pre_topc(sK3) ),
    inference(resolution,[],[f81,f34])).

fof(f34,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f102,plain,
    ( ~ l1_struct_0(sK3)
    | r1_tsep_1(sK2,sK3) ),
    inference(duplicate_literal_removal,[],[f101])).

fof(f101,plain,
    ( ~ l1_struct_0(sK3)
    | r1_tsep_1(sK2,sK3)
    | r1_tsep_1(sK2,sK3) ),
    inference(resolution,[],[f99,f31])).

fof(f31,plain,
    ( r1_tsep_1(sK3,sK2)
    | r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f99,plain,(
    ! [X2] :
      ( ~ r1_tsep_1(X2,sK2)
      | ~ l1_struct_0(X2)
      | r1_tsep_1(sK2,X2) ) ),
    inference(resolution,[],[f61,f90])).

fof(f61,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f100,plain,(
    ! [X3] :
      ( ~ r1_tsep_1(X3,sK3)
      | ~ l1_struct_0(X3)
      | r1_tsep_1(sK3,X3) ) ),
    inference(resolution,[],[f61,f86])).

fof(f272,plain,
    ( r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK2))
    | ~ r1_tsep_1(sK3,sK2) ),
    inference(subsumption_resolution,[],[f268,f90])).

fof(f268,plain,
    ( r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK2))
    | ~ l1_struct_0(sK2)
    | ~ r1_tsep_1(sK3,sK2) ),
    inference(superposition,[],[f168,f93])).

fof(f93,plain,(
    k2_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(resolution,[],[f90,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f168,plain,(
    ! [X3] :
      ( r1_xboole_0(k2_struct_0(sK3),u1_struct_0(X3))
      | ~ l1_struct_0(X3)
      | ~ r1_tsep_1(sK3,X3) ) ),
    inference(subsumption_resolution,[],[f159,f86])).

fof(f159,plain,(
    ! [X3] :
      ( r1_xboole_0(k2_struct_0(sK3),u1_struct_0(X3))
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(sK3)
      | ~ r1_tsep_1(sK3,X3) ) ),
    inference(superposition,[],[f45,f91])).

fof(f91,plain,(
    k2_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(resolution,[],[f86,f43])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | ~ r1_tsep_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f412,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,k2_struct_0(sK2))
      | r1_xboole_0(X1,k2_struct_0(sK1)) ) ),
    inference(superposition,[],[f66,f409])).

fof(f409,plain,(
    k2_struct_0(sK2) = k2_xboole_0(k2_struct_0(sK2),k2_struct_0(sK1)) ),
    inference(resolution,[],[f308,f35])).

fof(f35,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f308,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK2)
      | k2_struct_0(sK2) = k2_xboole_0(k2_struct_0(sK2),k2_struct_0(X2)) ) ),
    inference(resolution,[],[f227,f84])).

fof(f227,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1)
      | k2_struct_0(X1) = k2_xboole_0(k2_struct_0(X1),k2_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f225,f57])).

fof(f225,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1)
      | k2_struct_0(X1) = k2_xboole_0(k2_struct_0(X1),k2_struct_0(X0)) ) ),
    inference(resolution,[],[f56,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X1,X0) = X1 ) ),
    inference(subsumption_resolution,[],[f109,f74])).

fof(f74,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X1)
      | k2_xboole_0(X1,X0) = X1 ) ),
    inference(resolution,[],[f71,f96])).

fof(f96,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k2_xboole_0(X1,X2),X1)
      | k2_xboole_0(X1,X2) = X1 ) ),
    inference(resolution,[],[f64,f60])).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f223,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1))
    | r1_tsep_1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f220,f88])).

% (19170)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% (19162)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (19173)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% (19157)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% (19150)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% (19156)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% (19172)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% (19169)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
fof(f88,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f83,f46])).

fof(f83,plain,(
    l1_pre_topc(sK1) ),
    inference(resolution,[],[f81,f39])).

fof(f39,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f220,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | r1_tsep_1(sK3,sK1) ),
    inference(superposition,[],[f142,f92])).

fof(f92,plain,(
    k2_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(resolution,[],[f88,f43])).

fof(f142,plain,(
    ! [X3] :
      ( ~ r1_xboole_0(k2_struct_0(sK3),u1_struct_0(X3))
      | ~ l1_struct_0(X3)
      | r1_tsep_1(sK3,X3) ) ),
    inference(subsumption_resolution,[],[f134,f86])).

fof(f134,plain,(
    ! [X3] :
      ( ~ r1_xboole_0(k2_struct_0(sK3),u1_struct_0(X3))
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(sK3)
      | r1_tsep_1(sK3,X3) ) ),
    inference(superposition,[],[f44,f91])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | r1_tsep_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f32,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | ~ r1_tsep_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f432,plain,(
    r1_tsep_1(sK1,sK3) ),
    inference(subsumption_resolution,[],[f431,f86])).

fof(f431,plain,
    ( ~ l1_struct_0(sK3)
    | r1_tsep_1(sK1,sK3) ),
    inference(resolution,[],[f423,f98])).

fof(f98,plain,(
    ! [X1] :
      ( ~ r1_tsep_1(X1,sK1)
      | ~ l1_struct_0(X1)
      | r1_tsep_1(sK1,X1) ) ),
    inference(resolution,[],[f61,f88])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:14:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (19163)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.51  % (19171)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.54  % (19153)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.54  % (19154)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.54  % (19152)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.54  % (19166)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.54  % (19151)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.55  % (19159)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.55  % (19158)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.55  % (19161)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (19161)Refutation not found, incomplete strategy% (19161)------------------------------
% 0.22/0.55  % (19161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (19161)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (19161)Memory used [KB]: 6140
% 0.22/0.55  % (19161)Time elapsed: 0.115 s
% 0.22/0.55  % (19161)------------------------------
% 0.22/0.55  % (19161)------------------------------
% 0.22/0.55  % (19160)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.55  % (19164)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.55  % (19167)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.55  % (19148)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.56  % (19168)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.56  % (19148)Refutation not found, incomplete strategy% (19148)------------------------------
% 0.22/0.56  % (19148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (19148)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (19148)Memory used [KB]: 10618
% 0.22/0.56  % (19148)Time elapsed: 0.121 s
% 0.22/0.56  % (19148)------------------------------
% 0.22/0.56  % (19148)------------------------------
% 0.22/0.56  % (19149)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.56  % (19167)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f433,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(subsumption_resolution,[],[f432,f425])).
% 0.22/0.56  fof(f425,plain,(
% 0.22/0.56    ~r1_tsep_1(sK1,sK3)),
% 0.22/0.56    inference(subsumption_resolution,[],[f32,f423])).
% 0.22/0.56  fof(f423,plain,(
% 0.22/0.56    r1_tsep_1(sK3,sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f223,f422])).
% 0.22/0.56  fof(f422,plain,(
% 0.22/0.56    r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1))),
% 0.22/0.56    inference(resolution,[],[f412,f273])).
% 0.22/0.56  fof(f273,plain,(
% 0.22/0.56    r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK2))),
% 0.22/0.56    inference(subsumption_resolution,[],[f272,f105])).
% 0.22/0.56  fof(f105,plain,(
% 0.22/0.56    r1_tsep_1(sK3,sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f104,f90])).
% 0.22/0.56  fof(f90,plain,(
% 0.22/0.56    l1_struct_0(sK2)),
% 0.22/0.56    inference(resolution,[],[f84,f46])).
% 0.22/0.56  fof(f46,plain,(
% 0.22/0.56    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f19])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,axiom,(
% 0.22/0.56    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.56  fof(f84,plain,(
% 0.22/0.56    l1_pre_topc(sK2)),
% 0.22/0.56    inference(resolution,[],[f81,f37])).
% 0.22/0.56  fof(f37,plain,(
% 0.22/0.56    m1_pre_topc(sK2,sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f16])).
% 0.22/0.56  fof(f16,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.56    inference(flattening,[],[f15])).
% 0.22/0.56  fof(f15,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3))) & m1_pre_topc(X1,X2)) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f14])).
% 0.22/0.56  fof(f14,negated_conjecture,(
% 0.22/0.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 0.22/0.56    inference(negated_conjecture,[],[f13])).
% 0.22/0.56  fof(f13,conjecture,(
% 0.22/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tmap_1)).
% 0.22/0.56  fof(f81,plain,(
% 0.22/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) )),
% 0.22/0.56    inference(resolution,[],[f57,f42])).
% 0.22/0.56  fof(f42,plain,(
% 0.22/0.56    l1_pre_topc(sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f16])).
% 0.22/0.56  fof(f57,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f21])).
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,axiom,(
% 0.22/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.56  fof(f104,plain,(
% 0.22/0.56    ~l1_struct_0(sK2) | r1_tsep_1(sK3,sK2)),
% 0.22/0.56    inference(resolution,[],[f100,f103])).
% 0.22/0.56  fof(f103,plain,(
% 0.22/0.56    r1_tsep_1(sK2,sK3)),
% 0.22/0.56    inference(subsumption_resolution,[],[f102,f86])).
% 0.22/0.56  fof(f86,plain,(
% 0.22/0.56    l1_struct_0(sK3)),
% 0.22/0.56    inference(resolution,[],[f82,f46])).
% 0.22/0.56  fof(f82,plain,(
% 0.22/0.56    l1_pre_topc(sK3)),
% 0.22/0.56    inference(resolution,[],[f81,f34])).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    m1_pre_topc(sK3,sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f16])).
% 0.22/0.56  fof(f102,plain,(
% 0.22/0.56    ~l1_struct_0(sK3) | r1_tsep_1(sK2,sK3)),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f101])).
% 0.22/0.56  fof(f101,plain,(
% 0.22/0.56    ~l1_struct_0(sK3) | r1_tsep_1(sK2,sK3) | r1_tsep_1(sK2,sK3)),
% 0.22/0.56    inference(resolution,[],[f99,f31])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    r1_tsep_1(sK3,sK2) | r1_tsep_1(sK2,sK3)),
% 0.22/0.56    inference(cnf_transformation,[],[f16])).
% 0.22/0.56  fof(f99,plain,(
% 0.22/0.56    ( ! [X2] : (~r1_tsep_1(X2,sK2) | ~l1_struct_0(X2) | r1_tsep_1(sK2,X2)) )),
% 0.22/0.56    inference(resolution,[],[f61,f90])).
% 0.22/0.56  fof(f61,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~l1_struct_0(X1) | ~l1_struct_0(X0) | ~r1_tsep_1(X0,X1) | r1_tsep_1(X1,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f25])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 0.22/0.56    inference(flattening,[],[f24])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f12])).
% 0.22/0.56  fof(f12,axiom,(
% 0.22/0.56    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).
% 0.22/0.56  fof(f100,plain,(
% 0.22/0.56    ( ! [X3] : (~r1_tsep_1(X3,sK3) | ~l1_struct_0(X3) | r1_tsep_1(sK3,X3)) )),
% 0.22/0.56    inference(resolution,[],[f61,f86])).
% 0.22/0.56  fof(f272,plain,(
% 0.22/0.56    r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK2)) | ~r1_tsep_1(sK3,sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f268,f90])).
% 0.22/0.56  fof(f268,plain,(
% 0.22/0.56    r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK2)) | ~l1_struct_0(sK2) | ~r1_tsep_1(sK3,sK2)),
% 0.22/0.56    inference(superposition,[],[f168,f93])).
% 0.22/0.56  fof(f93,plain,(
% 0.22/0.56    k2_struct_0(sK2) = u1_struct_0(sK2)),
% 0.22/0.56    inference(resolution,[],[f90,f43])).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f17])).
% 0.22/0.56  fof(f17,plain,(
% 0.22/0.56    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,axiom,(
% 0.22/0.56    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.56  fof(f168,plain,(
% 0.22/0.56    ( ! [X3] : (r1_xboole_0(k2_struct_0(sK3),u1_struct_0(X3)) | ~l1_struct_0(X3) | ~r1_tsep_1(sK3,X3)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f159,f86])).
% 0.22/0.56  fof(f159,plain,(
% 0.22/0.56    ( ! [X3] : (r1_xboole_0(k2_struct_0(sK3),u1_struct_0(X3)) | ~l1_struct_0(X3) | ~l1_struct_0(sK3) | ~r1_tsep_1(sK3,X3)) )),
% 0.22/0.56    inference(superposition,[],[f45,f91])).
% 0.22/0.56  fof(f91,plain,(
% 0.22/0.56    k2_struct_0(sK3) = u1_struct_0(sK3)),
% 0.22/0.56    inference(resolution,[],[f86,f43])).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~l1_struct_0(X0) | ~r1_tsep_1(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f18])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f10])).
% 0.22/0.56  fof(f10,axiom,(
% 0.22/0.56    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).
% 0.22/0.56  fof(f412,plain,(
% 0.22/0.56    ( ! [X1] : (~r1_xboole_0(X1,k2_struct_0(sK2)) | r1_xboole_0(X1,k2_struct_0(sK1))) )),
% 0.22/0.56    inference(superposition,[],[f66,f409])).
% 0.22/0.56  fof(f409,plain,(
% 0.22/0.56    k2_struct_0(sK2) = k2_xboole_0(k2_struct_0(sK2),k2_struct_0(sK1))),
% 0.22/0.56    inference(resolution,[],[f308,f35])).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    m1_pre_topc(sK1,sK2)),
% 0.22/0.56    inference(cnf_transformation,[],[f16])).
% 0.22/0.56  fof(f308,plain,(
% 0.22/0.56    ( ! [X2] : (~m1_pre_topc(X2,sK2) | k2_struct_0(sK2) = k2_xboole_0(k2_struct_0(sK2),k2_struct_0(X2))) )),
% 0.22/0.56    inference(resolution,[],[f227,f84])).
% 0.22/0.56  fof(f227,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1) | k2_struct_0(X1) = k2_xboole_0(k2_struct_0(X1),k2_struct_0(X0))) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f225,f57])).
% 0.22/0.56  fof(f225,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1) | k2_struct_0(X1) = k2_xboole_0(k2_struct_0(X1),k2_struct_0(X0))) )),
% 0.22/0.56    inference(resolution,[],[f56,f111])).
% 0.22/0.56  fof(f111,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X1,X0) = X1) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f109,f74])).
% 0.22/0.56  fof(f74,plain,(
% 0.22/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.56    inference(equality_resolution,[],[f63])).
% 0.22/0.56  fof(f63,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f1])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.56  fof(f109,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X1) | k2_xboole_0(X1,X0) = X1) )),
% 0.22/0.56    inference(resolution,[],[f71,f96])).
% 0.22/0.56  fof(f96,plain,(
% 0.22/0.56    ( ! [X2,X1] : (~r1_tarski(k2_xboole_0(X1,X2),X1) | k2_xboole_0(X1,X2) = X1) )),
% 0.22/0.56    inference(resolution,[],[f64,f60])).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.56  fof(f64,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f1])).
% 0.22/0.56  fof(f71,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.22/0.56    inference(flattening,[],[f29])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.22/0.56    inference(ennf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f20])).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).
% 0.22/0.56  fof(f66,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f26])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.22/0.56    inference(ennf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.22/0.56  fof(f223,plain,(
% 0.22/0.56    ~r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1)) | r1_tsep_1(sK3,sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f220,f88])).
% 0.22/0.56  % (19170)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.56  % (19162)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.56  % (19173)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.56  % (19157)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.56  % (19150)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.56  % (19156)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.57  % (19172)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.57  % (19169)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.57  fof(f88,plain,(
% 0.22/0.57    l1_struct_0(sK1)),
% 0.22/0.57    inference(resolution,[],[f83,f46])).
% 0.22/0.57  fof(f83,plain,(
% 0.22/0.57    l1_pre_topc(sK1)),
% 0.22/0.57    inference(resolution,[],[f81,f39])).
% 0.22/0.57  fof(f39,plain,(
% 0.22/0.57    m1_pre_topc(sK1,sK0)),
% 0.22/0.57    inference(cnf_transformation,[],[f16])).
% 0.22/0.57  fof(f220,plain,(
% 0.22/0.57    ~r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1)) | ~l1_struct_0(sK1) | r1_tsep_1(sK3,sK1)),
% 0.22/0.57    inference(superposition,[],[f142,f92])).
% 0.22/0.57  fof(f92,plain,(
% 0.22/0.57    k2_struct_0(sK1) = u1_struct_0(sK1)),
% 0.22/0.57    inference(resolution,[],[f88,f43])).
% 0.22/0.57  fof(f142,plain,(
% 0.22/0.57    ( ! [X3] : (~r1_xboole_0(k2_struct_0(sK3),u1_struct_0(X3)) | ~l1_struct_0(X3) | r1_tsep_1(sK3,X3)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f134,f86])).
% 0.22/0.57  fof(f134,plain,(
% 0.22/0.57    ( ! [X3] : (~r1_xboole_0(k2_struct_0(sK3),u1_struct_0(X3)) | ~l1_struct_0(X3) | ~l1_struct_0(sK3) | r1_tsep_1(sK3,X3)) )),
% 0.22/0.57    inference(superposition,[],[f44,f91])).
% 0.22/0.57  fof(f44,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~l1_struct_0(X0) | r1_tsep_1(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f18])).
% 0.22/0.57  fof(f32,plain,(
% 0.22/0.57    ~r1_tsep_1(sK3,sK1) | ~r1_tsep_1(sK1,sK3)),
% 0.22/0.57    inference(cnf_transformation,[],[f16])).
% 0.22/0.57  fof(f432,plain,(
% 0.22/0.57    r1_tsep_1(sK1,sK3)),
% 0.22/0.57    inference(subsumption_resolution,[],[f431,f86])).
% 0.22/0.57  fof(f431,plain,(
% 0.22/0.57    ~l1_struct_0(sK3) | r1_tsep_1(sK1,sK3)),
% 0.22/0.57    inference(resolution,[],[f423,f98])).
% 0.22/0.57  fof(f98,plain,(
% 0.22/0.57    ( ! [X1] : (~r1_tsep_1(X1,sK1) | ~l1_struct_0(X1) | r1_tsep_1(sK1,X1)) )),
% 0.22/0.57    inference(resolution,[],[f61,f88])).
% 0.22/0.57  % SZS output end Proof for theBenchmark
% 0.22/0.57  % (19167)------------------------------
% 0.22/0.57  % (19167)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (19167)Termination reason: Refutation
% 0.22/0.57  
% 0.22/0.57  % (19167)Memory used [KB]: 1791
% 0.22/0.57  % (19167)Time elapsed: 0.129 s
% 0.22/0.57  % (19167)------------------------------
% 0.22/0.57  % (19167)------------------------------
% 0.22/0.57  % (19147)Success in time 0.206 s
%------------------------------------------------------------------------------
