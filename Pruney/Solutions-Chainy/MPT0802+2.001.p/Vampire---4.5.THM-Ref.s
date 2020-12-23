%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:07 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 378 expanded)
%              Number of leaves         :    9 (  80 expanded)
%              Depth                    :   10
%              Number of atoms          :  246 (2074 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f94,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f27,f53,f78,f75,f81,f84,f72,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_wellord1(X0,X1)
      | ~ r1_relat_2(X0,X1)
      | ~ r8_relat_2(X0,X1)
      | ~ r4_relat_2(X0,X1)
      | ~ r6_relat_2(X0,X1)
      | ~ v1_relat_1(X0)
      | r2_wellord1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_wellord1(X0,X1)
        <=> ( r1_wellord1(X0,X1)
            & r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r2_wellord1(X0,X1)
        <=> ( r1_wellord1(X0,X1)
            & r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_wellord1)).

fof(f72,plain,(
    r1_wellord1(sK1,k3_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f27,f71,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_wellord1(X0)
      | r1_wellord1(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_wellord1(X0)
      <=> r1_wellord1(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_wellord1(X0)
      <=> r1_wellord1(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_wellord1)).

fof(f71,plain,(
    v1_wellord1(sK1) ),
    inference(unit_resulting_resolution,[],[f69,f28,f23,f22,f27,f25,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_wellord1(X0,X1,X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X0)
      | ~ v1_wellord1(X0)
      | v1_wellord1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v1_wellord1(X1)
                  | ~ v1_wellord1(X0) )
                & ( v4_relat_2(X1)
                  | ~ v4_relat_2(X0) )
                & ( v6_relat_2(X1)
                  | ~ v6_relat_2(X0) )
                & ( v8_relat_2(X1)
                  | ~ v8_relat_2(X0) )
                & ( v1_relat_2(X1)
                  | ~ v1_relat_2(X0) ) )
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v1_wellord1(X1)
                  | ~ v1_wellord1(X0) )
                & ( v4_relat_2(X1)
                  | ~ v4_relat_2(X0) )
                & ( v6_relat_2(X1)
                  | ~ v6_relat_2(X0) )
                & ( v8_relat_2(X1)
                  | ~ v8_relat_2(X0) )
                & ( v1_relat_2(X1)
                  | ~ v1_relat_2(X0) ) )
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( r3_wellord1(X0,X1,X2)
               => ( ( v1_wellord1(X0)
                   => v1_wellord1(X1) )
                  & ( v4_relat_2(X0)
                   => v4_relat_2(X1) )
                  & ( v6_relat_2(X0)
                   => v6_relat_2(X1) )
                  & ( v8_relat_2(X0)
                   => v8_relat_2(X1) )
                  & ( v1_relat_2(X0)
                   => v1_relat_2(X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_wellord1)).

fof(f25,plain,(
    r3_wellord1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_wellord1(X1)
              & r3_wellord1(X0,X1,X2)
              & v2_wellord1(X0)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_wellord1(X1)
              & r3_wellord1(X0,X1,X2)
              & v2_wellord1(X0)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( r3_wellord1(X0,X1,X2)
                    & v2_wellord1(X0) )
                 => v2_wellord1(X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( r3_wellord1(X0,X1,X2)
                  & v2_wellord1(X0) )
               => v2_wellord1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_wellord1)).

fof(f22,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f23,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f28,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f69,plain,(
    v1_wellord1(sK0) ),
    inference(unit_resulting_resolution,[],[f28,f68,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ r1_wellord1(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_wellord1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f68,plain,(
    r1_wellord1(sK0,k3_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f28,f52,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_wellord1(X0,X1)
      | r1_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f52,plain,(
    r2_wellord1(sK0,k3_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f24,f28,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0)
      | r2_wellord1(X0,k3_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( r2_wellord1(X0,k3_relat_1(X0))
      <=> v2_wellord1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( r2_wellord1(X0,k3_relat_1(X0))
      <=> v2_wellord1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord1)).

fof(f24,plain,(
    v2_wellord1(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f84,plain,(
    r1_relat_2(sK1,k3_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f27,f83,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_relat_2(X0)
      | r1_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
      <=> r1_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_relat_2(X0)
      <=> r1_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_relat_2)).

fof(f83,plain,(
    v1_relat_2(sK1) ),
    inference(unit_resulting_resolution,[],[f57,f28,f23,f22,f27,f25,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_wellord1(X0,X1,X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_2(X0)
      | v1_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f57,plain,(
    v1_relat_2(sK0) ),
    inference(unit_resulting_resolution,[],[f28,f56,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ r1_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f56,plain,(
    r1_relat_2(sK0,k3_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f28,f52,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_wellord1(X0,X1)
      | r1_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f81,plain,(
    r8_relat_2(sK1,k3_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f27,f80,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v8_relat_2(X0)
      | r8_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> r8_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v8_relat_2(X0)
      <=> r8_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_2)).

fof(f80,plain,(
    v8_relat_2(sK1) ),
    inference(unit_resulting_resolution,[],[f60,f28,f23,f22,f27,f25,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_wellord1(X0,X1,X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X0)
      | ~ v8_relat_2(X0)
      | v8_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f60,plain,(
    v8_relat_2(sK0) ),
    inference(unit_resulting_resolution,[],[f28,f59,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ r8_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v8_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f59,plain,(
    r8_relat_2(sK0,k3_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f28,f52,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_wellord1(X0,X1)
      | r8_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f75,plain,(
    r4_relat_2(sK1,k3_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f27,f74,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v4_relat_2(X0)
      | r4_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> r4_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v4_relat_2(X0)
      <=> r4_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_2)).

fof(f74,plain,(
    v4_relat_2(sK1) ),
    inference(unit_resulting_resolution,[],[f63,f28,f23,f22,f27,f25,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_wellord1(X0,X1,X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_2(X0)
      | v4_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f63,plain,(
    v4_relat_2(sK0) ),
    inference(unit_resulting_resolution,[],[f28,f62,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ r4_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v4_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f62,plain,(
    r4_relat_2(sK0,k3_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f28,f52,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_wellord1(X0,X1)
      | r4_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f78,plain,(
    r6_relat_2(sK1,k3_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f27,f77,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v6_relat_2(X0)
      | r6_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> r6_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v6_relat_2(X0)
      <=> r6_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_2)).

fof(f77,plain,(
    v6_relat_2(sK1) ),
    inference(unit_resulting_resolution,[],[f66,f28,f23,f22,f27,f25,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_wellord1(X0,X1,X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X0)
      | ~ v6_relat_2(X0)
      | v6_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f66,plain,(
    v6_relat_2(sK0) ),
    inference(unit_resulting_resolution,[],[f28,f65,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ r6_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v6_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f65,plain,(
    r6_relat_2(sK0,k3_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f28,f52,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_wellord1(X0,X1)
      | r6_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f53,plain,(
    ~ r2_wellord1(sK1,k3_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f27,f26,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ r2_wellord1(X0,k3_relat_1(X0))
      | v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f26,plain,(
    ~ v2_wellord1(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:16:54 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (7774)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.46  % (7781)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.20/0.47  % (7769)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.20/0.47  % (7781)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f94,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f27,f53,f78,f75,f81,f84,f72,f51])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_wellord1(X0,X1) | ~r1_relat_2(X0,X1) | ~r8_relat_2(X0,X1) | ~r4_relat_2(X0,X1) | ~r6_relat_2(X0,X1) | ~v1_relat_1(X0) | r2_wellord1(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (r2_wellord1(X0,X1) <=> (r1_wellord1(X0,X1) & r6_relat_2(X0,X1) & r4_relat_2(X0,X1) & r8_relat_2(X0,X1) & r1_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r2_wellord1(X0,X1) <=> (r1_wellord1(X0,X1) & r6_relat_2(X0,X1) & r4_relat_2(X0,X1) & r8_relat_2(X0,X1) & r1_relat_2(X0,X1))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_wellord1)).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    r1_wellord1(sK1,k3_relat_1(sK1))),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f27,f71,f38])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_wellord1(X0) | r1_wellord1(X0,k3_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0] : ((v1_wellord1(X0) <=> r1_wellord1(X0,k3_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => (v1_wellord1(X0) <=> r1_wellord1(X0,k3_relat_1(X0))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_wellord1)).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    v1_wellord1(sK1)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f69,f28,f23,f22,f27,f25,f41])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r3_wellord1(X0,X1,X2) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X0) | ~v1_wellord1(X0) | v1_wellord1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (((v1_wellord1(X1) | ~v1_wellord1(X0)) & (v4_relat_2(X1) | ~v4_relat_2(X0)) & (v6_relat_2(X1) | ~v6_relat_2(X0)) & (v8_relat_2(X1) | ~v8_relat_2(X0)) & (v1_relat_2(X1) | ~v1_relat_2(X0))) | ~r3_wellord1(X0,X1,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : ((((v1_wellord1(X1) | ~v1_wellord1(X0)) & (v4_relat_2(X1) | ~v4_relat_2(X0)) & (v6_relat_2(X1) | ~v6_relat_2(X0)) & (v8_relat_2(X1) | ~v8_relat_2(X0)) & (v1_relat_2(X1) | ~v1_relat_2(X0))) | ~r3_wellord1(X0,X1,X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r3_wellord1(X0,X1,X2) => ((v1_wellord1(X0) => v1_wellord1(X1)) & (v4_relat_2(X0) => v4_relat_2(X1)) & (v6_relat_2(X0) => v6_relat_2(X1)) & (v8_relat_2(X0) => v8_relat_2(X1)) & (v1_relat_2(X0) => v1_relat_2(X1)))))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_wellord1)).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    r3_wellord1(sK0,sK1,sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : (~v2_wellord1(X1) & r3_wellord1(X0,X1,X2) & v2_wellord1(X0) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : ((~v2_wellord1(X1) & (r3_wellord1(X0,X1,X2) & v2_wellord1(X0))) & (v1_funct_1(X2) & v1_relat_1(X2))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,negated_conjecture,(
% 0.20/0.47    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r3_wellord1(X0,X1,X2) & v2_wellord1(X0)) => v2_wellord1(X1)))))),
% 0.20/0.47    inference(negated_conjecture,[],[f9])).
% 0.20/0.47  fof(f9,conjecture,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r3_wellord1(X0,X1,X2) & v2_wellord1(X0)) => v2_wellord1(X1)))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_wellord1)).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    v1_relat_1(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    v1_funct_1(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    v1_relat_1(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    v1_wellord1(sK0)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f28,f68,f37])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_wellord1(X0,k3_relat_1(X0)) | ~v1_relat_1(X0) | v1_wellord1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    r1_wellord1(sK0,k3_relat_1(sK0))),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f28,f52,f50])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_wellord1(X0,X1) | r1_wellord1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    r2_wellord1(sK0,k3_relat_1(sK0))),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f24,f28,f39])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ( ! [X0] : (~v2_wellord1(X0) | ~v1_relat_1(X0) | r2_wellord1(X0,k3_relat_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0] : ((r2_wellord1(X0,k3_relat_1(X0)) <=> v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => (r2_wellord1(X0,k3_relat_1(X0)) <=> v2_wellord1(X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord1)).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    v2_wellord1(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f84,plain,(
% 0.20/0.47    r1_relat_2(sK1,k3_relat_1(sK1))),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f27,f83,f36])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_relat_2(X0) | r1_relat_2(X0,k3_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0] : ((v1_relat_2(X0) <=> r1_relat_2(X0,k3_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => (v1_relat_2(X0) <=> r1_relat_2(X0,k3_relat_1(X0))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_relat_2)).
% 0.20/0.47  fof(f83,plain,(
% 0.20/0.47    v1_relat_2(sK1)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f57,f28,f23,f22,f27,f25,f45])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r3_wellord1(X0,X1,X2) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X0) | ~v1_relat_2(X0) | v1_relat_2(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f20])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    v1_relat_2(sK0)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f28,f56,f35])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_relat_2(X0,k3_relat_1(X0)) | ~v1_relat_1(X0) | v1_relat_2(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    r1_relat_2(sK0,k3_relat_1(sK0))),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f28,f52,f46])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_wellord1(X0,X1) | r1_relat_2(X0,X1) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    r8_relat_2(sK1,k3_relat_1(sK1))),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f27,f80,f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ( ! [X0] : (~v8_relat_2(X0) | r8_relat_2(X0,k3_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0] : ((v8_relat_2(X0) <=> r8_relat_2(X0,k3_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => (v8_relat_2(X0) <=> r8_relat_2(X0,k3_relat_1(X0))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_2)).
% 0.20/0.47  fof(f80,plain,(
% 0.20/0.47    v8_relat_2(sK1)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f60,f28,f23,f22,f27,f25,f44])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r3_wellord1(X0,X1,X2) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X0) | ~v8_relat_2(X0) | v8_relat_2(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f20])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    v8_relat_2(sK0)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f28,f59,f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ( ! [X0] : (~r8_relat_2(X0,k3_relat_1(X0)) | ~v1_relat_1(X0) | v8_relat_2(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    r8_relat_2(sK0,k3_relat_1(sK0))),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f28,f52,f47])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_wellord1(X0,X1) | r8_relat_2(X0,X1) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f75,plain,(
% 0.20/0.47    r4_relat_2(sK1,k3_relat_1(sK1))),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f27,f74,f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X0] : (~v4_relat_2(X0) | r4_relat_2(X0,k3_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0] : ((v4_relat_2(X0) <=> r4_relat_2(X0,k3_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => (v4_relat_2(X0) <=> r4_relat_2(X0,k3_relat_1(X0))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_2)).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    v4_relat_2(sK1)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f63,f28,f23,f22,f27,f25,f42])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r3_wellord1(X0,X1,X2) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X0) | ~v4_relat_2(X0) | v4_relat_2(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f20])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    v4_relat_2(sK0)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f28,f62,f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ( ! [X0] : (~r4_relat_2(X0,k3_relat_1(X0)) | ~v1_relat_1(X0) | v4_relat_2(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    r4_relat_2(sK0,k3_relat_1(sK0))),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f28,f52,f48])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_wellord1(X0,X1) | r4_relat_2(X0,X1) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    r6_relat_2(sK1,k3_relat_1(sK1))),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f27,f77,f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ( ! [X0] : (~v6_relat_2(X0) | r6_relat_2(X0,k3_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0] : ((v6_relat_2(X0) <=> r6_relat_2(X0,k3_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => (v6_relat_2(X0) <=> r6_relat_2(X0,k3_relat_1(X0))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_2)).
% 0.20/0.47  fof(f77,plain,(
% 0.20/0.47    v6_relat_2(sK1)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f66,f28,f23,f22,f27,f25,f43])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r3_wellord1(X0,X1,X2) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X0) | ~v6_relat_2(X0) | v6_relat_2(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f20])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    v6_relat_2(sK0)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f28,f65,f31])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ( ! [X0] : (~r6_relat_2(X0,k3_relat_1(X0)) | ~v1_relat_1(X0) | v6_relat_2(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    r6_relat_2(sK0,k3_relat_1(sK0))),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f28,f52,f49])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_wellord1(X0,X1) | r6_relat_2(X0,X1) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    ~r2_wellord1(sK1,k3_relat_1(sK1))),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f27,f26,f40])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_wellord1(X0,k3_relat_1(X0)) | v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ~v2_wellord1(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    v1_relat_1(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (7781)------------------------------
% 0.20/0.47  % (7781)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (7781)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (7781)Memory used [KB]: 895
% 0.20/0.47  % (7781)Time elapsed: 0.007 s
% 0.20/0.47  % (7781)------------------------------
% 0.20/0.47  % (7781)------------------------------
% 0.20/0.47  % (7780)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.20/0.47  % (7765)Success in time 0.111 s
%------------------------------------------------------------------------------
