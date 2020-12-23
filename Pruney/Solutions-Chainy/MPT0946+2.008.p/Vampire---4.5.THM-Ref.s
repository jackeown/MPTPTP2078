%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  133 (1824 expanded)
%              Number of leaves         :   12 ( 348 expanded)
%              Depth                    :   52
%              Number of atoms          :  383 (5972 expanded)
%              Number of equality atoms :   84 (1301 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f250,plain,(
    $false ),
    inference(subsumption_resolution,[],[f249,f70])).

fof(f70,plain,(
    r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) ),
    inference(subsumption_resolution,[],[f69,f38])).

fof(f38,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f69,plain,
    ( ~ v1_relat_1(k1_wellord2(sK0))
    | r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) ),
    inference(subsumption_resolution,[],[f68,f38])).

fof(f68,plain,
    ( ~ v1_relat_1(k1_wellord2(sK1))
    | ~ v1_relat_1(k1_wellord2(sK0))
    | r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) ),
    inference(resolution,[],[f40,f35])).

fof(f35,plain,(
    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | r4_wellord1(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).

fof(f249,plain,(
    ~ r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) ),
    inference(backward_demodulation,[],[f240,f248])).

fof(f248,plain,(
    k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0) ),
    inference(resolution,[],[f246,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).

fof(f246,plain,(
    r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f245,f37])).

fof(f37,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f245,plain,
    ( r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f244,f34])).

fof(f34,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f244,plain,
    ( ~ v3_ordinal1(sK1)
    | r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f239,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f239,plain,(
    r1_ordinal1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f88,f237])).

fof(f237,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f236,f35])).

fof(f236,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
    | ~ r2_hidden(sK1,sK0) ),
    inference(backward_demodulation,[],[f214,f235])).

fof(f235,plain,(
    k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f234,f52])).

fof(f234,plain,
    ( k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)
    | r1_tarski(sK1,sK0) ),
    inference(subsumption_resolution,[],[f233,f34])).

fof(f233,plain,
    ( k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)
    | r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(subsumption_resolution,[],[f232,f37])).

fof(f232,plain,
    ( k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)
    | ~ v3_ordinal1(sK0)
    | r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f231,f55])).

fof(f231,plain,
    ( r1_ordinal1(sK1,sK0)
    | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(resolution,[],[f230,f87])).

fof(f87,plain,
    ( r2_hidden(sK0,sK1)
    | r1_ordinal1(sK1,sK0) ),
    inference(resolution,[],[f71,f37])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | r1_ordinal1(sK1,X0)
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f42,f34])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f230,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f229,f70])).

fof(f229,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | ~ r2_hidden(sK0,sK1)
    | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(superposition,[],[f228,f203])).

fof(f203,plain,
    ( k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0)
    | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(resolution,[],[f183,f52])).

fof(f183,plain,
    ( r1_tarski(sK0,sK1)
    | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f182,f37])).

fof(f182,plain,
    ( k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)
    | r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f181,f34])).

fof(f181,plain,
    ( k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)
    | ~ v3_ordinal1(sK1)
    | r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f137,f55])).

fof(f137,plain,
    ( r1_ordinal1(sK0,sK1)
    | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(resolution,[],[f128,f52])).

fof(f128,plain,
    ( r1_tarski(sK1,sK0)
    | r1_ordinal1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f127,f34])).

fof(f127,plain,
    ( r1_ordinal1(sK0,sK1)
    | r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(subsumption_resolution,[],[f126,f37])).

fof(f126,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ v3_ordinal1(sK0)
    | r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f91,f55])).

fof(f91,plain,
    ( r1_ordinal1(sK1,sK0)
    | r1_ordinal1(sK0,sK1) ),
    inference(resolution,[],[f73,f37])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | r1_ordinal1(sK1,X0)
      | r1_ordinal1(X0,sK1) ) ),
    inference(resolution,[],[f53,f34])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_ordinal1(X0,X1)
      | r1_ordinal1(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f228,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ r2_hidden(sK0,sK1) ),
    inference(forward_demodulation,[],[f227,f63])).

fof(f63,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(subsumption_resolution,[],[f56,f38])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_wellord2(X0))
      | k3_relat_1(k1_wellord2(X0)) = X0 ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

% (14197)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
fof(f227,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1))) ),
    inference(subsumption_resolution,[],[f226,f38])).

fof(f226,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1)))
    | ~ v1_relat_1(k1_wellord2(sK1)) ),
    inference(subsumption_resolution,[],[f225,f66])).

fof(f66,plain,(
    v2_wellord1(k1_wellord2(sK1)) ),
    inference(resolution,[],[f41,f34])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v2_wellord1(k1_wellord2(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).

fof(f225,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ v2_wellord1(k1_wellord2(sK1))
    | ~ r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1)))
    | ~ v1_relat_1(k1_wellord2(sK1)) ),
    inference(superposition,[],[f39,f224])).

fof(f224,plain,(
    sK0 = k1_wellord1(k1_wellord2(sK1),sK0) ),
    inference(subsumption_resolution,[],[f223,f37])).

fof(f223,plain,
    ( sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | ~ v3_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f222,f34])).

fof(f222,plain,
    ( sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(duplicate_literal_removal,[],[f221])).

fof(f221,plain,
    ( sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | sK0 = k1_wellord1(k1_wellord2(sK1),sK0) ),
    inference(resolution,[],[f217,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | k1_wellord1(k1_wellord2(X1),X0) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
           => k1_wellord1(k1_wellord2(X1),X0) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).

fof(f217,plain,
    ( r2_hidden(sK0,sK1)
    | sK0 = k1_wellord1(k1_wellord2(sK1),sK0) ),
    inference(resolution,[],[f216,f102])).

fof(f102,plain,
    ( r2_hidden(sK1,sK0)
    | r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f100,f36])).

fof(f36,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

fof(f100,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 = sK1
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f75,f37])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | r2_hidden(sK1,X0)
      | sK1 = X0
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f44,f34])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X0,X1)
      | X0 = X1
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f216,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k1_wellord1(k1_wellord2(sK1),sK0) ),
    inference(subsumption_resolution,[],[f215,f35])).

% (14198)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f215,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
    | ~ r2_hidden(sK1,sK0)
    | sK0 = k1_wellord1(k1_wellord2(sK1),sK0) ),
    inference(superposition,[],[f214,f166])).

fof(f166,plain,
    ( k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)
    | sK0 = k1_wellord1(k1_wellord2(sK1),sK0) ),
    inference(resolution,[],[f140,f52])).

fof(f140,plain,
    ( r1_tarski(sK1,sK0)
    | sK0 = k1_wellord1(k1_wellord2(sK1),sK0) ),
    inference(subsumption_resolution,[],[f139,f34])).

fof(f139,plain,
    ( sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(subsumption_resolution,[],[f138,f37])).

fof(f138,plain,
    ( sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | ~ v3_ordinal1(sK0)
    | r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f115,f55])).

fof(f115,plain,
    ( r1_ordinal1(sK1,sK0)
    | sK0 = k1_wellord1(k1_wellord2(sK1),sK0) ),
    inference(subsumption_resolution,[],[f114,f37])).

fof(f114,plain,
    ( r1_ordinal1(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | sK0 = k1_wellord1(k1_wellord2(sK1),sK0) ),
    inference(subsumption_resolution,[],[f113,f34])).

fof(f113,plain,
    ( r1_ordinal1(sK1,sK0)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | sK0 = k1_wellord1(k1_wellord2(sK1),sK0) ),
    inference(resolution,[],[f87,f43])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
      | ~ v2_wellord1(X0)
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).

fof(f214,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1))
    | ~ r2_hidden(sK1,sK0) ),
    inference(forward_demodulation,[],[f213,f63])).

fof(f213,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1))
    | ~ r2_hidden(sK1,k3_relat_1(k1_wellord2(sK0))) ),
    inference(subsumption_resolution,[],[f212,f38])).

fof(f212,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1))
    | ~ r2_hidden(sK1,k3_relat_1(k1_wellord2(sK0)))
    | ~ v1_relat_1(k1_wellord2(sK0)) ),
    inference(subsumption_resolution,[],[f211,f67])).

fof(f67,plain,(
    v2_wellord1(k1_wellord2(sK0)) ),
    inference(resolution,[],[f41,f37])).

fof(f211,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1))
    | ~ v2_wellord1(k1_wellord2(sK0))
    | ~ r2_hidden(sK1,k3_relat_1(k1_wellord2(sK0)))
    | ~ v1_relat_1(k1_wellord2(sK0)) ),
    inference(superposition,[],[f39,f210])).

fof(f210,plain,(
    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f209,f70])).

fof(f209,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(duplicate_literal_removal,[],[f208])).

fof(f208,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(superposition,[],[f188,f168])).

fof(f168,plain,
    ( k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(resolution,[],[f143,f52])).

fof(f143,plain,
    ( r1_tarski(sK0,sK1)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f142,f37])).

fof(f142,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f141,f34])).

fof(f141,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | ~ v3_ordinal1(sK1)
    | r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f119,f55])).

fof(f119,plain,
    ( r1_ordinal1(sK0,sK1)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f118,f34])).

fof(f118,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f117,f37])).

fof(f117,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(resolution,[],[f88,f43])).

fof(f188,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f187,f132])).

fof(f132,plain,
    ( r2_hidden(sK0,sK1)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f131,f34])).

fof(f131,plain,
    ( r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f130,f37])).

fof(f130,plain,
    ( r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(resolution,[],[f102,f43])).

fof(f187,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(forward_demodulation,[],[f186,f63])).

fof(f186,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1)))
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f185,f38])).

fof(f185,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1)))
    | ~ v1_relat_1(k1_wellord2(sK1))
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f184,f66])).

fof(f184,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ v2_wellord1(k1_wellord2(sK1))
    | ~ r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1)))
    | ~ v1_relat_1(k1_wellord2(sK1))
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(superposition,[],[f39,f147])).

fof(f147,plain,
    ( sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f146,f37])).

fof(f146,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | ~ v3_ordinal1(sK0)
    | sK0 = k1_wellord1(k1_wellord2(sK1),sK0) ),
    inference(subsumption_resolution,[],[f145,f34])).

fof(f145,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | sK0 = k1_wellord1(k1_wellord2(sK1),sK0) ),
    inference(resolution,[],[f132,f43])).

fof(f88,plain,
    ( r2_hidden(sK1,sK0)
    | r1_ordinal1(sK0,sK1) ),
    inference(resolution,[],[f72,f34])).

fof(f72,plain,(
    ! [X1] :
      ( ~ v3_ordinal1(X1)
      | r1_ordinal1(sK0,X1)
      | r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f42,f37])).

fof(f240,plain,(
    ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) ),
    inference(subsumption_resolution,[],[f228,f238])).

fof(f238,plain,(
    r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f102,f237])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:33:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (14192)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.51  % (14202)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.52  % (14203)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.52  % (14205)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.52  % (14193)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (14195)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.52  % (14201)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.52  % (14201)Refutation not found, incomplete strategy% (14201)------------------------------
% 0.21/0.52  % (14201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (14201)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (14201)Memory used [KB]: 1663
% 0.21/0.52  % (14201)Time elapsed: 0.073 s
% 0.21/0.52  % (14201)------------------------------
% 0.21/0.52  % (14201)------------------------------
% 0.21/0.52  % (14208)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.52  % (14194)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.52  % (14208)Refutation not found, incomplete strategy% (14208)------------------------------
% 0.21/0.52  % (14208)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (14208)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (14208)Memory used [KB]: 10618
% 0.21/0.52  % (14208)Time elapsed: 0.086 s
% 0.21/0.52  % (14208)------------------------------
% 0.21/0.52  % (14208)------------------------------
% 0.21/0.53  % (14205)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f250,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f249,f70])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))),
% 0.21/0.53    inference(subsumption_resolution,[],[f69,f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    ~v1_relat_1(k1_wellord2(sK0)) | r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))),
% 0.21/0.53    inference(subsumption_resolution,[],[f68,f38])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ~v1_relat_1(k1_wellord2(sK1)) | ~v1_relat_1(k1_wellord2(sK0)) | r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))),
% 0.21/0.53    inference(resolution,[],[f40,f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.53    inference(flattening,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,negated_conjecture,(
% 0.21/0.53    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 0.21/0.53    inference(negated_conjecture,[],[f12])).
% 0.21/0.53  fof(f12,conjecture,(
% 0.21/0.53    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r4_wellord1(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | r4_wellord1(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) => r4_wellord1(X1,X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).
% 0.21/0.53  fof(f249,plain,(
% 0.21/0.53    ~r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))),
% 0.21/0.53    inference(backward_demodulation,[],[f240,f248])).
% 0.21/0.53  fof(f248,plain,(
% 0.21/0.53    k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0)),
% 0.21/0.53    inference(resolution,[],[f246,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) | ~r1_tarski(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).
% 0.21/0.53  fof(f246,plain,(
% 0.21/0.53    r1_tarski(sK0,sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f245,f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    v3_ordinal1(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f245,plain,(
% 0.21/0.53    r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f244,f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    v3_ordinal1(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f244,plain,(
% 0.21/0.53    ~v3_ordinal1(sK1) | r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0)),
% 0.21/0.53    inference(resolution,[],[f239,f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.53    inference(flattening,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.21/0.53  fof(f239,plain,(
% 0.21/0.53    r1_ordinal1(sK0,sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f88,f237])).
% 0.21/0.53  fof(f237,plain,(
% 0.21/0.53    ~r2_hidden(sK1,sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f236,f35])).
% 0.21/0.53  fof(f236,plain,(
% 0.21/0.53    ~r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) | ~r2_hidden(sK1,sK0)),
% 0.21/0.53    inference(backward_demodulation,[],[f214,f235])).
% 0.21/0.53  fof(f235,plain,(
% 0.21/0.53    k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f234,f52])).
% 0.21/0.53  fof(f234,plain,(
% 0.21/0.53    k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) | r1_tarski(sK1,sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f233,f34])).
% 0.21/0.53  fof(f233,plain,(
% 0.21/0.53    k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) | r1_tarski(sK1,sK0) | ~v3_ordinal1(sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f232,f37])).
% 0.21/0.53  fof(f232,plain,(
% 0.21/0.53    k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) | ~v3_ordinal1(sK0) | r1_tarski(sK1,sK0) | ~v3_ordinal1(sK1)),
% 0.21/0.53    inference(resolution,[],[f231,f55])).
% 0.21/0.53  fof(f231,plain,(
% 0.21/0.53    r1_ordinal1(sK1,sK0) | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.53    inference(resolution,[],[f230,f87])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    r2_hidden(sK0,sK1) | r1_ordinal1(sK1,sK0)),
% 0.21/0.53    inference(resolution,[],[f71,f37])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ( ! [X0] : (~v3_ordinal1(X0) | r1_ordinal1(sK1,X0) | r2_hidden(X0,sK1)) )),
% 0.21/0.53    inference(resolution,[],[f42,f34])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r1_ordinal1(X0,X1) | r2_hidden(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.53    inference(flattening,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.21/0.53  fof(f230,plain,(
% 0.21/0.53    ~r2_hidden(sK0,sK1) | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f229,f70])).
% 0.21/0.53  fof(f229,plain,(
% 0.21/0.53    ~r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) | ~r2_hidden(sK0,sK1) | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.53    inference(superposition,[],[f228,f203])).
% 0.21/0.53  fof(f203,plain,(
% 0.21/0.53    k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0) | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.53    inference(resolution,[],[f183,f52])).
% 0.21/0.53  fof(f183,plain,(
% 0.21/0.53    r1_tarski(sK0,sK1) | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f182,f37])).
% 0.21/0.53  fof(f182,plain,(
% 0.21/0.53    k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) | r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f181,f34])).
% 0.21/0.53  fof(f181,plain,(
% 0.21/0.53    k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) | ~v3_ordinal1(sK1) | r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0)),
% 0.21/0.53    inference(resolution,[],[f137,f55])).
% 0.21/0.53  fof(f137,plain,(
% 0.21/0.53    r1_ordinal1(sK0,sK1) | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.53    inference(resolution,[],[f128,f52])).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    r1_tarski(sK1,sK0) | r1_ordinal1(sK0,sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f127,f34])).
% 0.21/0.53  fof(f127,plain,(
% 0.21/0.53    r1_ordinal1(sK0,sK1) | r1_tarski(sK1,sK0) | ~v3_ordinal1(sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f126,f37])).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    r1_ordinal1(sK0,sK1) | ~v3_ordinal1(sK0) | r1_tarski(sK1,sK0) | ~v3_ordinal1(sK1)),
% 0.21/0.53    inference(resolution,[],[f91,f55])).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    r1_ordinal1(sK1,sK0) | r1_ordinal1(sK0,sK1)),
% 0.21/0.53    inference(resolution,[],[f73,f37])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    ( ! [X0] : (~v3_ordinal1(X0) | r1_ordinal1(sK1,X0) | r1_ordinal1(X0,sK1)) )),
% 0.21/0.53    inference(resolution,[],[f53,f34])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r1_ordinal1(X0,X1) | r1_ordinal1(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.53    inference(flattening,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 0.21/0.53  fof(f228,plain,(
% 0.21/0.53    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | ~r2_hidden(sK0,sK1)),
% 0.21/0.53    inference(forward_demodulation,[],[f227,f63])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f56,f38])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_relat_1(k1_wellord2(X0)) | k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.21/0.53    inference(equality_resolution,[],[f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(flattening,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).
% 0.21/0.53  % (14197)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.53  fof(f227,plain,(
% 0.21/0.53    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | ~r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f226,f38])).
% 0.21/0.53  fof(f226,plain,(
% 0.21/0.53    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | ~r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1))) | ~v1_relat_1(k1_wellord2(sK1))),
% 0.21/0.53    inference(subsumption_resolution,[],[f225,f66])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    v2_wellord1(k1_wellord2(sK1))),
% 0.21/0.53    inference(resolution,[],[f41,f34])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X0] : (~v3_ordinal1(X0) | v2_wellord1(k1_wellord2(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0] : (v3_ordinal1(X0) => v2_wellord1(k1_wellord2(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).
% 0.21/0.53  fof(f225,plain,(
% 0.21/0.53    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | ~v2_wellord1(k1_wellord2(sK1)) | ~r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1))) | ~v1_relat_1(k1_wellord2(sK1))),
% 0.21/0.53    inference(superposition,[],[f39,f224])).
% 0.21/0.53  fof(f224,plain,(
% 0.21/0.53    sK0 = k1_wellord1(k1_wellord2(sK1),sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f223,f37])).
% 0.21/0.53  fof(f223,plain,(
% 0.21/0.53    sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | ~v3_ordinal1(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f222,f34])).
% 0.21/0.53  fof(f222,plain,(
% 0.21/0.53    sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0)),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f221])).
% 0.21/0.53  fof(f221,plain,(
% 0.21/0.53    sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | sK0 = k1_wellord1(k1_wellord2(sK1),sK0)),
% 0.21/0.53    inference(resolution,[],[f217,f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | k1_wellord1(k1_wellord2(X1),X0) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.53    inference(flattening,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => k1_wellord1(k1_wellord2(X1),X0) = X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).
% 0.21/0.53  fof(f217,plain,(
% 0.21/0.53    r2_hidden(sK0,sK1) | sK0 = k1_wellord1(k1_wellord2(sK1),sK0)),
% 0.21/0.53    inference(resolution,[],[f216,f102])).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    r2_hidden(sK1,sK0) | r2_hidden(sK0,sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f100,f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    sK0 != sK1),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    r2_hidden(sK1,sK0) | sK0 = sK1 | r2_hidden(sK0,sK1)),
% 0.21/0.53    inference(resolution,[],[f75,f37])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    ( ! [X0] : (~v3_ordinal1(X0) | r2_hidden(sK1,X0) | sK1 = X0 | r2_hidden(X0,sK1)) )),
% 0.21/0.53    inference(resolution,[],[f44,f34])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r2_hidden(X0,X1) | X0 = X1 | r2_hidden(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.53    inference(flattening,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).
% 0.21/0.53  fof(f216,plain,(
% 0.21/0.53    ~r2_hidden(sK1,sK0) | sK0 = k1_wellord1(k1_wellord2(sK1),sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f215,f35])).
% 0.21/0.53  % (14198)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.53  fof(f215,plain,(
% 0.21/0.53    ~r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) | ~r2_hidden(sK1,sK0) | sK0 = k1_wellord1(k1_wellord2(sK1),sK0)),
% 0.21/0.53    inference(superposition,[],[f214,f166])).
% 0.21/0.53  fof(f166,plain,(
% 0.21/0.53    k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) | sK0 = k1_wellord1(k1_wellord2(sK1),sK0)),
% 0.21/0.53    inference(resolution,[],[f140,f52])).
% 0.21/0.53  fof(f140,plain,(
% 0.21/0.53    r1_tarski(sK1,sK0) | sK0 = k1_wellord1(k1_wellord2(sK1),sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f139,f34])).
% 0.21/0.53  fof(f139,plain,(
% 0.21/0.53    sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | r1_tarski(sK1,sK0) | ~v3_ordinal1(sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f138,f37])).
% 0.21/0.53  fof(f138,plain,(
% 0.21/0.53    sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | ~v3_ordinal1(sK0) | r1_tarski(sK1,sK0) | ~v3_ordinal1(sK1)),
% 0.21/0.53    inference(resolution,[],[f115,f55])).
% 0.21/0.53  fof(f115,plain,(
% 0.21/0.53    r1_ordinal1(sK1,sK0) | sK0 = k1_wellord1(k1_wellord2(sK1),sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f114,f37])).
% 0.21/0.53  fof(f114,plain,(
% 0.21/0.53    r1_ordinal1(sK1,sK0) | ~v3_ordinal1(sK0) | sK0 = k1_wellord1(k1_wellord2(sK1),sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f113,f34])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    r1_ordinal1(sK1,sK0) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | sK0 = k1_wellord1(k1_wellord2(sK1),sK0)),
% 0.21/0.53    inference(resolution,[],[f87,f43])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~v2_wellord1(X0) | ~r2_hidden(X1,k3_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0] : ((! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) & r2_hidden(X1,k3_relat_1(X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).
% 0.21/0.53  fof(f214,plain,(
% 0.21/0.53    ~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1)) | ~r2_hidden(sK1,sK0)),
% 0.21/0.53    inference(forward_demodulation,[],[f213,f63])).
% 0.21/0.53  fof(f213,plain,(
% 0.21/0.53    ~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1)) | ~r2_hidden(sK1,k3_relat_1(k1_wellord2(sK0)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f212,f38])).
% 0.21/0.53  fof(f212,plain,(
% 0.21/0.53    ~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1)) | ~r2_hidden(sK1,k3_relat_1(k1_wellord2(sK0))) | ~v1_relat_1(k1_wellord2(sK0))),
% 0.21/0.53    inference(subsumption_resolution,[],[f211,f67])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    v2_wellord1(k1_wellord2(sK0))),
% 0.21/0.53    inference(resolution,[],[f41,f37])).
% 0.21/0.53  fof(f211,plain,(
% 0.21/0.53    ~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1)) | ~v2_wellord1(k1_wellord2(sK0)) | ~r2_hidden(sK1,k3_relat_1(k1_wellord2(sK0))) | ~v1_relat_1(k1_wellord2(sK0))),
% 0.21/0.53    inference(superposition,[],[f39,f210])).
% 0.21/0.53  fof(f210,plain,(
% 0.21/0.53    sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f209,f70])).
% 0.21/0.53  fof(f209,plain,(
% 0.21/0.53    ~r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f208])).
% 0.21/0.53  fof(f208,plain,(
% 0.21/0.53    ~r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.53    inference(superposition,[],[f188,f168])).
% 0.21/0.53  fof(f168,plain,(
% 0.21/0.53    k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.53    inference(resolution,[],[f143,f52])).
% 0.21/0.53  fof(f143,plain,(
% 0.21/0.53    r1_tarski(sK0,sK1) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f142,f37])).
% 0.21/0.53  fof(f142,plain,(
% 0.21/0.53    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f141,f34])).
% 0.21/0.53  fof(f141,plain,(
% 0.21/0.53    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | ~v3_ordinal1(sK1) | r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0)),
% 0.21/0.53    inference(resolution,[],[f119,f55])).
% 0.21/0.53  fof(f119,plain,(
% 0.21/0.53    r1_ordinal1(sK0,sK1) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f118,f34])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    r1_ordinal1(sK0,sK1) | ~v3_ordinal1(sK1) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f117,f37])).
% 0.21/0.53  fof(f117,plain,(
% 0.21/0.53    r1_ordinal1(sK0,sK1) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.53    inference(resolution,[],[f88,f43])).
% 0.21/0.53  fof(f188,plain,(
% 0.21/0.53    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f187,f132])).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    r2_hidden(sK0,sK1) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f131,f34])).
% 0.21/0.53  fof(f131,plain,(
% 0.21/0.53    r2_hidden(sK0,sK1) | ~v3_ordinal1(sK1) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f130,f37])).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    r2_hidden(sK0,sK1) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.53    inference(resolution,[],[f102,f43])).
% 0.21/0.53  fof(f187,plain,(
% 0.21/0.53    ~r2_hidden(sK0,sK1) | ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.53    inference(forward_demodulation,[],[f186,f63])).
% 0.21/0.53  fof(f186,plain,(
% 0.21/0.53    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | ~r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1))) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f185,f38])).
% 0.21/0.53  fof(f185,plain,(
% 0.21/0.53    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | ~r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1))) | ~v1_relat_1(k1_wellord2(sK1)) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f184,f66])).
% 0.21/0.53  fof(f184,plain,(
% 0.21/0.53    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | ~v2_wellord1(k1_wellord2(sK1)) | ~r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1))) | ~v1_relat_1(k1_wellord2(sK1)) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.53    inference(superposition,[],[f39,f147])).
% 0.21/0.53  fof(f147,plain,(
% 0.21/0.53    sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f146,f37])).
% 0.21/0.53  fof(f146,plain,(
% 0.21/0.53    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | ~v3_ordinal1(sK0) | sK0 = k1_wellord1(k1_wellord2(sK1),sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f145,f34])).
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | sK0 = k1_wellord1(k1_wellord2(sK1),sK0)),
% 0.21/0.53    inference(resolution,[],[f132,f43])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    r2_hidden(sK1,sK0) | r1_ordinal1(sK0,sK1)),
% 0.21/0.53    inference(resolution,[],[f72,f34])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    ( ! [X1] : (~v3_ordinal1(X1) | r1_ordinal1(sK0,X1) | r2_hidden(X1,sK0)) )),
% 0.21/0.53    inference(resolution,[],[f42,f37])).
% 0.21/0.53  fof(f240,plain,(
% 0.21/0.53    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))),
% 0.21/0.53    inference(subsumption_resolution,[],[f228,f238])).
% 0.21/0.53  fof(f238,plain,(
% 0.21/0.53    r2_hidden(sK0,sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f102,f237])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (14205)------------------------------
% 0.21/0.53  % (14205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (14205)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (14205)Memory used [KB]: 1663
% 0.21/0.53  % (14205)Time elapsed: 0.114 s
% 0.21/0.53  % (14205)------------------------------
% 0.21/0.53  % (14205)------------------------------
% 0.21/0.53  % (14198)Refutation not found, incomplete strategy% (14198)------------------------------
% 0.21/0.53  % (14198)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (14198)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (14198)Memory used [KB]: 6140
% 0.21/0.53  % (14198)Time elapsed: 0.119 s
% 0.21/0.53  % (14198)------------------------------
% 0.21/0.53  % (14198)------------------------------
% 0.21/0.53  % (14190)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.53  % (14181)Success in time 0.174 s
%------------------------------------------------------------------------------
