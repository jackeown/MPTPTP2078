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
% DateTime   : Thu Dec  3 12:53:56 EST 2020

% Result     : Theorem 4.04s
% Output     : Refutation 4.04s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 122 expanded)
%              Number of leaves         :   14 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :  182 ( 349 expanded)
%              Number of equality atoms :   34 (  75 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11618,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f384,f388,f11608])).

fof(f11608,plain,(
    ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f11567])).

fof(f11567,plain,
    ( $false
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f1298,f4553,f822])).

fof(f822,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k10_relat_1(sK1,X2),k10_relat_1(sK1,X3))
      | k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X2,X3)) ) ),
    inference(superposition,[],[f80,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k6_subset_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f55,f59])).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f80,plain,(
    ! [X0,X1] : k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) ),
    inference(unit_resulting_resolution,[],[f36,f37,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

fof(f37,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(X0,k2_relat_1(X1))
         => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f36,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f4553,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK1,X0),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X0))))
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f36,f4523,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f4523,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))
    | ~ spl4_5 ),
    inference(duplicate_literal_removal,[],[f4519])).

fof(f4519,plain,
    ( ! [X0] :
        ( r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))
        | r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) )
    | ~ spl4_5 ),
    inference(resolution,[],[f449,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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

fof(f449,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK3(X0,k1_relat_1(sK1)),k10_relat_1(sK1,X1))
        | r1_tarski(X0,k1_relat_1(sK1)) )
    | ~ spl4_5 ),
    inference(resolution,[],[f379,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f379,plain,
    ( ! [X12,X11] :
        ( r2_hidden(X11,k1_relat_1(sK1))
        | ~ r2_hidden(X11,k10_relat_1(sK1,X12)) )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f378])).

fof(f378,plain,
    ( spl4_5
  <=> ! [X11,X12] :
        ( r2_hidden(X11,k1_relat_1(sK1))
        | ~ r2_hidden(X11,k10_relat_1(sK1,X12)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f1298,plain,(
    k1_xboole_0 != k10_relat_1(sK1,k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))) ),
    inference(unit_resulting_resolution,[],[f36,f92,f436,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
          & r1_tarski(X0,k2_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).

fof(f436,plain,(
    k1_xboole_0 != k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))) ),
    inference(unit_resulting_resolution,[],[f188,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f56,f59])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f188,plain,(
    ~ r1_tarski(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))) ),
    inference(unit_resulting_resolution,[],[f39,f79,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f79,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ),
    inference(unit_resulting_resolution,[],[f36,f37,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f39,plain,(
    sK0 != k9_relat_1(sK1,k10_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f92,plain,(
    ! [X0] : r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f65,f38,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f38,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f65,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f46,f59])).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f388,plain,(
    spl4_6 ),
    inference(avatar_contradiction_clause,[],[f385])).

fof(f385,plain,
    ( $false
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f36,f383])).

fof(f383,plain,
    ( ~ v1_relat_1(sK1)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f381])).

fof(f381,plain,
    ( spl4_6
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f384,plain,
    ( spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f87,f381,f378])).

fof(f87,plain,(
    ! [X12,X11] :
      ( ~ v1_relat_1(sK1)
      | r2_hidden(X11,k1_relat_1(sK1))
      | ~ r2_hidden(X11,k10_relat_1(sK1,X12)) ) ),
    inference(resolution,[],[f37,f74])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:38:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (5298)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (5304)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.51  % (5291)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (5290)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (5312)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.51  % (5287)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (5286)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (5303)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.52  % (5296)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (5306)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (5288)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (5308)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (5297)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (5314)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.52  % (5300)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (5301)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (5311)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (5289)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (5305)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.53  % (5299)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (5292)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (5294)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (5293)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (5295)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (5313)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (5315)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (5302)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (5307)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.55  % (5310)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.55/0.56  % (5309)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 3.21/0.81  % (5291)Time limit reached!
% 3.21/0.81  % (5291)------------------------------
% 3.21/0.81  % (5291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.21/0.81  % (5291)Termination reason: Time limit
% 3.21/0.81  
% 3.21/0.81  % (5291)Memory used [KB]: 8571
% 3.21/0.81  % (5291)Time elapsed: 0.407 s
% 3.21/0.81  % (5291)------------------------------
% 3.21/0.81  % (5291)------------------------------
% 4.04/0.88  % (5290)Refutation found. Thanks to Tanya!
% 4.04/0.88  % SZS status Theorem for theBenchmark
% 4.04/0.89  % SZS output start Proof for theBenchmark
% 4.04/0.89  fof(f11618,plain,(
% 4.04/0.89    $false),
% 4.04/0.89    inference(avatar_sat_refutation,[],[f384,f388,f11608])).
% 4.04/0.89  fof(f11608,plain,(
% 4.04/0.89    ~spl4_5),
% 4.04/0.89    inference(avatar_contradiction_clause,[],[f11567])).
% 4.04/0.89  fof(f11567,plain,(
% 4.04/0.89    $false | ~spl4_5),
% 4.04/0.89    inference(unit_resulting_resolution,[],[f1298,f4553,f822])).
% 4.04/0.89  fof(f822,plain,(
% 4.04/0.89    ( ! [X2,X3] : (~r1_tarski(k10_relat_1(sK1,X2),k10_relat_1(sK1,X3)) | k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X2,X3))) )),
% 4.04/0.89    inference(superposition,[],[f80,f67])).
% 4.04/0.89  fof(f67,plain,(
% 4.04/0.89    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 4.04/0.89    inference(definition_unfolding,[],[f55,f59])).
% 4.04/0.89  fof(f59,plain,(
% 4.04/0.89    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 4.04/0.89    inference(cnf_transformation,[],[f11])).
% 4.04/0.89  fof(f11,axiom,(
% 4.04/0.89    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 4.04/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 4.04/0.89  fof(f55,plain,(
% 4.04/0.89    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 4.04/0.89    inference(cnf_transformation,[],[f3])).
% 4.04/0.89  fof(f3,axiom,(
% 4.04/0.89    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 4.04/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 4.04/0.89  fof(f80,plain,(
% 4.04/0.89    ( ! [X0,X1] : (k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))) )),
% 4.04/0.89    inference(unit_resulting_resolution,[],[f36,f37,f48])).
% 4.04/0.89  fof(f48,plain,(
% 4.04/0.89    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) )),
% 4.04/0.89    inference(cnf_transformation,[],[f31])).
% 4.04/0.89  fof(f31,plain,(
% 4.04/0.89    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 4.04/0.89    inference(flattening,[],[f30])).
% 4.04/0.89  fof(f30,plain,(
% 4.04/0.89    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 4.04/0.89    inference(ennf_transformation,[],[f15])).
% 4.04/0.89  fof(f15,axiom,(
% 4.04/0.89    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 4.04/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).
% 4.04/0.89  fof(f37,plain,(
% 4.04/0.89    v1_funct_1(sK1)),
% 4.04/0.89    inference(cnf_transformation,[],[f21])).
% 4.04/0.89  fof(f21,plain,(
% 4.04/0.89    ? [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) != X0 & r1_tarski(X0,k2_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 4.04/0.89    inference(flattening,[],[f20])).
% 4.04/0.89  fof(f20,plain,(
% 4.04/0.89    ? [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) != X0 & r1_tarski(X0,k2_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 4.04/0.89    inference(ennf_transformation,[],[f19])).
% 4.04/0.89  fof(f19,negated_conjecture,(
% 4.04/0.89    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 4.04/0.89    inference(negated_conjecture,[],[f18])).
% 4.04/0.89  fof(f18,conjecture,(
% 4.04/0.89    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 4.04/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 4.04/0.89  fof(f36,plain,(
% 4.04/0.89    v1_relat_1(sK1)),
% 4.04/0.89    inference(cnf_transformation,[],[f21])).
% 4.04/0.89  fof(f4553,plain,(
% 4.04/0.89    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,X0),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X0))))) ) | ~spl4_5),
% 4.04/0.89    inference(unit_resulting_resolution,[],[f36,f4523,f44])).
% 4.04/0.89  fof(f44,plain,(
% 4.04/0.89    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) )),
% 4.04/0.89    inference(cnf_transformation,[],[f25])).
% 4.04/0.89  fof(f25,plain,(
% 4.04/0.89    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 4.04/0.89    inference(flattening,[],[f24])).
% 4.04/0.89  fof(f24,plain,(
% 4.04/0.89    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 4.04/0.89    inference(ennf_transformation,[],[f17])).
% 4.04/0.89  fof(f17,axiom,(
% 4.04/0.89    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 4.04/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 4.04/0.89  fof(f4523,plain,(
% 4.04/0.89    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))) ) | ~spl4_5),
% 4.04/0.89    inference(duplicate_literal_removal,[],[f4519])).
% 4.04/0.89  fof(f4519,plain,(
% 4.04/0.89    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) | r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))) ) | ~spl4_5),
% 4.04/0.89    inference(resolution,[],[f449,f61])).
% 4.04/0.89  fof(f61,plain,(
% 4.04/0.89    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 4.04/0.89    inference(cnf_transformation,[],[f34])).
% 4.04/0.89  fof(f34,plain,(
% 4.04/0.89    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 4.04/0.89    inference(ennf_transformation,[],[f1])).
% 4.04/0.89  fof(f1,axiom,(
% 4.04/0.89    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 4.04/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 4.04/0.89  fof(f449,plain,(
% 4.04/0.89    ( ! [X0,X1] : (~r2_hidden(sK3(X0,k1_relat_1(sK1)),k10_relat_1(sK1,X1)) | r1_tarski(X0,k1_relat_1(sK1))) ) | ~spl4_5),
% 4.04/0.89    inference(resolution,[],[f379,f62])).
% 4.04/0.89  fof(f62,plain,(
% 4.04/0.89    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 4.04/0.89    inference(cnf_transformation,[],[f34])).
% 4.04/0.89  fof(f379,plain,(
% 4.04/0.89    ( ! [X12,X11] : (r2_hidden(X11,k1_relat_1(sK1)) | ~r2_hidden(X11,k10_relat_1(sK1,X12))) ) | ~spl4_5),
% 4.04/0.89    inference(avatar_component_clause,[],[f378])).
% 4.04/0.89  fof(f378,plain,(
% 4.04/0.89    spl4_5 <=> ! [X11,X12] : (r2_hidden(X11,k1_relat_1(sK1)) | ~r2_hidden(X11,k10_relat_1(sK1,X12)))),
% 4.04/0.89    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 4.04/0.89  fof(f1298,plain,(
% 4.04/0.89    k1_xboole_0 != k10_relat_1(sK1,k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))))),
% 4.04/0.89    inference(unit_resulting_resolution,[],[f36,f92,f436,f47])).
% 4.04/0.89  fof(f47,plain,(
% 4.04/0.89    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 4.04/0.89    inference(cnf_transformation,[],[f29])).
% 4.04/0.89  fof(f29,plain,(
% 4.04/0.89    ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1))),
% 4.04/0.89    inference(flattening,[],[f28])).
% 4.04/0.89  fof(f28,plain,(
% 4.04/0.89    ! [X0,X1] : ((k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0) | ~v1_relat_1(X1))),
% 4.04/0.89    inference(ennf_transformation,[],[f13])).
% 4.04/0.89  fof(f13,axiom,(
% 4.04/0.89    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 4.04/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).
% 4.04/0.89  fof(f436,plain,(
% 4.04/0.89    k1_xboole_0 != k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))),
% 4.04/0.89    inference(unit_resulting_resolution,[],[f188,f66])).
% 4.04/0.89  fof(f66,plain,(
% 4.04/0.89    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X0,X1) | r1_tarski(X0,X1)) )),
% 4.04/0.89    inference(definition_unfolding,[],[f56,f59])).
% 4.04/0.89  fof(f56,plain,(
% 4.04/0.89    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 4.04/0.89    inference(cnf_transformation,[],[f3])).
% 4.04/0.89  fof(f188,plain,(
% 4.04/0.89    ~r1_tarski(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))),
% 4.04/0.89    inference(unit_resulting_resolution,[],[f39,f79,f42])).
% 4.04/0.89  fof(f42,plain,(
% 4.04/0.89    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 4.04/0.89    inference(cnf_transformation,[],[f2])).
% 4.04/0.89  fof(f2,axiom,(
% 4.04/0.89    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.04/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 4.04/0.89  fof(f79,plain,(
% 4.04/0.89    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) )),
% 4.04/0.89    inference(unit_resulting_resolution,[],[f36,f37,f43])).
% 4.04/0.89  fof(f43,plain,(
% 4.04/0.89    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)) )),
% 4.04/0.89    inference(cnf_transformation,[],[f23])).
% 4.04/0.89  fof(f23,plain,(
% 4.04/0.89    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 4.04/0.89    inference(flattening,[],[f22])).
% 4.04/0.89  fof(f22,plain,(
% 4.04/0.89    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 4.04/0.89    inference(ennf_transformation,[],[f16])).
% 4.04/0.89  fof(f16,axiom,(
% 4.04/0.89    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 4.04/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 4.04/0.89  fof(f39,plain,(
% 4.04/0.89    sK0 != k9_relat_1(sK1,k10_relat_1(sK1,sK0))),
% 4.04/0.89    inference(cnf_transformation,[],[f21])).
% 4.04/0.89  fof(f92,plain,(
% 4.04/0.89    ( ! [X0] : (r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK1))) )),
% 4.04/0.89    inference(unit_resulting_resolution,[],[f65,f38,f45])).
% 4.04/0.89  fof(f45,plain,(
% 4.04/0.89    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 4.04/0.89    inference(cnf_transformation,[],[f27])).
% 4.04/0.89  fof(f27,plain,(
% 4.04/0.89    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 4.04/0.89    inference(flattening,[],[f26])).
% 4.04/0.89  fof(f26,plain,(
% 4.04/0.89    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 4.04/0.89    inference(ennf_transformation,[],[f4])).
% 4.04/0.89  fof(f4,axiom,(
% 4.04/0.89    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 4.04/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 4.04/0.89  fof(f38,plain,(
% 4.04/0.89    r1_tarski(sK0,k2_relat_1(sK1))),
% 4.04/0.89    inference(cnf_transformation,[],[f21])).
% 4.04/0.89  fof(f65,plain,(
% 4.04/0.89    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 4.04/0.89    inference(definition_unfolding,[],[f46,f59])).
% 4.04/0.89  fof(f46,plain,(
% 4.04/0.89    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 4.04/0.89    inference(cnf_transformation,[],[f6])).
% 4.04/0.89  fof(f6,axiom,(
% 4.04/0.89    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 4.04/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 4.04/0.89  fof(f388,plain,(
% 4.04/0.89    spl4_6),
% 4.04/0.89    inference(avatar_contradiction_clause,[],[f385])).
% 4.04/0.89  fof(f385,plain,(
% 4.04/0.89    $false | spl4_6),
% 4.04/0.89    inference(unit_resulting_resolution,[],[f36,f383])).
% 4.04/0.89  fof(f383,plain,(
% 4.04/0.89    ~v1_relat_1(sK1) | spl4_6),
% 4.04/0.89    inference(avatar_component_clause,[],[f381])).
% 4.04/0.89  fof(f381,plain,(
% 4.04/0.89    spl4_6 <=> v1_relat_1(sK1)),
% 4.04/0.89    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 4.04/0.89  fof(f384,plain,(
% 4.04/0.89    spl4_5 | ~spl4_6),
% 4.04/0.89    inference(avatar_split_clause,[],[f87,f381,f378])).
% 4.04/0.89  fof(f87,plain,(
% 4.04/0.89    ( ! [X12,X11] : (~v1_relat_1(sK1) | r2_hidden(X11,k1_relat_1(sK1)) | ~r2_hidden(X11,k10_relat_1(sK1,X12))) )),
% 4.04/0.89    inference(resolution,[],[f37,f74])).
% 4.04/0.89  fof(f74,plain,(
% 4.04/0.89    ( ! [X0,X3,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,k10_relat_1(X0,X1))) )),
% 4.04/0.89    inference(equality_resolution,[],[f52])).
% 4.04/0.89  fof(f52,plain,(
% 4.04/0.89    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 4.04/0.89    inference(cnf_transformation,[],[f33])).
% 4.04/0.89  fof(f33,plain,(
% 4.04/0.89    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.04/0.89    inference(flattening,[],[f32])).
% 4.04/0.89  fof(f32,plain,(
% 4.04/0.89    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.04/0.89    inference(ennf_transformation,[],[f14])).
% 4.04/0.89  fof(f14,axiom,(
% 4.04/0.89    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))))),
% 4.04/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_1)).
% 4.04/0.89  % SZS output end Proof for theBenchmark
% 4.04/0.89  % (5290)------------------------------
% 4.04/0.89  % (5290)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.04/0.89  % (5290)Termination reason: Refutation
% 4.04/0.89  
% 4.04/0.89  % (5290)Memory used [KB]: 8955
% 4.04/0.89  % (5290)Time elapsed: 0.484 s
% 4.04/0.89  % (5290)------------------------------
% 4.04/0.89  % (5290)------------------------------
% 4.04/0.89  % (5285)Success in time 0.538 s
%------------------------------------------------------------------------------
