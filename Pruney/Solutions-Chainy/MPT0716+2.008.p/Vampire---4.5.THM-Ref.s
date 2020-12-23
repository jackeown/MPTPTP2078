%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:49 EST 2020

% Result     : Theorem 1.82s
% Output     : Refutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 163 expanded)
%              Number of leaves         :   11 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :  203 ( 693 expanded)
%              Number of equality atoms :    8 (  16 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f225,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f110,f132,f184,f206,f224])).

fof(f224,plain,
    ( ~ spl5_1
    | spl5_2
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f219])).

fof(f219,plain,
    ( $false
    | ~ spl5_1
    | spl5_2
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f29,f30,f89,f92,f109,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | r1_tarski(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(f109,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl5_3
  <=> r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f92,plain,
    ( ~ r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl5_2
  <=> r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f89,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl5_1
  <=> r1_tarski(sK2,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f30,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <~> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <~> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
              <=> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <=> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_1)).

fof(f29,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f206,plain,
    ( ~ spl5_2
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f199])).

fof(f199,plain,
    ( $false
    | ~ spl5_2
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f67,f98,f108,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f108,plain,
    ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f107])).

fof(f98,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k9_relat_1(sK0,k10_relat_1(sK0,k1_relat_1(sK1))))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f29,f93,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

fof(f93,plain,
    ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f91])).

fof(f67,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK0,k10_relat_1(sK0,X0)),X0) ),
    inference(unit_resulting_resolution,[],[f29,f30,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f184,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | spl5_1
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f93,f133,f141,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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

fof(f141,plain,
    ( ! [X0] : ~ r2_hidden(sK4(sK2,k1_relat_1(sK0)),k10_relat_1(sK0,X0))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f29,f30,f134,f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f134,plain,
    ( ~ r2_hidden(sK4(sK2,k1_relat_1(sK0)),k1_relat_1(sK0))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f88,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f88,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK0))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f87])).

fof(f133,plain,
    ( r2_hidden(sK4(sK2,k1_relat_1(sK0)),sK2)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f88,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f132,plain,
    ( ~ spl5_3
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f64,f91,f87,f107])).

fof(f64,plain,
    ( ~ r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | ~ r1_tarski(sK2,k1_relat_1(sK0))
    | ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f24,f61])).

fof(f61,plain,(
    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f27,f29,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f24,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK0))
    | ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f11])).

fof(f110,plain,
    ( spl5_3
    | spl5_2 ),
    inference(avatar_split_clause,[],[f66,f91,f107])).

fof(f66,plain,
    ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f26,f61])).

fof(f26,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f11])).

fof(f94,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f65,f91,f87])).

fof(f65,plain,
    ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | r1_tarski(sK2,k1_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f25,f61])).

fof(f25,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:37:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.56  % (5092)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.56  % (5100)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.58  % (5091)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.58  % (5114)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.58  % (5096)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.58  % (5106)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.51/0.58  % (5101)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.51/0.58  % (5094)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.51/0.59  % (5098)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.51/0.59  % (5097)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.51/0.59  % (5093)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.51/0.60  % (5095)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.51/0.60  % (5117)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.82/0.60  % (5120)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.82/0.60  % (5115)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.82/0.60  % (5107)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.82/0.61  % (5112)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.82/0.61  % (5110)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.82/0.61  % (5119)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.82/0.61  % (5109)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.82/0.62  % (5113)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.82/0.62  % (5099)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.82/0.62  % (5118)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.82/0.62  % (5104)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.82/0.62  % (5095)Refutation found. Thanks to Tanya!
% 1.82/0.62  % SZS status Theorem for theBenchmark
% 1.82/0.62  % SZS output start Proof for theBenchmark
% 1.82/0.62  fof(f225,plain,(
% 1.82/0.62    $false),
% 1.82/0.62    inference(avatar_sat_refutation,[],[f94,f110,f132,f184,f206,f224])).
% 1.82/0.62  fof(f224,plain,(
% 1.82/0.62    ~spl5_1 | spl5_2 | ~spl5_3),
% 1.82/0.62    inference(avatar_contradiction_clause,[],[f219])).
% 1.82/0.62  fof(f219,plain,(
% 1.82/0.62    $false | (~spl5_1 | spl5_2 | ~spl5_3)),
% 1.82/0.62    inference(unit_resulting_resolution,[],[f29,f30,f89,f92,f109,f31])).
% 1.82/0.62  fof(f31,plain,(
% 1.82/0.62    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | r1_tarski(X0,k10_relat_1(X2,X1))) )),
% 1.82/0.62    inference(cnf_transformation,[],[f13])).
% 1.82/0.62  fof(f13,plain,(
% 1.82/0.62    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.82/0.62    inference(flattening,[],[f12])).
% 1.82/0.62  fof(f12,plain,(
% 1.82/0.62    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.82/0.62    inference(ennf_transformation,[],[f7])).
% 1.82/0.62  fof(f7,axiom,(
% 1.82/0.62    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 1.82/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).
% 1.82/0.62  fof(f109,plain,(
% 1.82/0.62    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~spl5_3),
% 1.82/0.62    inference(avatar_component_clause,[],[f107])).
% 1.82/0.62  fof(f107,plain,(
% 1.82/0.62    spl5_3 <=> r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))),
% 1.82/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.82/0.62  fof(f92,plain,(
% 1.82/0.62    ~r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | spl5_2),
% 1.82/0.62    inference(avatar_component_clause,[],[f91])).
% 1.82/0.62  fof(f91,plain,(
% 1.82/0.62    spl5_2 <=> r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))),
% 1.82/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.82/0.62  fof(f89,plain,(
% 1.82/0.62    r1_tarski(sK2,k1_relat_1(sK0)) | ~spl5_1),
% 1.82/0.62    inference(avatar_component_clause,[],[f87])).
% 1.82/0.62  fof(f87,plain,(
% 1.82/0.62    spl5_1 <=> r1_tarski(sK2,k1_relat_1(sK0))),
% 1.82/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.82/0.62  fof(f30,plain,(
% 1.82/0.62    v1_funct_1(sK0)),
% 1.82/0.62    inference(cnf_transformation,[],[f11])).
% 1.82/0.62  fof(f11,plain,(
% 1.82/0.62    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.82/0.62    inference(flattening,[],[f10])).
% 1.82/0.62  fof(f10,plain,(
% 1.82/0.62    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.82/0.62    inference(ennf_transformation,[],[f9])).
% 1.82/0.62  fof(f9,negated_conjecture,(
% 1.82/0.62    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 1.82/0.62    inference(negated_conjecture,[],[f8])).
% 1.82/0.62  fof(f8,conjecture,(
% 1.82/0.62    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 1.82/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_1)).
% 1.82/0.62  fof(f29,plain,(
% 1.82/0.62    v1_relat_1(sK0)),
% 1.82/0.62    inference(cnf_transformation,[],[f11])).
% 1.82/0.62  fof(f206,plain,(
% 1.82/0.62    ~spl5_2 | spl5_3),
% 1.82/0.62    inference(avatar_contradiction_clause,[],[f199])).
% 1.82/0.62  fof(f199,plain,(
% 1.82/0.62    $false | (~spl5_2 | spl5_3)),
% 1.82/0.62    inference(unit_resulting_resolution,[],[f67,f98,f108,f34])).
% 1.82/0.62  fof(f34,plain,(
% 1.82/0.62    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.82/0.62    inference(cnf_transformation,[],[f19])).
% 1.82/0.62  fof(f19,plain,(
% 1.82/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.82/0.62    inference(flattening,[],[f18])).
% 1.82/0.62  fof(f18,plain,(
% 1.82/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.82/0.62    inference(ennf_transformation,[],[f2])).
% 1.82/0.62  fof(f2,axiom,(
% 1.82/0.62    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.82/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.82/0.62  fof(f108,plain,(
% 1.82/0.62    ~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | spl5_3),
% 1.82/0.62    inference(avatar_component_clause,[],[f107])).
% 1.82/0.62  fof(f98,plain,(
% 1.82/0.62    r1_tarski(k9_relat_1(sK0,sK2),k9_relat_1(sK0,k10_relat_1(sK0,k1_relat_1(sK1)))) | ~spl5_2),
% 1.82/0.62    inference(unit_resulting_resolution,[],[f29,f93,f32])).
% 1.82/0.62  fof(f32,plain,(
% 1.82/0.62    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 1.82/0.62    inference(cnf_transformation,[],[f15])).
% 1.82/0.62  fof(f15,plain,(
% 1.82/0.62    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 1.82/0.62    inference(flattening,[],[f14])).
% 1.82/0.62  fof(f14,plain,(
% 1.82/0.62    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 1.82/0.62    inference(ennf_transformation,[],[f3])).
% 1.82/0.62  fof(f3,axiom,(
% 1.82/0.62    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 1.82/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).
% 1.82/0.62  fof(f93,plain,(
% 1.82/0.62    r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | ~spl5_2),
% 1.82/0.62    inference(avatar_component_clause,[],[f91])).
% 1.82/0.62  fof(f67,plain,(
% 1.82/0.62    ( ! [X0] : (r1_tarski(k9_relat_1(sK0,k10_relat_1(sK0,X0)),X0)) )),
% 1.82/0.62    inference(unit_resulting_resolution,[],[f29,f30,f33])).
% 1.82/0.62  fof(f33,plain,(
% 1.82/0.62    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)) )),
% 1.82/0.62    inference(cnf_transformation,[],[f17])).
% 1.82/0.62  fof(f17,plain,(
% 1.82/0.62    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.82/0.62    inference(flattening,[],[f16])).
% 1.82/0.62  fof(f16,plain,(
% 1.82/0.62    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.82/0.62    inference(ennf_transformation,[],[f6])).
% 1.82/0.62  fof(f6,axiom,(
% 1.82/0.62    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 1.82/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 1.82/0.62  fof(f184,plain,(
% 1.82/0.62    spl5_1 | ~spl5_2),
% 1.82/0.62    inference(avatar_contradiction_clause,[],[f182])).
% 1.82/0.62  fof(f182,plain,(
% 1.82/0.62    $false | (spl5_1 | ~spl5_2)),
% 1.82/0.62    inference(unit_resulting_resolution,[],[f93,f133,f141,f42])).
% 1.82/0.62  fof(f42,plain,(
% 1.82/0.62    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.82/0.62    inference(cnf_transformation,[],[f23])).
% 1.82/0.62  fof(f23,plain,(
% 1.82/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.82/0.62    inference(ennf_transformation,[],[f1])).
% 1.82/0.62  fof(f1,axiom,(
% 1.82/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.82/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.82/0.62  fof(f141,plain,(
% 1.82/0.62    ( ! [X0] : (~r2_hidden(sK4(sK2,k1_relat_1(sK0)),k10_relat_1(sK0,X0))) ) | spl5_1),
% 1.82/0.62    inference(unit_resulting_resolution,[],[f29,f30,f134,f47])).
% 1.82/0.62  fof(f47,plain,(
% 1.82/0.62    ( ! [X0,X3,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,k10_relat_1(X0,X1))) )),
% 1.82/0.62    inference(equality_resolution,[],[f39])).
% 1.82/0.62  fof(f39,plain,(
% 1.82/0.62    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 1.82/0.62    inference(cnf_transformation,[],[f22])).
% 1.82/0.62  fof(f22,plain,(
% 1.82/0.62    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.82/0.62    inference(flattening,[],[f21])).
% 1.82/0.62  fof(f21,plain,(
% 1.82/0.62    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.82/0.62    inference(ennf_transformation,[],[f5])).
% 1.82/0.62  fof(f5,axiom,(
% 1.82/0.62    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.82/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_1)).
% 1.82/0.62  fof(f134,plain,(
% 1.82/0.62    ~r2_hidden(sK4(sK2,k1_relat_1(sK0)),k1_relat_1(sK0)) | spl5_1),
% 1.82/0.62    inference(unit_resulting_resolution,[],[f88,f44])).
% 1.82/0.62  fof(f44,plain,(
% 1.82/0.62    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.82/0.62    inference(cnf_transformation,[],[f23])).
% 1.82/0.62  fof(f88,plain,(
% 1.82/0.62    ~r1_tarski(sK2,k1_relat_1(sK0)) | spl5_1),
% 1.82/0.62    inference(avatar_component_clause,[],[f87])).
% 1.82/0.62  fof(f133,plain,(
% 1.82/0.62    r2_hidden(sK4(sK2,k1_relat_1(sK0)),sK2) | spl5_1),
% 1.82/0.62    inference(unit_resulting_resolution,[],[f88,f43])).
% 1.82/0.62  fof(f43,plain,(
% 1.82/0.62    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 1.82/0.62    inference(cnf_transformation,[],[f23])).
% 1.82/0.62  fof(f132,plain,(
% 1.82/0.62    ~spl5_3 | ~spl5_1 | ~spl5_2),
% 1.82/0.62    inference(avatar_split_clause,[],[f64,f91,f87,f107])).
% 1.82/0.62  fof(f64,plain,(
% 1.82/0.62    ~r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))),
% 1.82/0.62    inference(backward_demodulation,[],[f24,f61])).
% 1.82/0.62  fof(f61,plain,(
% 1.82/0.62    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1))),
% 1.82/0.62    inference(unit_resulting_resolution,[],[f27,f29,f35])).
% 1.82/0.62  fof(f35,plain,(
% 1.82/0.62    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 1.82/0.62    inference(cnf_transformation,[],[f20])).
% 1.82/0.62  fof(f20,plain,(
% 1.82/0.62    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.82/0.62    inference(ennf_transformation,[],[f4])).
% 1.82/0.62  fof(f4,axiom,(
% 1.82/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.82/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 1.82/0.62  fof(f27,plain,(
% 1.82/0.62    v1_relat_1(sK1)),
% 1.82/0.62    inference(cnf_transformation,[],[f11])).
% 1.82/0.62  fof(f24,plain,(
% 1.82/0.62    ~r1_tarski(sK2,k1_relat_1(sK0)) | ~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 1.82/0.62    inference(cnf_transformation,[],[f11])).
% 1.82/0.62  fof(f110,plain,(
% 1.82/0.62    spl5_3 | spl5_2),
% 1.82/0.62    inference(avatar_split_clause,[],[f66,f91,f107])).
% 1.82/0.62  fof(f66,plain,(
% 1.82/0.62    r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))),
% 1.82/0.62    inference(backward_demodulation,[],[f26,f61])).
% 1.82/0.62  fof(f26,plain,(
% 1.82/0.62    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 1.82/0.62    inference(cnf_transformation,[],[f11])).
% 1.82/0.62  fof(f94,plain,(
% 1.82/0.62    spl5_1 | spl5_2),
% 1.82/0.62    inference(avatar_split_clause,[],[f65,f91,f87])).
% 1.82/0.62  fof(f65,plain,(
% 1.82/0.62    r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | r1_tarski(sK2,k1_relat_1(sK0))),
% 1.82/0.62    inference(backward_demodulation,[],[f25,f61])).
% 1.82/0.62  fof(f25,plain,(
% 1.82/0.62    r1_tarski(sK2,k1_relat_1(sK0)) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 1.82/0.62    inference(cnf_transformation,[],[f11])).
% 1.82/0.62  % SZS output end Proof for theBenchmark
% 1.82/0.62  % (5095)------------------------------
% 1.82/0.62  % (5095)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.62  % (5095)Termination reason: Refutation
% 1.82/0.62  
% 1.82/0.62  % (5095)Memory used [KB]: 6396
% 1.82/0.62  % (5095)Time elapsed: 0.202 s
% 1.82/0.62  % (5095)------------------------------
% 1.82/0.62  % (5095)------------------------------
% 1.82/0.63  % (5090)Success in time 0.257 s
%------------------------------------------------------------------------------
