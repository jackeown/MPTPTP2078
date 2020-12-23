%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0479+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:03 EST 2020

% Result     : Theorem 0.15s
% Output     : Refutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 136 expanded)
%              Number of leaves         :    8 (  36 expanded)
%              Depth                    :   12
%              Number of atoms          :  209 ( 440 expanded)
%              Number of equality atoms :   18 (  33 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f96,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f50,f79,f95])).

fof(f95,plain,(
    ~ spl10_1 ),
    inference(avatar_contradiction_clause,[],[f94])).

fof(f94,plain,
    ( $false
    | ~ spl10_1 ),
    inference(global_subsumption,[],[f12,f40,f91,f87])).

fof(f87,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl10_1 ),
    inference(resolution,[],[f85,f54])).

fof(f54,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),k6_relat_1(X0))
      | r2_hidden(X2,X0) ) ),
    inference(subsumption_resolution,[],[f36,f16])).

fof(f16,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f36,plain,(
    ! [X2,X0,X3] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | r2_hidden(X2,X0)
      | ~ r2_hidden(k4_tarski(X2,X3),k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | r2_hidden(X2,X0)
      | ~ r2_hidden(k4_tarski(X2,X3),X1)
      | k6_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).

fof(f85,plain,
    ( r2_hidden(k4_tarski(sK0,sK6(k6_relat_1(sK2),sK3,sK0,sK1)),k6_relat_1(sK2))
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f84,f16])).

fof(f84,plain,
    ( r2_hidden(k4_tarski(sK0,sK6(k6_relat_1(sK2),sK3,sK0,sK1)),k6_relat_1(sK2))
    | ~ v1_relat_1(k6_relat_1(sK2))
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f81,f15])).

fof(f15,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <~> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) )
      & v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
        <=> ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X0,X2) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_relat_1)).

fof(f81,plain,
    ( ~ v1_relat_1(sK3)
    | r2_hidden(k4_tarski(sK0,sK6(k6_relat_1(sK2),sK3,sK0,sK1)),k6_relat_1(sK2))
    | ~ v1_relat_1(k6_relat_1(sK2))
    | ~ spl10_1 ),
    inference(resolution,[],[f40,f56])).

fof(f56,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | r2_hidden(k4_tarski(X3,sK6(X0,X1,X3,X4)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f32,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f32,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X3,sK6(X0,X1,X3,X4)),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X3,sK6(X0,X1,X3,X4)),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

fof(f91,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK3)
    | ~ spl10_1 ),
    inference(backward_demodulation,[],[f83,f88])).

fof(f88,plain,
    ( sK0 = sK6(k6_relat_1(sK2),sK3,sK0,sK1)
    | ~ spl10_1 ),
    inference(resolution,[],[f85,f53])).

fof(f53,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),k6_relat_1(X0))
      | X2 = X3 ) ),
    inference(subsumption_resolution,[],[f35,f16])).

fof(f35,plain,(
    ! [X2,X0,X3] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | X2 = X3
      | ~ r2_hidden(k4_tarski(X2,X3),k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | X2 = X3
      | ~ r2_hidden(k4_tarski(X2,X3),X1)
      | k6_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f83,plain,
    ( r2_hidden(k4_tarski(sK6(k6_relat_1(sK2),sK3,sK0,sK1),sK1),sK3)
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f82,f16])).

fof(f82,plain,
    ( r2_hidden(k4_tarski(sK6(k6_relat_1(sK2),sK3,sK0,sK1),sK1),sK3)
    | ~ v1_relat_1(k6_relat_1(sK2))
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f80,f15])).

fof(f80,plain,
    ( ~ v1_relat_1(sK3)
    | r2_hidden(k4_tarski(sK6(k6_relat_1(sK2),sK3,sK0,sK1),sK1),sK3)
    | ~ v1_relat_1(k6_relat_1(sK2))
    | ~ spl10_1 ),
    inference(resolution,[],[f40,f57])).

fof(f57,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | r2_hidden(k4_tarski(sK6(X0,X1,X3,X4),X4),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f31,f29])).

fof(f31,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(sK6(X0,X1,X3,X4),X4),X1)
      | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK6(X0,X1,X3,X4),X4),X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f40,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(k6_relat_1(sK2),sK3))
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl10_1
  <=> r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(k6_relat_1(sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

% (19041)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
fof(f12,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(k4_tarski(sK0,sK1),sK3)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(k6_relat_1(sK2),sK3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f79,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(avatar_contradiction_clause,[],[f78])).

fof(f78,plain,
    ( $false
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f77,f49])).

fof(f49,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl10_3
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f77,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl10_1
    | ~ spl10_2 ),
    inference(resolution,[],[f74,f52])).

fof(f52,plain,(
    ! [X0,X3] :
      ( r2_hidden(k4_tarski(X3,X3),k6_relat_1(X0))
      | ~ r2_hidden(X3,X0) ) ),
    inference(subsumption_resolution,[],[f34,f16])).

fof(f34,plain,(
    ! [X0,X3] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | ~ r2_hidden(X3,X0)
      | r2_hidden(k4_tarski(X3,X3),k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(k4_tarski(X3,X3),X1)
      | k6_relat_1(X0) != X1 ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X2,X0)
      | X2 != X3
      | r2_hidden(k4_tarski(X2,X3),X1)
      | k6_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f74,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK0),k6_relat_1(sK2))
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f69,f16])).

fof(f69,plain,
    ( ~ v1_relat_1(k6_relat_1(sK2))
    | ~ r2_hidden(k4_tarski(sK0,sK0),k6_relat_1(sK2))
    | spl10_1
    | ~ spl10_2 ),
    inference(resolution,[],[f67,f39])).

fof(f39,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(k6_relat_1(sK2),sK3))
    | spl10_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f67,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,sK1),k5_relat_1(X1,sK3))
        | ~ v1_relat_1(X1)
        | ~ r2_hidden(k4_tarski(X0,sK0),X1) )
    | ~ spl10_2 ),
    inference(resolution,[],[f64,f44])).

fof(f44,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK3)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl10_2
  <=> r2_hidden(k4_tarski(sK0,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),sK3)
      | ~ r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X1,X3),k5_relat_1(X0,sK3)) ) ),
    inference(resolution,[],[f58,f15])).

fof(f58,plain,(
    ! [X4,X0,X5,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X5),X0)
      | ~ r2_hidden(k4_tarski(X5,X4),X1)
      | r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f30,f29])).

fof(f30,plain,(
    ! [X4,X0,X5,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X3,X5),X0)
      | ~ r2_hidden(k4_tarski(X5,X4),X1)
      | r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X3,X5),X0)
      | ~ r2_hidden(k4_tarski(X5,X4),X1)
      | r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f50,plain,
    ( spl10_1
    | spl10_3 ),
    inference(avatar_split_clause,[],[f13,f47,f38])).

fof(f13,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(k6_relat_1(sK2),sK3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f45,plain,
    ( spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f14,f42,f38])).

fof(f14,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK3)
    | r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(k6_relat_1(sK2),sK3)) ),
    inference(cnf_transformation,[],[f7])).

%------------------------------------------------------------------------------
