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
% DateTime   : Thu Dec  3 12:52:48 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 125 expanded)
%              Number of leaves         :   19 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :  209 ( 347 expanded)
%              Number of equality atoms :   57 (  97 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f204,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f43,f48,f57,f64,f71,f96,f102,f148,f152,f202,f203])).

fof(f203,plain,
    ( k2_funct_1(sK0) != k4_relat_1(sK0)
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f202,plain,
    ( spl1_11
    | ~ spl1_17
    | ~ spl1_3
    | ~ spl1_6
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f201,f68,f61,f45,f145,f99])).

fof(f99,plain,
    ( spl1_11
  <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f145,plain,
    ( spl1_17
  <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).

fof(f45,plain,
    ( spl1_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f61,plain,
    ( spl1_6
  <=> k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f68,plain,
    ( spl1_7
  <=> k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f201,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | ~ spl1_3
    | ~ spl1_6
    | ~ spl1_7 ),
    inference(forward_demodulation,[],[f200,f63])).

fof(f63,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f61])).

fof(f200,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | ~ r1_tarski(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(sK0))
    | ~ spl1_3
    | ~ spl1_7 ),
    inference(forward_demodulation,[],[f198,f70])).

fof(f70,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f68])).

fof(f198,plain,
    ( k2_relat_1(k4_relat_1(sK0)) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | ~ r1_tarski(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(sK0))
    | ~ spl1_3 ),
    inference(resolution,[],[f159,f47])).

fof(f47,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f159,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k2_relat_1(k4_relat_1(X0)) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(X0)))
        | ~ r1_tarski(k1_relat_1(k4_relat_1(X0)),k2_relat_1(sK0)) )
    | ~ spl1_3 ),
    inference(resolution,[],[f153,f23])).

fof(f23,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f153,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(sK0))
        | k2_relat_1(X0) = k2_relat_1(k5_relat_1(sK0,X0)) )
    | ~ spl1_3 ),
    inference(resolution,[],[f27,f47])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

fof(f152,plain,(
    spl1_17 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | spl1_17 ),
    inference(unit_resulting_resolution,[],[f32,f147])).

fof(f147,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | spl1_17 ),
    inference(avatar_component_clause,[],[f145])).

fof(f32,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
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

fof(f148,plain,
    ( spl1_16
    | ~ spl1_17
    | ~ spl1_3
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f139,f61,f45,f145,f141])).

fof(f141,plain,
    ( spl1_16
  <=> k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).

fof(f139,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | ~ spl1_3
    | ~ spl1_6 ),
    inference(forward_demodulation,[],[f137,f63])).

fof(f137,plain,
    ( k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | ~ r1_tarski(k2_relat_1(sK0),k1_relat_1(k4_relat_1(sK0)))
    | ~ spl1_3 ),
    inference(resolution,[],[f136,f47])).

fof(f136,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(X0)))
        | ~ r1_tarski(k2_relat_1(sK0),k1_relat_1(k4_relat_1(X0))) )
    | ~ spl1_3 ),
    inference(resolution,[],[f121,f23])).

fof(f121,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ r1_tarski(k2_relat_1(sK0),k1_relat_1(X0))
        | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,X0)) )
    | ~ spl1_3 ),
    inference(resolution,[],[f26,f47])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(f102,plain,
    ( ~ spl1_11
    | spl1_4
    | ~ spl1_10 ),
    inference(avatar_split_clause,[],[f97,f93,f50,f99])).

fof(f50,plain,
    ( spl1_4
  <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f93,plain,
    ( spl1_10
  <=> k2_funct_1(sK0) = k4_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f97,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | spl1_4
    | ~ spl1_10 ),
    inference(backward_demodulation,[],[f52,f95])).

fof(f95,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f93])).

fof(f52,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | spl1_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f96,plain,
    ( spl1_10
    | ~ spl1_3
    | ~ spl1_2
    | ~ spl1_1 ),
    inference(avatar_split_clause,[],[f91,f35,f40,f45,f93])).

fof(f40,plain,
    ( spl1_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f35,plain,
    ( spl1_1
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f91,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl1_1 ),
    inference(resolution,[],[f28,f37])).

fof(f37,plain,
    ( v2_funct_1(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f71,plain,
    ( spl1_7
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f65,f45,f68])).

fof(f65,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))
    | ~ spl1_3 ),
    inference(resolution,[],[f25,f47])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f64,plain,
    ( spl1_6
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f58,f45,f61])).

fof(f58,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))
    | ~ spl1_3 ),
    inference(resolution,[],[f24,f47])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f57,plain,
    ( ~ spl1_4
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f19,f54,f50])).

fof(f54,plain,
    ( spl1_5
  <=> k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f19,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
            & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

fof(f48,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f20,f45])).

fof(f20,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f43,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f21,f40])).

fof(f21,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f38,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f22,f35])).

fof(f22,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:59:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (22312)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.47  % (22320)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.47  % (22320)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % (22305)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f204,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f38,f43,f48,f57,f64,f71,f96,f102,f148,f152,f202,f203])).
% 0.22/0.48  fof(f203,plain,(
% 0.22/0.48    k2_funct_1(sK0) != k4_relat_1(sK0) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.22/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.48  fof(f202,plain,(
% 0.22/0.48    spl1_11 | ~spl1_17 | ~spl1_3 | ~spl1_6 | ~spl1_7),
% 0.22/0.48    inference(avatar_split_clause,[],[f201,f68,f61,f45,f145,f99])).
% 0.22/0.48  fof(f99,plain,(
% 0.22/0.48    spl1_11 <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.22/0.48  fof(f145,plain,(
% 0.22/0.48    spl1_17 <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    spl1_3 <=> v1_relat_1(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    spl1_6 <=> k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    spl1_7 <=> k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.22/0.48  fof(f201,plain,(
% 0.22/0.48    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | (~spl1_3 | ~spl1_6 | ~spl1_7)),
% 0.22/0.48    inference(forward_demodulation,[],[f200,f63])).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) | ~spl1_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f61])).
% 0.22/0.48  fof(f200,plain,(
% 0.22/0.48    k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | ~r1_tarski(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(sK0)) | (~spl1_3 | ~spl1_7)),
% 0.22/0.48    inference(forward_demodulation,[],[f198,f70])).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) | ~spl1_7),
% 0.22/0.48    inference(avatar_component_clause,[],[f68])).
% 0.22/0.48  fof(f198,plain,(
% 0.22/0.48    k2_relat_1(k4_relat_1(sK0)) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | ~r1_tarski(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(sK0)) | ~spl1_3),
% 0.22/0.48    inference(resolution,[],[f159,f47])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    v1_relat_1(sK0) | ~spl1_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f45])).
% 0.22/0.48  fof(f159,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k4_relat_1(X0)) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(X0))) | ~r1_tarski(k1_relat_1(k4_relat_1(X0)),k2_relat_1(sK0))) ) | ~spl1_3),
% 0.22/0.48    inference(resolution,[],[f153,f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.22/0.48  fof(f153,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(sK0)) | k2_relat_1(X0) = k2_relat_1(k5_relat_1(sK0,X0))) ) | ~spl1_3),
% 0.22/0.48    inference(resolution,[],[f27,f47])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(flattening,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).
% 0.22/0.48  fof(f152,plain,(
% 0.22/0.48    spl1_17),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f149])).
% 0.22/0.48  fof(f149,plain,(
% 0.22/0.48    $false | spl1_17),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f32,f147])).
% 0.22/0.48  fof(f147,plain,(
% 0.22/0.48    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | spl1_17),
% 0.22/0.48    inference(avatar_component_clause,[],[f145])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.48    inference(equality_resolution,[],[f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.48  fof(f148,plain,(
% 0.22/0.48    spl1_16 | ~spl1_17 | ~spl1_3 | ~spl1_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f139,f61,f45,f145,f141])).
% 0.22/0.48  fof(f141,plain,(
% 0.22/0.48    spl1_16 <=> k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).
% 0.22/0.48  fof(f139,plain,(
% 0.22/0.48    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | (~spl1_3 | ~spl1_6)),
% 0.22/0.48    inference(forward_demodulation,[],[f137,f63])).
% 0.22/0.48  fof(f137,plain,(
% 0.22/0.48    k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | ~r1_tarski(k2_relat_1(sK0),k1_relat_1(k4_relat_1(sK0))) | ~spl1_3),
% 0.22/0.48    inference(resolution,[],[f136,f47])).
% 0.22/0.48  fof(f136,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(X0))) | ~r1_tarski(k2_relat_1(sK0),k1_relat_1(k4_relat_1(X0)))) ) | ~spl1_3),
% 0.22/0.48    inference(resolution,[],[f121,f23])).
% 0.22/0.48  fof(f121,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(sK0),k1_relat_1(X0)) | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,X0))) ) | ~spl1_3),
% 0.22/0.48    inference(resolution,[],[f26,f47])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(flattening,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
% 0.22/0.48  fof(f102,plain,(
% 0.22/0.48    ~spl1_11 | spl1_4 | ~spl1_10),
% 0.22/0.48    inference(avatar_split_clause,[],[f97,f93,f50,f99])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    spl1_4 <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.22/0.48  fof(f93,plain,(
% 0.22/0.48    spl1_10 <=> k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.22/0.48  fof(f97,plain,(
% 0.22/0.48    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | (spl1_4 | ~spl1_10)),
% 0.22/0.48    inference(backward_demodulation,[],[f52,f95])).
% 0.22/0.48  fof(f95,plain,(
% 0.22/0.48    k2_funct_1(sK0) = k4_relat_1(sK0) | ~spl1_10),
% 0.22/0.48    inference(avatar_component_clause,[],[f93])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | spl1_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f50])).
% 0.22/0.48  fof(f96,plain,(
% 0.22/0.48    spl1_10 | ~spl1_3 | ~spl1_2 | ~spl1_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f91,f35,f40,f45,f93])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    spl1_2 <=> v1_funct_1(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    spl1_1 <=> v2_funct_1(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.48  fof(f91,plain,(
% 0.22/0.48    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k2_funct_1(sK0) = k4_relat_1(sK0) | ~spl1_1),
% 0.22/0.48    inference(resolution,[],[f28,f37])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    v2_funct_1(sK0) | ~spl1_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f35])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(flattening,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    spl1_7 | ~spl1_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f65,f45,f68])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) | ~spl1_3),
% 0.22/0.48    inference(resolution,[],[f25,f47])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    spl1_6 | ~spl1_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f58,f45,f61])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) | ~spl1_3),
% 0.22/0.48    inference(resolution,[],[f24,f47])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f57,plain,(
% 0.22/0.48    ~spl1_4 | ~spl1_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f19,f54,f50])).
% 0.22/0.48  fof(f54,plain,(
% 0.22/0.48    spl1_5 <=> k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.48    inference(flattening,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ? [X0] : (((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,negated_conjecture,(
% 0.22/0.48    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.22/0.48    inference(negated_conjecture,[],[f7])).
% 0.22/0.48  fof(f7,conjecture,(
% 0.22/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    spl1_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f20,f45])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    v1_relat_1(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    spl1_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f21,f40])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    v1_funct_1(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    spl1_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f22,f35])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    v2_funct_1(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (22320)------------------------------
% 0.22/0.48  % (22320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (22320)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (22320)Memory used [KB]: 6268
% 0.22/0.48  % (22320)Time elapsed: 0.062 s
% 0.22/0.48  % (22320)------------------------------
% 0.22/0.48  % (22320)------------------------------
% 0.22/0.48  % (22304)Success in time 0.116 s
%------------------------------------------------------------------------------
