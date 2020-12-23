%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 114 expanded)
%              Number of leaves         :   14 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :  229 ( 417 expanded)
%              Number of equality atoms :   64 ( 135 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f602,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f59,f67,f85,f117,f590,f594,f601])).

fof(f601,plain,(
    ~ spl7_12 ),
    inference(avatar_contradiction_clause,[],[f595])).

fof(f595,plain,
    ( $false
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f17,f589])).

fof(f589,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f587])).

fof(f587,plain,
    ( spl7_12
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f17,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( k1_relat_1(X2) = X0
                    & k1_relat_1(X1) = X0 )
                 => X1 = X2 ) ) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( k1_relat_1(X2) = X0
                  & k1_relat_1(X1) = X0 )
               => X1 = X2 ) ) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).

fof(f594,plain,(
    ~ spl7_11 ),
    inference(avatar_contradiction_clause,[],[f592])).

fof(f592,plain,
    ( $false
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f33,f585])).

fof(f585,plain,
    ( ! [X0] : ~ v1_relat_1(X0)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f584])).

fof(f584,plain,
    ( spl7_11
  <=> ! [X0] : ~ v1_relat_1(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f33,plain,(
    ! [X0,X1] : v1_relat_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f590,plain,
    ( spl7_11
    | spl7_12
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f485,f80,f587,f584])).

fof(f80,plain,
    ( spl7_5
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f485,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK0
        | ~ v1_relat_1(X0) )
    | ~ spl7_5 ),
    inference(duplicate_literal_removal,[],[f462])).

fof(f462,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK0
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl7_5 ),
    inference(superposition,[],[f417,f435])).

fof(f435,plain,
    ( ! [X63] :
        ( sK0 = k9_relat_1(X63,sK0)
        | ~ v1_relat_1(X63) )
    | ~ spl7_5 ),
    inference(resolution,[],[f326,f81])).

fof(f81,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f326,plain,
    ( ! [X76,X77] :
        ( r2_hidden(sK1(X76,sK0,X77),X77)
        | ~ v1_relat_1(X76)
        | k9_relat_1(X76,sK0) = X77 )
    | ~ spl7_5 ),
    inference(resolution,[],[f22,f81])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2)
      | k9_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

fof(f417,plain,
    ( ! [X12] :
        ( k1_xboole_0 = k9_relat_1(X12,sK0)
        | ~ v1_relat_1(X12) )
    | ~ spl7_5 ),
    inference(resolution,[],[f326,f164])).

fof(f164,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f162,f19])).

fof(f19,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f162,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(resolution,[],[f30,f18])).

fof(f18,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f117,plain,(
    ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f90])).

fof(f90,plain,
    ( $false
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f17,f88])).

fof(f88,plain,
    ( ! [X0] : k1_xboole_0 = X0
    | ~ spl7_6 ),
    inference(resolution,[],[f86,f33])).

fof(f86,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK6(sK0,X0))
        | k1_xboole_0 = X0 )
    | ~ spl7_6 ),
    inference(resolution,[],[f84,f34])).

fof(f34,plain,(
    ! [X0,X1] : v1_funct_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f84,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK6(sK0,X1))
        | k1_xboole_0 = X1
        | ~ v1_relat_1(sK6(sK0,X1)) )
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl7_6
  <=> ! [X1] :
        ( k1_xboole_0 = X1
        | ~ v1_funct_1(sK6(sK0,X1))
        | ~ v1_relat_1(sK6(sK0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f85,plain,
    ( spl7_5
    | spl7_6
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f76,f65,f83,f80])).

fof(f65,plain,
    ( spl7_4
  <=> ! [X1,X0] :
        ( ~ v1_funct_1(sK6(X0,X1))
        | sK6(X0,X1) = sK4(sK0)
        | ~ v1_relat_1(sK6(X0,X1))
        | sK0 != X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f76,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X1
        | ~ r2_hidden(X0,sK0)
        | ~ v1_relat_1(sK6(sK0,X1))
        | ~ v1_funct_1(sK6(sK0,X1)) )
    | ~ spl7_4 ),
    inference(duplicate_literal_removal,[],[f75])).

fof(f75,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X1
        | ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK0)
        | ~ v1_relat_1(sK6(sK0,X1))
        | ~ v1_funct_1(sK6(sK0,X1)) )
    | ~ spl7_4 ),
    inference(superposition,[],[f26,f69])).

fof(f69,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(sK4(sK0),X1) = X0
        | ~ r2_hidden(X1,sK0)
        | ~ v1_relat_1(sK6(sK0,X0))
        | ~ v1_funct_1(sK6(sK0,X0)) )
    | ~ spl7_4 ),
    inference(superposition,[],[f32,f68])).

fof(f68,plain,
    ( ! [X0] :
        ( sK4(sK0) = sK6(sK0,X0)
        | ~ v1_relat_1(sK6(sK0,X0))
        | ~ v1_funct_1(sK6(sK0,X0)) )
    | ~ spl7_4 ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,
    ( ! [X0,X1] :
        ( sK0 != X0
        | sK6(X0,X1) = sK4(sK0)
        | ~ v1_relat_1(sK6(X0,X1))
        | ~ v1_funct_1(sK6(X0,X1)) )
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | k1_funct_1(sK6(X0,X1),X3) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f26,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | k1_xboole_0 = k1_funct_1(sK4(X0),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f67,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | spl7_4 ),
    inference(avatar_split_clause,[],[f63,f65,f49,f45])).

fof(f45,plain,
    ( spl7_1
  <=> v1_funct_1(sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f49,plain,
    ( spl7_2
  <=> v1_relat_1(sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(sK6(X0,X1))
      | ~ v1_relat_1(sK4(sK0))
      | ~ v1_funct_1(sK4(sK0))
      | sK0 != X0
      | ~ v1_relat_1(sK6(X0,X1))
      | sK6(X0,X1) = sK4(sK0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X4,X2,X3] :
      ( sK0 != X4
      | ~ v1_funct_1(sK6(X2,X3))
      | ~ v1_relat_1(sK4(X4))
      | ~ v1_funct_1(sK4(X4))
      | sK0 != X2
      | ~ v1_relat_1(sK6(X2,X3))
      | sK6(X2,X3) = sK4(X4) ) ),
    inference(superposition,[],[f39,f35])).

fof(f35,plain,(
    ! [X0,X1] : k1_relat_1(sK6(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != sK0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(sK4(X0))
      | ~ v1_funct_1(sK4(X0))
      | sK0 != X0
      | ~ v1_relat_1(X1)
      | sK4(X0) = X1 ) ),
    inference(superposition,[],[f16,f29])).

fof(f29,plain,(
    ! [X0] : k1_relat_1(sK4(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f16,plain,(
    ! [X2,X1] :
      ( k1_relat_1(X2) != sK0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X1) != sK0
      | ~ v1_relat_1(X1)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f59,plain,(
    spl7_2 ),
    inference(avatar_contradiction_clause,[],[f58])).

fof(f58,plain,
    ( $false
    | spl7_2 ),
    inference(resolution,[],[f51,f27])).

fof(f27,plain,(
    ! [X0] : v1_relat_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f51,plain,
    ( ~ v1_relat_1(sK4(sK0))
    | spl7_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f57,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f56])).

fof(f56,plain,
    ( $false
    | spl7_1 ),
    inference(resolution,[],[f47,f28])).

fof(f28,plain,(
    ! [X0] : v1_funct_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f47,plain,
    ( ~ v1_funct_1(sK4(sK0))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:43:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.47  % (18616)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.48  % (18613)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.48  % (18620)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.48  % (18613)Refutation not found, incomplete strategy% (18613)------------------------------
% 0.20/0.48  % (18613)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (18613)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (18613)Memory used [KB]: 10490
% 0.20/0.48  % (18613)Time elapsed: 0.059 s
% 0.20/0.48  % (18613)------------------------------
% 0.20/0.48  % (18613)------------------------------
% 0.20/0.49  % (18638)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.50  % (18619)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.50  % (18630)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.50  % (18620)Refutation not found, incomplete strategy% (18620)------------------------------
% 0.20/0.50  % (18620)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (18620)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (18620)Memory used [KB]: 2046
% 0.20/0.50  % (18620)Time elapsed: 0.068 s
% 0.20/0.50  % (18620)------------------------------
% 0.20/0.50  % (18620)------------------------------
% 0.20/0.50  % (18619)Refutation not found, incomplete strategy% (18619)------------------------------
% 0.20/0.50  % (18619)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (18619)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (18619)Memory used [KB]: 10618
% 0.20/0.50  % (18619)Time elapsed: 0.065 s
% 0.20/0.50  % (18619)------------------------------
% 0.20/0.50  % (18619)------------------------------
% 0.20/0.51  % (18623)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.51  % (18633)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.52  % (18628)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.52  % (18618)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.52  % (18634)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.52  % (18633)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f602,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f57,f59,f67,f85,f117,f590,f594,f601])).
% 0.20/0.52  fof(f601,plain,(
% 0.20/0.52    ~spl7_12),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f595])).
% 0.20/0.52  fof(f595,plain,(
% 0.20/0.52    $false | ~spl7_12),
% 0.20/0.52    inference(subsumption_resolution,[],[f17,f589])).
% 0.20/0.52  fof(f589,plain,(
% 0.20/0.52    k1_xboole_0 = sK0 | ~spl7_12),
% 0.20/0.52    inference(avatar_component_clause,[],[f587])).
% 0.20/0.52  fof(f587,plain,(
% 0.20/0.52    spl7_12 <=> k1_xboole_0 = sK0),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    k1_xboole_0 != sK0),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.52    inference(flattening,[],[f10])).
% 0.20/0.52  fof(f10,plain,(
% 0.20/0.52    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,negated_conjecture,(
% 0.20/0.52    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 0.20/0.52    inference(negated_conjecture,[],[f7])).
% 0.20/0.52  fof(f7,conjecture,(
% 0.20/0.52    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).
% 0.20/0.52  fof(f594,plain,(
% 0.20/0.52    ~spl7_11),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f592])).
% 0.20/0.52  fof(f592,plain,(
% 0.20/0.52    $false | ~spl7_11),
% 0.20/0.52    inference(subsumption_resolution,[],[f33,f585])).
% 0.20/0.52  fof(f585,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_relat_1(X0)) ) | ~spl7_11),
% 0.20/0.52    inference(avatar_component_clause,[],[f584])).
% 0.20/0.52  fof(f584,plain,(
% 0.20/0.52    spl7_11 <=> ! [X0] : ~v1_relat_1(X0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ( ! [X0,X1] : (v1_relat_1(sK6(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 0.20/0.52  fof(f590,plain,(
% 0.20/0.52    spl7_11 | spl7_12 | ~spl7_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f485,f80,f587,f584])).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    spl7_5 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.52  fof(f485,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = sK0 | ~v1_relat_1(X0)) ) | ~spl7_5),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f462])).
% 0.20/0.52  fof(f462,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = sK0 | ~v1_relat_1(X0) | ~v1_relat_1(X0)) ) | ~spl7_5),
% 0.20/0.52    inference(superposition,[],[f417,f435])).
% 0.20/0.52  fof(f435,plain,(
% 0.20/0.52    ( ! [X63] : (sK0 = k9_relat_1(X63,sK0) | ~v1_relat_1(X63)) ) | ~spl7_5),
% 0.20/0.52    inference(resolution,[],[f326,f81])).
% 0.20/0.52  fof(f81,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl7_5),
% 0.20/0.52    inference(avatar_component_clause,[],[f80])).
% 0.20/0.52  fof(f326,plain,(
% 0.20/0.52    ( ! [X76,X77] : (r2_hidden(sK1(X76,sK0,X77),X77) | ~v1_relat_1(X76) | k9_relat_1(X76,sK0) = X77) ) | ~spl7_5),
% 0.20/0.52    inference(resolution,[],[f22,f81])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2) | k9_relat_1(X0,X1) = X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).
% 0.20/0.52  fof(f417,plain,(
% 0.20/0.52    ( ! [X12] : (k1_xboole_0 = k9_relat_1(X12,sK0) | ~v1_relat_1(X12)) ) | ~spl7_5),
% 0.20/0.52    inference(resolution,[],[f326,f164])).
% 0.20/0.52  fof(f164,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.52    inference(forward_demodulation,[],[f162,f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.52  fof(f162,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0))) )),
% 0.20/0.52    inference(resolution,[],[f30,f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,plain,(
% 0.20/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.52    inference(rectify,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.20/0.52  fof(f117,plain,(
% 0.20/0.52    ~spl7_6),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f90])).
% 0.20/0.52  fof(f90,plain,(
% 0.20/0.52    $false | ~spl7_6),
% 0.20/0.52    inference(subsumption_resolution,[],[f17,f88])).
% 0.20/0.52  fof(f88,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = X0) ) | ~spl7_6),
% 0.20/0.52    inference(resolution,[],[f86,f33])).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_relat_1(sK6(sK0,X0)) | k1_xboole_0 = X0) ) | ~spl7_6),
% 0.20/0.52    inference(resolution,[],[f84,f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ( ! [X0,X1] : (v1_funct_1(sK6(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f84,plain,(
% 0.20/0.52    ( ! [X1] : (~v1_funct_1(sK6(sK0,X1)) | k1_xboole_0 = X1 | ~v1_relat_1(sK6(sK0,X1))) ) | ~spl7_6),
% 0.20/0.52    inference(avatar_component_clause,[],[f83])).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    spl7_6 <=> ! [X1] : (k1_xboole_0 = X1 | ~v1_funct_1(sK6(sK0,X1)) | ~v1_relat_1(sK6(sK0,X1)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.20/0.52  fof(f85,plain,(
% 0.20/0.52    spl7_5 | spl7_6 | ~spl7_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f76,f65,f83,f80])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    spl7_4 <=> ! [X1,X0] : (~v1_funct_1(sK6(X0,X1)) | sK6(X0,X1) = sK4(sK0) | ~v1_relat_1(sK6(X0,X1)) | sK0 != X0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_xboole_0 = X1 | ~r2_hidden(X0,sK0) | ~v1_relat_1(sK6(sK0,X1)) | ~v1_funct_1(sK6(sK0,X1))) ) | ~spl7_4),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f75])).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_xboole_0 = X1 | ~r2_hidden(X0,sK0) | ~r2_hidden(X0,sK0) | ~v1_relat_1(sK6(sK0,X1)) | ~v1_funct_1(sK6(sK0,X1))) ) | ~spl7_4),
% 0.20/0.52    inference(superposition,[],[f26,f69])).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_funct_1(sK4(sK0),X1) = X0 | ~r2_hidden(X1,sK0) | ~v1_relat_1(sK6(sK0,X0)) | ~v1_funct_1(sK6(sK0,X0))) ) | ~spl7_4),
% 0.20/0.52    inference(superposition,[],[f32,f68])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    ( ! [X0] : (sK4(sK0) = sK6(sK0,X0) | ~v1_relat_1(sK6(sK0,X0)) | ~v1_funct_1(sK6(sK0,X0))) ) | ~spl7_4),
% 0.20/0.52    inference(equality_resolution,[],[f66])).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    ( ! [X0,X1] : (sK0 != X0 | sK6(X0,X1) = sK4(sK0) | ~v1_relat_1(sK6(X0,X1)) | ~v1_funct_1(sK6(X0,X1))) ) | ~spl7_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f65])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | k1_funct_1(sK6(X0,X1),X3) = X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ( ! [X2,X0] : (~r2_hidden(X2,X0) | k1_xboole_0 = k1_funct_1(sK4(X0),X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    ~spl7_1 | ~spl7_2 | spl7_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f63,f65,f49,f45])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    spl7_1 <=> v1_funct_1(sK4(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    spl7_2 <=> v1_relat_1(sK4(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_funct_1(sK6(X0,X1)) | ~v1_relat_1(sK4(sK0)) | ~v1_funct_1(sK4(sK0)) | sK0 != X0 | ~v1_relat_1(sK6(X0,X1)) | sK6(X0,X1) = sK4(sK0)) )),
% 0.20/0.52    inference(equality_resolution,[],[f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ( ! [X4,X2,X3] : (sK0 != X4 | ~v1_funct_1(sK6(X2,X3)) | ~v1_relat_1(sK4(X4)) | ~v1_funct_1(sK4(X4)) | sK0 != X2 | ~v1_relat_1(sK6(X2,X3)) | sK6(X2,X3) = sK4(X4)) )),
% 0.20/0.52    inference(superposition,[],[f39,f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_relat_1(sK6(X0,X1)) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_relat_1(X1) != sK0 | ~v1_funct_1(X1) | ~v1_relat_1(sK4(X0)) | ~v1_funct_1(sK4(X0)) | sK0 != X0 | ~v1_relat_1(X1) | sK4(X0) = X1) )),
% 0.20/0.52    inference(superposition,[],[f16,f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ( ! [X0] : (k1_relat_1(sK4(X0)) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ( ! [X2,X1] : (k1_relat_1(X2) != sK0 | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_relat_1(X1) != sK0 | ~v1_relat_1(X1) | X1 = X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    spl7_2),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f58])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    $false | spl7_2),
% 0.20/0.52    inference(resolution,[],[f51,f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ( ! [X0] : (v1_relat_1(sK4(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ~v1_relat_1(sK4(sK0)) | spl7_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f49])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    spl7_1),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f56])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    $false | spl7_1),
% 0.20/0.52    inference(resolution,[],[f47,f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ( ! [X0] : (v1_funct_1(sK4(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ~v1_funct_1(sK4(sK0)) | spl7_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f45])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (18633)------------------------------
% 0.20/0.52  % (18633)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (18633)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (18633)Memory used [KB]: 11129
% 0.20/0.52  % (18633)Time elapsed: 0.090 s
% 0.20/0.52  % (18633)------------------------------
% 0.20/0.52  % (18633)------------------------------
% 0.20/0.52  % (18612)Success in time 0.158 s
%------------------------------------------------------------------------------
