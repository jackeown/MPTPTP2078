%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0591+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:39 EST 2020

% Result     : Theorem 2.83s
% Output     : Refutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   56 (  91 expanded)
%              Number of leaves         :   12 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :  132 ( 243 expanded)
%              Number of equality atoms :   38 ( 102 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (10775)lrs+1002_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:cond=fast:fde=none:gs=on:gsem=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence_8 on theBenchmark
fof(f5393,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4481,f5383,f5392])).

fof(f5392,plain,(
    spl161_2 ),
    inference(avatar_contradiction_clause,[],[f5391])).

fof(f5391,plain,
    ( $false
    | spl161_2 ),
    inference(subsumption_resolution,[],[f5385,f4522])).

fof(f4522,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(resolution,[],[f3623,f3529])).

fof(f3529,plain,(
    ~ sQ160_eqProxy(k1_xboole_0,sK3) ),
    inference(equality_proxy_replacement,[],[f1983,f3509])).

fof(f3509,plain,(
    ! [X1,X0] :
      ( sQ160_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ160_eqProxy])])).

fof(f1983,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f1539])).

fof(f1539,plain,
    ( ( sK4 != k2_relat_1(k2_zfmisc_1(sK3,sK4))
      | sK3 != k1_relat_1(k2_zfmisc_1(sK3,sK4)) )
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f869,f1538])).

fof(f1538,plain,
    ( ? [X0,X1] :
        ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) != X1
          | k1_relat_1(k2_zfmisc_1(X0,X1)) != X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ( sK4 != k2_relat_1(k2_zfmisc_1(sK3,sK4))
        | sK3 != k1_relat_1(k2_zfmisc_1(sK3,sK4)) )
      & k1_xboole_0 != sK4
      & k1_xboole_0 != sK3 ) ),
    introduced(choice_axiom,[])).

fof(f869,plain,(
    ? [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) != X1
        | k1_relat_1(k2_zfmisc_1(X0,X1)) != X0 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f786])).

fof(f786,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
              & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f785])).

fof(f785,conjecture,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

fof(f3623,plain,(
    ! [X0] :
      ( sQ160_eqProxy(k1_xboole_0,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f2170,f3509])).

fof(f2170,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f964])).

fof(f964,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f136])).

fof(f136,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f5385,plain,
    ( v1_xboole_0(sK3)
    | spl161_2 ),
    inference(resolution,[],[f5374,f4535])).

fof(f4535,plain,(
    ! [X6,X7] :
      ( r1_tarski(X6,k2_relat_1(k2_zfmisc_1(X7,X6)))
      | v1_xboole_0(X7) ) ),
    inference(subsumption_resolution,[],[f4533,f2220])).

fof(f2220,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f686])).

fof(f686,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f4533,plain,(
    ! [X6,X7] :
      ( r1_tarski(X6,k2_relat_1(k2_zfmisc_1(X7,X6)))
      | v1_xboole_0(X7)
      | ~ v1_relat_1(k2_zfmisc_1(X7,X6)) ) ),
    inference(resolution,[],[f2058,f2082])).

fof(f2082,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f900])).

fof(f900,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f789])).

fof(f789,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f2058,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
      | r1_tarski(X1,X3)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f880])).

fof(f880,plain,(
    ! [X0] :
      ( ! [X1,X2,X3] :
          ( r1_tarski(X1,X3)
          | ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            & ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f355])).

fof(f355,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1,X2,X3] :
          ( ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
         => r1_tarski(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_zfmisc_1)).

fof(f5374,plain,
    ( ~ r1_tarski(sK4,k2_relat_1(k2_zfmisc_1(sK3,sK4)))
    | spl161_2 ),
    inference(subsumption_resolution,[],[f5362,f2232])).

fof(f2232,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f784])).

fof(f784,axiom,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t194_relat_1)).

fof(f5362,plain,
    ( ~ r1_tarski(k2_relat_1(k2_zfmisc_1(sK3,sK4)),sK4)
    | ~ r1_tarski(sK4,k2_relat_1(k2_zfmisc_1(sK3,sK4)))
    | spl161_2 ),
    inference(resolution,[],[f3850,f4480])).

fof(f4480,plain,
    ( ~ sQ160_eqProxy(sK4,k2_relat_1(k2_zfmisc_1(sK3,sK4)))
    | spl161_2 ),
    inference(avatar_component_clause,[],[f4478])).

fof(f4478,plain,
    ( spl161_2
  <=> sQ160_eqProxy(sK4,k2_relat_1(k2_zfmisc_1(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl161_2])])).

fof(f3850,plain,(
    ! [X0,X1] :
      ( sQ160_eqProxy(X0,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f2597,f3509])).

fof(f2597,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1732])).

fof(f1732,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f1731])).

fof(f1731,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f5383,plain,(
    spl161_1 ),
    inference(avatar_contradiction_clause,[],[f5382])).

fof(f5382,plain,
    ( $false
    | spl161_1 ),
    inference(subsumption_resolution,[],[f5376,f4523])).

fof(f4523,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(resolution,[],[f3623,f3528])).

fof(f3528,plain,(
    ~ sQ160_eqProxy(k1_xboole_0,sK4) ),
    inference(equality_proxy_replacement,[],[f1984,f3509])).

fof(f1984,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f1539])).

fof(f5376,plain,
    ( v1_xboole_0(sK4)
    | spl161_1 ),
    inference(resolution,[],[f5373,f4540])).

fof(f4540,plain,(
    ! [X6,X7] :
      ( r1_tarski(X6,k1_relat_1(k2_zfmisc_1(X6,X7)))
      | v1_xboole_0(X7) ) ),
    inference(subsumption_resolution,[],[f4538,f2220])).

fof(f4538,plain,(
    ! [X6,X7] :
      ( r1_tarski(X6,k1_relat_1(k2_zfmisc_1(X6,X7)))
      | v1_xboole_0(X7)
      | ~ v1_relat_1(k2_zfmisc_1(X6,X7)) ) ),
    inference(resolution,[],[f2059,f2082])).

fof(f2059,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
      | r1_tarski(X1,X3)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f880])).

fof(f5373,plain,
    ( ~ r1_tarski(sK3,k1_relat_1(k2_zfmisc_1(sK3,sK4)))
    | spl161_1 ),
    inference(subsumption_resolution,[],[f5361,f2233])).

fof(f2233,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f783])).

fof(f783,axiom,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_relat_1)).

fof(f5361,plain,
    ( ~ r1_tarski(k1_relat_1(k2_zfmisc_1(sK3,sK4)),sK3)
    | ~ r1_tarski(sK3,k1_relat_1(k2_zfmisc_1(sK3,sK4)))
    | spl161_1 ),
    inference(resolution,[],[f3850,f4476])).

fof(f4476,plain,
    ( ~ sQ160_eqProxy(sK3,k1_relat_1(k2_zfmisc_1(sK3,sK4)))
    | spl161_1 ),
    inference(avatar_component_clause,[],[f4474])).

fof(f4474,plain,
    ( spl161_1
  <=> sQ160_eqProxy(sK3,k1_relat_1(k2_zfmisc_1(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl161_1])])).

fof(f4481,plain,
    ( ~ spl161_1
    | ~ spl161_2 ),
    inference(avatar_split_clause,[],[f3527,f4478,f4474])).

fof(f3527,plain,
    ( ~ sQ160_eqProxy(sK4,k2_relat_1(k2_zfmisc_1(sK3,sK4)))
    | ~ sQ160_eqProxy(sK3,k1_relat_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(equality_proxy_replacement,[],[f1985,f3509,f3509])).

fof(f1985,plain,
    ( sK4 != k2_relat_1(k2_zfmisc_1(sK3,sK4))
    | sK3 != k1_relat_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(cnf_transformation,[],[f1539])).
%------------------------------------------------------------------------------
