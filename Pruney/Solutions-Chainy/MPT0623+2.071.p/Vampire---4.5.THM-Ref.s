%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:12 EST 2020

% Result     : Theorem 0.80s
% Output     : Refutation 0.80s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 119 expanded)
%              Number of leaves         :   15 (  40 expanded)
%              Depth                    :   14
%              Number of atoms          :  214 ( 487 expanded)
%              Number of equality atoms :   89 ( 216 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f90,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f63,f70,f82,f89])).

fof(f89,plain,
    ( spl5_1
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | spl5_1
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f87,f43])).

fof(f43,plain,
    ( k1_xboole_0 != sK0
    | spl5_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl5_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f87,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_4 ),
    inference(resolution,[],[f83,f34])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f20])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f83,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl5_4 ),
    inference(resolution,[],[f69,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f69,plain,
    ( ! [X0] : ~ r1_tarski(k1_tarski(X0),sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl5_4
  <=> ! [X0] : ~ r1_tarski(k1_tarski(X0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f82,plain,(
    ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f81])).

fof(f81,plain,
    ( $false
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f80,f27])).

fof(f27,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f80,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f73,f79])).

fof(f79,plain,(
    k1_xboole_0 = k2_relat_1(sK4(k1_xboole_0)) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_relat_1(sK4(X0)) ) ),
    inference(subsumption_resolution,[],[f56,f35])).

fof(f35,plain,(
    ! [X0] : v1_relat_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X2] :
          ( np__1 = k1_funct_1(sK4(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK4(X0)) = X0
      & v1_funct_1(sK4(X0))
      & v1_relat_1(sK4(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_funct_1(X1,X2) = np__1
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( np__1 = k1_funct_1(sK4(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK4(X0)) = X0
        & v1_funct_1(sK4(X0))
        & v1_relat_1(sK4(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = np__1
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_funct_1(X1,X2) = np__1 )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

fof(f56,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_relat_1(sK4(X0))
      | ~ v1_relat_1(sK4(X0)) ) ),
    inference(superposition,[],[f28,f37])).

fof(f37,plain,(
    ! [X0] : k1_relat_1(sK4(X0)) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f73,plain,
    ( ~ r1_tarski(k2_relat_1(sK4(k1_xboole_0)),sK0)
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f51,f46])).

fof(f46,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f51,plain,(
    ~ r1_tarski(k2_relat_1(sK4(sK1)),sK0) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( sK1 != X0
      | ~ r1_tarski(k2_relat_1(sK4(X0)),sK0) ) ),
    inference(subsumption_resolution,[],[f49,f35])).

fof(f49,plain,(
    ! [X0] :
      ( sK1 != X0
      | ~ r1_tarski(k2_relat_1(sK4(X0)),sK0)
      | ~ v1_relat_1(sK4(X0)) ) ),
    inference(subsumption_resolution,[],[f48,f36])).

fof(f36,plain,(
    ! [X0] : v1_funct_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f48,plain,(
    ! [X0] :
      ( sK1 != X0
      | ~ r1_tarski(k2_relat_1(sK4(X0)),sK0)
      | ~ v1_funct_1(sK4(X0))
      | ~ v1_relat_1(sK4(X0)) ) ),
    inference(superposition,[],[f26,f37])).

fof(f26,plain,(
    ! [X2] :
      ( k1_relat_1(X2) != sK1
      | ~ r1_tarski(k2_relat_1(X2),sK0)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK0)
        | k1_relat_1(X2) != sK1
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ~ r1_tarski(k2_relat_1(X2),X0)
            | k1_relat_1(X2) != X1
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 != X0 ) )
   => ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),sK0)
          | k1_relat_1(X2) != sK1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = sK1
        | k1_xboole_0 != sK0 ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

fof(f70,plain,
    ( spl5_2
    | spl5_4
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f66,f61,f68,f45])).

fof(f61,plain,
    ( spl5_3
  <=> ! [X0] : ~ r1_tarski(k2_relat_1(sK2(sK1,X0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f66,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_tarski(X0),sK0)
        | k1_xboole_0 = sK1 )
    | ~ spl5_3 ),
    inference(superposition,[],[f62,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
          & k1_relat_1(sK2(X0,X1)) = X0
          & v1_funct_1(sK2(X0,X1))
          & v1_relat_1(sK2(X0,X1)) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
        & k1_relat_1(sK2(X0,X1)) = X0
        & v1_funct_1(sK2(X0,X1))
        & v1_relat_1(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).

fof(f62,plain,
    ( ! [X0] : ~ r1_tarski(k2_relat_1(sK2(sK1,X0)),sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f63,plain,
    ( spl5_2
    | spl5_3 ),
    inference(avatar_split_clause,[],[f59,f61,f45])).

fof(f59,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK2(sK1,X0)),sK0)
      | k1_xboole_0 = sK1 ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | ~ r1_tarski(k2_relat_1(sK2(X0,X1)),sK0)
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f54,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f54,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | ~ r1_tarski(k2_relat_1(sK2(X0,X1)),sK0)
      | ~ v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f53,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f53,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | ~ r1_tarski(k2_relat_1(sK2(X0,X1)),sK0)
      | ~ v1_funct_1(sK2(X0,X1))
      | ~ v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f26,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK2(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f25,f45,f42])).

fof(f25,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:42:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.36  ipcrm: permission denied for id (801046529)
% 0.20/0.36  ipcrm: permission denied for id (801079299)
% 0.20/0.37  ipcrm: permission denied for id (801144839)
% 0.20/0.38  ipcrm: permission denied for id (801341455)
% 0.20/0.38  ipcrm: permission denied for id (801406993)
% 0.20/0.38  ipcrm: permission denied for id (801472530)
% 0.20/0.38  ipcrm: permission denied for id (801505299)
% 0.20/0.38  ipcrm: permission denied for id (801538068)
% 0.20/0.39  ipcrm: permission denied for id (801603613)
% 0.20/0.40  ipcrm: permission denied for id (801669152)
% 0.20/0.42  ipcrm: permission denied for id (801767472)
% 0.20/0.43  ipcrm: permission denied for id (802029623)
% 0.20/0.43  ipcrm: permission denied for id (802193470)
% 0.20/0.44  ipcrm: permission denied for id (802291777)
% 0.20/0.44  ipcrm: permission denied for id (802390084)
% 0.20/0.45  ipcrm: permission denied for id (802455623)
% 0.20/0.45  ipcrm: permission denied for id (802586702)
% 0.20/0.46  ipcrm: permission denied for id (802619474)
% 0.20/0.46  ipcrm: permission denied for id (802685012)
% 0.20/0.46  ipcrm: permission denied for id (802750550)
% 0.20/0.47  ipcrm: permission denied for id (802848859)
% 0.20/0.47  ipcrm: permission denied for id (802881628)
% 0.20/0.48  ipcrm: permission denied for id (803012705)
% 0.20/0.48  ipcrm: permission denied for id (803078244)
% 0.20/0.48  ipcrm: permission denied for id (803143783)
% 0.20/0.49  ipcrm: permission denied for id (803209321)
% 0.20/0.49  ipcrm: permission denied for id (803242090)
% 0.20/0.49  ipcrm: permission denied for id (803340397)
% 0.20/0.49  ipcrm: permission denied for id (803405935)
% 0.20/0.50  ipcrm: permission denied for id (803438705)
% 0.20/0.50  ipcrm: permission denied for id (803537013)
% 0.20/0.50  ipcrm: permission denied for id (803569782)
% 0.20/0.51  ipcrm: permission denied for id (803635322)
% 0.20/0.51  ipcrm: permission denied for id (803700860)
% 0.20/0.51  ipcrm: permission denied for id (803733629)
% 0.20/0.59  % (7956)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.80/0.61  % (7956)Refutation found. Thanks to Tanya!
% 0.80/0.61  % SZS status Theorem for theBenchmark
% 0.80/0.61  % (7971)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.80/0.62  % (7963)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.80/0.62  % SZS output start Proof for theBenchmark
% 0.80/0.62  fof(f90,plain,(
% 0.80/0.62    $false),
% 0.80/0.62    inference(avatar_sat_refutation,[],[f47,f63,f70,f82,f89])).
% 0.80/0.62  fof(f89,plain,(
% 0.80/0.62    spl5_1 | ~spl5_4),
% 0.80/0.62    inference(avatar_contradiction_clause,[],[f88])).
% 0.80/0.62  fof(f88,plain,(
% 0.80/0.62    $false | (spl5_1 | ~spl5_4)),
% 0.80/0.62    inference(subsumption_resolution,[],[f87,f43])).
% 0.80/0.62  fof(f43,plain,(
% 0.80/0.62    k1_xboole_0 != sK0 | spl5_1),
% 0.80/0.62    inference(avatar_component_clause,[],[f42])).
% 0.80/0.62  fof(f42,plain,(
% 0.80/0.62    spl5_1 <=> k1_xboole_0 = sK0),
% 0.80/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.80/0.62  fof(f87,plain,(
% 0.80/0.62    k1_xboole_0 = sK0 | ~spl5_4),
% 0.80/0.62    inference(resolution,[],[f83,f34])).
% 0.80/0.62  fof(f34,plain,(
% 0.80/0.62    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.80/0.62    inference(cnf_transformation,[],[f21])).
% 0.80/0.62  fof(f21,plain,(
% 0.80/0.62    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.80/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f20])).
% 0.80/0.62  fof(f20,plain,(
% 0.80/0.62    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.80/0.62    introduced(choice_axiom,[])).
% 0.80/0.62  fof(f13,plain,(
% 0.80/0.62    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.80/0.62    inference(ennf_transformation,[],[f1])).
% 0.80/0.62  fof(f1,axiom,(
% 0.80/0.62    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.80/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.80/0.62  fof(f83,plain,(
% 0.80/0.62    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl5_4),
% 0.80/0.62    inference(resolution,[],[f69,f40])).
% 0.80/0.62  fof(f40,plain,(
% 0.80/0.62    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.80/0.62    inference(cnf_transformation,[],[f24])).
% 0.80/0.62  fof(f24,plain,(
% 0.80/0.62    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.80/0.62    inference(nnf_transformation,[],[f3])).
% 0.80/0.62  fof(f3,axiom,(
% 0.80/0.62    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.80/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.80/0.62  fof(f69,plain,(
% 0.80/0.62    ( ! [X0] : (~r1_tarski(k1_tarski(X0),sK0)) ) | ~spl5_4),
% 0.80/0.62    inference(avatar_component_clause,[],[f68])).
% 0.80/0.62  fof(f68,plain,(
% 0.80/0.62    spl5_4 <=> ! [X0] : ~r1_tarski(k1_tarski(X0),sK0)),
% 0.80/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.80/0.62  fof(f82,plain,(
% 0.80/0.62    ~spl5_2),
% 0.80/0.62    inference(avatar_contradiction_clause,[],[f81])).
% 0.80/0.62  fof(f81,plain,(
% 0.80/0.62    $false | ~spl5_2),
% 0.80/0.62    inference(subsumption_resolution,[],[f80,f27])).
% 0.80/0.62  fof(f27,plain,(
% 0.80/0.62    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.80/0.62    inference(cnf_transformation,[],[f2])).
% 0.80/0.62  fof(f2,axiom,(
% 0.80/0.62    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.80/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.80/0.62  fof(f80,plain,(
% 0.80/0.62    ~r1_tarski(k1_xboole_0,sK0) | ~spl5_2),
% 0.80/0.62    inference(backward_demodulation,[],[f73,f79])).
% 0.80/0.62  fof(f79,plain,(
% 0.80/0.62    k1_xboole_0 = k2_relat_1(sK4(k1_xboole_0))),
% 0.80/0.62    inference(equality_resolution,[],[f58])).
% 0.80/0.62  fof(f58,plain,(
% 0.80/0.62    ( ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_relat_1(sK4(X0))) )),
% 0.80/0.62    inference(subsumption_resolution,[],[f56,f35])).
% 0.80/0.62  fof(f35,plain,(
% 0.80/0.62    ( ! [X0] : (v1_relat_1(sK4(X0))) )),
% 0.80/0.62    inference(cnf_transformation,[],[f23])).
% 0.80/0.62  fof(f23,plain,(
% 0.80/0.62    ! [X0] : (! [X2] : (np__1 = k1_funct_1(sK4(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK4(X0)) = X0 & v1_funct_1(sK4(X0)) & v1_relat_1(sK4(X0)))),
% 0.80/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f22])).
% 0.80/0.62  fof(f22,plain,(
% 0.80/0.62    ! [X0] : (? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (np__1 = k1_funct_1(sK4(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK4(X0)) = X0 & v1_funct_1(sK4(X0)) & v1_relat_1(sK4(X0))))),
% 0.80/0.62    introduced(choice_axiom,[])).
% 0.80/0.62  fof(f14,plain,(
% 0.80/0.62    ! [X0] : ? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.80/0.62    inference(ennf_transformation,[],[f5])).
% 0.80/0.62  fof(f5,axiom,(
% 0.80/0.62    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = np__1) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.80/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).
% 0.80/0.62  fof(f56,plain,(
% 0.80/0.62    ( ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_relat_1(sK4(X0)) | ~v1_relat_1(sK4(X0))) )),
% 0.80/0.62    inference(superposition,[],[f28,f37])).
% 0.80/0.62  fof(f37,plain,(
% 0.80/0.62    ( ! [X0] : (k1_relat_1(sK4(X0)) = X0) )),
% 0.80/0.62    inference(cnf_transformation,[],[f23])).
% 0.80/0.62  fof(f28,plain,(
% 0.80/0.62    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.80/0.62    inference(cnf_transformation,[],[f17])).
% 0.80/0.62  fof(f17,plain,(
% 0.80/0.62    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.80/0.62    inference(nnf_transformation,[],[f11])).
% 0.80/0.62  fof(f11,plain,(
% 0.80/0.62    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.80/0.62    inference(ennf_transformation,[],[f4])).
% 0.80/0.62  fof(f4,axiom,(
% 0.80/0.62    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.80/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 0.80/0.62  fof(f73,plain,(
% 0.80/0.62    ~r1_tarski(k2_relat_1(sK4(k1_xboole_0)),sK0) | ~spl5_2),
% 0.80/0.62    inference(backward_demodulation,[],[f51,f46])).
% 0.80/0.62  fof(f46,plain,(
% 0.80/0.62    k1_xboole_0 = sK1 | ~spl5_2),
% 0.80/0.62    inference(avatar_component_clause,[],[f45])).
% 0.80/0.62  fof(f45,plain,(
% 0.80/0.62    spl5_2 <=> k1_xboole_0 = sK1),
% 0.80/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.80/0.62  fof(f51,plain,(
% 0.80/0.62    ~r1_tarski(k2_relat_1(sK4(sK1)),sK0)),
% 0.80/0.62    inference(equality_resolution,[],[f50])).
% 0.80/0.62  fof(f50,plain,(
% 0.80/0.62    ( ! [X0] : (sK1 != X0 | ~r1_tarski(k2_relat_1(sK4(X0)),sK0)) )),
% 0.80/0.62    inference(subsumption_resolution,[],[f49,f35])).
% 0.80/0.62  fof(f49,plain,(
% 0.80/0.62    ( ! [X0] : (sK1 != X0 | ~r1_tarski(k2_relat_1(sK4(X0)),sK0) | ~v1_relat_1(sK4(X0))) )),
% 0.80/0.62    inference(subsumption_resolution,[],[f48,f36])).
% 0.80/0.62  fof(f36,plain,(
% 0.80/0.62    ( ! [X0] : (v1_funct_1(sK4(X0))) )),
% 0.80/0.62    inference(cnf_transformation,[],[f23])).
% 0.80/0.62  fof(f48,plain,(
% 0.80/0.62    ( ! [X0] : (sK1 != X0 | ~r1_tarski(k2_relat_1(sK4(X0)),sK0) | ~v1_funct_1(sK4(X0)) | ~v1_relat_1(sK4(X0))) )),
% 0.80/0.62    inference(superposition,[],[f26,f37])).
% 0.80/0.62  fof(f26,plain,(
% 0.80/0.62    ( ! [X2] : (k1_relat_1(X2) != sK1 | ~r1_tarski(k2_relat_1(X2),sK0) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.80/0.62    inference(cnf_transformation,[],[f16])).
% 0.80/0.62  fof(f16,plain,(
% 0.80/0.62    ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK0)),
% 0.80/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f15])).
% 0.80/0.62  fof(f15,plain,(
% 0.80/0.62    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0)) => (! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK0))),
% 0.80/0.62    introduced(choice_axiom,[])).
% 0.80/0.62  fof(f10,plain,(
% 0.80/0.62    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.80/0.62    inference(flattening,[],[f9])).
% 0.80/0.62  fof(f9,plain,(
% 0.80/0.62    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.80/0.62    inference(ennf_transformation,[],[f8])).
% 0.80/0.62  fof(f8,negated_conjecture,(
% 0.80/0.62    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.80/0.62    inference(negated_conjecture,[],[f7])).
% 0.80/0.62  fof(f7,conjecture,(
% 0.80/0.62    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.80/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).
% 0.80/0.62  fof(f70,plain,(
% 0.80/0.62    spl5_2 | spl5_4 | ~spl5_3),
% 0.80/0.62    inference(avatar_split_clause,[],[f66,f61,f68,f45])).
% 0.80/0.62  fof(f61,plain,(
% 0.80/0.62    spl5_3 <=> ! [X0] : ~r1_tarski(k2_relat_1(sK2(sK1,X0)),sK0)),
% 0.80/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.80/0.62  fof(f66,plain,(
% 0.80/0.62    ( ! [X0] : (~r1_tarski(k1_tarski(X0),sK0) | k1_xboole_0 = sK1) ) | ~spl5_3),
% 0.80/0.62    inference(superposition,[],[f62,f33])).
% 0.80/0.62  fof(f33,plain,(
% 0.80/0.62    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.80/0.62    inference(cnf_transformation,[],[f19])).
% 0.80/0.62  fof(f19,plain,(
% 0.80/0.62    ! [X0] : (! [X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))) | k1_xboole_0 = X0)),
% 0.80/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f18])).
% 0.80/0.62  fof(f18,plain,(
% 0.80/0.62    ! [X1,X0] : (? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))))),
% 0.80/0.62    introduced(choice_axiom,[])).
% 0.80/0.62  fof(f12,plain,(
% 0.80/0.62    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 0.80/0.62    inference(ennf_transformation,[],[f6])).
% 0.80/0.62  fof(f6,axiom,(
% 0.80/0.62    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.80/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).
% 0.80/0.62  fof(f62,plain,(
% 0.80/0.62    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2(sK1,X0)),sK0)) ) | ~spl5_3),
% 0.80/0.62    inference(avatar_component_clause,[],[f61])).
% 0.80/0.62  fof(f63,plain,(
% 0.80/0.62    spl5_2 | spl5_3),
% 0.80/0.62    inference(avatar_split_clause,[],[f59,f61,f45])).
% 0.80/0.62  fof(f59,plain,(
% 0.80/0.62    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2(sK1,X0)),sK0) | k1_xboole_0 = sK1) )),
% 0.80/0.62    inference(equality_resolution,[],[f55])).
% 0.80/0.62  fof(f55,plain,(
% 0.80/0.62    ( ! [X0,X1] : (sK1 != X0 | ~r1_tarski(k2_relat_1(sK2(X0,X1)),sK0) | k1_xboole_0 = X0) )),
% 0.80/0.62    inference(subsumption_resolution,[],[f54,f30])).
% 0.80/0.62  fof(f30,plain,(
% 0.80/0.62    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.80/0.62    inference(cnf_transformation,[],[f19])).
% 0.80/0.62  fof(f54,plain,(
% 0.80/0.62    ( ! [X0,X1] : (sK1 != X0 | ~r1_tarski(k2_relat_1(sK2(X0,X1)),sK0) | ~v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.80/0.62    inference(subsumption_resolution,[],[f53,f31])).
% 0.80/0.62  fof(f31,plain,(
% 0.80/0.62    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.80/0.62    inference(cnf_transformation,[],[f19])).
% 0.80/0.62  fof(f53,plain,(
% 0.80/0.62    ( ! [X0,X1] : (sK1 != X0 | ~r1_tarski(k2_relat_1(sK2(X0,X1)),sK0) | ~v1_funct_1(sK2(X0,X1)) | ~v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.80/0.62    inference(superposition,[],[f26,f32])).
% 0.80/0.62  fof(f32,plain,(
% 0.80/0.62    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 0.80/0.62    inference(cnf_transformation,[],[f19])).
% 0.80/0.62  fof(f47,plain,(
% 0.80/0.62    ~spl5_1 | spl5_2),
% 0.80/0.62    inference(avatar_split_clause,[],[f25,f45,f42])).
% 0.80/0.62  fof(f25,plain,(
% 0.80/0.62    k1_xboole_0 = sK1 | k1_xboole_0 != sK0),
% 0.80/0.62    inference(cnf_transformation,[],[f16])).
% 0.80/0.62  % SZS output end Proof for theBenchmark
% 0.80/0.62  % (7956)------------------------------
% 0.80/0.62  % (7956)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.80/0.62  % (7956)Termination reason: Refutation
% 0.80/0.62  
% 0.80/0.62  % (7956)Memory used [KB]: 10618
% 0.80/0.62  % (7956)Time elapsed: 0.053 s
% 0.80/0.62  % (7956)------------------------------
% 0.80/0.62  % (7956)------------------------------
% 0.97/0.62  % (7813)Success in time 0.266 s
%------------------------------------------------------------------------------
