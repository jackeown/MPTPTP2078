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
% DateTime   : Thu Dec  3 12:52:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 106 expanded)
%              Number of leaves         :   11 (  35 expanded)
%              Depth                    :   14
%              Number of atoms          :  209 ( 525 expanded)
%              Number of equality atoms :   47 ( 101 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f141,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f86,f138])).

fof(f138,plain,(
    ~ spl7_3 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f134,f26])).

fof(f26,plain,(
    ~ r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_tarski(sK0,k2_relat_1(sK1))
    & ! [X2] :
        ( ( k1_funct_1(sK1,sK2(X2)) = X2
          & r2_hidden(sK2(X2),k1_relat_1(sK1)) )
        | ~ r2_hidden(X2,sK0) )
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f12,f11])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k2_relat_1(X1))
        & ! [X2] :
            ( ? [X3] :
                ( k1_funct_1(X1,X3) = X2
                & r2_hidden(X3,k1_relat_1(X1)) )
            | ~ r2_hidden(X2,X0) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k2_relat_1(sK1))
      & ! [X2] :
          ( ? [X3] :
              ( k1_funct_1(sK1,X3) = X2
              & r2_hidden(X3,k1_relat_1(sK1)) )
          | ~ r2_hidden(X2,sK0) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X2] :
      ( ? [X3] :
          ( k1_funct_1(sK1,X3) = X2
          & r2_hidden(X3,k1_relat_1(sK1)) )
     => ( k1_funct_1(sK1,sK2(X2)) = X2
        & r2_hidden(sK2(X2),k1_relat_1(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      & ! [X2] :
          ( ? [X3] :
              ( k1_funct_1(X1,X3) = X2
              & r2_hidden(X3,k1_relat_1(X1)) )
          | ~ r2_hidden(X2,X0) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      & ! [X2] :
          ( ? [X3] :
              ( k1_funct_1(X1,X3) = X2
              & r2_hidden(X3,k1_relat_1(X1)) )
          | ~ r2_hidden(X2,X0) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ! [X2] :
              ~ ( ! [X3] :
                    ~ ( k1_funct_1(X1,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X1)) )
                & r2_hidden(X2,X0) )
         => r1_tarski(X0,k2_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( k1_funct_1(X1,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X1)) )
              & r2_hidden(X2,X0) )
       => r1_tarski(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_funct_1)).

fof(f134,plain,
    ( r1_tarski(sK0,k2_relat_1(sK1))
    | ~ spl7_3 ),
    inference(resolution,[],[f72,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f10,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f72,plain,
    ( r2_hidden(sK6(sK0,k2_relat_1(sK1)),k2_relat_1(sK1))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl7_3
  <=> r2_hidden(sK6(sK0,k2_relat_1(sK1)),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f86,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f85])).

fof(f85,plain,
    ( $false
    | spl7_1 ),
    inference(subsumption_resolution,[],[f84,f26])).

fof(f84,plain,
    ( r1_tarski(sK0,k2_relat_1(sK1))
    | spl7_1 ),
    inference(resolution,[],[f63,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f63,plain,
    ( ~ r2_hidden(sK6(sK0,k2_relat_1(sK1)),sK0)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl7_1
  <=> r2_hidden(sK6(sK0,k2_relat_1(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f73,plain,
    ( ~ spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f58,f70,f61])).

fof(f58,plain,
    ( r2_hidden(sK6(sK0,k2_relat_1(sK1)),k2_relat_1(sK1))
    | ~ r2_hidden(sK6(sK0,k2_relat_1(sK1)),sK0) ),
    inference(superposition,[],[f45,f56])).

fof(f56,plain,(
    sK6(sK0,k2_relat_1(sK1)) = k1_funct_1(sK1,sK2(sK6(sK0,k2_relat_1(sK1)))) ),
    inference(resolution,[],[f46,f26])).

fof(f46,plain,(
    ! [X0] :
      ( r1_tarski(sK0,X0)
      | sK6(sK0,X0) = k1_funct_1(sK1,sK2(sK6(sK0,X0))) ) ),
    inference(resolution,[],[f25,f33])).

fof(f25,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | k1_funct_1(sK1,sK2(X2)) = X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK1,sK2(X0)),k2_relat_1(sK1))
      | ~ r2_hidden(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f44,f22])).

fof(f22,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f44,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(k1_funct_1(sK1,sK2(X0)),k2_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f43,f23])).

fof(f23,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f43,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(k1_funct_1(sK1,sK2(X0)),k2_relat_1(sK1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f24,f36])).

fof(f36,plain,(
    ! [X6,X0] :
      ( ~ r2_hidden(X6,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK3(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK3(X0,X1),X1) )
              & ( ( sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1))
                  & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK3(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK5(X0,X5)) = X5
                    & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f15,f18,f17,f16])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK3(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK3(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK3(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X5)) = X5
        & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f14])).

% (16520)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f24,plain,(
    ! [X2] :
      ( r2_hidden(sK2(X2),k1_relat_1(sK1))
      | ~ r2_hidden(X2,sK0) ) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:20:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (16513)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (16508)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (16517)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (16514)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (16515)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (16517)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f141,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f73,f86,f138])).
% 0.21/0.52  fof(f138,plain,(
% 0.21/0.52    ~spl7_3),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f137])).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    $false | ~spl7_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f134,f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ~r1_tarski(sK0,k2_relat_1(sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ~r1_tarski(sK0,k2_relat_1(sK1)) & ! [X2] : ((k1_funct_1(sK1,sK2(X2)) = X2 & r2_hidden(sK2(X2),k1_relat_1(sK1))) | ~r2_hidden(X2,sK0)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f12,f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ? [X0,X1] : (~r1_tarski(X0,k2_relat_1(X1)) & ! [X2] : (? [X3] : (k1_funct_1(X1,X3) = X2 & r2_hidden(X3,k1_relat_1(X1))) | ~r2_hidden(X2,X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => (~r1_tarski(sK0,k2_relat_1(sK1)) & ! [X2] : (? [X3] : (k1_funct_1(sK1,X3) = X2 & r2_hidden(X3,k1_relat_1(sK1))) | ~r2_hidden(X2,sK0)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X2] : (? [X3] : (k1_funct_1(sK1,X3) = X2 & r2_hidden(X3,k1_relat_1(sK1))) => (k1_funct_1(sK1,sK2(X2)) = X2 & r2_hidden(sK2(X2),k1_relat_1(sK1))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f7,plain,(
% 0.21/0.52    ? [X0,X1] : (~r1_tarski(X0,k2_relat_1(X1)) & ! [X2] : (? [X3] : (k1_funct_1(X1,X3) = X2 & r2_hidden(X3,k1_relat_1(X1))) | ~r2_hidden(X2,X0)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f6])).
% 0.21/0.52  fof(f6,plain,(
% 0.21/0.52    ? [X0,X1] : ((~r1_tarski(X0,k2_relat_1(X1)) & ! [X2] : (? [X3] : (k1_funct_1(X1,X3) = X2 & r2_hidden(X3,k1_relat_1(X1))) | ~r2_hidden(X2,X0))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : ~(! [X3] : ~(k1_funct_1(X1,X3) = X2 & r2_hidden(X3,k1_relat_1(X1))) & r2_hidden(X2,X0)) => r1_tarski(X0,k2_relat_1(X1))))),
% 0.21/0.52    inference(negated_conjecture,[],[f3])).
% 0.21/0.52  fof(f3,conjecture,(
% 0.21/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : ~(! [X3] : ~(k1_funct_1(X1,X3) = X2 & r2_hidden(X3,k1_relat_1(X1))) & r2_hidden(X2,X0)) => r1_tarski(X0,k2_relat_1(X1))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_funct_1)).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    r1_tarski(sK0,k2_relat_1(sK1)) | ~spl7_3),
% 0.21/0.52    inference(resolution,[],[f72,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f10,f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 0.21/0.52    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    r2_hidden(sK6(sK0,k2_relat_1(sK1)),k2_relat_1(sK1)) | ~spl7_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f70])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    spl7_3 <=> r2_hidden(sK6(sK0,k2_relat_1(sK1)),k2_relat_1(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    spl7_1),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f85])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    $false | spl7_1),
% 0.21/0.52    inference(subsumption_resolution,[],[f84,f26])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    r1_tarski(sK0,k2_relat_1(sK1)) | spl7_1),
% 0.21/0.52    inference(resolution,[],[f63,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ~r2_hidden(sK6(sK0,k2_relat_1(sK1)),sK0) | spl7_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    spl7_1 <=> r2_hidden(sK6(sK0,k2_relat_1(sK1)),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    ~spl7_1 | spl7_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f58,f70,f61])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    r2_hidden(sK6(sK0,k2_relat_1(sK1)),k2_relat_1(sK1)) | ~r2_hidden(sK6(sK0,k2_relat_1(sK1)),sK0)),
% 0.21/0.52    inference(superposition,[],[f45,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    sK6(sK0,k2_relat_1(sK1)) = k1_funct_1(sK1,sK2(sK6(sK0,k2_relat_1(sK1))))),
% 0.21/0.52    inference(resolution,[],[f46,f26])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(sK0,X0) | sK6(sK0,X0) = k1_funct_1(sK1,sK2(sK6(sK0,X0)))) )),
% 0.21/0.52    inference(resolution,[],[f25,f33])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ( ! [X2] : (~r2_hidden(X2,sK0) | k1_funct_1(sK1,sK2(X2)) = X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(k1_funct_1(sK1,sK2(X0)),k2_relat_1(sK1)) | ~r2_hidden(X0,sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f44,f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    v1_relat_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK1,sK2(X0)),k2_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f43,f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    v1_funct_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK1,sK2(X0)),k2_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.21/0.52    inference(resolution,[],[f24,f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X6,X0] : (~r2_hidden(X6,k1_relat_1(X0)) | r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & ((sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f15,f18,f17,f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK3(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK3(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(rectify,[],[f14])).
% 1.21/0.52  % (16520)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.21/0.52  fof(f14,plain,(
% 1.21/0.52    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.21/0.52    inference(nnf_transformation,[],[f9])).
% 1.21/0.52  fof(f9,plain,(
% 1.21/0.52    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.21/0.52    inference(flattening,[],[f8])).
% 1.21/0.52  fof(f8,plain,(
% 1.21/0.52    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.21/0.52    inference(ennf_transformation,[],[f2])).
% 1.21/0.52  fof(f2,axiom,(
% 1.21/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 1.21/0.52  fof(f24,plain,(
% 1.21/0.52    ( ! [X2] : (r2_hidden(sK2(X2),k1_relat_1(sK1)) | ~r2_hidden(X2,sK0)) )),
% 1.21/0.52    inference(cnf_transformation,[],[f13])).
% 1.21/0.52  % SZS output end Proof for theBenchmark
% 1.21/0.52  % (16517)------------------------------
% 1.21/0.52  % (16517)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.52  % (16517)Termination reason: Refutation
% 1.21/0.52  
% 1.21/0.52  % (16517)Memory used [KB]: 10746
% 1.21/0.52  % (16517)Time elapsed: 0.108 s
% 1.21/0.52  % (16517)------------------------------
% 1.21/0.52  % (16517)------------------------------
% 1.21/0.52  % (16504)Success in time 0.162 s
%------------------------------------------------------------------------------
