%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 175 expanded)
%              Number of leaves         :    8 (  58 expanded)
%              Depth                    :   15
%              Number of atoms          :  178 ( 865 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f58,plain,(
    $false ),
    inference(subsumption_resolution,[],[f57,f22])).

fof(f22,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ v2_wellord1(sK3)
    & v2_wellord1(sK2)
    & r4_wellord1(sK2,sK3)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f6,f14,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_wellord1(X1)
            & v2_wellord1(X0)
            & r4_wellord1(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ v2_wellord1(X1)
          & v2_wellord1(sK2)
          & r4_wellord1(sK2,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X1] :
        ( ~ v2_wellord1(X1)
        & v2_wellord1(sK2)
        & r4_wellord1(sK2,X1)
        & v1_relat_1(X1) )
   => ( ~ v2_wellord1(sK3)
      & v2_wellord1(sK2)
      & r4_wellord1(sK2,sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_wellord1(X1)
          & v2_wellord1(X0)
          & r4_wellord1(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_wellord1(X1)
          & v2_wellord1(X0)
          & r4_wellord1(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( ( v2_wellord1(X0)
                & r4_wellord1(X0,X1) )
             => v2_wellord1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( ( v2_wellord1(X0)
              & r4_wellord1(X0,X1) )
           => v2_wellord1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_wellord1)).

fof(f57,plain,(
    ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f56,f25])).

fof(f25,plain,(
    ~ v2_wellord1(sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f56,plain,
    ( v2_wellord1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f55,f46])).

fof(f46,plain,(
    r3_wellord1(sK2,sK3,sK4(sK3,sK2)) ),
    inference(resolution,[],[f43,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | r3_wellord1(X1,X0,sK4(X0,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( ~ r3_wellord1(X1,X0,X2)
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) ) )
      & ( ( r3_wellord1(X1,X0,sK4(X0,X1))
          & v1_funct_1(sK4(X0,X1))
          & v1_relat_1(sK4(X0,X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r3_wellord1(X1,X0,X3)
          & v1_funct_1(X3)
          & v1_relat_1(X3) )
     => ( r3_wellord1(X1,X0,sK4(X0,X1))
        & v1_funct_1(sK4(X0,X1))
        & v1_relat_1(sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( ~ r3_wellord1(X1,X0,X2)
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) ) )
      & ( ? [X3] :
            ( r3_wellord1(X1,X0,X3)
            & v1_funct_1(X3)
            & v1_relat_1(X3) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ! [X2] :
            ( ~ r3_wellord1(X0,X1,X2)
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) ) )
      & ( ? [X2] :
            ( r3_wellord1(X0,X1,X2)
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ? [X2] :
          ( r3_wellord1(X0,X1,X2)
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f43,plain,(
    sP0(sK3,sK2) ),
    inference(subsumption_resolution,[],[f42,f22])).

fof(f42,plain,
    ( ~ v1_relat_1(sK3)
    | sP0(sK3,sK2) ),
    inference(resolution,[],[f38,f23])).

fof(f23,plain,(
    r4_wellord1(sK2,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0] :
      ( ~ r4_wellord1(sK2,X0)
      | ~ v1_relat_1(X0)
      | sP0(X0,sK2) ) ),
    inference(resolution,[],[f34,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ r4_wellord1(X0,X1)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( r4_wellord1(X0,X1)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ r4_wellord1(X0,X1) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( r4_wellord1(X0,X1)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f34,plain,(
    ! [X0] :
      ( sP1(sK2,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f21,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f7,f11,f10])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r4_wellord1(X0,X1)
          <=> ? [X2] :
                ( r3_wellord1(X0,X1,X2)
                & v1_funct_1(X2)
                & v1_relat_1(X2) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
          <=> ? [X2] :
                ( r3_wellord1(X0,X1,X2)
                & v1_funct_1(X2)
                & v1_relat_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_wellord1)).

fof(f21,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f55,plain,(
    ! [X0] :
      ( ~ r3_wellord1(sK2,X0,sK4(sK3,sK2))
      | v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f54,f44])).

fof(f44,plain,(
    v1_relat_1(sK4(sK3,sK2)) ),
    inference(resolution,[],[f43,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | v1_relat_1(sK4(X0,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f54,plain,(
    ! [X0] :
      ( v2_wellord1(X0)
      | ~ r3_wellord1(sK2,X0,sK4(sK3,sK2))
      | ~ v1_relat_1(sK4(sK3,sK2))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f37,f45])).

fof(f45,plain,(
    v1_funct_1(sK4(sK3,sK2)) ),
    inference(resolution,[],[f43,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | v1_funct_1(sK4(X0,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | v2_wellord1(X0)
      | ~ r3_wellord1(sK2,X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f36,f21])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r3_wellord1(sK2,X0,X1)
      | v2_wellord1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f24,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_wellord1(X0)
      | ~ r3_wellord1(X0,X1,X2)
      | v2_wellord1(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_wellord1(X1)
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v2_wellord1(X0)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_wellord1(X1)
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v2_wellord1(X0)
              | ~ v1_funct_1(X2)
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
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( r3_wellord1(X0,X1,X2)
                  & v2_wellord1(X0) )
               => v2_wellord1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_wellord1)).

fof(f24,plain,(
    v2_wellord1(sK2) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:44:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.42  % (7082)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.20/0.42  % (7082)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f58,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(subsumption_resolution,[],[f57,f22])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    v1_relat_1(sK3)),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    (~v2_wellord1(sK3) & v2_wellord1(sK2) & r4_wellord1(sK2,sK3) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f6,f14,f13])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : (~v2_wellord1(X1) & v2_wellord1(X0) & r4_wellord1(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~v2_wellord1(X1) & v2_wellord1(sK2) & r4_wellord1(sK2,X1) & v1_relat_1(X1)) & v1_relat_1(sK2))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    ? [X1] : (~v2_wellord1(X1) & v2_wellord1(sK2) & r4_wellord1(sK2,X1) & v1_relat_1(X1)) => (~v2_wellord1(sK3) & v2_wellord1(sK2) & r4_wellord1(sK2,sK3) & v1_relat_1(sK3))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f6,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : (~v2_wellord1(X1) & v2_wellord1(X0) & r4_wellord1(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.42    inference(flattening,[],[f5])).
% 0.20/0.42  fof(f5,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : ((~v2_wellord1(X1) & (v2_wellord1(X0) & r4_wellord1(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,negated_conjecture,(
% 0.20/0.42    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ((v2_wellord1(X0) & r4_wellord1(X0,X1)) => v2_wellord1(X1))))),
% 0.20/0.42    inference(negated_conjecture,[],[f3])).
% 0.20/0.42  fof(f3,conjecture,(
% 0.20/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ((v2_wellord1(X0) & r4_wellord1(X0,X1)) => v2_wellord1(X1))))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_wellord1)).
% 0.20/0.42  fof(f57,plain,(
% 0.20/0.42    ~v1_relat_1(sK3)),
% 0.20/0.42    inference(subsumption_resolution,[],[f56,f25])).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    ~v2_wellord1(sK3)),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  fof(f56,plain,(
% 0.20/0.42    v2_wellord1(sK3) | ~v1_relat_1(sK3)),
% 0.20/0.42    inference(resolution,[],[f55,f46])).
% 0.20/0.42  fof(f46,plain,(
% 0.20/0.42    r3_wellord1(sK2,sK3,sK4(sK3,sK2))),
% 0.20/0.42    inference(resolution,[],[f43,f30])).
% 0.20/0.42  fof(f30,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~sP0(X0,X1) | r3_wellord1(X1,X0,sK4(X0,X1))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f20])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    ! [X0,X1] : ((sP0(X0,X1) | ! [X2] : (~r3_wellord1(X1,X0,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))) & ((r3_wellord1(X1,X0,sK4(X0,X1)) & v1_funct_1(sK4(X0,X1)) & v1_relat_1(sK4(X0,X1))) | ~sP0(X0,X1)))),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f19])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    ! [X1,X0] : (? [X3] : (r3_wellord1(X1,X0,X3) & v1_funct_1(X3) & v1_relat_1(X3)) => (r3_wellord1(X1,X0,sK4(X0,X1)) & v1_funct_1(sK4(X0,X1)) & v1_relat_1(sK4(X0,X1))))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    ! [X0,X1] : ((sP0(X0,X1) | ! [X2] : (~r3_wellord1(X1,X0,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))) & (? [X3] : (r3_wellord1(X1,X0,X3) & v1_funct_1(X3) & v1_relat_1(X3)) | ~sP0(X0,X1)))),
% 0.20/0.42    inference(rectify,[],[f17])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    ! [X1,X0] : ((sP0(X1,X0) | ! [X2] : (~r3_wellord1(X0,X1,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))) & (? [X2] : (r3_wellord1(X0,X1,X2) & v1_funct_1(X2) & v1_relat_1(X2)) | ~sP0(X1,X0)))),
% 0.20/0.42    inference(nnf_transformation,[],[f10])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ! [X1,X0] : (sP0(X1,X0) <=> ? [X2] : (r3_wellord1(X0,X1,X2) & v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.20/0.42    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.42  fof(f43,plain,(
% 0.20/0.42    sP0(sK3,sK2)),
% 0.20/0.42    inference(subsumption_resolution,[],[f42,f22])).
% 0.20/0.42  fof(f42,plain,(
% 0.20/0.42    ~v1_relat_1(sK3) | sP0(sK3,sK2)),
% 0.20/0.42    inference(resolution,[],[f38,f23])).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    r4_wellord1(sK2,sK3)),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  fof(f38,plain,(
% 0.20/0.42    ( ! [X0] : (~r4_wellord1(sK2,X0) | ~v1_relat_1(X0) | sP0(X0,sK2)) )),
% 0.20/0.42    inference(resolution,[],[f34,f26])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~sP1(X0,X1) | ~r4_wellord1(X0,X1) | sP0(X1,X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f16])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    ! [X0,X1] : (((r4_wellord1(X0,X1) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~r4_wellord1(X0,X1))) | ~sP1(X0,X1))),
% 0.20/0.42    inference(nnf_transformation,[],[f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ! [X0,X1] : ((r4_wellord1(X0,X1) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 0.20/0.42    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.42  fof(f34,plain,(
% 0.20/0.42    ( ! [X0] : (sP1(sK2,X0) | ~v1_relat_1(X0)) )),
% 0.20/0.42    inference(resolution,[],[f21,f32])).
% 0.20/0.42  fof(f32,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | sP1(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f12])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : (sP1(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.42    inference(definition_folding,[],[f7,f11,f10])).
% 0.20/0.42  fof(f7,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : ((r4_wellord1(X0,X1) <=> ? [X2] : (r3_wellord1(X0,X1,X2) & v1_funct_1(X2) & v1_relat_1(X2))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) <=> ? [X2] : (r3_wellord1(X0,X1,X2) & v1_funct_1(X2) & v1_relat_1(X2)))))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_wellord1)).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    v1_relat_1(sK2)),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  fof(f55,plain,(
% 0.20/0.42    ( ! [X0] : (~r3_wellord1(sK2,X0,sK4(sK3,sK2)) | v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.42    inference(subsumption_resolution,[],[f54,f44])).
% 0.20/0.42  fof(f44,plain,(
% 0.20/0.42    v1_relat_1(sK4(sK3,sK2))),
% 0.20/0.42    inference(resolution,[],[f43,f28])).
% 0.20/0.42  fof(f28,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~sP0(X0,X1) | v1_relat_1(sK4(X0,X1))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f20])).
% 0.20/0.42  fof(f54,plain,(
% 0.20/0.42    ( ! [X0] : (v2_wellord1(X0) | ~r3_wellord1(sK2,X0,sK4(sK3,sK2)) | ~v1_relat_1(sK4(sK3,sK2)) | ~v1_relat_1(X0)) )),
% 0.20/0.42    inference(resolution,[],[f37,f45])).
% 0.20/0.42  fof(f45,plain,(
% 0.20/0.42    v1_funct_1(sK4(sK3,sK2))),
% 0.20/0.42    inference(resolution,[],[f43,f29])).
% 0.20/0.42  fof(f29,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~sP0(X0,X1) | v1_funct_1(sK4(X0,X1))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f20])).
% 0.20/0.42  fof(f37,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~v1_funct_1(X1) | v2_wellord1(X0) | ~r3_wellord1(sK2,X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.42    inference(subsumption_resolution,[],[f36,f21])).
% 0.20/0.42  fof(f36,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r3_wellord1(sK2,X0,X1) | v2_wellord1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | ~v1_relat_1(sK2)) )),
% 0.20/0.42    inference(resolution,[],[f24,f33])).
% 0.20/0.42  fof(f33,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~v2_wellord1(X0) | ~r3_wellord1(X0,X1,X2) | v2_wellord1(X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f9])).
% 0.20/0.42  fof(f9,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : (! [X2] : (v2_wellord1(X1) | ~r3_wellord1(X0,X1,X2) | ~v2_wellord1(X0) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.42    inference(flattening,[],[f8])).
% 0.20/0.42  fof(f8,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : (! [X2] : ((v2_wellord1(X1) | (~r3_wellord1(X0,X1,X2) | ~v2_wellord1(X0))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r3_wellord1(X0,X1,X2) & v2_wellord1(X0)) => v2_wellord1(X1)))))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_wellord1)).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    v2_wellord1(sK2)),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (7082)------------------------------
% 0.20/0.42  % (7082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (7082)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (7082)Memory used [KB]: 9850
% 0.20/0.42  % (7082)Time elapsed: 0.005 s
% 0.20/0.42  % (7082)------------------------------
% 0.20/0.42  % (7082)------------------------------
% 0.20/0.42  % (7072)Success in time 0.065 s
%------------------------------------------------------------------------------
