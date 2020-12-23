%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 173 expanded)
%              Number of leaves         :    4 (  30 expanded)
%              Depth                    :   16
%              Number of atoms          :  194 ( 794 expanded)
%              Number of equality atoms :   11 (  45 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f90,plain,(
    $false ),
    inference(subsumption_resolution,[],[f89,f64])).

fof(f64,plain,(
    ~ r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f56,f63])).

fof(f63,plain,(
    r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(subsumption_resolution,[],[f62,f17])).

fof(f17,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <~> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <~> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
        <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_funct_1)).

fof(f62,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f61,f18])).

fof(f18,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f61,plain,
    ( ~ v1_funct_1(sK2)
    | r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f59])).

fof(f59,plain,
    ( ~ v1_funct_1(sK2)
    | r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ v1_relat_1(sK2)
    | r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(resolution,[],[f41,f16])).

fof(f16,plain,
    ( r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))
    | r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f41,plain,(
    ! [X4,X2,X0] :
      ( ~ r2_hidden(X4,k1_relat_1(k8_relat_1(X0,X2)))
      | ~ v1_funct_1(X2)
      | r2_hidden(k1_funct_1(X2,X4),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f40,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | v1_funct_1(k8_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_funct_1)).

fof(f40,plain,(
    ! [X4,X2,X0] :
      ( ~ v1_funct_1(k8_relat_1(X0,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | r2_hidden(k1_funct_1(X2,X4),X0)
      | ~ r2_hidden(X4,k1_relat_1(k8_relat_1(X0,X2))) ) ),
    inference(subsumption_resolution,[],[f34,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | v1_relat_1(k8_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f34,plain,(
    ! [X4,X2,X0] :
      ( ~ v1_relat_1(k8_relat_1(X0,X2))
      | ~ v1_funct_1(k8_relat_1(X0,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | r2_hidden(k1_funct_1(X2,X4),X0)
      | ~ r2_hidden(X4,k1_relat_1(k8_relat_1(X0,X2))) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | r2_hidden(k1_funct_1(X2,X4),X0)
      | ~ r2_hidden(X4,k1_relat_1(X1))
      | k8_relat_1(X0,X2) != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( k1_funct_1(X2,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( k1_funct_1(X2,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X2,X3) = k1_funct_1(X1,X3) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) ) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X2,X3) = k1_funct_1(X1,X3) )
              & ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X3),X0)
                    & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_1)).

fof(f56,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))
    | ~ r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(subsumption_resolution,[],[f14,f55])).

fof(f55,plain,(
    r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f54,f17])).

fof(f54,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f51,f18])).

fof(f51,plain,
    ( ~ v1_funct_1(sK2)
    | r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f50])).

fof(f50,plain,
    ( ~ v1_funct_1(sK2)
    | r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(resolution,[],[f43,f15])).

fof(f15,plain,
    ( r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))
    | r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f43,plain,(
    ! [X4,X2,X0] :
      ( ~ r2_hidden(X4,k1_relat_1(k8_relat_1(X0,X2)))
      | ~ v1_funct_1(X2)
      | r2_hidden(X4,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f42,f21])).

fof(f42,plain,(
    ! [X4,X2,X0] :
      ( ~ v1_funct_1(k8_relat_1(X0,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | r2_hidden(X4,k1_relat_1(X2))
      | ~ r2_hidden(X4,k1_relat_1(k8_relat_1(X0,X2))) ) ),
    inference(subsumption_resolution,[],[f35,f19])).

fof(f35,plain,(
    ! [X4,X2,X0] :
      ( ~ v1_relat_1(k8_relat_1(X0,X2))
      | ~ v1_funct_1(k8_relat_1(X0,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | r2_hidden(X4,k1_relat_1(X2))
      | ~ r2_hidden(X4,k1_relat_1(k8_relat_1(X0,X2))) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | r2_hidden(X4,k1_relat_1(X2))
      | ~ r2_hidden(X4,k1_relat_1(X1))
      | k8_relat_1(X0,X2) != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))
    | ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f89,plain,(
    r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f88,f17])).

fof(f88,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f87,f55])).

fof(f87,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f86,f18])).

fof(f86,plain,
    ( ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) ),
    inference(resolution,[],[f63,f39])).

fof(f39,plain,(
    ! [X4,X2,X0] :
      ( ~ r2_hidden(k1_funct_1(X2,X4),X0)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X4,k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | r2_hidden(X4,k1_relat_1(k8_relat_1(X0,X2))) ) ),
    inference(subsumption_resolution,[],[f38,f21])).

fof(f38,plain,(
    ! [X4,X2,X0] :
      ( ~ v1_funct_1(k8_relat_1(X0,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X4,k1_relat_1(X2))
      | ~ r2_hidden(k1_funct_1(X2,X4),X0)
      | r2_hidden(X4,k1_relat_1(k8_relat_1(X0,X2))) ) ),
    inference(subsumption_resolution,[],[f33,f19])).

fof(f33,plain,(
    ! [X4,X2,X0] :
      ( ~ v1_relat_1(k8_relat_1(X0,X2))
      | ~ v1_funct_1(k8_relat_1(X0,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X4,k1_relat_1(X2))
      | ~ r2_hidden(k1_funct_1(X2,X4),X0)
      | r2_hidden(X4,k1_relat_1(k8_relat_1(X0,X2))) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X4,k1_relat_1(X2))
      | ~ r2_hidden(k1_funct_1(X2,X4),X0)
      | r2_hidden(X4,k1_relat_1(X1))
      | k8_relat_1(X0,X2) != X1 ) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n007.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:59:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (14572)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (14575)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.47  % (14564)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (14571)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (14569)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.48  % (14575)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f89,f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ~r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))),
% 0.21/0.48    inference(subsumption_resolution,[],[f56,f63])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f62,f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    v1_relat_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ? [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <~> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.48    inference(flattening,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ? [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <~> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f4])).
% 0.21/0.48  fof(f4,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_funct_1)).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~v1_relat_1(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f61,f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    v1_funct_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ~v1_funct_1(sK2) | r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~v1_relat_1(sK2)),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ~v1_funct_1(sK2) | r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~v1_relat_1(sK2) | r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.21/0.48    inference(resolution,[],[f41,f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) | r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X4,X2,X0] : (~r2_hidden(X4,k1_relat_1(k8_relat_1(X0,X2))) | ~v1_funct_1(X2) | r2_hidden(k1_funct_1(X2,X4),X0) | ~v1_relat_1(X2)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f40,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | v1_funct_1(k8_relat_1(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(k8_relat_1(X0,X1)) & v1_relat_1(k8_relat_1(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(k8_relat_1(X0,X1)) & v1_relat_1(k8_relat_1(X0,X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v1_funct_1(k8_relat_1(X0,X1)) & v1_relat_1(k8_relat_1(X0,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_funct_1)).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X4,X2,X0] : (~v1_funct_1(k8_relat_1(X0,X2)) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | r2_hidden(k1_funct_1(X2,X4),X0) | ~r2_hidden(X4,k1_relat_1(k8_relat_1(X0,X2)))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f34,f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | v1_relat_1(k8_relat_1(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X4,X2,X0] : (~v1_relat_1(k8_relat_1(X0,X2)) | ~v1_funct_1(k8_relat_1(X0,X2)) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | r2_hidden(k1_funct_1(X2,X4),X0) | ~r2_hidden(X4,k1_relat_1(k8_relat_1(X0,X2)))) )),
% 0.21/0.48    inference(equality_resolution,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | r2_hidden(k1_funct_1(X2,X4),X0) | ~r2_hidden(X4,k1_relat_1(X1)) | k8_relat_1(X0,X2) != X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : ((k8_relat_1(X0,X2) = X1 <=> (! [X3] : (k1_funct_1(X2,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X1))) & ! [X4] : (r2_hidden(X4,k1_relat_1(X1)) <=> (r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2)))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : ((k8_relat_1(X0,X2) = X1 <=> (! [X3] : (k1_funct_1(X2,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X1))) & ! [X4] : (r2_hidden(X4,k1_relat_1(X1)) <=> (r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2)))))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,plain,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (k8_relat_1(X0,X2) = X1 <=> (! [X3] : (r2_hidden(X3,k1_relat_1(X1)) => k1_funct_1(X2,X3) = k1_funct_1(X1,X3)) & ! [X4] : (r2_hidden(X4,k1_relat_1(X1)) <=> (r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2))))))))),
% 0.21/0.48    inference(rectify,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (k8_relat_1(X0,X2) = X1 <=> (! [X3] : (r2_hidden(X3,k1_relat_1(X1)) => k1_funct_1(X2,X3) = k1_funct_1(X1,X3)) & ! [X3] : (r2_hidden(X3,k1_relat_1(X1)) <=> (r2_hidden(k1_funct_1(X2,X3),X0) & r2_hidden(X3,k1_relat_1(X2))))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_1)).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ~r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) | ~r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f14,f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    r2_hidden(sK0,k1_relat_1(sK2))),
% 0.21/0.48    inference(subsumption_resolution,[],[f54,f17])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f51,f18])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ~v1_funct_1(sK2) | r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ~v1_funct_1(sK2) | r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | r2_hidden(sK0,k1_relat_1(sK2))),
% 0.21/0.48    inference(resolution,[],[f43,f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) | r2_hidden(sK0,k1_relat_1(sK2))),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X4,X2,X0] : (~r2_hidden(X4,k1_relat_1(k8_relat_1(X0,X2))) | ~v1_funct_1(X2) | r2_hidden(X4,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f42,f21])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X4,X2,X0] : (~v1_funct_1(k8_relat_1(X0,X2)) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | r2_hidden(X4,k1_relat_1(X2)) | ~r2_hidden(X4,k1_relat_1(k8_relat_1(X0,X2)))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f35,f19])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X4,X2,X0] : (~v1_relat_1(k8_relat_1(X0,X2)) | ~v1_funct_1(k8_relat_1(X0,X2)) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | r2_hidden(X4,k1_relat_1(X2)) | ~r2_hidden(X4,k1_relat_1(k8_relat_1(X0,X2)))) )),
% 0.21/0.48    inference(equality_resolution,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | r2_hidden(X4,k1_relat_1(X2)) | ~r2_hidden(X4,k1_relat_1(X1)) | k8_relat_1(X0,X2) != X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ~r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) | ~r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~r2_hidden(sK0,k1_relat_1(sK2))),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))),
% 0.21/0.48    inference(subsumption_resolution,[],[f88,f17])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    ~v1_relat_1(sK2) | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))),
% 0.21/0.48    inference(subsumption_resolution,[],[f87,f55])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))),
% 0.21/0.48    inference(subsumption_resolution,[],[f86,f18])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    ~v1_funct_1(sK2) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))),
% 0.21/0.48    inference(resolution,[],[f63,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X4,X2,X0] : (~r2_hidden(k1_funct_1(X2,X4),X0) | ~v1_funct_1(X2) | ~r2_hidden(X4,k1_relat_1(X2)) | ~v1_relat_1(X2) | r2_hidden(X4,k1_relat_1(k8_relat_1(X0,X2)))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f38,f21])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X4,X2,X0] : (~v1_funct_1(k8_relat_1(X0,X2)) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X4,k1_relat_1(X2)) | ~r2_hidden(k1_funct_1(X2,X4),X0) | r2_hidden(X4,k1_relat_1(k8_relat_1(X0,X2)))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f33,f19])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X4,X2,X0] : (~v1_relat_1(k8_relat_1(X0,X2)) | ~v1_funct_1(k8_relat_1(X0,X2)) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X4,k1_relat_1(X2)) | ~r2_hidden(k1_funct_1(X2,X4),X0) | r2_hidden(X4,k1_relat_1(k8_relat_1(X0,X2)))) )),
% 0.21/0.48    inference(equality_resolution,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X4,k1_relat_1(X2)) | ~r2_hidden(k1_funct_1(X2,X4),X0) | r2_hidden(X4,k1_relat_1(X1)) | k8_relat_1(X0,X2) != X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (14575)------------------------------
% 0.21/0.48  % (14575)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (14575)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (14575)Memory used [KB]: 1663
% 0.21/0.48  % (14575)Time elapsed: 0.068 s
% 0.21/0.48  % (14575)------------------------------
% 0.21/0.48  % (14575)------------------------------
% 0.21/0.48  % (14557)Success in time 0.133 s
%------------------------------------------------------------------------------
