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
% DateTime   : Thu Dec  3 12:52:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 275 expanded)
%              Number of leaves         :    6 (  47 expanded)
%              Depth                    :   15
%              Number of atoms          :  210 (1252 expanded)
%              Number of equality atoms :   60 ( 393 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f251,plain,(
    $false ),
    inference(subsumption_resolution,[],[f250,f113])).

fof(f113,plain,(
    sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) ),
    inference(subsumption_resolution,[],[f112,f57])).

fof(f57,plain,(
    sK0 = k1_funct_1(sK1,sK3(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f56,f21])).

fof(f21,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( r2_hidden(X0,k2_relat_1(X1))
            & v2_funct_1(X1) )
         => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
            & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k2_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
          & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_funct_1)).

fof(f56,plain,
    ( sK0 = k1_funct_1(sK1,sK3(sK1,sK0))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f55,f22])).

fof(f22,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f55,plain,
    ( ~ v1_funct_1(sK1)
    | sK0 = k1_funct_1(sK1,sK3(sK1,sK0))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f40,f24])).

fof(f24,plain,(
    r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f40,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK3(X0,X2)) = X2
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK3(X0,X2)) = X2
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f112,plain,
    ( sK0 != k1_funct_1(sK1,sK3(sK1,sK0))
    | sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) ),
    inference(backward_demodulation,[],[f20,f111])).

fof(f111,plain,(
    k1_funct_1(k2_funct_1(sK1),sK0) = sK3(sK1,sK0) ),
    inference(forward_demodulation,[],[f110,f57])).

fof(f110,plain,(
    sK3(sK1,sK0) = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f109,f21])).

fof(f109,plain,
    ( ~ v1_relat_1(sK1)
    | sK3(sK1,sK0) = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f108,f23])).

fof(f23,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f108,plain,
    ( ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | sK3(sK1,sK0) = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f100,f22])).

fof(f100,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | sK3(sK1,sK0) = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3(sK1,sK0))) ),
    inference(resolution,[],[f54,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).

fof(f54,plain,(
    r2_hidden(sK3(sK1,sK0),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f53,f21])).

fof(f53,plain,
    ( r2_hidden(sK3(sK1,sK0),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f52,f22])).

fof(f52,plain,
    ( ~ v1_funct_1(sK1)
    | r2_hidden(sK3(sK1,sK0),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f41,f24])).

fof(f41,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | r2_hidden(sK3(X0,X2),k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK3(X0,X2),k1_relat_1(X0))
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f20,plain,
    ( sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)
    | sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f250,plain,(
    sK0 = k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) ),
    inference(forward_demodulation,[],[f249,f57])).

fof(f249,plain,(
    k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) = k1_funct_1(sK1,sK3(sK1,sK0)) ),
    inference(forward_demodulation,[],[f243,f111])).

fof(f243,plain,(
    k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) = k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) ),
    inference(resolution,[],[f154,f24])).

fof(f154,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),X0) = k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),X0)) ) ),
    inference(subsumption_resolution,[],[f153,f45])).

fof(f45,plain,(
    v1_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f44,f21])).

fof(f44,plain,
    ( ~ v1_relat_1(sK1)
    | v1_funct_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f26,f22])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f153,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | ~ v1_funct_1(k2_funct_1(sK1))
      | k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),X0) = k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),X0)) ) ),
    inference(subsumption_resolution,[],[f147,f43])).

fof(f43,plain,(
    v1_relat_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f42,f21])).

fof(f42,plain,
    ( ~ v1_relat_1(sK1)
    | v1_relat_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f25,f22])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f147,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | ~ v1_relat_1(k2_funct_1(sK1))
      | ~ v1_funct_1(k2_funct_1(sK1))
      | k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),X0) = k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),X0)) ) ),
    inference(superposition,[],[f63,f48])).

fof(f48,plain,(
    k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f47,f21])).

fof(f47,plain,
    ( ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f46,f22])).

fof(f46,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f27,f23])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(k5_relat_1(X0,sK1),X1) = k1_funct_1(sK1,k1_funct_1(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f62,f21])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | k1_funct_1(k5_relat_1(X0,sK1),X1) = k1_funct_1(sK1,k1_funct_1(X0,X1)) ) ),
    inference(resolution,[],[f37,f22])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:27:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.48  % (10191)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (10203)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.49  % (10200)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (10199)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (10187)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (10187)Refutation not found, incomplete strategy% (10187)------------------------------
% 0.22/0.49  % (10187)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (10187)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (10187)Memory used [KB]: 10618
% 0.22/0.49  % (10187)Time elapsed: 0.073 s
% 0.22/0.49  % (10187)------------------------------
% 0.22/0.49  % (10187)------------------------------
% 0.22/0.49  % (10195)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.50  % (10192)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.51  % (10189)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (10203)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f251,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(subsumption_resolution,[],[f250,f113])).
% 0.22/0.51  fof(f113,plain,(
% 0.22/0.51    sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f112,f57])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    sK0 = k1_funct_1(sK1,sK3(sK1,sK0))),
% 0.22/0.51    inference(subsumption_resolution,[],[f56,f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    v1_relat_1(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,plain,(
% 0.22/0.51    ? [X0,X1] : ((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.51    inference(flattening,[],[f8])).
% 0.22/0.51  fof(f8,plain,(
% 0.22/0.51    ? [X0,X1] : (((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & (r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 0.22/0.51    inference(negated_conjecture,[],[f6])).
% 0.22/0.51  fof(f6,conjecture,(
% 0.22/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_funct_1)).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    sK0 = k1_funct_1(sK1,sK3(sK1,sK0)) | ~v1_relat_1(sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f55,f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    v1_funct_1(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f9])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    ~v1_funct_1(sK1) | sK0 = k1_funct_1(sK1,sK3(sK1,sK0)) | ~v1_relat_1(sK1)),
% 0.22/0.51    inference(resolution,[],[f40,f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    r2_hidden(sK0,k2_relat_1(sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f9])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ( ! [X2,X0] : (~r2_hidden(X2,k2_relat_1(X0)) | ~v1_funct_1(X0) | k1_funct_1(X0,sK3(X0,X2)) = X2 | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK3(X0,X2)) = X2 | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 0.22/0.51  fof(f112,plain,(
% 0.22/0.51    sK0 != k1_funct_1(sK1,sK3(sK1,sK0)) | sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)),
% 0.22/0.51    inference(backward_demodulation,[],[f20,f111])).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    k1_funct_1(k2_funct_1(sK1),sK0) = sK3(sK1,sK0)),
% 0.22/0.51    inference(forward_demodulation,[],[f110,f57])).
% 0.22/0.51  fof(f110,plain,(
% 0.22/0.51    sK3(sK1,sK0) = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3(sK1,sK0)))),
% 0.22/0.51    inference(subsumption_resolution,[],[f109,f21])).
% 0.22/0.51  fof(f109,plain,(
% 0.22/0.51    ~v1_relat_1(sK1) | sK3(sK1,sK0) = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3(sK1,sK0)))),
% 0.22/0.51    inference(subsumption_resolution,[],[f108,f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    v2_funct_1(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f9])).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    ~v2_funct_1(sK1) | ~v1_relat_1(sK1) | sK3(sK1,sK0) = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3(sK1,sK0)))),
% 0.22/0.51    inference(subsumption_resolution,[],[f100,f22])).
% 0.22/0.51  fof(f100,plain,(
% 0.22/0.51    ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1) | sK3(sK1,sK0) = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3(sK1,sK0)))),
% 0.22/0.51    inference(resolution,[],[f54,f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v2_funct_1(X1) | ~v1_relat_1(X1) | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(flattening,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | (~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    r2_hidden(sK3(sK1,sK0),k1_relat_1(sK1))),
% 0.22/0.51    inference(subsumption_resolution,[],[f53,f21])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    r2_hidden(sK3(sK1,sK0),k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f52,f22])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    ~v1_funct_1(sK1) | r2_hidden(sK3(sK1,sK0),k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 0.22/0.51    inference(resolution,[],[f41,f24])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ( ! [X2,X0] : (~r2_hidden(X2,k2_relat_1(X0)) | ~v1_funct_1(X0) | r2_hidden(sK3(X0,X2),k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK3(X0,X2),k1_relat_1(X0)) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) | sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))),
% 0.22/0.51    inference(cnf_transformation,[],[f9])).
% 0.22/0.51  fof(f250,plain,(
% 0.22/0.51    sK0 = k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)),
% 0.22/0.51    inference(forward_demodulation,[],[f249,f57])).
% 0.22/0.51  fof(f249,plain,(
% 0.22/0.51    k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) = k1_funct_1(sK1,sK3(sK1,sK0))),
% 0.22/0.51    inference(forward_demodulation,[],[f243,f111])).
% 0.22/0.51  fof(f243,plain,(
% 0.22/0.51    k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) = k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)),
% 0.22/0.51    inference(resolution,[],[f154,f24])).
% 0.22/0.51  fof(f154,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),X0) = k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),X0))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f153,f45])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    v1_funct_1(k2_funct_1(sK1))),
% 0.22/0.51    inference(subsumption_resolution,[],[f44,f21])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ~v1_relat_1(sK1) | v1_funct_1(k2_funct_1(sK1))),
% 0.22/0.51    inference(resolution,[],[f26,f22])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.22/0.51  fof(f153,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | ~v1_funct_1(k2_funct_1(sK1)) | k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),X0) = k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),X0))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f147,f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    v1_relat_1(k2_funct_1(sK1))),
% 0.22/0.51    inference(subsumption_resolution,[],[f42,f21])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ~v1_relat_1(sK1) | v1_relat_1(k2_funct_1(sK1))),
% 0.22/0.51    inference(resolution,[],[f25,f22])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f147,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(k2_funct_1(sK1)) | k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),X0) = k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),X0))) )),
% 0.22/0.51    inference(superposition,[],[f63,f48])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1))),
% 0.22/0.51    inference(subsumption_resolution,[],[f47,f21])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ~v1_relat_1(sK1) | k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1))),
% 0.22/0.51    inference(subsumption_resolution,[],[f46,f22])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1))),
% 0.22/0.51    inference(resolution,[],[f27,f23])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X1,k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(k5_relat_1(X0,sK1),X1) = k1_funct_1(sK1,k1_funct_1(X0,X1))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f62,f21])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(sK1) | ~v1_relat_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)) | k1_funct_1(k5_relat_1(X0,sK1),X1) = k1_funct_1(sK1,k1_funct_1(X0,X1))) )),
% 0.22/0.51    inference(resolution,[],[f37,f22])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(flattening,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (10203)------------------------------
% 0.22/0.51  % (10203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (10203)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (10203)Memory used [KB]: 1791
% 0.22/0.51  % (10203)Time elapsed: 0.070 s
% 0.22/0.51  % (10203)------------------------------
% 0.22/0.51  % (10203)------------------------------
% 0.22/0.51  % (10185)Success in time 0.143 s
%------------------------------------------------------------------------------
