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
% DateTime   : Thu Dec  3 12:51:45 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   35 ( 188 expanded)
%              Number of leaves         :    4 (  37 expanded)
%              Depth                    :   14
%              Number of atoms          :  154 (1149 expanded)
%              Number of equality atoms :   39 ( 273 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f64,plain,(
    $false ),
    inference(global_subsumption,[],[f20,f41,f59,f61])).

fof(f61,plain,(
    r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(backward_demodulation,[],[f43,f59])).

fof(f43,plain,(
    r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) ),
    inference(unit_resulting_resolution,[],[f16,f17,f41,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

fof(f17,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( sK1 != k1_funct_1(sK2,sK0)
      | ~ r2_hidden(sK0,k1_relat_1(sK2))
      | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) )
    & ( ( sK1 = k1_funct_1(sK2,sK0)
        & r2_hidden(sK0,k1_relat_1(sK2)) )
      | r2_hidden(k4_tarski(sK0,sK1),sK2) )
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | r2_hidden(k4_tarski(X0,X1),X2) )
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( sK1 != k1_funct_1(sK2,sK0)
        | ~ r2_hidden(sK0,k1_relat_1(sK2))
        | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) )
      & ( ( sK1 = k1_funct_1(sK2,sK0)
          & r2_hidden(sK0,k1_relat_1(sK2)) )
        | r2_hidden(k4_tarski(sK0,sK1),sK2) )
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( k1_funct_1(X2,X0) != X1
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) )
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( k1_funct_1(X2,X0) != X1
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) )
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(k4_tarski(X0,X1),X2)
        <=> ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f16,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f59,plain,(
    sK1 = k1_funct_1(sK2,sK0) ),
    inference(duplicate_literal_removal,[],[f56])).

fof(f56,plain,
    ( sK1 = k1_funct_1(sK2,sK0)
    | sK1 = k1_funct_1(sK2,sK0) ),
    inference(resolution,[],[f38,f19])).

fof(f19,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | sK1 = k1_funct_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),sK2)
      | k1_funct_1(sK2,X1) = X2 ) ),
    inference(subsumption_resolution,[],[f37,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
      | r2_hidden(X0,k1_relat_1(sK2)) ) ),
    inference(resolution,[],[f16,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

fof(f37,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),sK2)
      | ~ r2_hidden(X1,k1_relat_1(sK2))
      | k1_funct_1(sK2,X1) = X2 ) ),
    inference(subsumption_resolution,[],[f33,f16])).

fof(f33,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),sK2)
      | ~ r2_hidden(X1,k1_relat_1(sK2))
      | k1_funct_1(sK2,X1) = X2
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f17,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(k4_tarski(X1,X2),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | k1_funct_1(X0,X1) = X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f41,plain,(
    r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(duplicate_literal_removal,[],[f40])).

fof(f40,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(resolution,[],[f30,f18])).

fof(f18,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f20,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | sK1 != k1_funct_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:49:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.47  % (8762)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.48  % (8754)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.48  % (8762)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(global_subsumption,[],[f20,f41,f59,f61])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 0.20/0.48    inference(backward_demodulation,[],[f43,f59])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f16,f17,f41,f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_funct_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)) | r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(equality_resolution,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2 | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(nnf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(flattening,[],[f7])).
% 0.20/0.48  fof(f7,plain,(
% 0.20/0.48    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    v1_funct_1(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    (sK1 != k1_funct_1(sK2,sK0) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(k4_tarski(sK0,sK1),sK2)) & ((sK1 = k1_funct_1(sK2,sK0) & r2_hidden(sK0,k1_relat_1(sK2))) | r2_hidden(k4_tarski(sK0,sK1),sK2)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ? [X0,X1,X2] : ((k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | r2_hidden(k4_tarski(X0,X1),X2)) & v1_funct_1(X2) & v1_relat_1(X2)) => ((sK1 != k1_funct_1(sK2,sK0) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(k4_tarski(sK0,sK1),sK2)) & ((sK1 = k1_funct_1(sK2,sK0) & r2_hidden(sK0,k1_relat_1(sK2))) | r2_hidden(k4_tarski(sK0,sK1),sK2)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ? [X0,X1,X2] : ((k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | r2_hidden(k4_tarski(X0,X1),X2)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.48    inference(flattening,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ? [X0,X1,X2] : ((((k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | r2_hidden(k4_tarski(X0,X1),X2))) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.48    inference(nnf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,plain,(
% 0.20/0.48    ? [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <~> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.48    inference(flattening,[],[f5])).
% 0.20/0.48  fof(f5,plain,(
% 0.20/0.48    ? [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <~> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.20/0.48    inference(negated_conjecture,[],[f3])).
% 0.20/0.48  fof(f3,conjecture,(
% 0.20/0.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    v1_relat_1(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    sK1 = k1_funct_1(sK2,sK0)),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f56])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    sK1 = k1_funct_1(sK2,sK0) | sK1 = k1_funct_1(sK2,sK0)),
% 0.20/0.48    inference(resolution,[],[f38,f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    r2_hidden(k4_tarski(sK0,sK1),sK2) | sK1 = k1_funct_1(sK2,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ( ! [X2,X1] : (~r2_hidden(k4_tarski(X1,X2),sK2) | k1_funct_1(sK2,X1) = X2) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f37,f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | r2_hidden(X0,k1_relat_1(sK2))) )),
% 0.20/0.48    inference(resolution,[],[f16,f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k1_relat_1(X2))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(flattening,[],[f9])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ( ! [X2,X1] : (~r2_hidden(k4_tarski(X1,X2),sK2) | ~r2_hidden(X1,k1_relat_1(sK2)) | k1_funct_1(sK2,X1) = X2) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f33,f16])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ( ! [X2,X1] : (~r2_hidden(k4_tarski(X1,X2),sK2) | ~r2_hidden(X1,k1_relat_1(sK2)) | k1_funct_1(sK2,X1) = X2 | ~v1_relat_1(sK2)) )),
% 0.20/0.48    inference(resolution,[],[f17,f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~r2_hidden(k4_tarski(X1,X2),X0) | ~r2_hidden(X1,k1_relat_1(X0)) | k1_funct_1(X0,X1) = X2 | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    r2_hidden(sK0,k1_relat_1(sK2))),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    r2_hidden(sK0,k1_relat_1(sK2)) | r2_hidden(sK0,k1_relat_1(sK2))),
% 0.20/0.48    inference(resolution,[],[f30,f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    r2_hidden(k4_tarski(sK0,sK1),sK2) | r2_hidden(sK0,k1_relat_1(sK2))),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ~r2_hidden(k4_tarski(sK0,sK1),sK2) | ~r2_hidden(sK0,k1_relat_1(sK2)) | sK1 != k1_funct_1(sK2,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (8762)------------------------------
% 0.20/0.48  % (8762)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (8762)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (8762)Memory used [KB]: 6140
% 0.20/0.48  % (8762)Time elapsed: 0.010 s
% 0.20/0.48  % (8762)------------------------------
% 0.20/0.48  % (8762)------------------------------
% 0.20/0.48  % (8746)Success in time 0.124 s
%------------------------------------------------------------------------------
