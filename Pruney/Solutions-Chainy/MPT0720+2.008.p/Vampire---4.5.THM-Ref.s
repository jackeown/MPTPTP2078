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
% DateTime   : Thu Dec  3 12:55:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   43 (  81 expanded)
%              Number of leaves         :    6 (  15 expanded)
%              Depth                    :   13
%              Number of atoms          :  148 ( 352 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f68,plain,(
    $false ),
    inference(subsumption_resolution,[],[f66,f20])).

fof(f20,plain,(
    ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X0))
          & v5_funct_1(X1,X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X0))
          & v5_funct_1(X1,X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v5_funct_1(X1,X0)
              & v1_funct_1(X1)
              & v1_relat_1(X1) )
           => r1_tarski(k1_relat_1(X1),k1_relat_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v5_funct_1(X1,X0)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
         => r1_tarski(k1_relat_1(X1),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_1)).

fof(f66,plain,(
    r1_tarski(k1_relat_1(sK1),k1_relat_1(sK0)) ),
    inference(resolution,[],[f65,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
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

fof(f65,plain,(
    ~ r2_hidden(sK3(k1_relat_1(sK1),k1_relat_1(sK0)),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f64,f39])).

fof(f39,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f33,f23])).

fof(f23,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f64,plain,
    ( r2_hidden(k1_funct_1(sK1,sK3(k1_relat_1(sK1),k1_relat_1(sK0))),k1_xboole_0)
    | ~ r2_hidden(sK3(k1_relat_1(sK1),k1_relat_1(sK0)),k1_relat_1(sK1)) ),
    inference(superposition,[],[f63,f45])).

fof(f45,plain,(
    k1_xboole_0 = k1_funct_1(sK0,sK3(k1_relat_1(sK1),k1_relat_1(sK0))) ),
    inference(subsumption_resolution,[],[f44,f22])).

fof(f22,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f44,plain,
    ( k1_xboole_0 = k1_funct_1(sK0,sK3(k1_relat_1(sK1),k1_relat_1(sK0)))
    | ~ v1_funct_1(sK0) ),
    inference(subsumption_resolution,[],[f43,f21])).

fof(f21,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f43,plain,
    ( ~ v1_relat_1(sK0)
    | k1_xboole_0 = k1_funct_1(sK0,sK3(k1_relat_1(sK1),k1_relat_1(sK0)))
    | ~ v1_funct_1(sK0) ),
    inference(resolution,[],[f41,f20])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k1_funct_1(X0,sK3(X1,k1_relat_1(X0)))
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f35,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k1_funct_1(X0,X1) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(X1,k1_relat_1(X0))
      | k1_xboole_0 = X2
      | k1_funct_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

fof(f63,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK1,X0),k1_funct_1(sK0,X0))
      | ~ r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f62,f21])).

fof(f62,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | r2_hidden(k1_funct_1(sK1,X0),k1_funct_1(sK0,X0))
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f61,f18])).

fof(f18,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK1)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | r2_hidden(k1_funct_1(sK1,X0),k1_funct_1(sK0,X0))
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f60,f17])).

fof(f17,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | ~ v1_funct_1(sK1)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | r2_hidden(k1_funct_1(sK1,X0),k1_funct_1(sK0,X0))
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f59,f22])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK0)
      | ~ v1_relat_1(sK1)
      | ~ v1_funct_1(sK1)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | r2_hidden(k1_funct_1(sK1,X0),k1_funct_1(sK0,X0))
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f24,f19])).

fof(f19,plain,(
    v5_funct_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_funct_1(X1,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,k1_relat_1(X1))
               => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:52:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (22063)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (22063)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(subsumption_resolution,[],[f66,f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK0))),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (~r1_tarski(k1_relat_1(X1),k1_relat_1(X0)) & v5_funct_1(X1,X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f9])).
% 0.20/0.51  fof(f9,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (~r1_tarski(k1_relat_1(X1),k1_relat_1(X0)) & (v5_funct_1(X1,X0) & v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,negated_conjecture,(
% 0.20/0.51    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v5_funct_1(X1,X0) & v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k1_relat_1(X1),k1_relat_1(X0))))),
% 0.20/0.51    inference(negated_conjecture,[],[f6])).
% 0.20/0.51  fof(f6,conjecture,(
% 0.20/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v5_funct_1(X1,X0) & v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k1_relat_1(X1),k1_relat_1(X0))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_1)).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    r1_tarski(k1_relat_1(sK1),k1_relat_1(sK0))),
% 0.20/0.51    inference(resolution,[],[f65,f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,plain,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 0.20/0.51    inference(unused_predicate_definition_removal,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.51  fof(f65,plain,(
% 0.20/0.51    ~r2_hidden(sK3(k1_relat_1(sK1),k1_relat_1(sK0)),k1_relat_1(sK1))),
% 0.20/0.51    inference(subsumption_resolution,[],[f64,f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.51    inference(resolution,[],[f33,f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r1_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    r2_hidden(k1_funct_1(sK1,sK3(k1_relat_1(sK1),k1_relat_1(sK0))),k1_xboole_0) | ~r2_hidden(sK3(k1_relat_1(sK1),k1_relat_1(sK0)),k1_relat_1(sK1))),
% 0.20/0.51    inference(superposition,[],[f63,f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    k1_xboole_0 = k1_funct_1(sK0,sK3(k1_relat_1(sK1),k1_relat_1(sK0)))),
% 0.20/0.51    inference(subsumption_resolution,[],[f44,f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    v1_funct_1(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    k1_xboole_0 = k1_funct_1(sK0,sK3(k1_relat_1(sK1),k1_relat_1(sK0))) | ~v1_funct_1(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f43,f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    v1_relat_1(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ~v1_relat_1(sK0) | k1_xboole_0 = k1_funct_1(sK0,sK3(k1_relat_1(sK1),k1_relat_1(sK0))) | ~v1_funct_1(sK0)),
% 0.20/0.51    inference(resolution,[],[f41,f20])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X1,k1_relat_1(X0)) | ~v1_relat_1(X0) | k1_xboole_0 = k1_funct_1(X0,sK3(X1,k1_relat_1(X0))) | ~v1_funct_1(X0)) )),
% 0.20/0.51    inference(resolution,[],[f35,f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = k1_funct_1(X0,X1)) )),
% 0.20/0.51    inference(equality_resolution,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(X1,k1_relat_1(X0)) | k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(k1_funct_1(sK1,X0),k1_funct_1(sK0,X0)) | ~r2_hidden(X0,k1_relat_1(sK1))) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f62,f21])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | r2_hidden(k1_funct_1(sK1,X0),k1_funct_1(sK0,X0)) | ~v1_relat_1(sK0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f61,f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    v1_funct_1(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_funct_1(sK1) | ~r2_hidden(X0,k1_relat_1(sK1)) | r2_hidden(k1_funct_1(sK1,X0),k1_funct_1(sK0,X0)) | ~v1_relat_1(sK0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f60,f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    v1_relat_1(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~r2_hidden(X0,k1_relat_1(sK1)) | r2_hidden(k1_funct_1(sK1,X0),k1_funct_1(sK0,X0)) | ~v1_relat_1(sK0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f59,f22])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_funct_1(sK0) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~r2_hidden(X0,k1_relat_1(sK1)) | r2_hidden(k1_funct_1(sK1,X0),k1_funct_1(sK0,X0)) | ~v1_relat_1(sK0)) )),
% 0.20/0.51    inference(resolution,[],[f24,f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    v5_funct_1(sK1,sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v5_funct_1(X1,X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (22063)------------------------------
% 0.20/0.51  % (22063)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (22063)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (22063)Memory used [KB]: 6268
% 0.20/0.51  % (22063)Time elapsed: 0.106 s
% 0.20/0.51  % (22063)------------------------------
% 0.20/0.51  % (22063)------------------------------
% 0.20/0.51  % (22082)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.52  % (22057)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (22057)Refutation not found, incomplete strategy% (22057)------------------------------
% 0.20/0.52  % (22057)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (22057)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (22057)Memory used [KB]: 1663
% 0.20/0.52  % (22057)Time elapsed: 0.108 s
% 0.20/0.52  % (22057)------------------------------
% 0.20/0.52  % (22057)------------------------------
% 0.20/0.52  % (22072)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (22058)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (22079)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (22068)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (22079)Refutation not found, incomplete strategy% (22079)------------------------------
% 0.20/0.52  % (22079)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (22079)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (22079)Memory used [KB]: 10746
% 0.20/0.52  % (22079)Time elapsed: 0.120 s
% 0.20/0.52  % (22079)------------------------------
% 0.20/0.52  % (22079)------------------------------
% 0.20/0.53  % (22074)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.53  % (22061)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (22083)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (22056)Success in time 0.171 s
%------------------------------------------------------------------------------
