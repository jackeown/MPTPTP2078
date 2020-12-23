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
% DateTime   : Thu Dec  3 12:54:58 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 109 expanded)
%              Number of leaves         :   11 (  29 expanded)
%              Depth                    :   17
%              Number of atoms          :  162 ( 375 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f97,plain,(
    $false ),
    inference(resolution,[],[f88,f75])).

fof(f75,plain,(
    r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f74,f29])).

fof(f29,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f74,plain,
    ( r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f67,f33])).

fof(f33,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f67,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f66,f29])).

fof(f66,plain,
    ( r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f63,f34])).

fof(f34,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f63,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f62,f30])).

fof(f30,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f62,plain,
    ( r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f61,f26])).

fof(f26,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ v5_funct_1(k1_xboole_0,sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ~ v5_funct_1(k1_xboole_0,X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v5_funct_1(k1_xboole_0,sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => v5_funct_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v5_funct_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

fof(f61,plain,
    ( r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f59,f27])).

fof(f27,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f59,plain,
    ( r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f28,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v5_funct_1(X1,X0)
      | r2_hidden(sK1(X0,X1),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ( ~ r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1)))
                & r2_hidden(sK1(X0,X1),k1_relat_1(X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
          & r2_hidden(X2,k1_relat_1(X1)) )
     => ( ~ r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1)))
        & r2_hidden(sK1(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  & r2_hidden(X2,k1_relat_1(X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  & r2_hidden(X2,k1_relat_1(X1)) ) )
            & ( ! [X2] :
                  ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  | ~ r2_hidden(X2,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f28,plain,(
    ~ v5_funct_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f88,plain,(
    ! [X1] : ~ r2_hidden(sK1(sK0,k1_xboole_0),X1) ),
    inference(subsumption_resolution,[],[f87,f32])).

fof(f32,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f87,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,k1_xboole_0)
      | ~ r2_hidden(sK1(sK0,k1_xboole_0),X1) ) ),
    inference(resolution,[],[f75,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.15  % Command    : run_vampire %s %d
% 0.15/0.37  % Computer   : n007.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % WCLimit    : 600
% 0.15/0.37  % DateTime   : Tue Dec  1 16:41:06 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.24/0.47  % (15029)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.24/0.48  % (15037)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.24/0.49  % (15029)Refutation found. Thanks to Tanya!
% 0.24/0.49  % SZS status Theorem for theBenchmark
% 0.24/0.49  % SZS output start Proof for theBenchmark
% 0.24/0.49  fof(f97,plain,(
% 0.24/0.49    $false),
% 0.24/0.49    inference(resolution,[],[f88,f75])).
% 0.24/0.49  fof(f75,plain,(
% 0.24/0.49    r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0)),
% 0.24/0.49    inference(subsumption_resolution,[],[f74,f29])).
% 0.24/0.49  fof(f29,plain,(
% 0.24/0.49    v1_xboole_0(k1_xboole_0)),
% 0.24/0.49    inference(cnf_transformation,[],[f1])).
% 0.24/0.49  fof(f1,axiom,(
% 0.24/0.49    v1_xboole_0(k1_xboole_0)),
% 0.24/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.24/0.49  fof(f74,plain,(
% 0.24/0.49    r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0) | ~v1_xboole_0(k1_xboole_0)),
% 0.24/0.49    inference(resolution,[],[f67,f33])).
% 0.24/0.49  fof(f33,plain,(
% 0.24/0.49    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.24/0.49    inference(cnf_transformation,[],[f13])).
% 0.24/0.49  fof(f13,plain,(
% 0.24/0.49    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.24/0.49    inference(ennf_transformation,[],[f4])).
% 0.24/0.49  fof(f4,axiom,(
% 0.24/0.49    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.24/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.24/0.49  fof(f67,plain,(
% 0.24/0.49    ~v1_relat_1(k1_xboole_0) | r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0)),
% 0.24/0.49    inference(subsumption_resolution,[],[f66,f29])).
% 0.24/0.49  fof(f66,plain,(
% 0.24/0.49    r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_xboole_0(k1_xboole_0)),
% 0.24/0.49    inference(resolution,[],[f63,f34])).
% 0.24/0.49  fof(f34,plain,(
% 0.24/0.49    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 0.24/0.49    inference(cnf_transformation,[],[f14])).
% 0.24/0.49  fof(f14,plain,(
% 0.24/0.49    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 0.24/0.49    inference(ennf_transformation,[],[f6])).
% 0.24/0.49  fof(f6,axiom,(
% 0.24/0.49    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 0.24/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).
% 0.24/0.49  fof(f63,plain,(
% 0.24/0.49    ~v1_funct_1(k1_xboole_0) | r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.24/0.49    inference(forward_demodulation,[],[f62,f30])).
% 0.24/0.49  fof(f30,plain,(
% 0.24/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.24/0.49    inference(cnf_transformation,[],[f5])).
% 0.24/0.49  fof(f5,axiom,(
% 0.24/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.24/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.24/0.49  fof(f62,plain,(
% 0.24/0.49    r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.24/0.49    inference(subsumption_resolution,[],[f61,f26])).
% 0.24/0.49  fof(f26,plain,(
% 0.24/0.49    v1_relat_1(sK0)),
% 0.24/0.49    inference(cnf_transformation,[],[f19])).
% 0.24/0.49  fof(f19,plain,(
% 0.24/0.49    ~v5_funct_1(k1_xboole_0,sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.24/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f18])).
% 0.24/0.49  fof(f18,plain,(
% 0.24/0.49    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (~v5_funct_1(k1_xboole_0,sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.24/0.49    introduced(choice_axiom,[])).
% 0.24/0.49  fof(f12,plain,(
% 0.24/0.49    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.24/0.49    inference(flattening,[],[f11])).
% 0.24/0.49  fof(f11,plain,(
% 0.24/0.49    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.24/0.49    inference(ennf_transformation,[],[f9])).
% 0.24/0.49  fof(f9,negated_conjecture,(
% 0.24/0.49    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 0.24/0.49    inference(negated_conjecture,[],[f8])).
% 0.24/0.49  fof(f8,conjecture,(
% 0.24/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 0.24/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).
% 0.24/0.49  fof(f61,plain,(
% 0.24/0.49    r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0)),
% 0.24/0.49    inference(subsumption_resolution,[],[f59,f27])).
% 0.24/0.49  fof(f27,plain,(
% 0.24/0.49    v1_funct_1(sK0)),
% 0.24/0.49    inference(cnf_transformation,[],[f19])).
% 0.24/0.49  fof(f59,plain,(
% 0.24/0.49    r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 0.24/0.49    inference(resolution,[],[f28,f36])).
% 0.24/0.49  fof(f36,plain,(
% 0.24/0.49    ( ! [X0,X1] : (v5_funct_1(X1,X0) | r2_hidden(sK1(X0,X1),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.24/0.49    inference(cnf_transformation,[],[f23])).
% 0.24/0.49  fof(f23,plain,(
% 0.24/0.49    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | (~r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1))) & r2_hidden(sK1(X0,X1),k1_relat_1(X1)))) & (! [X3] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.24/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).
% 0.24/0.49  fof(f22,plain,(
% 0.24/0.49    ! [X1,X0] : (? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1))) => (~r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1))) & r2_hidden(sK1(X0,X1),k1_relat_1(X1))))),
% 0.24/0.49    introduced(choice_axiom,[])).
% 0.24/0.49  fof(f21,plain,(
% 0.24/0.49    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | ? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1)))) & (! [X3] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.24/0.49    inference(rectify,[],[f20])).
% 0.24/0.49  fof(f20,plain,(
% 0.24/0.49    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | ? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1)))) & (! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.24/0.49    inference(nnf_transformation,[],[f16])).
% 0.24/0.49  fof(f16,plain,(
% 0.24/0.49    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.24/0.49    inference(flattening,[],[f15])).
% 0.24/0.49  fof(f15,plain,(
% 0.24/0.49    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.24/0.49    inference(ennf_transformation,[],[f7])).
% 0.24/0.49  fof(f7,axiom,(
% 0.24/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))))))),
% 0.24/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).
% 0.24/0.49  fof(f28,plain,(
% 0.24/0.49    ~v5_funct_1(k1_xboole_0,sK0)),
% 0.24/0.49    inference(cnf_transformation,[],[f19])).
% 0.24/0.49  fof(f88,plain,(
% 0.24/0.49    ( ! [X1] : (~r2_hidden(sK1(sK0,k1_xboole_0),X1)) )),
% 0.24/0.49    inference(subsumption_resolution,[],[f87,f32])).
% 0.24/0.49  fof(f32,plain,(
% 0.24/0.49    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.24/0.49    inference(cnf_transformation,[],[f3])).
% 0.24/0.49  fof(f3,axiom,(
% 0.24/0.49    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.24/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.24/0.49  fof(f87,plain,(
% 0.24/0.49    ( ! [X1] : (~r1_xboole_0(X1,k1_xboole_0) | ~r2_hidden(sK1(sK0,k1_xboole_0),X1)) )),
% 0.24/0.49    inference(resolution,[],[f75,f40])).
% 0.24/0.49  fof(f40,plain,(
% 0.24/0.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.24/0.49    inference(cnf_transformation,[],[f25])).
% 0.24/0.49  fof(f25,plain,(
% 0.24/0.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.24/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f24])).
% 0.24/0.49  fof(f24,plain,(
% 0.24/0.49    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.24/0.49    introduced(choice_axiom,[])).
% 0.24/0.49  fof(f17,plain,(
% 0.24/0.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.24/0.49    inference(ennf_transformation,[],[f10])).
% 0.24/0.49  fof(f10,plain,(
% 0.24/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.24/0.49    inference(rectify,[],[f2])).
% 0.24/0.49  fof(f2,axiom,(
% 0.24/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.24/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.24/0.49  % SZS output end Proof for theBenchmark
% 0.24/0.49  % (15029)------------------------------
% 0.24/0.49  % (15029)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.24/0.49  % (15029)Termination reason: Refutation
% 0.24/0.49  
% 0.24/0.49  % (15029)Memory used [KB]: 1663
% 0.24/0.49  % (15029)Time elapsed: 0.048 s
% 0.24/0.49  % (15029)------------------------------
% 0.24/0.49  % (15029)------------------------------
% 0.24/0.49  % (15017)Success in time 0.107 s
%------------------------------------------------------------------------------
