%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t90_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:06 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 168 expanded)
%              Number of leaves         :    5 (  41 expanded)
%              Depth                    :   13
%              Number of atoms          :  155 ( 765 expanded)
%              Number of equality atoms :   22 ( 132 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1165,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1164,f1163])).

fof(f1163,plain,(
    r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),sK0) ),
    inference(subsumption_resolution,[],[f1144,f41])).

fof(f41,plain,(
    k1_relat_1(k7_relat_1(sK1,sK0)) != k3_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) != k3_xboole_0(k1_relat_1(sK1),sK0)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f28])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( k1_relat_1(k7_relat_1(X1,X0)) != k3_xboole_0(k1_relat_1(X1),X0)
        & v1_relat_1(X1) )
   => ( k1_relat_1(k7_relat_1(sK1,sK0)) != k3_xboole_0(k1_relat_1(sK1),sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) != k3_xboole_0(k1_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t90_relat_1.p',t90_relat_1)).

fof(f1144,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = k3_xboole_0(k1_relat_1(sK1),sK0)
    | r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),sK0) ),
    inference(resolution,[],[f1142,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t90_relat_1.p',d4_xboole_0)).

fof(f1142,plain,(
    ~ r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f1141,f61])).

fof(f61,plain,(
    ! [X2,X1] :
      ( r2_hidden(X1,X2)
      | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(sK1,X2))) ) ),
    inference(resolution,[],[f40,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t90_relat_1.p',t86_relat_1)).

fof(f40,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f1141,plain,
    ( ~ r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),sK0)
    | ~ r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f1140,f62])).

fof(f62,plain,(
    ! [X4,X3] :
      ( r2_hidden(X3,k1_relat_1(sK1))
      | ~ r2_hidden(X3,k1_relat_1(k7_relat_1(sK1,X4))) ) ),
    inference(resolution,[],[f40,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1140,plain,
    ( ~ r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),sK0)
    | ~ r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1))
    | ~ r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2] :
      ( k1_relat_1(k7_relat_1(sK1,sK0)) != X2
      | ~ r2_hidden(sK2(k1_relat_1(sK1),sK0,X2),sK0)
      | ~ r2_hidden(sK2(k1_relat_1(sK1),sK0,X2),k1_relat_1(sK1))
      | ~ r2_hidden(sK2(k1_relat_1(sK1),sK0,X2),X2) ) ),
    inference(superposition,[],[f41,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1164,plain,(
    ~ r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),sK0) ),
    inference(subsumption_resolution,[],[f1145,f1162])).

fof(f1162,plain,(
    r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f1143,f41])).

fof(f1143,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = k3_xboole_0(k1_relat_1(sK1),sK0)
    | r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1)) ),
    inference(resolution,[],[f1142,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1145,plain,
    ( ~ r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1))
    | ~ r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),sK0) ),
    inference(resolution,[],[f1142,f63])).

fof(f63,plain,(
    ! [X6,X5] :
      ( r2_hidden(X5,k1_relat_1(k7_relat_1(sK1,X6)))
      | ~ r2_hidden(X5,k1_relat_1(sK1))
      | ~ r2_hidden(X5,X6) ) ),
    inference(resolution,[],[f40,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
