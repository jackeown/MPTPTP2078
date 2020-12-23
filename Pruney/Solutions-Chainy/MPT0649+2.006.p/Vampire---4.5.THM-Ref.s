%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 274 expanded)
%              Number of leaves         :   12 (  68 expanded)
%              Depth                    :   26
%              Number of atoms          :  548 (1786 expanded)
%              Number of equality atoms :  118 ( 522 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f260,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f93,f145,f152,f162,f259])).

fof(f259,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f258])).

fof(f258,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f257,f26])).

fof(f26,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0)
      | sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) )
    & r2_hidden(sK0,k1_relat_1(sK1))
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0
          | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0 )
        & r2_hidden(X0,k1_relat_1(X1))
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0)
        | sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) )
      & r2_hidden(sK0,k1_relat_1(sK1))
      & v2_funct_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0
        | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0 )
      & r2_hidden(X0,k1_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0
        | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0 )
      & r2_hidden(X0,k1_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( r2_hidden(X0,k1_relat_1(X1))
            & v2_funct_1(X1) )
         => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
            & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).

fof(f257,plain,
    ( ~ v1_relat_1(sK1)
    | spl4_5 ),
    inference(subsumption_resolution,[],[f256,f27])).

fof(f27,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f256,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_5 ),
    inference(subsumption_resolution,[],[f255,f28])).

fof(f28,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

% (7620)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% (7610)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f255,plain,
    ( ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_5 ),
    inference(subsumption_resolution,[],[f254,f29])).

fof(f29,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f254,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_5 ),
    inference(resolution,[],[f253,f70])).

fof(f70,plain,(
    ! [X0,X5] :
      ( r2_hidden(k1_funct_1(X0,X5),k2_relat_1(X0))
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f69,f31])).

fof(f31,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f69,plain,(
    ! [X0,X5] :
      ( r2_hidden(k1_funct_1(X0,X5),k2_relat_1(X0))
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f54,f32])).

fof(f32,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X0,X5] :
      ( r2_hidden(k1_funct_1(X0,X5),k2_relat_1(X0))
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k1_funct_1(X0,X5),k2_relat_1(X0))
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X4,k2_relat_1(X0))
      | k1_funct_1(X0,X5) != X4
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ( ( sK3(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
                  | ~ r2_hidden(sK2(X0,X1),k2_relat_1(X0)) )
                & sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
                & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
              | ( ( sK2(X0,X1) != k1_funct_1(X0,sK3(X0,X1))
                  | ~ r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
                & sK3(X0,X1) = k1_funct_1(X1,sK2(X0,X1))
                & r2_hidden(sK2(X0,X1),k2_relat_1(X0)) )
              | k1_relat_1(X1) != k2_relat_1(X0) )
            & ( ( ! [X4,X5] :
                    ( ( ( k1_funct_1(X1,X4) = X5
                        & r2_hidden(X4,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X5) != X4
                      | ~ r2_hidden(X5,k1_relat_1(X0)) )
                    & ( ( k1_funct_1(X0,X5) = X4
                        & r2_hidden(X5,k1_relat_1(X0)) )
                      | k1_funct_1(X1,X4) != X5
                      | ~ r2_hidden(X4,k2_relat_1(X0)) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ( k1_funct_1(X1,X2) != X3
              | ~ r2_hidden(X2,k2_relat_1(X0)) )
            & k1_funct_1(X0,X3) = X2
            & r2_hidden(X3,k1_relat_1(X0)) )
          | ( ( k1_funct_1(X0,X3) != X2
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
            & k1_funct_1(X1,X2) = X3
            & r2_hidden(X2,k2_relat_1(X0)) ) )
     => ( ( ( sK3(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
            | ~ r2_hidden(sK2(X0,X1),k2_relat_1(X0)) )
          & sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
          & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
        | ( ( sK2(X0,X1) != k1_funct_1(X0,sK3(X0,X1))
            | ~ r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
          & sK3(X0,X1) = k1_funct_1(X1,sK2(X0,X1))
          & r2_hidden(sK2(X0,X1),k2_relat_1(X0)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) )
                    & k1_funct_1(X0,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ( ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & k1_funct_1(X1,X2) = X3
                    & r2_hidden(X2,k2_relat_1(X0)) ) )
              | k1_relat_1(X1) != k2_relat_1(X0) )
            & ( ( ! [X4,X5] :
                    ( ( ( k1_funct_1(X1,X4) = X5
                        & r2_hidden(X4,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X5) != X4
                      | ~ r2_hidden(X5,k1_relat_1(X0)) )
                    & ( ( k1_funct_1(X0,X5) = X4
                        & r2_hidden(X5,k1_relat_1(X0)) )
                      | k1_funct_1(X1,X4) != X5
                      | ~ r2_hidden(X4,k2_relat_1(X0)) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) )
                    & k1_funct_1(X0,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ( ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & k1_funct_1(X1,X2) = X3
                    & r2_hidden(X2,k2_relat_1(X0)) ) )
              | k1_relat_1(X1) != k2_relat_1(X0) )
            & ( ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                      | k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) )
                    & k1_funct_1(X0,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ( ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & k1_funct_1(X1,X2) = X3
                    & r2_hidden(X2,k2_relat_1(X0)) ) )
              | k1_relat_1(X1) != k2_relat_1(X0) )
            & ( ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                      | k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k1_relat_1(X1) = k2_relat_1(X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k1_relat_1(X1) = k2_relat_1(X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( k2_funct_1(X0) = X1
            <=> ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                     => ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) ) )
                    & ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                     => ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) ) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_funct_1)).

fof(f253,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | spl4_5 ),
    inference(subsumption_resolution,[],[f252,f28])).

fof(f252,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | ~ v2_funct_1(sK1)
    | spl4_5 ),
    inference(subsumption_resolution,[],[f251,f26])).

fof(f251,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ v2_funct_1(sK1)
    | spl4_5 ),
    inference(subsumption_resolution,[],[f250,f27])).

fof(f250,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v2_funct_1(sK1)
    | spl4_5 ),
    inference(subsumption_resolution,[],[f245,f29])).

fof(f245,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v2_funct_1(sK1)
    | spl4_5 ),
    inference(duplicate_literal_removal,[],[f244])).

fof(f244,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_5 ),
    inference(resolution,[],[f119,f144])).

fof(f144,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1))))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl4_5
  <=> r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_relat_1(k5_relat_1(X1,k2_funct_1(X0))))
      | ~ r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X0))
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f118,f31])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X0))
      | r2_hidden(X2,k1_relat_1(k5_relat_1(X1,k2_funct_1(X0))))
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f110,f32])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X0))
      | r2_hidden(X2,k1_relat_1(k5_relat_1(X1,k2_funct_1(X0))))
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f50,f76])).

fof(f76,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f75,f31])).

fof(f75,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f59,f32])).

fof(f59,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = k2_relat_1(X0)
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
      | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
              | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2)) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
              | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2)) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).

fof(f162,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f161])).

% (7607)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f161,plain,
    ( $false
    | spl4_4 ),
    inference(subsumption_resolution,[],[f160,f26])).

fof(f160,plain,
    ( ~ v1_relat_1(sK1)
    | spl4_4 ),
    inference(subsumption_resolution,[],[f159,f27])).

fof(f159,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_4 ),
    inference(resolution,[],[f141,f32])).

fof(f141,plain,
    ( ~ v1_funct_1(k2_funct_1(sK1))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl4_4
  <=> v1_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f152,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f150,f26])).

fof(f150,plain,
    ( ~ v1_relat_1(sK1)
    | spl4_3 ),
    inference(subsumption_resolution,[],[f149,f27])).

fof(f149,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_3 ),
    inference(resolution,[],[f138,f31])).

fof(f138,plain,
    ( ~ v1_relat_1(k2_funct_1(sK1))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl4_3
  <=> v1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f145,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f135,f64,f61,f143,f140,f137])).

fof(f61,plain,
    ( spl4_1
  <=> sK0 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f64,plain,
    ( spl4_2
  <=> sK0 = k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f135,plain,
    ( sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1))))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | spl4_2 ),
    inference(subsumption_resolution,[],[f134,f26])).

fof(f134,plain,
    ( sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1))))
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | spl4_2 ),
    inference(subsumption_resolution,[],[f125,f27])).

fof(f125,plain,
    ( sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1))))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | spl4_2 ),
    inference(superposition,[],[f65,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
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
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

fof(f65,plain,
    ( sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f93,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f92])).

fof(f92,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f91,f26])).

fof(f91,plain,
    ( ~ v1_relat_1(sK1)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f90,f27])).

fof(f90,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f89,f28])).

fof(f89,plain,
    ( ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f86,f29])).

fof(f86,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_1 ),
    inference(trivial_inequality_removal,[],[f82])).

fof(f82,plain,
    ( sK0 != sK0
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_1 ),
    inference(superposition,[],[f62,f68])).

fof(f68,plain,(
    ! [X0,X5] :
      ( k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X5)) = X5
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f67,f31])).

fof(f67,plain,(
    ! [X0,X5] :
      ( k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X5)) = X5
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f52,f32])).

fof(f52,plain,(
    ! [X0,X5] :
      ( k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X5)) = X5
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X1,k1_funct_1(X0,X5)) = X5
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X4,X0,X5,X1] :
      ( k1_funct_1(X1,X4) = X5
      | k1_funct_1(X0,X5) != X4
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f62,plain,
    ( sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f66,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f30,f64,f61])).

fof(f30,plain,
    ( sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0)
    | sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:03:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (7621)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.46  % (7611)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (7608)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.47  % (7613)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (7619)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (7608)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (7616)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f260,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f66,f93,f145,f152,f162,f259])).
% 0.21/0.50  fof(f259,plain,(
% 0.21/0.50    spl4_5),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f258])).
% 0.21/0.50  fof(f258,plain,(
% 0.21/0.50    $false | spl4_5),
% 0.21/0.50    inference(subsumption_resolution,[],[f257,f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    v1_relat_1(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    (sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0) | sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))) & r2_hidden(sK0,k1_relat_1(sK1)) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ? [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0 | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0) & r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => ((sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0) | sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))) & r2_hidden(sK0,k1_relat_1(sK1)) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f8,plain,(
% 0.21/0.50    ? [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0 | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0) & r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f7])).
% 0.21/0.50  fof(f7,plain,(
% 0.21/0.50    ? [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0 | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0) & (r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 0.21/0.50    inference(negated_conjecture,[],[f5])).
% 0.21/0.50  fof(f5,conjecture,(
% 0.21/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).
% 0.21/0.50  fof(f257,plain,(
% 0.21/0.50    ~v1_relat_1(sK1) | spl4_5),
% 0.21/0.50    inference(subsumption_resolution,[],[f256,f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    v1_funct_1(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f256,plain,(
% 0.21/0.50    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_5),
% 0.21/0.50    inference(subsumption_resolution,[],[f255,f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    v2_funct_1(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  % (7620)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (7610)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  fof(f255,plain,(
% 0.21/0.50    ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_5),
% 0.21/0.50    inference(subsumption_resolution,[],[f254,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f254,plain,(
% 0.21/0.50    ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_5),
% 0.21/0.50    inference(resolution,[],[f253,f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X0,X5] : (r2_hidden(k1_funct_1(X0,X5),k2_relat_1(X0)) | ~r2_hidden(X5,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f69,f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ( ! [X0,X5] : (r2_hidden(k1_funct_1(X0,X5),k2_relat_1(X0)) | ~r2_hidden(X5,k1_relat_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f54,f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X0,X5] : (r2_hidden(k1_funct_1(X0,X5),k2_relat_1(X0)) | ~r2_hidden(X5,k1_relat_1(X0)) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X0,X5,X1] : (r2_hidden(k1_funct_1(X0,X5),k2_relat_1(X0)) | ~r2_hidden(X5,k1_relat_1(X0)) | k2_funct_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X4,X0,X5,X1] : (r2_hidden(X4,k2_relat_1(X0)) | k1_funct_1(X0,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X0)) | k2_funct_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | (((sK3(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) | ~r2_hidden(sK2(X0,X1),k2_relat_1(X0))) & sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | ((sK2(X0,X1) != k1_funct_1(X0,sK3(X0,X1)) | ~r2_hidden(sK3(X0,X1),k1_relat_1(X0))) & sK3(X0,X1) = k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k2_relat_1(X0)))) | k1_relat_1(X1) != k2_relat_1(X0)) & ((! [X4,X5] : (((k1_funct_1(X1,X4) = X5 & r2_hidden(X4,k2_relat_1(X0))) | k1_funct_1(X0,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X0))) & ((k1_funct_1(X0,X5) = X4 & r2_hidden(X5,k1_relat_1(X0))) | k1_funct_1(X1,X4) != X5 | ~r2_hidden(X4,k2_relat_1(X0)))) & k1_relat_1(X1) = k2_relat_1(X0)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f21,f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ((k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) => (((sK3(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) | ~r2_hidden(sK2(X0,X1),k2_relat_1(X0))) & sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | ((sK2(X0,X1) != k1_funct_1(X0,sK3(X0,X1)) | ~r2_hidden(sK3(X0,X1),k1_relat_1(X0))) & sK3(X0,X1) = k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k2_relat_1(X0)))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | ? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ((k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) | k1_relat_1(X1) != k2_relat_1(X0)) & ((! [X4,X5] : (((k1_funct_1(X1,X4) = X5 & r2_hidden(X4,k2_relat_1(X0))) | k1_funct_1(X0,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X0))) & ((k1_funct_1(X0,X5) = X4 & r2_hidden(X5,k1_relat_1(X0))) | k1_funct_1(X1,X4) != X5 | ~r2_hidden(X4,k2_relat_1(X0)))) & k1_relat_1(X1) = k2_relat_1(X0)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(rectify,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | ? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ((k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) | k1_relat_1(X1) != k2_relat_1(X0)) & ((! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)))) & k1_relat_1(X1) = k2_relat_1(X0)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | (? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ((k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) | k1_relat_1(X1) != k2_relat_1(X0))) & ((! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)))) & k1_relat_1(X1) = k2_relat_1(X0)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)))) & k1_relat_1(X1) = k2_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0] : ((! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | (k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))))) & k1_relat_1(X1) = k2_relat_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) => (k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) & ((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) => (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) & k1_relat_1(X1) = k2_relat_1(X0))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_funct_1)).
% 0.21/0.50  fof(f253,plain,(
% 0.21/0.50    ~r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) | spl4_5),
% 0.21/0.50    inference(subsumption_resolution,[],[f252,f28])).
% 0.21/0.50  fof(f252,plain,(
% 0.21/0.50    ~r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) | ~v2_funct_1(sK1) | spl4_5),
% 0.21/0.50    inference(subsumption_resolution,[],[f251,f26])).
% 0.21/0.50  fof(f251,plain,(
% 0.21/0.50    ~r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) | ~v1_relat_1(sK1) | ~v2_funct_1(sK1) | spl4_5),
% 0.21/0.50    inference(subsumption_resolution,[],[f250,f27])).
% 0.21/0.50  fof(f250,plain,(
% 0.21/0.50    ~r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v2_funct_1(sK1) | spl4_5),
% 0.21/0.50    inference(subsumption_resolution,[],[f245,f29])).
% 0.21/0.50  fof(f245,plain,(
% 0.21/0.50    ~r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) | ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v2_funct_1(sK1) | spl4_5),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f244])).
% 0.21/0.50  fof(f244,plain,(
% 0.21/0.50    ~r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) | ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_5),
% 0.21/0.50    inference(resolution,[],[f119,f144])).
% 0.21/0.50  fof(f144,plain,(
% 0.21/0.50    ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1)))) | spl4_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f143])).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    spl4_5 <=> r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(X2,k1_relat_1(k5_relat_1(X1,k2_funct_1(X0)))) | ~r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X0)) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f118,f31])).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X0)) | r2_hidden(X2,k1_relat_1(k5_relat_1(X1,k2_funct_1(X0)))) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f110,f32])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X0)) | r2_hidden(X2,k1_relat_1(k5_relat_1(X1,k2_funct_1(X0)))) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(superposition,[],[f50,f76])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f75,f31])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f59,f32])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_relat_1(X1) = k2_relat_1(X0) | k2_funct_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | (~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2)))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    spl4_4),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f161])).
% 0.21/0.50  % (7607)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    $false | spl4_4),
% 0.21/0.50    inference(subsumption_resolution,[],[f160,f26])).
% 0.21/0.50  fof(f160,plain,(
% 0.21/0.50    ~v1_relat_1(sK1) | spl4_4),
% 0.21/0.50    inference(subsumption_resolution,[],[f159,f27])).
% 0.21/0.50  fof(f159,plain,(
% 0.21/0.50    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_4),
% 0.21/0.50    inference(resolution,[],[f141,f32])).
% 0.21/0.50  fof(f141,plain,(
% 0.21/0.50    ~v1_funct_1(k2_funct_1(sK1)) | spl4_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f140])).
% 0.21/0.50  fof(f140,plain,(
% 0.21/0.50    spl4_4 <=> v1_funct_1(k2_funct_1(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.50  fof(f152,plain,(
% 0.21/0.50    spl4_3),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f151])).
% 0.21/0.50  fof(f151,plain,(
% 0.21/0.50    $false | spl4_3),
% 0.21/0.50    inference(subsumption_resolution,[],[f150,f26])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    ~v1_relat_1(sK1) | spl4_3),
% 0.21/0.50    inference(subsumption_resolution,[],[f149,f27])).
% 0.21/0.50  fof(f149,plain,(
% 0.21/0.50    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_3),
% 0.21/0.50    inference(resolution,[],[f138,f31])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    ~v1_relat_1(k2_funct_1(sK1)) | spl4_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f137])).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    spl4_3 <=> v1_relat_1(k2_funct_1(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.50  fof(f145,plain,(
% 0.21/0.50    ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_1 | spl4_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f135,f64,f61,f143,f140,f137])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    spl4_1 <=> sK0 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    spl4_2 <=> sK0 = k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.50  fof(f135,plain,(
% 0.21/0.50    sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1)))) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | spl4_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f134,f26])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1)))) | ~v1_relat_1(sK1) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | spl4_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f125,f27])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1)))) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | spl4_2),
% 0.21/0.50    inference(superposition,[],[f65,f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0) | spl4_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f64])).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    spl4_1),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f92])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    $false | spl4_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f91,f26])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    ~v1_relat_1(sK1) | spl4_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f90,f27])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f89,f28])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f86,f29])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_1),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f82])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    sK0 != sK0 | ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_1),
% 0.21/0.50    inference(superposition,[],[f62,f68])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ( ! [X0,X5] : (k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X5)) = X5 | ~r2_hidden(X5,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f67,f31])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ( ! [X0,X5] : (k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X5)) = X5 | ~r2_hidden(X5,k1_relat_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f52,f32])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X0,X5] : (k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X5)) = X5 | ~r2_hidden(X5,k1_relat_1(X0)) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X0,X5,X1] : (k1_funct_1(X1,k1_funct_1(X0,X5)) = X5 | ~r2_hidden(X5,k1_relat_1(X0)) | k2_funct_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X4,X0,X5,X1] : (k1_funct_1(X1,X4) = X5 | k1_funct_1(X0,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X0)) | k2_funct_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) | spl4_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f61])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ~spl4_1 | ~spl4_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f30,f64,f61])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0) | sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (7608)------------------------------
% 0.21/0.50  % (7608)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (7608)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (7608)Memory used [KB]: 10746
% 0.21/0.50  % (7608)Time elapsed: 0.071 s
% 0.21/0.50  % (7608)------------------------------
% 0.21/0.50  % (7608)------------------------------
% 0.21/0.50  % (7605)Success in time 0.145 s
%------------------------------------------------------------------------------
