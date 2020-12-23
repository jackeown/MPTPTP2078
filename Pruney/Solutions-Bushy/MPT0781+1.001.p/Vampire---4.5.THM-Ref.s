%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0781+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:38 EST 2020

% Result     : Theorem 0.16s
% Output     : Refutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 255 expanded)
%              Number of leaves         :   12 (  66 expanded)
%              Depth                    :   20
%              Number of atoms          :  304 (1124 expanded)
%              Number of equality atoms :   49 ( 239 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f471,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f458,f467,f470])).

fof(f470,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f469])).

fof(f469,plain,
    ( $false
    | spl4_2 ),
    inference(subsumption_resolution,[],[f468,f28])).

fof(f28,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( sK0 != k2_wellord1(sK0,k3_relat_1(sK0))
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( k2_wellord1(X0,k3_relat_1(X0)) != X0
        & v1_relat_1(X0) )
   => ( sK0 != k2_wellord1(sK0,k3_relat_1(sK0))
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( k2_wellord1(X0,k3_relat_1(X0)) != X0
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k2_wellord1(X0,k3_relat_1(X0)) = X0 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_wellord1(X0,k3_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_wellord1)).

fof(f468,plain,
    ( ~ v1_relat_1(sK0)
    | spl4_2 ),
    inference(resolution,[],[f457,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(f457,plain,
    ( ~ v1_relat_1(k2_wellord1(sK0,k3_relat_1(sK0)))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f455])).

fof(f455,plain,
    ( spl4_2
  <=> v1_relat_1(k2_wellord1(sK0,k3_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f467,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f466])).

fof(f466,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f465,f28])).

fof(f465,plain,
    ( ~ v1_relat_1(sK0)
    | spl4_1 ),
    inference(resolution,[],[f460,f35])).

fof(f460,plain,
    ( ~ v1_relat_1(k2_wellord1(sK0,k3_relat_1(sK0)))
    | spl4_1 ),
    inference(subsumption_resolution,[],[f459,f29])).

fof(f29,plain,(
    sK0 != k2_wellord1(sK0,k3_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f459,plain,
    ( ~ v1_relat_1(k2_wellord1(sK0,k3_relat_1(sK0)))
    | sK0 = k2_wellord1(sK0,k3_relat_1(sK0))
    | spl4_1 ),
    inference(resolution,[],[f453,f416])).

fof(f416,plain,(
    ! [X1] :
      ( r2_hidden(sK1(k2_wellord1(sK0,X1),sK0),k3_relat_1(sK0))
      | ~ v1_relat_1(k2_wellord1(sK0,X1))
      | sK0 = k2_wellord1(sK0,X1) ) ),
    inference(subsumption_resolution,[],[f412,f28])).

fof(f412,plain,(
    ! [X1] :
      ( sK0 = k2_wellord1(sK0,X1)
      | ~ v1_relat_1(k2_wellord1(sK0,X1))
      | r2_hidden(sK1(k2_wellord1(sK0,X1),sK0),k3_relat_1(sK0))
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f386,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

fof(f386,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK1(k2_wellord1(sK0,X0),sK0),sK2(k2_wellord1(sK0,X0),sK0)),sK0)
      | sK0 = k2_wellord1(sK0,X0)
      | ~ v1_relat_1(k2_wellord1(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f377,f28])).

fof(f377,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK1(k2_wellord1(sK0,X0),sK0),sK2(k2_wellord1(sK0,X0),sK0)),sK0)
      | sK0 = k2_wellord1(sK0,X0)
      | ~ v1_relat_1(sK0)
      | ~ v1_relat_1(k2_wellord1(sK0,X0)) ) ),
    inference(factoring,[],[f59])).

fof(f59,plain,(
    ! [X2,X3] :
      ( r2_hidden(k4_tarski(sK1(k2_wellord1(sK0,X2),X3),sK2(k2_wellord1(sK0,X2),X3)),sK0)
      | r2_hidden(k4_tarski(sK1(k2_wellord1(sK0,X2),X3),sK2(k2_wellord1(sK0,X2),X3)),X3)
      | k2_wellord1(sK0,X2) = X3
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(k2_wellord1(sK0,X2)) ) ),
    inference(resolution,[],[f55,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
      | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
      | X0 = X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ( ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
                  | ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) )
                & ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
                  | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) )
                  & ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f18,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r2_hidden(k4_tarski(X2,X3),X0) )
          & ( r2_hidden(k4_tarski(X2,X3),X1)
            | r2_hidden(k4_tarski(X2,X3),X0) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
          | ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) )
        & ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
          | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | r2_hidden(k4_tarski(X2,X3),X0) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) )
                  & ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | r2_hidden(k4_tarski(X2,X3),X0) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( X0 = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X0)
              <=> r2_hidden(k4_tarski(X2,X3),X1) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( X0 = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X0)
              <=> r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_relat_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k2_wellord1(sK0,X0))
      | r2_hidden(X1,sK0) ) ),
    inference(superposition,[],[f51,f54])).

fof(f54,plain,(
    ! [X0] : k2_wellord1(sK0,X0) = k3_xboole_0(sK0,k2_zfmisc_1(X0,X0)) ),
    inference(resolution,[],[f28,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_wellord1)).

fof(f51,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f453,plain,
    ( ~ r2_hidden(sK1(k2_wellord1(sK0,k3_relat_1(sK0)),sK0),k3_relat_1(sK0))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f451])).

fof(f451,plain,
    ( spl4_1
  <=> r2_hidden(sK1(k2_wellord1(sK0,k3_relat_1(sK0)),sK0),k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f458,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f449,f455,f451])).

fof(f449,plain,
    ( ~ v1_relat_1(k2_wellord1(sK0,k3_relat_1(sK0)))
    | ~ r2_hidden(sK1(k2_wellord1(sK0,k3_relat_1(sK0)),sK0),k3_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f448,f29])).

fof(f448,plain,
    ( sK0 = k2_wellord1(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(k2_wellord1(sK0,k3_relat_1(sK0)))
    | ~ r2_hidden(sK1(k2_wellord1(sK0,k3_relat_1(sK0)),sK0),k3_relat_1(sK0)) ),
    inference(duplicate_literal_removal,[],[f444])).

fof(f444,plain,
    ( sK0 = k2_wellord1(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(k2_wellord1(sK0,k3_relat_1(sK0)))
    | ~ r2_hidden(sK1(k2_wellord1(sK0,k3_relat_1(sK0)),sK0),k3_relat_1(sK0))
    | ~ v1_relat_1(k2_wellord1(sK0,k3_relat_1(sK0)))
    | sK0 = k2_wellord1(sK0,k3_relat_1(sK0)) ),
    inference(resolution,[],[f443,f417])).

fof(f417,plain,(
    ! [X2] :
      ( r2_hidden(sK2(k2_wellord1(sK0,X2),sK0),k3_relat_1(sK0))
      | ~ v1_relat_1(k2_wellord1(sK0,X2))
      | sK0 = k2_wellord1(sK0,X2) ) ),
    inference(subsumption_resolution,[],[f413,f28])).

fof(f413,plain,(
    ! [X2] :
      ( sK0 = k2_wellord1(sK0,X2)
      | ~ v1_relat_1(k2_wellord1(sK0,X2))
      | r2_hidden(sK2(k2_wellord1(sK0,X2),sK0),k3_relat_1(sK0))
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f386,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f443,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK2(k2_wellord1(sK0,X1),sK0),X1)
      | sK0 = k2_wellord1(sK0,X1)
      | ~ v1_relat_1(k2_wellord1(sK0,X1))
      | ~ r2_hidden(sK1(k2_wellord1(sK0,X1),sK0),X1) ) ),
    inference(subsumption_resolution,[],[f441,f386])).

fof(f441,plain,(
    ! [X1] :
      ( ~ v1_relat_1(k2_wellord1(sK0,X1))
      | sK0 = k2_wellord1(sK0,X1)
      | ~ r2_hidden(k4_tarski(sK1(k2_wellord1(sK0,X1),sK0),sK2(k2_wellord1(sK0,X1),sK0)),sK0)
      | ~ r2_hidden(sK2(k2_wellord1(sK0,X1),sK0),X1)
      | ~ r2_hidden(sK1(k2_wellord1(sK0,X1),sK0),X1) ) ),
    inference(resolution,[],[f415,f72])).

fof(f72,plain,(
    ! [X6,X4,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k2_wellord1(sK0,X6))
      | ~ r2_hidden(k4_tarski(X4,X5),sK0)
      | ~ r2_hidden(X5,X6)
      | ~ r2_hidden(X4,X6) ) ),
    inference(resolution,[],[f57,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f57,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,k2_zfmisc_1(X4,X4))
      | r2_hidden(X5,k2_wellord1(sK0,X4))
      | ~ r2_hidden(X5,sK0) ) ),
    inference(superposition,[],[f49,f54])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f415,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK1(k2_wellord1(sK0,X0),sK0),sK2(k2_wellord1(sK0,X0),sK0)),k2_wellord1(sK0,X0))
      | ~ v1_relat_1(k2_wellord1(sK0,X0))
      | sK0 = k2_wellord1(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f414,f28])).

fof(f414,plain,(
    ! [X0] :
      ( sK0 = k2_wellord1(sK0,X0)
      | ~ v1_relat_1(k2_wellord1(sK0,X0))
      | ~ r2_hidden(k4_tarski(sK1(k2_wellord1(sK0,X0),sK0),sK2(k2_wellord1(sK0,X0),sK0)),k2_wellord1(sK0,X0))
      | ~ v1_relat_1(sK0) ) ),
    inference(duplicate_literal_removal,[],[f411])).

fof(f411,plain,(
    ! [X0] :
      ( sK0 = k2_wellord1(sK0,X0)
      | ~ v1_relat_1(k2_wellord1(sK0,X0))
      | sK0 = k2_wellord1(sK0,X0)
      | ~ r2_hidden(k4_tarski(sK1(k2_wellord1(sK0,X0),sK0),sK2(k2_wellord1(sK0,X0),sK0)),k2_wellord1(sK0,X0))
      | ~ v1_relat_1(sK0)
      | ~ v1_relat_1(k2_wellord1(sK0,X0)) ) ),
    inference(resolution,[],[f386,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
      | X0 = X1
      | ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

%------------------------------------------------------------------------------
